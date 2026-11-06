import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.Lie.PrimePowerCentralizer
import Langlands.GroupScheme.Lie.UnipotentTangent
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Torus.Weights

/-! # Prime powers of Lie elements under field extension -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section RepresentationBaseChange

variable {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

/-- The scalar extension of a matrix representation has, on affine points of the base change,
the matrices of the original representation on the corresponding points. -/
theorem MatrixRepresentation.affineMatrix_baseChange (ρ : MatrixRepresentation G (Fin n))
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (x : Lie.AffinePoints G_K A) :
    (((ρ.baseChange (algebraBaseMap k K)).affineMatrix (CommAlgCat.of (CommRingCat.of K) A) x :
        GL (Fin n) A) : Matrix (Fin n) (Fin n) A) =
      ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A)
        (Lie.affineBaseChangeEquiv k K G A x) := by
  have h₁ := ρ.pointMatrix_baseChange (algebraBaseMap k K)
    ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of (CommRingCat.of K) A))) x
  have h₂ := ρ.pointMatrix_naturality (Lie.affineBaseTestIso k K A).inv
    (GroupScheme.baseChangePointsEquiv (algebraBaseMap k K) G _ x)
  rw [MatrixRepresentation.pointMatrix_eq_affineMatrix] at h₁ h₂
  rw [← h₁] at h₂
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
  ext i j
  apply hinj
  have h := congrArg (fun M => M.1 i j) h₂
  exact h.symm

/-- The scalar extension of a matrix representation has, on tangent vectors of the base
change, the tangent matrices of the original representation on the corresponding vectors. -/
theorem MatrixRepresentation.tangentMatrix_baseChange (ρ : MatrixRepresentation G (Fin n))
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (X : lieKernel G_K A) :
    (ρ.baseChange (algebraBaseMap k K)).tangentMatrix A X =
      ρ.tangentMatrix A (Lie.kernelBaseChangeEquiv k K G A X) := by
  have h := ρ.affineMatrix_baseChange (DualNumber A) X.val
  have h₁ := (ρ.baseChange (algebraBaseMap k K)).affineMatrix_lieKernel A X
  have h₂ := ρ.affineMatrix_lieKernel A (Lie.kernelBaseChangeEquiv k K G A X)
  rw [Lie.kernelBaseChangeEquiv_val] at h₂
  rw [h₁, h₂] at h
  have h₃ := congrArg GeneralLinear.DualNumber.coefficients (Units.ext h)
  rwa [GeneralLinear.DualNumber.coefficients_matrixUnit,
    GeneralLinear.DualNumber.coefficients_matrixUnit] at h₃

end RepresentationBaseChange

section Injective

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : ℕ}

/-- A monomorphic representation has injective tangent matrices on every coefficient algebra. -/
theorem MatrixRepresentation.tangentMatrix_injective (ρ : MatrixRepresentation G (Fin n))
    (hρ : Mono ρ.hom.hom) (A : Type u) [CommRing A] [Algebra R A] :
    Function.Injective (ρ.tangentMatrix A) := fun _ _ h =>
  lieKernelTarget_injective ρ A hρ
    (GeneralLinear.DualNumber.pointKernelEquiv.symm.injective h)

/-- The tangent matrix of a conjugated tangent vector is the conjugated tangent matrix. -/
theorem MatrixRepresentation.tangentMatrix_conjugation (ρ : MatrixRepresentation G (Fin n))
    (A : Type u) [CommRing A] [Algebra R A] (g : Lie.AffinePoints G A) (X : lieKernel G A) :
    ρ.tangentMatrix A (lieKernelConjugation G g X) =
      (ρ.affineMatrix (CommAlgCat.of R A) g : Matrix (Fin n) (Fin n) A) * ρ.tangentMatrix A X *
        (((ρ.affineMatrix (CommAlgCat.of R A) g)⁻¹ : GL (Fin n) A) :
          Matrix (Fin n) (Fin n) A) := by
  have hX := ρ.pointKernelEquiv_tangentMatrix A X
  change GeneralLinear.DualNumber.pointKernelEquiv.symm
    (Lie.targetMap ρ A (lieKernelConjugation G g X)) = _
  rw [Lie.targetMap_conjugation, ← hX, Equiv.symm_apply_eq]
  apply Subtype.ext
  exact GeneralLinear.DualNumber.pointUnit_conjugation (g ≫ ρ.hom.hom) (ρ.tangentMatrix A X)

end Injective

section FieldPrimePower

variable (k : Type u) [CommRing k] (F : Type u) [CommRing F] [Algebra k F]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance primePowerFieldExtensionIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k F)).obj G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k F))
  infer_instance

/-- The `p ^ r`-th restricted power of a tangent vector of `G` with coefficients in `F`:
the prime-power Lie element of the base change `G_F` at the corresponding `F`-rational tangent
vector, transported back to the coefficient-`F` tangent vectors of `G`. -/
def fieldPrimePower (X : lieKernel G F) (p r : ℕ) [Fact p.Prime] [CharP F p] : lieKernel G F :=
  Lie.kernelBaseChangeEquiv k F G F
    (Lie.primePowerKernel ((GroupScheme.baseChange (algebraBaseMap k F)).obj G)
      ((Lie.kernelBaseChangeEquiv k F G F).symm X) p r)

variable {k F G}

/-- Every representation of `G` sends the field prime power to the same power of the tangent
matrix. -/
theorem MatrixRepresentation.tangentMatrix_fieldPrimePower {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n)) (X : lieKernel G F) (p r : ℕ) [Fact p.Prime]
    [CharP F p] :
    ρ.tangentMatrix F (fieldPrimePower k F G X p r) = ρ.tangentMatrix F X ^ (p ^ r) := by
  have h₁ := ρ.tangentMatrix_baseChange (K := F) F
    (Lie.primePowerKernel ((GroupScheme.baseChange (algebraBaseMap k F)).obj G)
      ((Lie.kernelBaseChangeEquiv k F G F).symm X) p r)
  have h₂ := (ρ.baseChange (algebraBaseMap k F)).tangentMatrix_primePowerKernel
    ((Lie.kernelBaseChangeEquiv k F G F).symm X) p r
  have h₃ := ρ.tangentMatrix_baseChange (K := F) F ((Lie.kernelBaseChangeEquiv k F G F).symm X)
  rw [MulEquiv.apply_symm_apply] at h₃
  rw [fieldPrimePower, ← h₁]
  exact h₂.trans (congrArg (· ^ (p ^ r)) h₃)

/-- Field prime powers commute with coefficient change, given a monomorphic representation. -/
theorem lieKernelMap_fieldPrimePower_of_mono {n : ℕ} (ρ : MatrixRepresentation G (Fin n))
    (hρ : Mono ρ.hom.hom) {F' : Type u} [CommRing F'] [Algebra k F'] (φ : F →ₐ[k] F')
    (X : lieKernel G F) (p r : ℕ) [Fact p.Prime] [CharP F p] [CharP F' p] :
    lieKernelMap G φ (fieldPrimePower k F G X p r) =
      fieldPrimePower k F' G (lieKernelMap G φ X) p r := by
  apply ρ.tangentMatrix_injective hρ F'
  rw [ρ.tangentMatrix_naturality, ρ.tangentMatrix_fieldPrimePower,
    ρ.tangentMatrix_fieldPrimePower, ρ.tangentMatrix_naturality]
  exact Matrix.map_pow _ φ.toRingHom _

/-- Field prime powers commute with constant-point conjugation, given a monomorphic
representation. -/
theorem lieKernelConjugation_fieldPrimePower_of_mono {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n)) (hρ : Mono ρ.hom.hom) (g : Lie.AffinePoints G F)
    (X : lieKernel G F) (p r : ℕ) [Fact p.Prime] [CharP F p] :
    lieKernelConjugation G g (fieldPrimePower k F G X p r) =
      fieldPrimePower k F G (lieKernelConjugation G g X) p r := by
  apply ρ.tangentMatrix_injective hρ F
  rw [ρ.tangentMatrix_conjugation, ρ.tangentMatrix_fieldPrimePower,
    ρ.tangentMatrix_fieldPrimePower, ρ.tangentMatrix_conjugation, Units.conj_pow]

end FieldPrimePower

section FieldEmbedding

variable {k : Type u} [Field k] {F : Type u} [CommRing F] [Algebra k F]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- An affine group of finite type over a field has a monomorphic matrix representation. -/
theorem exists_mono_matrixRepresentation :
    ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), Mono ρ.hom.hom := by
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  exact ⟨n, ρ, Over.mono_of_mono_left _⟩

/-- Over a field, field prime powers commute with coefficient change. -/
theorem lieKernelMap_fieldPrimePower {F' : Type u} [CommRing F'] [Algebra k F']
    (φ : F →ₐ[k] F') (X : lieKernel G F) (p r : ℕ) [Fact p.Prime] [CharP F p] [CharP F' p] :
    lieKernelMap G φ (fieldPrimePower k F G X p r) =
      fieldPrimePower k F' G (lieKernelMap G φ X) p r := by
  obtain ⟨n, ρ, hρ⟩ := exists_mono_matrixRepresentation (G := G)
  exact lieKernelMap_fieldPrimePower_of_mono ρ hρ φ X p r

/-- Over a field, field prime powers commute with constant-point conjugation. -/
theorem lieKernelConjugation_fieldPrimePower (g : Lie.AffinePoints G F) (X : lieKernel G F)
    (p r : ℕ) [Fact p.Prime] [CharP F p] :
    lieKernelConjugation G g (fieldPrimePower k F G X p r) =
      fieldPrimePower k F G (lieKernelConjugation G g X) p r := by
  obtain ⟨n, ρ, hρ⟩ := exists_mono_matrixRepresentation (G := G)
  exact lieKernelConjugation_fieldPrimePower_of_mono ρ hρ g X p r

end FieldEmbedding

section Relation

variable {k : Type u} [CommRing k] {F : Type u} [Field F] [Algebra k F]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A finite linear relation over the coefficient field `F` among the field prime powers of
`X`, whose coefficient at its first exponent `m` is nonzero. -/
def HasPrimePowerRelation (X : lieKernel G F) (p m : ℕ) [Fact p.Prime] [CharP F p] : Prop :=
  ∃ (s : Finset ℕ) (c : ℕ → F), m ∈ s ∧ (∀ i ∈ s, m ≤ i) ∧ c m ≠ 0 ∧
    ∑ i ∈ s, c i • Additive.ofMul (fieldPrimePower k F G X p i) = 0

local instance primePowerRelationIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k F)).obj G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k F))
  infer_instance

/-- Some field prime power of every tangent vector satisfies a prime-power relation. -/
theorem exists_hasPrimePowerRelation [LocallyOfFiniteType G.X.hom] (X : lieKernel G F)
    (p : ℕ) [Fact p.Prime] [CharP F p] : ∃ m : ℕ, HasPrimePowerRelation X p m := by
  classical
  have : LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k F)).obj G).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd G.X.hom (algebraBaseMap k F))
    infer_instance
  have : FiniteDimensional F (Additive (lieKernel G F)) :=
    (Lie.kernelBaseChangeLinearEquiv k F G F).finiteDimensional
  have hdep := Module.Finite.not_linearIndependent_of_infinite (R := F)
    (fun r : ℕ => Additive.ofMul (fieldPrimePower k F G X p r))
  obtain ⟨c, hrel, hc⟩ := not_linearIndependent_iff_finsupp.mp hdep
  have hs : c.support.Nonempty := Finsupp.support_nonempty_iff.mpr hc
  have hm : c.support.min' hs ∈ c.support := Finset.min'_mem c.support hs
  exact ⟨c.support.min' hs, c.support, c, hm, fun i hi => Finset.min'_le _ _ hi,
    Finsupp.mem_support_iff.mp hm, hrel⟩

namespace HasPrimePowerRelation

variable {X : lieKernel G F} {p m : ℕ} [Fact p.Prime] [CharP F p]

/-- Under a prime-power relation, every representation of `G` has geometrically semisimple
tangent matrix at the first field prime power. -/
theorem isGeometricallySemisimpleMatrix (h : HasPrimePowerRelation X p m) {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n)) :
    Lie.IsGeometricallySemisimpleMatrix (ρ.tangentMatrix F (fieldPrimePower k F G X p m)) := by
  obtain ⟨s, c, hm, hle, hc, hrel⟩ := h
  rw [ρ.tangentMatrix_fieldPrimePower]
  apply Lie.isGeometricallySemisimpleMatrix_primePower_of_relation _ s c p m hm hle hc
  have hρ := congrArg (ρ.kernelDifferential F) hrel
  simpa only [map_sum, map_smul, map_zero, MatrixRepresentation.kernelDifferential_apply,
    toMul_ofMul, ρ.tangentMatrix_fieldPrimePower] using hρ

/-- Under a prime-power relation, the first field prime power is a semisimple element of the
base change `G_F`. -/
theorem isSemisimpleElement (h : HasPrimePowerRelation X p m) :
    Lie.IsSemisimpleElement ((GroupScheme.baseChange (algebraBaseMap k F)).obj G)
      ((Lie.kernelBaseChangeEquiv k F G F).symm (fieldPrimePower k F G X p m)) := by
  obtain ⟨s, c, hm, hle, hc, hrel⟩ := h
  intro n ρ
  rw [fieldPrimePower, MulEquiv.symm_apply_apply,
    MatrixRepresentation.tangentMatrix_primePowerKernel]
  apply Lie.isGeometricallySemisimpleMatrix_primePower_of_relation _ s c p m hm hle hc
  have hpi (i : ℕ) : (Lie.kernelBaseChangeLinearEquiv k F G F).symm
      (Additive.ofMul (fieldPrimePower k F G X p i)) =
      Additive.ofMul (Lie.primePowerKernel ((GroupScheme.baseChange (algebraBaseMap k F)).obj G)
        ((Lie.kernelBaseChangeEquiv k F G F).symm X) p i) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have h₁ := congrArg (Lie.kernelBaseChangeLinearEquiv k F G F).symm.toLinearMap hrel
  simp only [map_sum, map_zero] at h₁
  simp only [map_smul, LinearEquiv.coe_coe, hpi] at h₁
  have hρ := congrArg (ρ.kernelDifferential F) h₁
  simpa only [map_sum, map_smul, map_zero, MatrixRepresentation.kernelDifferential_apply,
    toMul_ofMul, ρ.tangentMatrix_primePowerKernel] using hρ

/-- Prime-power relations transfer along field homomorphisms, given a monomorphic
representation. -/
theorem map_of_mono {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (hρ : Mono ρ.hom.hom)
    {F' : Type u} [Field F'] [Algebra k F'] [CharP F' p] (φ : F →ₐ[k] F')
    (h : HasPrimePowerRelation X p m) : HasPrimePowerRelation (lieKernelMap G φ X) p m := by
  obtain ⟨s, c, hm, hle, hc, hrel⟩ := h
  refine ⟨s, fun i => φ (c i), hm, hle, (map_ne_zero_iff φ φ.toRingHom.injective).mpr hc, ?_⟩
  have h₁ := congrArg (lieKernelMapLinear G φ) hrel
  simp only [map_sum, map_zero] at h₁
  rw [← h₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, ← lieKernelMap_fieldPrimePower_of_mono ρ hρ φ X p i]
  rfl

/-- Prime-power relations transfer along constant-point conjugation, given a monomorphic
representation. -/
theorem conjugation_of_mono {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (hρ : Mono ρ.hom.hom)
    (g : Lie.AffinePoints G F) (h : HasPrimePowerRelation X p m) :
    HasPrimePowerRelation (lieKernelConjugation G g X) p m := by
  obtain ⟨s, c, hm, hle, hc, hrel⟩ := h
  refine ⟨s, c, hm, hle, hc, ?_⟩
  have h₁ := congrArg (lieKernelConjugationLinear G g) hrel
  simp only [map_sum, map_zero] at h₁
  rw [← h₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← lieKernelConjugation_fieldPrimePower_of_mono ρ hρ g X p i]
  rfl

end HasPrimePowerRelation

end Relation

section FieldRelation

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {X : lieKernel G F} {p m : ℕ} [Fact p.Prime] [CharP F p]

/-- Over a field, prime-power relations transfer along field homomorphisms. -/
theorem HasPrimePowerRelation.map {F' : Type u} [Field F'] [Algebra k F'] [CharP F' p]
    (φ : F →ₐ[k] F') (h : HasPrimePowerRelation X p m) :
    HasPrimePowerRelation (lieKernelMap G φ X) p m := by
  obtain ⟨n, ρ, hρ⟩ := exists_mono_matrixRepresentation (G := G)
  exact h.map_of_mono ρ hρ φ

/-- Over a field, prime-power relations transfer along constant-point conjugation. -/
theorem HasPrimePowerRelation.conjugation (g : Lie.AffinePoints G F)
    (h : HasPrimePowerRelation X p m) : HasPrimePowerRelation (lieKernelConjugation G g X) p m := by
  obtain ⟨n, ρ, hρ⟩ := exists_mono_matrixRepresentation (G := G)
  exact h.conjugation_of_mono ρ hρ g

end FieldRelation

end Langlands.GroupScheme

import Langlands.GroupScheme.Dynamic.TwoPowerCocharacter
import Langlands.Group.RealTwoPowerUnitaryConjugation

/-! # Internal Hermitian conjugation over real coefficient fields -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.GeneralLinear

variable {k S : Type u} [CommRing k] [RCLike S] [Algebra k S]
  {n : Type} [Fintype n] [DecidableEq n]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme n (CommRingCat.of k))

/-- Evaluation of a Laurent polynomial over the coefficient field at a
unit of an extension algebra. -/
def cocharacterEvalExtensionUnit (t : Sˣ) : LaurentPolynomial k →ₐ[k] S :=
  { LaurentPolynomial.eval₂ (algebraMap k S) t with
    commutes' r := by
      change LaurentPolynomial.eval₂ (algebraMap k S) t
        (algebraMap k (LaurentPolynomial k) r) = algebraMap k S r
      rw [← LaurentPolynomial.C_eq_algebraMap]
      simp }

@[simp] theorem cocharacterEvalExtensionUnit_single (t : Sˣ) (a : ℤ) (r : k) :
    cocharacterEvalExtensionUnit t (AddMonoidAlgebra.single a r) =
      algebraMap k S r * (t : S) ^ a := by
  change LaurentPolynomial.eval₂ (algebraMap k S) t _ = _
  rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
  simp only [Units.val_zpow_eq_zpow_val]

/-- The value over an extension algebra is the finite sum of the extended
weight projectors with the corresponding scalar powers. -/
theorem cocharacterUnitsHom_eq_sum_map_weightProjector (t : Sˣ) :
    (cocharacterUnitsHom χ S t : Matrix n n S) =
      ∑ a ∈ cocharacterWeightSupport χ,
        (t : S) ^ a • (weightProjector χ a).map (algebraMap k S) := by
  have ht : Units.map (cocharacterEvalExtensionUnit t).toMonoidHom
      (cocharacterLaurentUnit (CommRingCat.of k)) = t := by
    apply Units.ext
    change LaurentPolynomial.eval₂ (algebraMap k S) t (LaurentPolynomial.T 1) = _
    simp
  have h := cocharacterUnitsHom_naturality χ (cocharacterEvalExtensionUnit t)
    (cocharacterLaurentUnit (CommRingCat.of k))
  rw [ht] at h
  ext i j
  have hij := congrArg (fun g : GL n S => (g : Matrix n n S) i j) h
  rw [hij, Matrix.sum_apply]
  change cocharacterEvalExtensionUnit t
    ((weightMatrix χ : Matrix n n (LaurentPolynomial k)) i j) = _
  rw [weightMatrix_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [cocharacterEvalExtensionUnit_single]
  exact mul_comm _ _

/-- Extended weight projectors remain mutually orthogonal idempotents. -/
theorem map_weightProjector_mul (a b : ℤ) :
    (weightProjector χ a).map (algebraMap k S) *
        (weightProjector χ b).map (algebraMap k S) =
      if a = b then (weightProjector χ a).map (algebraMap k S) else 0 := by
  rw [← Matrix.map_mul, weightProjector_mul]
  split_ifs with hab
  · subst b
    simp
  · simp

/-- The extended weight projectors sum to the identity. -/
theorem sum_map_weightProjector :
    ∑ a ∈ cocharacterWeightSupport χ,
      (weightProjector χ a).map (algebraMap k S) = 1 := by
  have h := congrArg (RingHom.mapMatrix (algebraMap k S))
    (sum_weightProjector χ)
  simpa only [map_sum, map_one, RingHom.mapMatrix_apply] using h

/-- A cocharacter value over the extension acts on each extended weight
projector by the corresponding scalar power. -/
theorem cocharacterUnitsHom_mul_map_weightProjector (t : Sˣ) (a : ℤ) :
    (cocharacterUnitsHom χ S t : Matrix n n S) *
        (weightProjector χ a).map (algebraMap k S) =
      (t : S) ^ a • (weightProjector χ a).map (algebraMap k S) := by
  rw [cocharacterUnitsHom_eq_sum_map_weightProjector, Finset.sum_mul]
  simp only [smul_mul_assoc]
  rw [Finset.sum_eq_single a]
  · rw [map_weightProjector_mul]
    simp
  · intro b _ hba
    rw [map_weightProjector_mul]
    simp [hba]
  · intro ha
    rw [weightProjector_eq_zero χ ha]
    simp

/-- Hermitianity of all actual Laurent projectors after scalar extension. -/
def HasHermitianExtensionWeightProjectors : Prop :=
  ∀ a : ℤ, ((weightProjector χ a).map (algebraMap k S)).IsHermitian

/-- Normality at an extension unit separating the finite weight support
makes the extended weight projectors Hermitian. -/
theorem hasHermitianExtensionWeightProjectors_of_normal_separating_unit
    (t : Sˣ)
    (ht : Set.InjOn (fun a : ℤ => (t : S) ^ a)
      (cocharacterWeightSupport χ : Set ℤ))
    [IsStarNormal (cocharacterUnitsHom χ S t : Matrix n n S)] :
    HasHermitianExtensionWeightProjectors (S := S) χ := by
  apply Langlands.LinearAlgebra.hermitian_projectors_of_normal_separating_support
    (fun a => (weightProjector χ a).map (algebraMap k S))
    (map_weightProjector_mul χ)
    (cocharacterWeightSupport χ) (sum_map_weightProjector χ)
    (fun a ha => by rw [weightProjector_eq_zero χ ha]; simp)
    (cocharacterUnitsHom χ S t : Matrix n n S)
    (fun a => (t : S) ^ a) ht
  exact cocharacterUnitsHom_mul_map_weightProjector χ t

/-- Scalar conjugation inverts a unit-circle cocharacter value whenever it
fixes all extended coefficients. -/
theorem conjugateEntries_cocharacterUnitsHom
    (hcoeff : ∀ z : k, star (algebraMap k S z) = algebraMap k S z)
    (t : Sˣ) (ht : ‖(t : S)‖ = 1) :
    Langlands.Group.RealTwoPowerUnitaryConjugation.conjugateEntries
      (cocharacterUnitsHom χ S t) = (cocharacterUnitsHom χ S t)⁻¹ := by
  let f : S →ₐ[k] S := { starRingEnd S with commutes' := hcoeff }
  have ht' : Units.map f.toMonoidHom t = t⁻¹ := by
    apply Units.ext
    rw [Units.coe_map, Units.val_inv_eq_inv_val]
    change star (t : S) = (t : S)⁻¹
    exact (RCLike.inv_eq_conj ht).symm
  have h := cocharacterUnitsHom_naturality χ f t
  rw [ht', map_inv] at h
  exact h.symm

/-- A two-power torsion scalar in an `RCLike` field has norm one. -/
theorem norm_eq_one_of_two_power_eq_one (t : Sˣ) (r : ℕ)
    (ht : t ^ (2 ^ r) = 1) : ‖(t : S)‖ = 1 := by
  have hn : (2 : ℕ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp
  have h := congrArg (fun z : Sˣ => ‖(z : S)‖) ht
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using h

/-- Conjugating the base cocharacter conjugates its extension value by the
scalar extension of the same base matrix. -/
theorem cocharacterUnitsHom_innerIso_baseOfMatrix_extension
    (g : GL n k) (t : Sˣ) :
    cocharacterUnitsHom
      (χ ≫ (innerIso (groupScheme n (CommRingCat.of k))
        (baseOfMatrix (CommRingCat.of k) g)).hom) S t =
      Matrix.GeneralLinearGroup.map (algebraMap k S) g *
        cocharacterUnitsHom χ S t *
          (Matrix.GeneralLinearGroup.map (algebraMap k S) g)⁻¹ := by
  rw [cocharacterUnitsHom_apply, Grp.comp_hom_hom, ← Category.assoc,
    comp_innerIso_hom, map_mul, map_mul, map_inv,
    affinePointsEquiv_constantPoint_baseOfMatrix]
  rfl

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.Group.RealTwoPowerUnitaryConjugation

variable {k S : Type u} [RCLike k] [RCLike S] [Algebra k S]
  {n : Type} [Fintype n] [DecidableEq n]

/-- A matrix unit fixed by entrywise conjugation is the scalar extension of
a real matrix unit. Both its matrix and its inverse descend. -/
theorem exists_real_matrix_of_conjugateEntries_eq_self
    (g : GL n S) (hg : conjugateEntries g = g) :
    ∃ a : GL n ℝ, Matrix.GeneralLinearGroup.map (algebraMap ℝ S) a = g := by
  let A : Matrix n n ℝ := g.val.map RCLike.re
  let B : Matrix n n ℝ := (g⁻¹).val.map RCLike.re
  have hA : A.map (algebraMap ℝ S) = g.val := by
    ext i j
    exact RCLike.conj_eq_iff_re.mp
      (congrArg (fun q : GL n S => q.val i j) hg)
  have hgi : conjugateEntries g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  have hB : B.map (algebraMap ℝ S) = (g⁻¹).val := by
    ext i j
    exact RCLike.conj_eq_iff_re.mp
      (congrArg (fun q : GL n S => q.val i j) hgi)
  have hinj : Function.Injective
      (fun C : Matrix n n ℝ => C.map (algebraMap ℝ S)) := by
    intro C D h
    ext i j
    exact (algebraMap ℝ S).injective (congrArg (fun E => E i j) h)
  have hAB : A * B = 1 := by
    apply hinj
    change (A * B).map (algebraMap ℝ S) = (1 : Matrix n n ℝ).map (algebraMap ℝ S)
    rw [Matrix.map_mul, hA, hB]
    simp
  have hBA : B * A = 1 := by
    apply hinj
    change (B * A).map (algebraMap ℝ S) = (1 : Matrix n n ℝ).map (algebraMap ℝ S)
    rw [Matrix.map_mul, hB, hA]
    simp
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

/-- Real matrix units lift to any `RCLike` coefficient field in a compatible
real scalar tower. -/
theorem exists_base_matrix_of_conjugateEntries_eq_self
    [IsScalarTower ℝ k S] (g : GL n S) (hg : conjugateEntries g = g) :
    ∃ a : GL n k, Matrix.GeneralLinearGroup.map (algebraMap k S) a = g := by
  obtain ⟨a, ha⟩ := exists_real_matrix_of_conjugateEntries_eq_self g hg
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap ℝ k) a, ?_⟩
  apply Units.ext
  ext i j
  change algebraMap k S (algebraMap ℝ k (a.val i j)) = g.val i j
  rw [← IsScalarTower.algebraMap_apply ℝ k S]
  exact congrArg (fun q : GL n S => q.val i j) ha

end Langlands.Group.RealTwoPowerUnitaryConjugation

namespace Langlands.GroupScheme.GeneralLinear

variable {k S : Type u} [RCLike k] [RCLike S] [Algebra k S]
  [IsScalarTower ℝ k S]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Coefficients of a real `RCLike` field remain fixed by conjugation in a
compatible real scalar extension. -/
theorem star_algebraMap_eq_self_of_real (hreal : ∀ z : k, star z = z) (z : k) :
    star (algebraMap k S z) = algebraMap k S z := by
  have hz : (RCLike.re z : k) = z := RCLike.conj_eq_iff_re.mp (hreal z)
  have heq : algebraMap k S z = (RCLike.re z : S) := by
    calc
      algebraMap k S z = algebraMap k S (RCLike.re z : k) :=
        (congrArg (algebraMap k S) hz).symm
      _ = (RCLike.re z : S) :=
        (IsScalarTower.algebraMap_apply ℝ k S (RCLike.re z)).symm
  rw [heq]
  exact RCLike.conj_ofReal _

/-- Hermitianity of actual weight projectors reflects through a compatible
scalar extension of a real coefficient field. -/
theorem hasHermitianWeightProjectors_of_extension
    (hreal : ∀ z : k, star z = z)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme n (CommRingCat.of k))
    (hχ : HasHermitianExtensionWeightProjectors (S := S) χ) :
    HasHermitianWeightProjectors χ := by
  have hstar : Function.Semiconj (algebraMap k S) star star := by
    intro z
    rw [hreal z, star_algebraMap_eq_self_of_real hreal]
  intro a
  exact (Matrix.isHermitian_map_iff hstar (algebraMap k S).injective).mp (hχ a)

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k S : Type u} [RCLike k] [RCLike S] [Algebra k S]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The actual cocharacter-point comparison holds at every extension test
algebra used here. -/
theorem affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom_extension
    (ρ : MatrixRepresentation G n)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (t : Sˣ) :
    ρ.affineMatrix (CommAlgCat.of k S)
        (Dynamic.cocharacterPointHom χ (CommAlgCat.of k S) t) =
      GeneralLinear.cocharacterUnitsHom (χ ≫ ρ) S t := by
  change GeneralLinear.affinePointsEquiv n _ _
      (((Gm.algebraPointsEquiv S).symm t ≫ χ.hom.hom) ≫ ρ.hom.hom) = _
  rw [Category.assoc, ← Grp.comp_hom_hom]
  rfl

/-- The range of a closed actual representation reflects membership under
an injective scalar extension. -/
theorem map_mem_affineMatrix_range_iff
    (ρ : MatrixRepresentation G n) [IsClosedImmersion ρ.hom.hom.left]
    (g : GL n k) :
    Matrix.GeneralLinearGroup.map (algebraMap k S) g ∈
        (ρ.affineMatrix (CommAlgCat.of k S)).range ↔
      g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range := by
  rw [ρ.mem_affineMatrix_range_iff_zeroLocus S,
    ρ.mem_affineMatrix_range_iff_zeroLocus k]
  constructor
  · intro hg p hp
    apply (algebraMap k S).injective
    rw [map_zero]
    have h := hg p hp
    rw [GeneralLinear.values_map] at h
    change MvPolynomial.aeval
      (fun v => (Algebra.ofId k S) (GeneralLinear.values g v)) p = 0 at h
    rw [← MvPolynomial.comp_aeval_apply] at h
    exact h
  · exact GeneralLinear.map_mem_zeroLocus (Algebra.ofId k S)

/-- Internal two-power unitarization over a complex extension descends to
the original real field and makes the original projectors Hermitian. -/
theorem exists_real_internal_conjugate_hermitian
    [IsScalarTower ℝ k S] [IsAlgClosed S]
    (hreal : ∀ z : k, star z = z)
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range,
      star g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ g : GL n k, g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range ∧
      GeneralLinear.HasHermitianWeightProjectors
        (χ ≫ ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of k) g)) := by
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let ψ := χ ≫ ρ
  obtain ⟨r, t, ht, hsep⟩ :=
    GeneralLinear.exists_two_power_unit_separating
      (𝕜 := S) (GeneralLinear.cocharacterWeightSupport ψ)
  have htχ : GeneralLinear.cocharacterUnitsHom ψ S t ∈
      (ρ.affineMatrix (CommAlgCat.of k S)).range :=
    ⟨Dynamic.cocharacterPointHom χ (CommAlgCat.of k S) t,
      ρ.affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom_extension χ t⟩
  have hbar := GeneralLinear.conjugateEntries_cocharacterUnitsHom ψ
    (GeneralLinear.star_algebraMap_eq_self_of_real (S := S) hreal) t
    (GeneralLinear.norm_eq_one_of_two_power_eq_one t r ht)
  have hpow : (GeneralLinear.cocharacterUnitsHom ψ S t) ^ (2 ^ r) = 1 := by
    rw [← map_pow, ht, map_one]
  obtain ⟨c, hc, hcr, hcu⟩ :=
    Langlands.Group.RealTwoPowerUnitaryConjugation.exists_real_conjugator_of_two_power_eq_one
      (ρ.affineMatrix (CommAlgCat.of k S)).range
      (ρ.affineMatrix_range_isPolynomiallyDefined S) hstar r
      (GeneralLinear.cocharacterUnitsHom ψ S t) htχ hbar hpow
  obtain ⟨g, hg⟩ :=
    Langlands.Group.RealTwoPowerUnitaryConjugation.exists_base_matrix_of_conjugateEntries_eq_self
      (k := k) c hcr
  have hgm : g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range :=
    (ρ.map_mem_affineMatrix_range_iff (S := S) g).mp (by rwa [hg])
  let θ := ψ ≫ (innerIso (GeneralLinear.groupScheme n (CommRingCat.of k))
    (GeneralLinear.baseOfMatrix (CommRingCat.of k) g)).hom
  have hθu : (GeneralLinear.cocharacterUnitsHom θ S t : Matrix n n S) ∈
      Matrix.unitaryGroup n S := by
    simpa only [θ, GeneralLinear.cocharacterUnitsHom_innerIso_baseOfMatrix_extension,
      hg] using hcu
  let : IsStarNormal (GeneralLinear.cocharacterUnitsHom θ S t : Matrix n n S) :=
    isStarNormal_of_mem_unitary hθu
  have hw : GeneralLinear.HasHermitianExtensionWeightProjectors (S := S) θ :=
    GeneralLinear.hasHermitianExtensionWeightProjectors_of_normal_separating_unit θ t
      (hsep.mono (GeneralLinear.cocharacterWeightSupport_innerIso_subset ψ g))
  refine ⟨g, hgm, ?_⟩
  have hw' := GeneralLinear.hasHermitianWeightProjectors_of_extension hreal θ hw
  simpa only [θ, ψ, MatrixRepresentation.conjugate, Category.assoc] using hw'

end Langlands.GroupScheme.MatrixRepresentation

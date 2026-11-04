import Langlands.GroupScheme.Lie.ActionBaseChange
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof
import Langlands.GroupScheme.Rational.ActionWeightSupport

/-! # Galois transport of actual action weight spaces -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
private instance algEquivInversePair {k A B : Type u} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (σ : A ≃ₐ[k] B) :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  ⟨by ext x; exact σ.symm_apply_apply x, by ext x; exact σ.apply_symm_apply x⟩

private instance algEquivInversePairReverse {k A B : Type u} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (σ : A ≃ₐ[k] B) :
    RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  ⟨by ext x; exact σ.apply_symm_apply x, by ext x; exact σ.symm_apply_apply x⟩

namespace Lie

section Coefficients
variable {k : Type u} [CommRing k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    {A B C : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]

theorem kernelCoefficientMap_comp (f : A →ₐ[k] B) (g : B →ₐ[k] C)
    (x : Additive (lieKernel G A)) :
    lieKernelMapLinear G (g.comp f) x =
      lieKernelMapLinear G g (lieKernelMapLinear G f x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [lieKernelMapLinear_toMul, lieKernelMap_val, ← affineMap_comp]
  congr 1

@[simp] theorem kernelCoefficientMap_id (x : Additive (lieKernel G A)) :
    lieKernelMapLinear G (AlgHom.id k A) x = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [lieKernelMapLinear_toMul, lieKernelMap_val]
  have h : GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k) (AlgHom.id k A) =
      AlgHom.id k (DualNumber A) := by
    apply AlgHom.ext
    intro z
    apply TrivSqZeroExt.ext <;> rfl
  rw [h, affineMap_id]

/-- An actual coefficient algebra equivalence gives a semilinear equivalence of
actual dual-number identity kernels. -/
def kernelCoefficientEquiv (σ : A ≃ₐ[k] B) :
    LinearEquiv (σ' := σ.symm.toRingHom) σ.toRingHom
      (Additive (lieKernel G A)) (Additive (lieKernel G B)) where
  toFun := lieKernelMapLinear G σ.toAlgHom
  invFun := lieKernelMapLinear G σ.symm.toAlgHom
  left_inv x := by
    rw [← kernelCoefficientMap_comp]
    have h : σ.symm.toAlgHom.comp σ.toAlgHom = AlgHom.id k A := by ext; simp
    rw [h, kernelCoefficientMap_id]
  right_inv x := by
    rw [← kernelCoefficientMap_comp]
    have h : σ.toAlgHom.comp σ.symm.toAlgHom = AlgHom.id k B := by ext; simp
    rw [h, kernelCoefficientMap_id]
  map_add' := (lieKernelMapLinear G σ.toAlgHom).map_add
  map_smul' := (lieKernelMapLinear G σ.toAlgHom).map_smulₛₗ

end Coefficients

section BaseChange
variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The canonical semilinear Galois map on the Lie kernel of a descended group. -/
def baseChangeGaloisEquiv (σ : K ≃ₐ[k] K) :
    LinearEquiv (σ' := σ.symm.toRingHom) σ.toRingHom
      (Additive (lieKernel G_K K)) (Additive (lieKernel G_K K)) :=
  (kernelBaseChangeLinearEquiv k K G K).trans
    ((kernelCoefficientEquiv G σ).trans (kernelBaseChangeLinearEquiv k K G K).symm)

theorem baseChangeGaloisEquiv_apply (σ : K ≃ₐ[k] K)
    (x : Additive (lieKernel G_K K)) :
    baseChangeGaloisEquiv k K G σ x =
      (kernelBaseChangeLinearEquiv k K G K).symm
        (lieKernelMapLinear G σ.toAlgHom (kernelBaseChangeLinearEquiv k K G K x)) := rfl

end BaseChange
end Lie

namespace Lie

/-- The affine character value is the global unit transported through `ΓSpecIso`. -/
theorem characterValue_eq_globalUnits {R : CommRingCat.{u}}
    {S : CommGroupScheme (Spec R)} {A : Type u} [CommRing A] [Algebra R A]
    (χ : characterLattice S) (s : AffinePoints S.toGrp A) :
    characterValue χ s =
      Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom
        (Gm.pointsEquiv _ _ (s ≫ (CommGroupScheme.groupHom χ).hom.hom)) := rfl

/-- The same coefficient ring with its `K`-algebra structure precomposed by `σ`.
Its original `k`-algebra structure is retained. -/
def GaloisTestAlgebra {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]
    (_σ : K ≃ₐ[k] K) (A : Type u) := A

namespace GaloisTestAlgebra
variable {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (A : Type u) [CommRing A]

instance : CommRing (GaloisTestAlgebra σ A) := inferInstanceAs (CommRing A)
instance [Algebra k A] : Algebra k (GaloisTestAlgebra σ A) :=
  inferInstanceAs (Algebra k A)
instance [Algebra K A] : Algebra K (GaloisTestAlgebra σ A) :=
  ((algebraMap K A).comp σ.toRingHom).toAlgebra
instance [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
    IsScalarTower k K (GaloisTestAlgebra σ A) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap k A x = algebraMap K A (σ (algebraMap k K x))
    rw [σ.commutes, IsScalarTower.algebraMap_apply k K A])

end GaloisTestAlgebra

section TwistedTests
variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (A : Type u) [CommRing A] [Algebra K A]

/-- Changing the structure map by `Spec σ` gives exactly the twisted algebra test. -/
def galoisTestIso :
    (Over.map (galoisBaseMap k K σ)).obj
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A))) ≅
      (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K (GaloisTestAlgebra σ A))) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of A))) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (GaloisTestAlgebra σ A))) =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom)
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1)

variable (G : GroupScheme (Spec (CommRingCat.of k)))
local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

/-- The canonical descent point, expressed as a point on the twisted algebra test. -/
def galoisTestPoint (x : AffinePoints G_K A) :
    AffinePoints G_K (GaloisTestAlgebra σ A) :=
  (galoisTestIso k K σ A).inv ≫
    descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G _ x

variable [Algebra k A] [IsScalarTower k K A]

/-- Over the original base, the twisted point is the same point. -/
theorem affineBaseChangeEquiv_galoisTestPoint (x : AffinePoints G_K A) :
    affineBaseChangeEquiv k K G (GaloisTestAlgebra σ A) (galoisTestPoint k K σ A G x) =
      affineBaseChangeEquiv k K G A x := by
  change (affineBaseTestIso k K (GaloisTestAlgebra σ A)).inv ≫
      baseChangePointsEquiv _ G _ ((galoisTestIso k K σ A).inv ≫ _) = _
  rw [baseChangePointsEquiv_naturality, baseChangePointsEquiv_descentPoint]
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _ ≫ _) = 𝟙 _ ≫ _
  simp only [Category.id_comp]
  rfl

omit [Algebra k A] [IsScalarTower k K A] in
/-- The twisted-test isomorphism is the identity on the underlying scheme,
so pullback along it leaves global units unchanged. -/
theorem pointsEquiv_galoisTestIso_inv
    (x : (Over.map (galoisBaseMap k K σ)).obj
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A))) ⟶
      (Gm (Spec (CommRingCat.of K))).X) :
    Gm.pointsEquiv _ _ ((galoisTestIso k K σ A).inv ≫ x) =
      Gm.pointsEquiv _ _ x := by
  calc
    _ = Units.map (galoisTestIso k K σ A).inv.left.appTop.hom.toMonoidHom
        (Gm.pointsEquiv _ _ x) :=
      Gm.pointsEquiv_naturality _ (galoisTestIso k K σ A).inv x
    _ = _ := by
      change Units.map
        (𝟙 _ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A)).appTop.hom.toMonoidHom
          (Gm.pointsEquiv _ _ x) = _
      simp

omit [Algebra k A] [IsScalarTower k K A] in
/-- Canonical Galois transport of a character evaluates on the twisted test point. -/
theorem characterValue_galoisRepresentation
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (s : AffinePoints
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp A) :
    characterValue (characterLattice.galoisRepresentation k K T σ χ) s =
      characterValue χ (galoisTestPoint k K σ A T.toGrp s) := by
  rw [characterValue_eq_globalUnits, characterValue_eq_globalUnits]
  have hg := characterLattice.galoisRepresentation_points k K T σ χ _ s
  have hi := pointsEquiv_galoisTestIso_inv k K σ A
    (descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) T.toGrp _ s ≫ (CommGroupScheme.groupHom χ).hom.hom)
  rw [galoisTestPoint, Category.assoc]
  exact congrArg (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom)
    (hg.trans hi.symm)

variable [IsAffineHom G.X.hom]

local instance : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- Mapping the semilinear Galois vector to a test algebra agrees with mapping
the original vector to the twisted algebra, over the original base. -/
theorem kernelBaseChangeLinearEquiv_galois_vector
    (x : Additive (lieKernel G_K K)) :
    kernelBaseChangeLinearEquiv k K G A
        (lieKernelMapLinear G_K (Algebra.ofId K A) (baseChangeGaloisEquiv k K G σ x)) =
      kernelBaseChangeLinearEquiv k K G (GaloisTestAlgebra σ A)
        (lieKernelMapLinear G_K (Algebra.ofId K (GaloisTestAlgebra σ A)) x) := by
  rw [kernelBaseChangeLinearEquiv_naturality, baseChangeGaloisEquiv_apply,
    LinearEquiv.apply_symm_apply, ← kernelCoefficientMap_comp,
    kernelBaseChangeLinearEquiv_naturality]
  congr 1

end TwistedTests
end Lie

namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The intrinsic all-test eigenvector condition can be written using the actual
linear differential. -/
theorem mem_actionWeightSpace_iff_differential
    (a : AutomorphicAction S.toGrp G) (χ : characterLattice S)
    {x : Additive (lieKernel G k)} :
    x ∈ actionWeightSpace a χ ↔
      ∀ (A : Type u) [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A),
        a.differential s (lieKernelMapLinear G (Algebra.ofId k A) x) =
          (Lie.characterValue χ s : A) • lieKernelMapLinear G (Algebra.ofId k A) x := by
  rw [mem_actionWeightSpace_iff]
  constructor
  · intro hx A _ _ s
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hx A s
  · intro hx A _ _ s
    exact congrArg (fun z : Additive (lieKernel G A) => z.toMul.val) (hx A s)

section Galois

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]
    (a : AutomorphicAction T.toGrp U)

local notation "b" => algebraBaseMap k K
local notation "T_K" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T
local notation "U_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) U

local instance : IsAffineHom (U_K).X.hom := by
  change IsAffineHom (pullback.snd U.X.hom b)
  infer_instance

/-- The actual semilinear Galois map transports each actual action weight vector
to the canonically transported character, with all coefficient tests retained. -/
theorem galois_mem_actionWeightSpace (σ : K ≃ₐ[k] K) (χ : characterLattice T_K)
    {x : Additive (lieKernel U_K K)}
    (hx : x ∈ actionWeightSpace (a.baseChange b) χ) :
    Lie.baseChangeGaloisEquiv k K U σ x ∈
      actionWeightSpace (a.baseChange b) (characterLattice.galoisRepresentation k K T σ χ) := by
  rw [mem_actionWeightSpace_iff_differential] at hx ⊢
  intro A _ _ s
  let : Algebra k A := Algebra.compHom A (algebraMap k K)
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  have ht := hx (Lie.GaloisTestAlgebra σ A) (Lie.galoisTestPoint k K σ A T.toGrp s)
  have h := congrArg (Lie.kernelBaseChangeLinearEquiv k K U (Lie.GaloisTestAlgebra σ A)) ht
  rw [a.differential_baseChange k K, LinearEquiv.map_smul,
    Lie.affineBaseChangeEquiv_galoisTestPoint] at h
  apply (Lie.kernelBaseChangeLinearEquiv k K U A).injective
  rw [a.differential_baseChange k K, LinearEquiv.map_smul,
    Lie.kernelBaseChangeLinearEquiv_galois_vector k K σ A U,
    Lie.characterValue_galoisRepresentation]
  exact h

/-- A nonzero actual weight space remains nonzero under canonical Galois transport. -/
theorem actionWeightSpace_galois_ne_bot (σ : K ≃ₐ[k] K) (χ : characterLattice T_K)
    (hχ : actionWeightSpace (a.baseChange b) χ ≠ ⊥) :
    actionWeightSpace (a.baseChange b) (characterLattice.galoisRepresentation k K T σ χ) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hχ
  refine (Submodule.ne_bot_iff _).mpr
    ⟨Lie.baseChangeGaloisEquiv k K U σ x, galois_mem_actionWeightSpace k K a σ χ hx, ?_⟩
  intro hzero
  exact hx0 ((Lie.baseChangeGaloisEquiv k K U σ).map_eq_zero_iff.mp hzero)

/-- Canonical Galois transport permutes exactly the nonzero actual weight spaces
of an action descended from the original base. -/
theorem actionWeightSpace_galois_ne_bot_iff (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) :
    actionWeightSpace (a.baseChange b) (characterLattice.galoisRepresentation k K T σ χ) ≠ ⊥ ↔
      actionWeightSpace (a.baseChange b) χ ≠ ⊥ := by
  constructor
  · intro hχ
    have h := actionWeightSpace_galois_ne_bot k K a σ.symm
      (characterLattice.galoisRepresentation k K T σ χ) hχ
    have hc : characterLattice.galoisRepresentation k K T σ.symm
        (characterLattice.galoisRepresentation k K T σ χ) = χ := by
      change characterLattice.galoisRepresentation k K T σ⁻¹
        (characterLattice.galoisRepresentation k K T σ χ) = χ
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [hc] at h
  · exact actionWeightSpace_galois_ne_bot k K a σ χ

/-- The whole-group intrinsic action weight support is Galois invariant. -/
theorem mem_actionWeightSupport_top_galois_iff
    (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) :
    characterLattice.galoisRepresentation k K T σ χ ∈
        actionWeightSupport (a.baseChange b) ⊤ ↔
      χ ∈ actionWeightSupport (a.baseChange b) ⊤ := by
  rw [actionWeightSupport_top]
  exact actionWeightSpace_galois_ne_bot_iff k K a σ χ

/-- The same support permutation applies after restricting a descended action
along an actual homomorphism from the commutative acting group. -/
theorem restricted_actionWeightSpace_galois_ne_bot_iff
    {H : GroupScheme (Spec (CommRingCat.of k))} (c : AutomorphicAction H U)
    (j : T.toGrp ⟶ H) (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) :
    actionWeightSpace
        ((c.baseChange b).restrict ((GroupScheme.baseChange b).map j))
        (characterLattice.galoisRepresentation k K T σ χ) ≠ ⊥ ↔
      actionWeightSpace
        ((c.baseChange b).restrict ((GroupScheme.baseChange b).map j)) χ ≠ ⊥ := by
  simpa only [AutomorphicAction.baseChange_restrict] using
    actionWeightSpace_galois_ne_bot_iff k K (c.restrict j) σ χ

/-- For conjugation, the original adjoint weight spaces have the same canonical
Galois permutation of their nonzero occurrences. -/
theorem weightSpace_galois_ne_bot_iff
    (i : T.toGrp ⟶ U) (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) :
    weightSpace ((GroupScheme.baseChange b).map i)
        (characterLattice.galoisRepresentation k K T σ χ) ≠ ⊥ ↔
      weightSpace ((GroupScheme.baseChange b).map i) χ ≠ ⊥ := by
  simpa only [AutomorphicAction.baseChange_conjugation, actionWeightSpace_conjugation] using
    actionWeightSpace_galois_ne_bot_iff k K (AutomorphicAction.conjugation i) σ χ

end Galois
end RelativeRoot

end Langlands.GroupScheme

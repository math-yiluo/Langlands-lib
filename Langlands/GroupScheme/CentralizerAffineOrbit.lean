import Langlands.GroupScheme.NormalizerRepresentability
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Affine coefficient parameters for conjugation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented

open Langlands.Algebra.ProjectiveTensorCoefficients

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B) (I : Ideal B)

/-- An affine parameter algebra recording every dual coefficient of the
universal conjugation map. -/
abbrev conjugationCoefficientAlgebra : CommAlgCat.{u} R :=
  CommAlgCat.of R (MvPolynomial (B × ((B ⧸ I) →ₗ[R] R)) R)

/-- The coefficient algebra map classifying universal conjugation. -/
def conjugationCoefficientMap : conjugationCoefficientAlgebra I ⟶ B :=
  CommAlgCat.ofHom (MvPolynomial.aeval fun v =>
    contract v.2 ((e.homEquiv.symm (universalConjugate e I)).hom v.1))

variable {e I}

/-- Equality after two coefficient maps is detected by every contraction of
the projective tensor factor. -/
theorem tensorQuotientMap_eq_iff [Module.Projective R (B ⧸ I)]
    {A : CommAlgCat.{u} R} (φ ψ : B ⟶ A) (z : B ⊗[R] (B ⧸ I)) :
    (tensorQuotientMap I φ).hom z = (tensorQuotientMap I ψ).hom z ↔
      ∀ f : (B ⧸ I) →ₗ[R] R, φ.hom (contract f z) = ψ.hom (contract f z) := by
  constructor
  · intro h f
    have h' := congrArg (contract f) h
    rw [tensorQuotientMap_apply, tensorQuotientMap_apply,
      contract_rTensor, contract_rTensor] at h'
    exact h'
  · intro h
    apply sub_eq_zero.mp
    apply (eq_zero_iff_contract _).2
    intro f
    rw [map_sub, tensorQuotientMap_apply, tensorQuotientMap_apply,
      contract_rTensor, contract_rTensor, sub_eq_zero]
    exact h f

/-- The coefficient parameters agree exactly when the universal conjugates
agree after the corresponding algebra maps. -/
theorem conjugationCoefficientMap_comp_eq_iff [Module.Projective R (B ⧸ I)]
    {A : CommAlgCat.{u} R} (φ ψ : B ⟶ A) :
    conjugationCoefficientMap e I ≫ φ = conjugationCoefficientMap e I ≫ ψ ↔
      F.map (tensorQuotientMap I φ) (universalConjugate e I) =
        F.map (tensorQuotientMap I ψ) (universalConjugate e I) := by
  have hcoeff :
      conjugationCoefficientMap e I ≫ φ = conjugationCoefficientMap e I ≫ ψ ↔
        ∀ b : B, ∀ f : (B ⧸ I) →ₗ[R] R,
          φ.hom (contract f ((e.homEquiv.symm (universalConjugate e I)).hom b)) =
            ψ.hom (contract f ((e.homEquiv.symm (universalConjugate e I)).hom b)) := by
    constructor
    · intro h b f
      have h' := congrArg (fun k : conjugationCoefficientAlgebra I ⟶ A =>
        k.hom (MvPolynomial.X (b, f))) h
      simpa only [CommAlgCat.hom_comp, AlgHom.comp_apply, conjugationCoefficientMap,
        CommAlgCat.hom_ofHom, MvPolynomial.aeval_X] using h'
    · intro h
      apply CommAlgCat.hom_ext
      apply MvPolynomial.algHom_ext
      rintro ⟨b, f⟩
      simpa only [CommAlgCat.hom_comp, AlgHom.comp_apply, conjugationCoefficientMap,
        CommAlgCat.hom_ofHom, MvPolynomial.aeval_X] using h b f
  rw [hcoeff]
  constructor
  · intro h
    apply e.homEquiv.symm.injective
    rw [homEquiv_symm_map, homEquiv_symm_map]
    ext b
    exact (tensorQuotientMap_eq_iff φ ψ _).2 (h b)
  · intro h b
    have h' := congrArg (fun y => (e.homEquiv.symm y).hom b) h
    rw [homEquiv_symm_map, homEquiv_symm_map] at h'
    exact (tensorQuotientMap_eq_iff φ ψ _).1 h'

/-- A group identity expressing equality of conjugation orbits as a
centralizer condition. -/
theorem conjugates_eq_iff_commute {M : Type*} [Group M] (g h x : M) :
    g * x * g⁻¹ = h * x * h⁻¹ ↔ Commute (g⁻¹ * h) x := by
  change _ ↔ (g⁻¹ * h) * x = x * (g⁻¹ * h)
  constructor
  · intro he
    have hh := congrArg (fun y => g⁻¹ * y * h) he
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      inv_mul_cancel, mul_one] using hh.symm
  · intro he
    have hh := congrArg (fun y => g * y * h⁻¹) he
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using hh.symm

/-- The affine coefficient parameters have exactly the centralizer cosets as
their fibers over every commutative algebra, including nonflat ones. -/
theorem conjugationCoefficientMap_fibers
    {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H I) [Module.Projective R (B ⧸ I)]
    {A : CommAlgCat.{u} R} (g h : F.obj A) :
    conjugationCoefficientMap e I ≫ e.homEquiv.symm g =
        conjugationCoefficientMap e I ≫ e.homEquiv.symm h ↔
      g⁻¹ * h ∈ centralizerFamily H A := by
  rw [conjugationCoefficientMap_comp_eq_iff, map_universalConjugate,
    map_universalConjugate, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    conjugates_eq_iff_commute, mem_centralizerFamily_iff hH, map_mul, map_inv]

variable (e I)

/-- The affine coefficient parameter scheme. Its dimension need not be finite. -/
abbrev conjugationCoefficientScheme : Over (Spec R) :=
  (algSpec R).obj (op (conjugationCoefficientAlgebra I))

/-- The actual affine coefficient orbit morphism. -/
def conjugationCoefficientOrbit :
    (groupScheme F e).X ⟶ conjugationCoefficientScheme I :=
  (algSpec R).map (conjugationCoefficientMap e I).op

variable {e I}

/-- For arbitrary scheme tests, equality of orbit parameters is equality of
the corresponding algebra maps on relative global sections. -/
theorem conjugationCoefficientOrbit_eq_iff
    (T : Over (Spec R)) (g h : T ⟶ (groupScheme F e).X) :
    g ≫ conjugationCoefficientOrbit e I = h ≫ conjugationCoefficientOrbit e I ↔
      conjugationCoefficientMap e I ≫ e.homEquiv.symm (pointsEquiv F e T g) =
        conjugationCoefficientMap e I ≫ e.homEquiv.symm (pointsEquiv F e T h) := by
  rw [pointsEquiv_apply, pointsEquiv_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  change T ⟶ (algSpec R).obj (op B) at g h
  change g ≫ (algSpec R).map (conjugationCoefficientMap e I).op =
      h ≫ (algSpec R).map (conjugationCoefficientMap e I).op ↔
    conjugationCoefficientMap e I ≫
        (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm g).unop =
      conjugationCoefficientMap e I ≫
        (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm h).unop
  constructor
  · intro he
    have hh := congrArg (fun k =>
      (((algΓAlgSpecAdjunction R).homEquiv T
        (op (conjugationCoefficientAlgebra I))).symm k).unop) he
    dsimp only [conjugationCoefficientOrbit] at hh
    rw [Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_right_symm, unop_comp, unop_comp] at hh
    exact hh
  · intro he
    apply ((algΓAlgSpecAdjunction R).homEquiv T
      (op (conjugationCoefficientAlgebra I))).symm.injective
    apply Quiver.Hom.unop_inj
    dsimp only [conjugationCoefficientOrbit]
    rw [Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_right_symm, unop_comp, unop_comp]
    exact he

section ClosedSubgroup

variable {K : GroupScheme (Spec R)} {j : K ⟶ groupScheme F e}
  (hI : ∀ (U : Over (Spec R)) (y : U ⟶ (groupScheme F e).X),
    y ∈ (SubgroupFunctor.range j).carrier U ↔
      ∀ b ∈ I, (e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0)
  [Module.Projective R (B ⧸ I)]

include hI

/-- The scheme-theoretic centralizer is the algebra centralizer on relative
global sections, on every test scheme. -/
theorem mem_centralizer_range_iff_pointsEquiv
    (T : Over (Spec R)) (g : T ⟶ (groupScheme F e).X) :
    g ∈ (SubgroupFunctor.range j).centralizer.carrier T ↔
      pointsEquiv F e T g ∈
        centralizerFamily (affineSubgroups (SubgroupFunctor.range j))
          ((algΓ R).obj T).unop := by
  rw [← (isRepresentedBy_centralizer hI).2, range_cutHom, mem_cutSubgroupFunctor,
    affineSubgroups_centralizer hI]

/-- The affine orbit morphism has exactly the full centralizer cosets as
fibers on every scheme test, with no affineness or flatness assumption on
that test. -/
theorem conjugationCoefficientOrbit_fibers
    (T : Over (Spec R)) (g h : T ⟶ (groupScheme F e).X) :
    g ≫ conjugationCoefficientOrbit e I = h ≫ conjugationCoefficientOrbit e I ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range j).centralizer.carrier T := by
  rw [conjugationCoefficientOrbit_eq_iff,
    conjugationCoefficientMap_fibers (isCutOutBy_range hI),
    mem_centralizer_range_iff_pointsEquiv hI, map_mul, map_inv]

end ClosedSubgroup

end Langlands.GroupScheme.Corepresented

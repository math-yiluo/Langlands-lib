import Langlands.GroupScheme.Reductive.LocalRootGroupLie
import Langlands.GroupScheme.Lie.CorepresentedCotangent
import Langlands.CommutativeAlgebra.GradedLineCotangent

/-! # Global root-group coordinates from a free actual root weight -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Polynomial TensorProduct

namespace Langlands.GroupScheme.Corepresented.RelativeUnipotent

open UnipotentPrimitive

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)

/-- Pullback by the actual contracting-group inclusion is the quotient map. -/
theorem pullback_unipotentHom_apply (b : B) :
    pullback (e := unipotentCorepresentation χ) (e' := e) (unipotentHom χ) b =
      unipQuot χ b := by
  change (Spec.preimage (unipotentHom χ).hom.hom.left) b = _
  rw [unipotentHom, cutHom_left]
  exact congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of (B ⧸ unipotentIdeal χ) =>
    φ.hom b) (Spec.preimage_map _)

/-- The quotient augmentation is the actual counit of the contracting group. -/
theorem unipotentAugmentation_eq_augmentation :
    unipotentAugmentation χ = augmentation (unipotentCorepresentation χ) := by
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [unipotentAugmentation_mk]
  have h := augmentation_pullback (e := unipotentCorepresentation χ) (e' := e)
    (unipotentHom χ) b
  rw [pullback_unipotentHom_apply] at h
  exact h.symm

end Langlands.GroupScheme.Corepresented.RelativeUnipotent

namespace Langlands.GroupScheme.LocalRootGroup

open Corepresented Corepresented.RelativeUnipotent Corepresented.UnipotentPrimitive
  LocalSplitCell CommutativeAlgebra.GradedLine

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu a : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance globalCoordinateAffineU : IsAffineHom (Uc i mu nu).X.hom := by
  change IsAffineHom (Spec.map _)
  infer_instance

omit [DecidableEq I] in
/-- Fixed equivariant additive-group fibres give the universal graded-line fibre data. -/
theorem exists_universalGradedLine_of_equivariantFibres {d : ℕ} (hd : 0 < d)
    (had : ∑ j, a j * nu j = d) (hfib : HasEquivariantFibres i mu nu a)
    (K : Type u) [Field K] [Algebra R K] :
    ∃ ψ : coordU i mu nu →ₐ[R] K[X], IsUniversalLine K ψ ∧
      ∀ (n : ℤ) (b : coordU i mu nu),
        b ∈ homog (isGrading_unipCoaction (unipCochar i mu nu)) n →
          ∀ j : ℕ, (j : ℤ) * d ≠ n → (ψ b).coeff j = 0 := by
  obtain ⟨Φ, hΦ⟩ := hfib K
  refine ⟨fibreAlgHom i mu nu Φ K[X] Polynomial.X, isUniversalLine_fibre i mu nu Φ, ?_⟩
  exact coeff_eq_zero_of_scaling hd
    (scaling_fibre i mu nu Φ _ hΦ d (by
      rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, had]))

variable [Smooth G.X.hom]

/-- The coordinate-degree component is globally a free line, from the actual
ambient root Lie trivialization and the fixed equivariant field fibres. -/
def rootCoordinateDegreeEquiv (hmu : ∑ j, a j * mu j = 0)
    {d : ℕ} (hd : 0 < d) (had : ∑ j, a j * nu j = d)
    (eW : splitTorus.exponentWeightSpace I G i a ≃ₗ[CommRingCat.of R] CommRingCat.of R)
    (hfib : HasEquivariantFibres i mu nu a) :
    CommRingCat.of R ≃ₗ[CommRingCat.of R]
      homog (isGrading_unipCoaction (unipCochar i mu nu)) d := by
  let χ := unipCochar i mu nu
  let ε := unipotentAugmentation χ
  letI : Algebra (coordU i mu nu) (CommRingCat.of R) := ε.toRingHom.toAlgebra
  letI : IsScalarTower (CommRingCat.of R) (coordU i mu nu) (CommRingCat.of R) :=
    IsScalarTower.of_algHom ε
  let : Algebra.FiniteType R (coordU i mu nu) := finiteType_coordU i mu nu
  let : Algebra.Smooth (CommRingCat.of R) (coordU i mu nu) :=
    (DynamicSmooth.smooth_algSpec_iff _).1 (smooth_Uc i mu nu)
  have hgen : Algebra.adjoin (CommRingCat.of R)
      (homog (isGrading_unipCoaction χ) d : Set (coordU i mu nu)) = ⊤ := by
    apply adjoin_homog_eq_top (isGrading_unipCoaction χ)
      (fun b n hn => unipCoaction_coeff_neg χ b hn) (unipCoaction_coeff_zero χ) hd
    intro p hp
    let : Field (R ⧸ p) := Ideal.Quotient.field p
    obtain ⟨ψ, hu, hg⟩ := exists_universalGradedLine_of_equivariantFibres
      i mu nu a hd had hfib (R ⧸ p)
    exact ⟨ψ, ⟨hg, hu.X_mem_span⟩, hu.ker_le_quotient⟩
  have haug : IsScalarTower.toAlgHom (CommRingCat.of R) (coordU i mu nu) (CommRingCat.of R) =
      augmentation (unipotentCorepresentation χ) := by
    change unipotentAugmentation χ = _
    exact unipotentAugmentation_eq_augmentation χ
  have hnu : ∑ j, a j * nu j = ((d - 1 : ℕ) : ℤ) + 1 := by
    rw [had]
    omega
  let eLie := (rootWeightLieEquiv i mu nu a hmu (d - 1) hnu eW
    (fun K _ _ => ⟨(hfib K).choose⟩)).symm.trans eW
  let eC := LieCoordinates.cotangentEquivOfLieEquiv
    (R := CommRingCat.of R) (F := unipotentFunctor χ) (B := coordU i mu nu)
    (unipotentCorepresentation χ) haug eLie
  exact ((degreeCotangentEquiv (isGrading_unipCoaction χ)
    (unipCoaction_zero χ) hd hgen).trans eC).symm

omit [DecidableEq I] in
/-- A global homogeneous polynomial coordinate from a supplied free actual root weight. -/
theorem exists_coordinate_of_free_weight (hmu : ∑ j, a j * mu j = 0)
    {d : ℕ} (hd : 0 < d) (had : ∑ j, a j * nu j = d)
    (eW : splitTorus.exponentWeightSpace I G i a ≃ₗ[CommRingCat.of R] CommRingCat.of R)
    (hfib : HasEquivariantFibres i mu nu a) :
    ∃ x ∈ homog (isGrading_unipCoaction (unipCochar i mu nu)) d,
      Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] coordU i mu nu) := by
  classical
  let : Algebra.FiniteType R (coordU i mu nu) := finiteType_coordU i mu nu
  let : Algebra.Smooth (CommRingCat.of R) (coordU i mu nu) :=
    (DynamicSmooth.smooth_algSpec_iff _).1 (smooth_Uc i mu nu)
  exact exists_aeval_bijective_of_flat_of_free_degree
    (isGrading_unipCoaction (unipCochar i mu nu))
    (fun b n hn => unipCoaction_coeff_neg (unipCochar i mu nu) b hn)
    (unipCoaction_coeff_zero (unipCochar i mu nu)) hd
    (rootCoordinateDegreeEquiv i mu nu a hmu hd had eW hfib)
    (exists_universalGradedLine_of_equivariantFibres i mu nu a hd had hfib)

end Langlands.GroupScheme.LocalRootGroup

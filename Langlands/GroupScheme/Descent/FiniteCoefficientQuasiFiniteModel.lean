import Langlands.GroupScheme.Descent.FiniteCoefficientSmoothHomModel
import Langlands.GroupScheme.Descent.FiniteCoefficientHomProperties
import Langlands.GroupScheme.Reductive.NoetherianIsogenyApproximation
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.FiniteType

/-! # Finite coefficient models of quasi-finite flat surjections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of A))} {f : G ⟶ H}

/-- The recovery square transfers any isomorphism invariant scheme property. -/
theorem SimultaneousHomModel.property_over_algebra
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (D : SimultaneousHomModel R A f) (hf : P f.hom.hom.left) :
    P ((baseChange (Spec.algebraMap D.coefficients A)).map D.hom).hom.hom.left := by
  have he : (baseChange (Spec.algebraMap D.coefficients A)).map D.hom =
      D.sourceIso.inv ≫ f ≫ D.targetIso.hom := by
    rw [← D.comm, Iso.inv_hom_id_assoc]
  rw [he]
  change P (D.sourceIso.inv.hom.hom.left ≫ f.hom.hom.left ≫
    D.targetIso.hom.hom.hom.left)
  rw [P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact hf

/-- Relative coefficient enlargement retains both smooth affine groups. -/
def SmoothAffineHomModel.enlarge (D : SmoothAffineHomModel R A f)
    (T : Subalgebra D.coefficients A) (hT : T.FG) : SmoothAffineHomModel R A f where
  toSimultaneousHomModel := D.toSimultaneousHomModel.enlarge T hT
  targetAffine := by
    let := D.targetAffine
    change IsAffineHom (pullback.snd D.target.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance
  targetSmooth := by
    let := D.targetSmooth
    change Smooth (pullback.snd D.target.X.hom (Spec.algebraMap D.coefficients T))
    infer_instance

variable (R A)

/-- Both smooth affine groups and the three map properties over finite coefficients. -/
structure QuasiFiniteSmoothAffineHomModel (f : G ⟶ H)
    extends SmoothAffineHomModel R A f where
  homProperty : quasiFiniteFlatSurjectiveProperty hom.hom.hom.left

variable {R A}

/-- Enlargement along an inclusion preserves all three map properties. -/
def QuasiFiniteSmoothAffineHomModel.enlargeTo
    (D : QuasiFiniteSmoothAffineHomModel R A f)
    (C : Subalgebra R A) (hC : C.FG) (hDC : D.coefficients ≤ C) :
    QuasiFiniteSmoothAffineHomModel R A f where
  toSmoothAffineHomModel := D.toSmoothAffineHomModel.enlargeTo C hC hDC
  homProperty := MorphismProperty.of_isPullback
    (baseChange_map_isPullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hDC).toRingHom)) D.hom).flip
    D.homProperty

/-- The supplied map acquires all three properties at one finite coefficient stage. -/
theorem exists_quasiFiniteSmoothAffineHomModel
    (hHom : HomGeneralStatement.{u}) (f : G ⟶ H)
    [IsAffine G.X.left] [Smooth G.X.hom] [IsAffine H.X.left] [Smooth H.X.hom]
    (hf : quasiFiniteFlatSurjectiveProperty f.hom.hom.left) (s : Finset A) :
    ∃ D : QuasiFiniteSmoothAffineHomModel (R := R) (A := A) f,
      (s : Set A) ⊆ D.coefficients := by
  obtain ⟨D, hs⟩ := exists_smoothAffineHomModel (R := R) hHom f s
  let := D.sourceAffine
  let := D.sourceSmooth
  let := D.targetAffine
  let := D.targetSmooth
  obtain ⟨T, hT, hp⟩ := exists_fg_hom_quasiFinite_flat_surjective
    D.coefficients A D.hom
      (D.toSimultaneousHomModel.property_over_algebra _ hf)
  refine ⟨{ toSmoothAffineHomModel := D.enlarge T hT, homProperty := hp }, ?_⟩
  intro x hx
  exact T.algebraMap_mem ⟨x, hs hx⟩

open Langlands.AlgebraicGeometry.NoetherianApproximation
open P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC

private def quasiFiniteCoefficientStages (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] : FGIndex R A →o Subalgebra R A where
  toFun i := i.1
  monotone' _ _ h := h

private theorem quasiFiniteCoefficientStages_cover (a : A) :
    ∃ i : FGIndex R A, a ∈ quasiFiniteCoefficientStages R A i := by
  classical
  refine ⟨⟨Algebra.adjoin R ↑({a} : Finset A), Subalgebra.fg_adjoin_finset _⟩, ?_⟩
  exact Algebra.subset_adjoin (by simp)

/-- Both groups become reductive at one common stage, retaining the map properties. -/
theorem QuasiFiniteSmoothAffineHomModel.exists_reductive_extension
    (hLimit : DirectLimitReductiveStatement.{u})
    (D : QuasiFiniteSmoothAffineHomModel R A f)
    (hG : IsReductive G) (hH : IsReductive H) :
    ∃ E : QuasiFiniteSmoothAffineHomModel R A f,
      D.coefficients ≤ E.coefficients ∧ IsReductive E.source ∧ IsReductive E.target := by
  let S := quasiFiniteCoefficientStages R A
  let i₀ : FGIndex R A := ⟨D.coefficients, D.finite⟩
  let := D.sourceSmooth
  let := D.sourceAffine
  let := D.targetSmooth
  let := D.targetAffine
  obtain ⟨hc⟩ := nonempty_isColimit_ringCocone S quasiFiniteCoefficientStages_cover
  have hG' : IsReductive
      ((baseChange (Spec.map ((ringCocone S).ι.app i₀))).obj D.source) :=
    IsReductive.of_iso D.sourceIso.symm hG
  have hH' : IsReductive
      ((baseChange (Spec.map ((ringCocone S).ι.app i₀))).obj D.target) :=
    IsReductive.of_iso D.targetIso.symm hH
  obtain ⟨i₁, hi₁, hredG⟩ :=
    (hLimit (FGIndex R A) (ringDiagram S) (ringCocone S) hc i₀ D.source).2.1.mp hG'
  obtain ⟨i₂, hi₂, hredH⟩ :=
    (hLimit (FGIndex R A) (ringDiagram S) (ringCocone S) hc i₀ D.target).2.1.mp hH'
  obtain ⟨i₃, h₁₃, h₂₃⟩ := exists_ge_ge i₁ i₂
  have h₀₃ : i₀ ≤ i₃ := hi₁.trans h₁₃
  exact ⟨D.enlargeTo i₃.1 i₃.2 h₀₃, h₀₃,
    hredG i₃ h₀₃ h₁₃, hredH i₃ h₀₃ h₂₃⟩

end Langlands.GroupScheme.Descent.FiniteCoefficient

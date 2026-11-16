import Langlands.GroupScheme.Descent.FiniteCoefficientReductiveModel
import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneral
import Langlands.GroupScheme.Reductive.DirectLimitAssembly

/-! # Reductive coefficient extensions from actual reductivity descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

open Langlands.AlgebraicGeometry.NoetherianApproximation
open P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of A))} {f : G ⟶ H}

/-- A recovered reductive source becomes reductive at a finite coefficient stage. -/
theorem SimultaneousHomModel.exists_reductive_extension_of_isReductive
    (D : SimultaneousHomModel R A f) (hG : IsReductive G) :
    ∃ (C : Subalgebra R A) (hC : C.FG) (hDC : D.coefficients ≤ C),
      IsReductive (D.enlargeTo C hC hDC).source := by
  let S : FGIndex R A →o Subalgebra R A :=
    { toFun := fun i => i.1, monotone' := fun _ _ h => h }
  have hS (a : A) : ∃ i : FGIndex R A, a ∈ S i := by
    classical
    refine ⟨⟨Algebra.adjoin R ↑({a} : Finset A), Subalgebra.fg_adjoin_finset _⟩, ?_⟩
    exact Algebra.subset_adjoin (by simp)
  let i₀ : FGIndex R A := ⟨D.coefficients, D.finite⟩
  let := D.sourceSmooth
  let := D.sourceAffine
  obtain ⟨hc⟩ := nonempty_isColimit_ringCocone S hS
  have hG' : IsReductive
      ((baseChange (Spec.map ((ringCocone S).ι.app i₀))).obj D.source) :=
    IsReductive.of_iso D.sourceIso.symm hG
  obtain ⟨i₁, hi₁, hred⟩ :=
    (isReductive_baseChange_iff_eventually
      (ringDiagram S) (ringCocone S) hc i₀ D.source).mp hG'
  exact ⟨i₁.1, i₁.2, hi₁, hred i₁ hi₁ le_rfl⟩

private theorem SimultaneousHomModel.exists_reductiveExtension
    (D : SimultaneousHomModel R A f) (hG : IsReductive G) :
    ∃ E : SimultaneousHomModel R A f, D.coefficients ≤ E.coefficients ∧
      IsReductive E.source ∧ (Mono D.hom.hom.hom.left → Mono E.hom.hom.hom.left) := by
  obtain ⟨C, hC, hDC, hred⟩ := D.exists_reductive_extension_of_isReductive hG
  refine ⟨D.enlargeTo C hC hDC, hDC, hred, ?_⟩
  intro hm
  let := hm
  exact D.enlargeTo_mono C hC hDC

/-- A chosen reductive finite coefficient extension of a recovered reductive model.
It recovers the same homomorphism and preserves monicity whenever the original model is monic. -/
def SimultaneousHomModel.reductiveExtension
    (D : SimultaneousHomModel R A f) (hG : IsReductive G) :
    SimultaneousHomModel R A f :=
  Classical.choose (D.exists_reductiveExtension hG)

/-- Specifications of the chosen reductive extension. Recovery is carried by the model fields. -/
theorem SimultaneousHomModel.reductiveExtension_spec
    (D : SimultaneousHomModel R A f) (hG : IsReductive G) :
    D.coefficients ≤ (D.reductiveExtension hG).coefficients ∧
      IsReductive (D.reductiveExtension hG).source ∧
      (Mono D.hom.hom.hom.left → Mono (D.reductiveExtension hG).hom.hom.hom.left) :=
  Classical.choose_spec (D.exists_reductiveExtension hG)

/-- A finite coefficient extension can retain monicity and make the source reductive. -/
theorem SimultaneousHomModel.exists_reductive_mono_extension_of_isReductive
    (D : SimultaneousHomModel R A f) (hG : IsReductive G)
    [Mono D.hom.hom.hom.left] :
    ∃ E : SimultaneousHomModel R A f, D.coefficients ≤ E.coefficients ∧
      IsReductive E.source ∧ Mono E.hom.hom.hom.left := by
  obtain ⟨hle, hred, hm⟩ := D.reductiveExtension_spec hG
  exact ⟨D.reductiveExtension hG, hle, hred, hm inferInstance⟩

/-- Scheme monicity descent gives a reductive monic model with prescribed coefficients. -/
theorem exists_reductiveMonoModel_of_monomorphism_descent
    (hMono : Langlands.AlgebraicGeometry.FiniteCoefficient.MonomorphismStatement.{u})
    (f : G ⟶ H) (hG : IsReductive G) [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    [Mono f.hom.hom.left] (s : Finset A) :
    ∃ E : SimultaneousHomModel R A f, (s : Set A) ⊆ E.coefficients ∧
      IsReductive E.source ∧ Mono E.hom.hom.hom.left := by
  let := hG.smooth
  let := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, hs⟩ := exists_homModel (R := R) (A := A) homGeneral f s
  let := D.sourceAffine
  let := D.sourceSmooth
  let := D.targetSeparated
  obtain ⟨T, hT, -, hm⟩ := hMono D.coefficients A D.source.X D.target.X D.hom.hom.hom
    D.mono_over_algebra ∅
  let D' := D.enlarge T hT
  have : Mono D'.hom.hom.hom.left := hm
  obtain ⟨E, hDE, hred, hmono⟩ := D'.exists_reductive_mono_extension_of_isReductive hG
  refine ⟨E, ?_, hred, hmono⟩
  intro x hx
  exact hDE (T.algebraMap_mem ⟨x, hs hx⟩)

end Langlands.GroupScheme.Descent.FiniteCoefficient

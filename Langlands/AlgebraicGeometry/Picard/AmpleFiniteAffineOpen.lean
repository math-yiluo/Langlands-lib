import Langlands.AlgebraicGeometry.Picard.AmpleFiniteSetSectionProof
import Langlands.AlgebraicGeometry.Picard.AmpleTrivialQuasiAffineProof
import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleProof
import Langlands.AlgebraicGeometry.GenericPointAvoidance

/-! # Affine neighbourhoods of finite sets on ample schemes -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- Pullback along an affine morphism preserves ampleness. -/
theorem LineBundle.IsAmple.pullback_of_isAffineHom
    {X Y : Scheme.{u}} {L : LineBundle X} (hL : L.IsAmple)
    (f : Y ⟶ X) [IsAffineHom f] :
    ((LineBundle.pullback f).obj L).IsAmple := by
  let : CompactSpace X := hL.compactSpace
  refine ⟨QuasiCompact.compactSpace_of_compactSpace f, fun y ↦ ?_⟩
  obtain ⟨n, hn, s, hy, hs⟩ := hL.exists_section (f y)
  refine ⟨n, hn, L.pullbackPowSection f s, ?_, ?_⟩
  · rw [LineBundle.sectionOpen_pullbackPowSection]
    exact hy
  · rw [LineBundle.sectionOpen_pullbackPowSection]
    exact hs.preimage f

/-- The inclusion of the whole generation locus of a line-bundle section is affine. -/
theorem isAffineHom_trivializationInclusion
    {X : Scheme.{u}} (L : LineBundle X) (s : GlobalSections L.obj) :
    IsAffineHom (trivializationOpen L.obj s).ι := by
  constructor
  intro V hV
  rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
      (trivializationOpen L.obj s).ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  exact affineGenerationLocusIntersection X L s V hV

/-- Every section open of a positive power of an ample bundle is quasi-affine. -/
theorem LineBundle.IsAmple.quasiAffine_sectionOpen
    {X : Scheme.{u}} {L : LineBundle X} (hL : L.IsAmple)
    {n : ℕ} (hn : 1 ≤ n) (s : L.powSections n) :
    Scheme.IsQuasiAffine (L.sectionSubscheme s) := by
  let M : LineBundle X :=
    ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
  have hM : M.IsAmple :=
    positiveTensorPowerAmple X L M n hn hL ⟨Iso.refl _⟩
  let : IsAffineHom (L.sectionOpen s).ι :=
    isAffineHom_trivializationInclusion M s
  have hP := hM.pullback_of_isAffineHom (L.sectionOpen s).ι
  apply ampleTrivialQuasiAffine (L.sectionSubscheme s)
    ((LineBundle.pullback (L.sectionOpen s).ι).obj M) hP
  refine ⟨?_⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback (L.sectionOpen s).ι).app M.obj).symm ≪≫
    (trivializationOpenIso M.obj s).symm

/-- A finite set on a quasi-affine scheme has one affine open neighbourhood. -/
theorem exists_isAffineOpen_of_finite_of_quasiAffine
    (X : Scheme.{u}) [X.IsQuasiAffine] (E : Set X) (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ U := by
  obtain ⟨a, haE, ha⟩ := GenericPointAvoidance.exists_basicOpen_of_finite
    (hE.image X.toSpecΓ) (W := X.toSpecΓ.opensRange)
    (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩)
  refine ⟨X.toSpecΓ ⁻¹ᵁ (Spec Γ(X, ⊤)).basicOpen a, ?_, ?_⟩
  · exact ((isAffineOpen_top _).basicOpen a).preimage_of_isOpenImmersion X.toSpecΓ ha
  · intro x hx
    exact haE ⟨x, hx, rfl⟩

/-- Every finite set in an open of a scheme carrying an ample line bundle
has one affine open neighbourhood contained in that open. -/
def AmpleFiniteAffineOpenStatement : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X), L.IsAmple →
    ∀ (E : Set X) (W : X.Opens), E.Finite → E ⊆ (W : Set X) →
      ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) ∧ U ≤ W

/-- A finite set in an open of an ample scheme has one affine neighbourhood inside it. -/
theorem exists_isAffineOpen_of_finite_of_ample
    (X : Scheme.{u}) (L : LineBundle X) (hL : L.IsAmple)
    (E : Set X) (W : X.Opens) (hE : E.Finite) (hEW : E ⊆ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ U ∧ U ≤ W := by
  obtain ⟨n, hn, s, hEs, hsW⟩ := ampleFiniteSetSection X L hL E W hE hEW
  let T : X.Opens := L.sectionOpen s
  let : Scheme.IsQuasiAffine T.toScheme := hL.quasiAffine_sectionOpen hn s
  have hE' : (T.ι ⁻¹' E).Finite :=
    hE.preimage T.ι.isOpenEmbedding.injective.injOn
  obtain ⟨U, hU, hEU⟩ := exists_isAffineOpen_of_finite_of_quasiAffine
    T.toScheme _ hE'
  refine ⟨T.ι ''ᵁ U, hU.image_of_isOpenImmersion T.ι, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hEs hx⟩, hEU hx, rfl⟩
  · rintro _ ⟨y, _, rfl⟩
    exact hsW y.2

end Langlands.AlgebraicGeometry.Picard

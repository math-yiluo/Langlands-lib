import Langlands.AlgebraicGeometry.Picard.LineHom.NoetherianModelStatement
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleHomRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineFinitePresentationBaseChange
import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomCartesian
import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomDescent
import Langlands.AlgebraicGeometry.FiniteLinearModelGluing
import Langlands.AlgebraicGeometry.NoetherianApproximation.TwoComparisonLineBundleDescent
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation

/-! # Arbitrary-base reduction for proper line-bundle Hom -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.LineHom

open CoherentSheaves NoetherianApproximation
open NoetherianApproximation.TwoComparisonDescent

set_option backward.isDefEq.respectTransparency false

private theorem noetherian_of_fg {C A : Type u} [CommRing C] [CommRing A]
    [IsNoetherianRing C] [Algebra C A] {B : Subalgebra C A} (hB : B.FG) :
    IsNoetherianRing B := by
  have := (Subalgebra.fg_iff_finiteType B).mp hB
  exact Algebra.FiniteType.isNoetherianRing C B

/-- Descend two line bundles successively from a proper flat noetherian stage,
then transport its full-slice Hom representation to the original base. -/
theorem intrinsicHom_representable_of_noetherianStage
    (h : NoetherianModelStatement.{u})
    {C A : Type u} [CommRing C] [CommRing A] [IsNoetherianRing C] [Algebra C A]
    {Y₀ Y : Scheme.{u}} (p₀ : Y₀ ⟶ Spec (CommRingCat.of C)) [IsProper p₀] [Flat p₀]
    (q : Y ⟶ Y₀) (p : Y ⟶ Spec (CommRingCat.of A))
    (hCart : IsPullback q p p₀ (Spec.map (CommRingCat.ofHom (algebraMap C A))))
    (L M : Y.Modules) (hL : IsLocallyFreeRankOne L) (hM : IsLocallyFreeRankOne M) :
    AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (intrinsicModuleHomPresheaf p L M) := by
  obtain ⟨B, hB, -, LB, hLB, hLBcomp⟩ :=
    lineBundleSubalgebraDescent p₀ q p hCart L hL ∅
  let β := Spec.map (CommRingCat.ofHom (algebraMap C B))
  let κ := Spec.map (CommRingCat.ofHom (algebraMap B A))
  have hκβ : κ ≫ β = Spec.map (CommRingCat.ofHom (algebraMap C A)) := by
    dsimp only [κ, β]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hw : q ≫ p₀ = p ≫ κ ≫ β := by rw [hκβ]; exact hCart.w
  let c := comparison q p p₀ β κ hw
  have hc : IsPullback c p (pullback.snd p₀ β) κ := by
    apply comparison_isPullback
    rw [hκβ]
    exact hCart
  obtain ⟨eLB⟩ := hLBcomp c (comparison_fst ..) (comparison_snd ..)
  let : IsNoetherianRing B := noetherian_of_fg hB
  obtain ⟨D, hD, -, MD, hMD, hMDcomp⟩ :=
    lineBundleSubalgebraDescent (pullback.snd p₀ β) c p hc M hM ∅
  let δ := Spec.map (CommRingCat.ofHom (algebraMap B D))
  let κD := Spec.map (CommRingCat.ofHom (algebraMap D A))
  have hκDδ : κD ≫ δ = κ := by
    dsimp only [κD, δ, κ]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hwD : c ≫ pullback.snd p₀ β = p ≫ κD ≫ δ := by
    rw [hκDδ]
    exact comparison_snd ..
  let d := comparison c p (pullback.snd p₀ β) δ κD hwD
  have hd : IsPullback d p (pullback.snd (pullback.snd p₀ β) δ) κD := by
    apply comparison_isPullback
    rw [hκDδ]
    exact hc
  obtain ⟨eMD⟩ := hMDcomp d (comparison_fst ..) (comparison_snd ..)
  let LD := (Scheme.Modules.pullback (pullback.fst (pullback.snd p₀ β) δ)).obj LB
  have hLD : IsLocallyFreeRankOne LD := hLB.pullback _
  have eLD : (Scheme.Modules.pullback d).obj LD ≅ L :=
    (Scheme.Modules.pullbackComp d (pullback.fst (pullback.snd p₀ β) δ)).app LB ≪≫
      (Scheme.Modules.pullbackCongr (comparison_fst ..)).app LB ≪≫ eLB
  let : IsNoetherianRing D := noetherian_of_fg hD
  have hrep : AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (intrinsicModuleHomPresheaf (pullback.snd (pullback.snd p₀ β) δ) LD MD) :=
    (h (CommRingCat.of D) inferInstance _ _ inferInstance inferInstance
      LD MD hLD hMD).exists_representation
  exact (hrep.baseChange κD).of_iso (intrinsicModuleHomCartesianOfIso hd eLD eMD)

/-- Proper flat finitely presented geometry and two line bundles over an
arbitrary affine base admit an affine finitely presented Hom representative. -/
theorem intrinsicHom_representable_affine
    (h : NoetherianModelStatement.{u}) (R : CommRingCat.{u})
    (Y : Scheme.{u}) (p : Y ⟶ Spec R)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (L M : Y.Modules) (hL : IsLocallyFreeRankOne L) (hM : IsLocallyFreeRankOne M) :
    AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (intrinsicModuleHomPresheaf p L M) := by
  let : IsNoetherianRing (⊥ : Subalgebra ℤ R) := by
    have := (Subalgebra.fg_iff_finiteType (⊥ : Subalgebra ℤ R)).mp Subalgebra.fg_bot
    exact Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨C, hC, -, Y₀, p₀, q, hp₀, hflat₀, hCart⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
      (A₀ := (⊥ : Subalgebra ℤ R)) p ∅
  let : IsNoetherianRing C := noetherian_of_fg hC
  let : IsProper p₀ := hp₀
  let : Flat p₀ := hflat₀
  exact intrinsicHom_representable_of_noetherianStage h p₀ q p hCart L M hL hM

/-- Affine open charts and actual Hom descent give representation over every
base scheme, with the natural comparison on its entire scheme slice. -/
theorem intrinsicHom_representable
    (h : NoetherianModelStatement.{u}) (B Y : Scheme.{u}) (p : Y ⟶ B)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (L M : Y.Modules) (hL : IsLocallyFreeRankOne L) (hM : IsLocallyFreeRankOne M) :
    AlgebraicSpace.IsAffineFinitePresentationRepresentable
      (intrinsicModuleHomPresheaf p L M) := by
  let : M.IsQuasicoherent := hM.isQuasicoherent
  let 𝒰 := B.affineOpenCover
  have hLocal : ∀ i : 𝒰.I₀,
      AlgebraicSpace.IsAffineFinitePresentationRepresentable
        ((Over.map (𝒰.f i)).op ⋙ intrinsicModuleHomPresheaf p L M) := by
    intro i
    let : IsProper (pullback.fst (𝒰.f i) p) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsProper p)
    let : Flat (pullback.fst (𝒰.f i) p) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : Flat p)
    let : LocallyOfFinitePresentation (pullback.fst (𝒰.f i) p) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : LocallyOfFinitePresentation p)
    exact (intrinsicHom_representable_affine h (𝒰.X i)
      (pullback (𝒰.f i) p) (pullback.fst (𝒰.f i) p)
      ((Scheme.Modules.pullback (pullback.snd (𝒰.f i) p)).obj L)
      ((Scheme.Modules.pullback (pullback.snd (𝒰.f i) p)).obj M)
      (hL.pullback _) (hM.pullback _)).of_iso
        (intrinsicModuleHomBaseChangeIso p (𝒰.f i) L M).symm
  choose H he hAffine hFP using hLocal
  exact AlgebraicSpace.LocalRepresentation.exists_affine_representation
    ((isSheaf_iff_isSheaf_of_type _ _).2
      (isSheaf_intrinsicModuleHomPresheaf_fppf p L M))
    𝒰.openCover H (fun i ↦ (he i).some) hAffine hFP

/-- The noetherian affine-base model statement implies the exact proper
line-bundle Hom proposition for arbitrary schemes and all test schemes. -/
theorem properLineBundleHomRepresentability_of_noetherianModel
    (h : NoetherianModelStatement.{u}) : ProperLineBundleHomRepresentabilityStatement.{u} := by
  intro S X f hf hflat hfp T L M
  let : IsProper ((relativeProjection f).app T) :=
    MorphismProperty.pullback_fst _ _ hf
  let : Flat ((relativeProjection f).app T) :=
    MorphismProperty.pullback_fst _ _ hflat
  let : LocallyOfFinitePresentation ((relativeProjection f).app T) :=
    MorphismProperty.pullback_fst _ _ hfp
  exact intrinsicHom_representable h T.left ((relativeSpace f).obj T)
    ((relativeProjection f).app T) L.of.obj M.of.obj L.of.property M.of.property

end Langlands.AlgebraicGeometry.Picard.LineHom

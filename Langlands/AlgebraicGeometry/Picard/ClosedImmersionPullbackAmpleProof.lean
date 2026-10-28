import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleStatement
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof

/-! # Closed-immersion preservation of ampleness -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- Actual pullback commutes with every tensor power of an arbitrary module sheaf. -/
def actualPullbackTensorPowIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) :
    (n : ℕ) → (Scheme.Modules.pullback f).obj (tensorPow M n) ≅
      tensorPow ((Scheme.Modules.pullback f).obj M) n
  | 0 => pullbackUnitIso f
  | n + 1 =>
    letI : IsIso (pullbackTensorComparison f) := pullbackTensorComparisonIsIso f
    (asIso (pullbackTensorComparison f)).app (M, tensorPow M n) ≪≫
      (tensorFunctor Y).mapIso
        ((Iso.refl _).prod (actualPullbackTensorPowIso f M n))

/-- Pull a power section back and transport it to the power of the pulled-back bundle. -/
def LineBundle.pullbackPowSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : LineBundle X) {n : ℕ}
    (s : L.powSections n) : ((LineBundle.pullback f).obj L).powSections n :=
  (actualPullbackTensorPowIso f L.obj n).hom.app ⊤
    (pullbackSection f (tensorPow L.obj n) s)

/-- Pulling back a power section pulls back its entire generation open. -/
theorem LineBundle.sectionOpen_pullbackPowSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : LineBundle X) {n : ℕ}
    (s : L.powSections n) :
    ((LineBundle.pullback f).obj L).sectionOpen (L.pullbackPowSection f s) =
      f ⁻¹ᵁ L.sectionOpen s := by
  change trivializationOpen (tensorPow ((Scheme.Modules.pullback f).obj L.obj) n)
      ((actualPullbackTensorPowIso f L.obj n).hom.app ⊤
        (pullbackSection f (tensorPow L.obj n) s)) = _
  rw [trivializationOpen_mapIso]
  exact lineBundlePullbackSectionOpen X Y f
    ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩ s

/-- Actual pullback along a closed immersion preserves ampleness. -/
theorem closedImmersionPullbackAmple :
    ClosedImmersionPullbackAmpleStatement.{u} := by
  intro X Z i L hi hL
  let : IsClosedImmersion i := hi
  let : CompactSpace X := hL.1
  refine ⟨i.isClosedEmbedding.compactSpace, ?_⟩
  intro z
  obtain ⟨n, hn, s, hz, ha⟩ := hL.2 (i z)
  let s' := L.pullbackPowSection i s
  have hopen :
      ((LineBundle.pullback i).obj L).sectionOpen s' = i ⁻¹ᵁ L.sectionOpen s :=
    LineBundle.sectionOpen_pullbackPowSection i L s
  refine ⟨n, hn, s', ?_, ?_⟩
  · rw [hopen]
    exact hz
  · rw [hopen]
    exact ha.preimage i

end Langlands.AlgebraicGeometry.Picard

import Langlands.Global.AdelicSpacePointTopologyStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitModelExistenceProof
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Langlands.Global.CurvePlaceExtension

/-!
# Separated models of algebraic spaces over rings of `S`-integers
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.SchemeLimitModel

namespace Langlands.Global

/-- Over a field, an atlas of finite type is locally of finite presentation. -/
theorem finitePresentationAtlas_of_finiteTypeOverRing {K : Type u} [Field K]
    {Y : AlgebraicSpace (Spec (CommRingCat.of K))} (h : FiniteTypeOverRing K Y) :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y := by
  obtain ⟨U, a, ha, hs, hl, hq⟩ := h
  have : LocallyOfFiniteType U.hom := hl
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  exact ⟨U, a, ha, hs, inferInstance, hq⟩

/-- A quasi-compact locally finitely presented atlas is of finite type. -/
theorem finiteTypeOverRing_of_atlas {C : Type u} [CommRing C]
    {X : AlgebraicSpace (Spec (CommRingCat.of C))}
    (h : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    FiniteTypeOverRing C X :=
  h.mono fun _ _ f hf => ⟨by have := hf.1; infer_instance, hf.2⟩

/-- **Function fields.** Every separated algebraic space of finite type over the function field
has a separated model of finite type over the `S`-integers for some nonempty `S`. -/
theorem curvePlaceSpaceSpreadExistence (k F : Type u) [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (Y : AlgebraicSpace (Spec (CommRingCat.of F))) (hY : IsSeparated Y)
    (hft : FiniteTypeOverRing F Y) :
    ∃ (S : Finset (AlgebraicCurve.Place k F))
      (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))),
      S.Nonempty ∧ IsSeparated X ∧ FiniteTypeOverRing (curvePlaceSIntegers k F S) X ∧
        Nonempty (curvePlaceSpaceGenericFiber k F S X ≅ Y) := by
  obtain ⟨v⟩ := curvePlace_nonempty k F
  let S₀ : Finset (AlgebraicCurve.Place k F) := {v}
  obtain ⟨i, X, hX, hXat, ⟨e⟩⟩ := spaceLimitModelExistence _
    (spectrumDiagram _ (curvePlaceSIntegersOverDiagram k F S₀))
    (spectrumCone _ _ (curvePlaceSIntegersOverCocone k F S₀))
    (spectrumConeIsLimit _ _ _ (curvePlaceSIntegersOverIsColimit k F S₀)) Y hY
    (finitePresentationAtlas_of_finiteTypeOverRing hft)
  exact ⟨i.unop.val, X, ⟨v, i.unop.property (Finset.mem_singleton_self v)⟩, hX,
    finiteTypeOverRing_of_atlas hXat, ⟨e⟩⟩

/-- **Number fields.** Every separated algebraic space of finite type over the number field has a
separated model of finite type over the `S`-integers for some `S`. -/
theorem numberFieldSpaceSpreadExistence (K : Type u) [Field K] [NumberField K]
    (Y : AlgebraicSpace (Spec (CommRingCat.of K))) (hY : IsSeparated Y)
    (hft : FiniteTypeOverRing K Y) :
    ∃ (S : Finset (FinitePlace K))
      (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
      IsSeparated X ∧ FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X ∧
        Nonempty (numberFieldSpaceGenericFiber K S X ≅ Y) := by
  obtain ⟨i, X, hX, hXat, ⟨e⟩⟩ := spaceLimitModelExistence _
    (spectrumDiagram _ (numberFieldSIntegersOverDiagram K ∅))
    (spectrumCone _ _ (numberFieldSIntegersOverCocone K ∅))
    (spectrumConeIsLimit _ _ _ (numberFieldSIntegersOverIsColimit K ∅)) Y hY
    (finitePresentationAtlas_of_finiteTypeOverRing hft)
  exact ⟨i.unop.val, X, hX, finiteTypeOverRing_of_atlas hXat, ⟨e⟩⟩

end Langlands.Global

import Langlands.Representation.Plancherel.SplitComponentLatticeBridge
import Langlands.GroupScheme.Rational.CentralTorusCharacterStatement
import Langlands.GroupScheme.Torus.CocharacterDetection

/-! # Detecting nonzero rational characters by the actual valuations

A rational character of `G` whose restriction along a split torus `s : T ⟶ G` is nonzero has
nonzero valuation at the image of some uniformizer point of `T`. Each of the three structural
detection statements for connected reductive groups therefore gives a rational point with nonzero
valuation for every nonzero rational character.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Plancherel.RationalValuationDetection

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- The rational point `s(ϖ^c)` of `G`: the image under `s : T ⟶ G` of the uniformizer point
`ϖ^c = uniformizerSection T (ofAdd c)` of `T` attached to the cocharacter `c`. -/
def splitTorusUniformizerPoint {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (s : T.toGrp ⟶ G) (c : cocharacterLattice T) : rationalPoints G :=
  rationalPoints.map s (RenardCartan.uniformizerSection T (Multiplicative.ofAdd c))

/-- The valuation of `s(ϖ^c)` on `χ` is the integer pairing of the restricted character with
`c`. -/
theorem rationalCharacterValuation_splitTorusUniformizerPoint
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G) (c : cocharacterLattice T)
    (χ : rationalCharacters G) :
    (rationalCharacterValuation G (splitTorusUniformizerPoint s c)).toAdd χ =
      latticePairing T (rationalCharacters.equivCharacterLattice T (characterRestrict s χ)) c :=
  RenardCartan.rationalCharacterValuation_map_uniformizerSection s c χ

/-- A rational character with nonzero restriction along a split torus `s : T ⟶ G` has nonzero
valuation at the image under `s` of some uniformizer point of `T`. -/
theorem exists_map_uniformizerSection_ne_zero {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (s : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) {χ : rationalCharacters G}
    (hχ : characterRestrict s χ ≠ 0) :
    ∃ c : cocharacterLattice T,
      (rationalCharacterValuation G (splitTorusUniformizerPoint s c)).toAdd χ ≠ 0 := by
  let := CocharacterUniformizer.latticePairing_isPerfPair F T hT
  have hinj := (LinearMap.IsPerfPair.bijective_left (latticePairing T)).injective
  have hα : rationalCharacters.equivCharacterLattice T (characterRestrict s χ) ≠ 0 :=
    (AddEquiv.map_ne_zero_iff _).mpr hχ
  have hne : latticePairing T (rationalCharacters.equivCharacterLattice T
      (characterRestrict s χ)) ≠ 0 := by
    intro h
    exact hα (hinj (h.trans (map_zero _).symm))
  obtain ⟨c, hc⟩ := not_forall.mp fun h => hne (LinearMap.ext h)
  refine ⟨c, ?_⟩
  rw [rationalCharacterValuation_splitTorusUniformizerPoint]
  exact hc

/-- A rational character with nonzero restriction along a split torus has nonzero valuation at
some rational point. -/
theorem exists_rationalCharacterValuation_ne_zero_of_splitTorus
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) {χ : rationalCharacters G} (hχ : characterRestrict s χ ≠ 0) :
    ∃ g : rationalPoints G, (rationalCharacterValuation G g).toAdd χ ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_map_uniformizerSection_ne_zero s hT hχ
  exact ⟨_, hc⟩

/-- If central split tori detect nonzero rational characters, the actual valuations detect every
nonzero rational character of a connected reductive group. -/
theorem exists_rationalCharacterValuation_ne_zero_of_centralSplitTorusCharacter
    (hS : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    {χ : rationalCharacters G} (hχ : χ ≠ 0) :
    ∃ g : rationalPoints G, (rationalCharacterValuation G g).toAdd χ ≠ 0 := by
  obtain ⟨A, i, hi, hne⟩ := hS F G hG χ hχ
  exact exists_rationalCharacterValuation_ne_zero_of_splitTorus i hi.1.1 hne

/-- If central tori detect nonzero rational characters, the actual valuations detect every
nonzero rational character of a connected reductive group: a cocharacter `𝔾_m ⟶ Z` of the
central torus detects the restricted character. -/
theorem exists_rationalCharacterValuation_ne_zero_of_centralTorusCharacter
    (hS : CentralTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    {χ : rationalCharacters G} (hχ : χ ≠ 0) :
    ∃ g : rationalPoints G, (rationalCharacterValuation G g).toAdd χ ≠ 0 := by
  obtain ⟨Z, i, hAff, hLFT, hZ, -, -, hne⟩ := hS F G hG χ hχ
  obtain ⟨φ, hφ⟩ := CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus hZ hne
  refine exists_rationalCharacterValuation_ne_zero_of_splitTorus (φ ≫ i) isSplitTorus_gm ?_
  rwa [characterRestrict_comp, AddMonoidHom.comp_apply]

/-- If restriction of rational characters to a split component is injective, the actual
valuations detect every nonzero rational character of a connected reductive group. -/
theorem exists_rationalCharacterValuation_ne_zero_of_characterRestriction
    (hR : CharacterRestrictionStatement.{u}) (hG : IsConnectedReductive G)
    {χ : rationalCharacters G} (hχ : χ ≠ 0) :
    ∃ g : rationalPoints G, (rationalCharacterValuation G g).toAdd χ ≠ 0 := by
  obtain ⟨A, i, hi⟩ := (splitComponentStatement F G hG).1
  have hne : characterRestrict i χ ≠ 0 := by
    intro h
    exact hχ ((hR F G hG A i hi).1 (h.trans (map_zero _).symm))
  exact exists_rationalCharacterValuation_ne_zero_of_splitTorus i hi.1.1.1 hne

end Langlands.Plancherel.RationalValuationDetection

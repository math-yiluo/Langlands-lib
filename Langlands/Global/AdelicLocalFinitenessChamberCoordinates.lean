import Langlands.Global.AdelicLocalFinitenessTorusCoordinates
import Langlands.Global.AdelicSiegelSetupExistenceProof
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.Global.AdelicIwasawaHeight
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Root and central coordinates of the minimal-parabolic height -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Set
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable (F : Type u) [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local notation "P" => Standard.parabolicScheme i ν ∅
local notation "M" => Standard.leviScheme i ν ∅
local notation "p" => Standard.parabolicHom i ν ∅
local notation "levi" => Standard.leviToParabolic i ν ∅
local notation "tM" => torusToStandardLevi F G T i ν
local notation "tP" => torusToStandardParabolic F G T i ν
local notation "Δ" => simpleRelativeRoots i ν

omit [NumberField F] in
/-- The actual algebraic Siegel setup can use the given maximal split torus and
its given generic cocharacter. Only the derived split factor has to be chosen. -/
theorem exists_siegelAlgebraicSetup_of_generic
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
      IsSiegelAlgebraicSetup F G T i ν T₀ j := by
  obtain ⟨D, d, -, -, hd⟩ := derivedSubgroupRepresentability F G
  obtain ⟨T₀, t₀, e, ht₀, he_closed, he⟩ := derivedMaximalSplitTorus F G D d hG hd T i hi
  obtain ⟨⟨A, a, ha⟩, -⟩ := splitComponentStatement F G hG
  obtain ⟨c, hc, -, -⟩ := ha.exists_commFactor_of_isMaximalSplitTorus hi
  have hiso := derivedCentralSplitTorusProduct F G D d hG hd T T₀ A i t₀ e a c hi ht₀ he_closed he ha hc
  obtain ⟨-, hRL, hU⟩ := standardMinimalLeviStructure F G T i ν hG hi hν
  refine ⟨T₀, e, hi, hν,
    Standard.isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal i ν genericMinimalParabolic
      hG hi hν, hRL, hU, standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν,
    relativeRoots_torusToStandardParabolic F G T i ν hG hi hν,
    ⟨D, d, t₀, hd, ht₀, he⟩, A, c, ?_, ?_⟩
  · rw [hc]
    exact ha
  · rw [subgroupProductMap_eq_prodHom e c]
    exact hiso.surjective

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- Restriction to the prescribed maximal split torus gives an isomorphism of
real character duals for the actual standard minimal parabolic. -/
theorem exists_minimalParabolicTorusDualEquiv
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    ∃ e : RealCharacterDual F T.toGrp ≃L[ℝ] RealCharacterDual F P,
      ∀ h, e h = realCharacterDualMap F T.toGrp P tP h := by
  obtain ⟨-, hLevi, -⟩ := standardMinimalLeviStructure F G T i ν hG hi hν
  have hM := hLevi.isConnectedReductive
  let : IsAffineHom (M).X.hom := hM.isAffineHom
  have hmax := hi.isMaximalSplitTorus_standardLeviTorusFactor i ν ∅
    (Standard.isRepresentedBy_leviHom i ν ∅) (Standard.isClosedSubgroup_leviHom i ν ∅)
  have hcent : IsCentral tM := by
    apply isCentral_of_range_le_torusCentralizer (Standard.isRepresentedBy_leviHom i ν ∅).1
    rw [torusToStandardLevi_comp, (Standard.isRepresentedBy_leviHom i ν ∅).2,
      standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν]
  have hsplit : IsSplitComponent tM :=
    ⟨⟨hmax.1, hcent⟩, fun S s hs x hx => hmax.2 S s hs.1 x hx⟩
  have hresM := characterRestrict_injective_of_centralSplitTorusCharacter
    centralSplitTorusCharacter hM hsplit
  have hresP : Function.Injective (characterRestrict tP) := by
    rw [torusToStandardParabolic, characterRestrict_comp]
    exact hresM.comp hLevi.characterRestrict_bijective.injective
  have hrange : (characterRestrict tP).range = (characterRestrict tM).range := by
    rw [torusToStandardParabolic, characterRestrict_comp]
    ext χ
    change (∃ ψ, characterRestrict tM (characterRestrict levi ψ) = χ) ↔
      (∃ ψ, characterRestrict tM ψ = χ)
    constructor
    · rintro ⟨ψ, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨ψ, rfl⟩
      obtain ⟨ξ, rfl⟩ := hLevi.characterRestrict_bijective.surjective ψ
      exact ⟨ξ, rfl⟩
  let : (characterRestrict tP).range.FiniteIndex :=
    hrange ▸ hsplit.finiteIndex_range_characterRestrict hM
  exact ⟨realCharacterDualRestrictionEquiv F P T.toGrp tP hresP, fun _ => rfl⟩

/-- The minimal-parabolic height coordinates have normalized root components
and central components detecting the ambient dual. Each prescribed positive
point has a single unit coordinate under its actual parabolic logarithm. -/
def AdelicLocalFinitenessChamberCoordinatesStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
  ∀ {Ua : Δ → GroupScheme (Spec (CommRingCat.of F))}
    (u : ∀ α, Ua α ⟶ G) (t : Δ → AdelicGroupPoints F T.toGrp)
    {r : ℕ} (z : Fin r → AdelicGroupPoints F T.toGrp),
  IsLocalFinitenessGroupData i ν u t z →
  ∃ (d : RealCharacterDual F T.toGrp ≃L[ℝ] RealCharacterDual F P)
    (e : RealCharacterDual F P ≃L[ℝ] ((Δ → ℝ) × (Fin r → ℝ))),
    (∀ h, d h = realCharacterDualMap F T.toGrp P tP h) ∧
    (∀ h α, (e (d h)).1 α = h α.val / localFinitenessRootStep i ν t α) ∧
    (∀ h, (e (d h)).2 = 0 ↔ realCharacterDualMap F T.toGrp G i h = 0) ∧
    (∀ α, 0 < localFinitenessRootStep i ν t α ∧
      e (characterLog F P (map F T.toGrp P tP (t α))) = (Pi.single α 1, 0)) ∧
    (∀ j, e (characterLog F P (map F T.toGrp P tP (z j))) = (0, Pi.single j 1))

omit [LocallyOfFiniteType G.X.hom] in
theorem adelicLocalFinitenessChamberCoordinates :
    AdelicLocalFinitenessChamberCoordinatesStatement F i ν := by
  intro hG hi hν Ua u t r z hData
  obtain ⟨d, hd⟩ := exists_minimalParabolicTorusDualEquiv F i ν hG hi hν
  obtain ⟨c, hc, hCen, hRootShift, hCenShift⟩ :=
    localFinitenessTorusCoordinates i ν hG hi hν u t z hData
  let e := d.symm.trans c
  have he (h : RealCharacterDual F T.toGrp) : e (d h) = c h := by
    change c (d.symm (d h)) = c h
    rw [d.symm_apply_apply]
  have hlog (a : AdelicGroupPoints F T.toGrp) :
      e (characterLog F P (map F T.toGrp P tP a)) = c (characterLog F T.toGrp a) := by
    rw [characterLog_map, ← hd, he]
  exact ⟨d, e, hd, fun h α => (congrArg (fun x => x.1 α) (he h)).trans (hc h α),
    fun h => by rw [he, hCen], fun α => ⟨(hRootShift α).1, (hlog _).trans (hRootShift α).2⟩,
    fun j => (hlog _).trans (hCenShift j)⟩

end Langlands.Global.AdelicSiegelFactors

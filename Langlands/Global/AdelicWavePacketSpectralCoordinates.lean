import Langlands.Global.ArthurParabolicSpaces
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.Representation.Exponents.MaximalLeviExponentTransport
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Spectral coordinates with a prescribed central frequency -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory Module
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Global

open GroupScheme RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

local notation "Z[" n "]" => (Fin n → ℝ)
local notation "ζ[" n "]" => (volume : Measure (Fin n → ℝ))

private theorem exists_product_coordinates {n m : ℕ} (L : Z[n] →ₗ[ℝ] Z[m])
    (hL : Function.Surjective L) :
    ∃ (k : ℕ) (ν₁ : Measure Z[k]) (A : (Z[k] × Z[m]) ≃ₗ[ℝ] Z[n]),
      ν₁.IsAddHaarMeasure ∧ MeasurePreserving A (ν₁.prod ζ[m]) ζ[n] ∧
      ∀ u z, L (A (u, z)) = z := by
  let W := LinearMap.ker L
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl W
  let B : U ≃ₗ[ℝ] Z[m] := LinearEquiv.ofBijective (L.domRestrict U)
    ⟨LinearMap.injective_domRestrict_iff.mpr hU.disjoint.symm,
      (LinearMap.surjective_domRestrict_iff hL).mpr hU.symm.codisjoint⟩
  let k := Module.finrank ℝ W
  let A := ((Module.finBasis ℝ W).equivFun.symm.prodCongr B.symm).trans
    (Submodule.prodEquivOfIsCompl W U hU)
  have hA₀ : ∀ u z, L (A (u, z)) = z := by
    intro u z
    change L (Submodule.prodEquivOfIsCompl W U hU ((Module.finBasis ℝ W).equivFun.symm u,
      B.symm z)) = _
    rw [Submodule.coe_prodEquivOfIsCompl', map_add, LinearMap.mem_ker.mp
      ((Module.finBasis ℝ W).equivFun.symm u).property, zero_add]
    exact B.apply_symm_apply z
  let e := A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let μPull := Measure.map e.symm ζ[n]
  let prodVol := ζ[k].prod ζ[m]
  let : μPull.IsAddHaarMeasure := A.toContinuousLinearEquiv.symm.isAddHaarMeasure_map ζ[n]
  let : prodVol.IsAddHaarMeasure := inferInstanceAs ((ζ[k].prod ζ[m]).IsAddHaarMeasure)
  let c := Measure.addHaarScalarFactor μPull prodVol
  have hc : c ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μPull prodVol).ne'
  let ν₁ := (c : ℝ≥0∞) • ζ[k]
  have hν₁ : ν₁.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _ (ENNReal.coe_ne_zero.mpr hc) ENNReal.coe_ne_top
  refine ⟨k, ν₁, A, hν₁, ?_, hA₀⟩
  have hμ : μPull = (c : ℝ≥0∞) • prodVol := Measure.isAddLeftInvariant_eq_smul μPull prodVol
  have hA : MeasurePreserving e μPull ζ[n] :=
    MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩
  change MeasurePreserving A (((c : ℝ≥0∞) • ζ[k]).prod ζ[m]) ζ[n]
  rw [Measure.prod_smul_left, ← hμ]
  exact hA

section CentralFrequency

variable {F : Type} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {m : ℕ}

/-- Restriction of a real parameter to the central directions, evaluated on their basis. -/
def wavePacketCentralFrequency (b : Basis (Fin m) ℝ (relativeCentralDirections i)) :
    Vstar T →ₗ[ℝ] Z[m] :=
  LinearMap.pi fun r => (pair T).flip (b r : V T)

@[simp] theorem wavePacketCentralFrequency_apply (b : Basis (Fin m) ℝ (relativeCentralDirections i))
    (x : Vstar T) (r : Fin m) : wavePacketCentralFrequency b x r = pair T x (b r : V T) := rfl

/-- Equality of central frequencies is equivalent to a difference in the real root span. -/
theorem wavePacketCentralFrequency_eq_iff (hT : IsSplitTorus T.toGrp)
    (b : Basis (Fin m) ℝ (relativeCentralDirections i)) (x y : Vstar T) :
    wavePacketCentralFrequency b x = wavePacketCentralFrequency b y ↔ x - y ∈ relativeRootSpanReal i := by
  have hker : (wavePacketCentralFrequency b).ker = characterAnnihilator (relativeCentralDirections i) := by
    ext z
    rw [LinearMap.mem_ker, mem_characterAnnihilator]
    constructor
    · intro hz v hv
      have hsum : ∑ r, b.equivFun ⟨v, hv⟩ r • (b r : V T) = v := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using
          congrArg Subtype.val (b.sum_equivFun ⟨v, hv⟩)
      rw [← hsum, map_sum]
      apply Finset.sum_eq_zero
      intro r _
      rw [map_smul, show pair T z (b r : V T) = 0 from congrFun hz r, smul_zero]
    · intro hz
      funext r
      exact hz _ (b r).property
  have hroot : characterAnnihilator (relativeCentralDirections i) = relativeRootSpanReal i := by
    rw [relativeCentralDirections, rootAnnihilator_eq_cocharacterAnnihilator,
      characterAnnihilator_cocharacterAnnihilator hT]
    rfl
  rw [← hroot, ← hker, LinearMap.mem_ker, map_sub, sub_eq_zero]

private theorem wavePacketCentralFrequency_surjective (hT : IsSplitTorus T.toGrp)
    (b : Basis (Fin m) ℝ (relativeCentralDirections i)) :
    Function.Surjective (wavePacketCentralFrequency b) := by
  let C := relativeCentralDirections i
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective C.subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  let hperf := isPerfPair_of_isSplitTorus hT
  intro z
  obtain ⟨x, hx⟩ := hperf.bijective_left.surjective ((b.constr ℝ z).comp p)
  refine ⟨x, ?_⟩
  funext r
  rw [wavePacketCentralFrequency_apply, LinearMap.congr_fun hx, LinearMap.comp_apply,
    show p (b r : V T) = b r from LinearMap.congr_fun hp (b r), Basis.constr_basis]

end CentralFrequency

/-- In spectral coordinates for any standard parabolic, a prescribed basis of the central
cocharacters can be used as the second coordinate block with unscaled Lebesgue measure. -/
def WavePacketSpectralCoordinatesStatement : Prop :=
  ∀ (F : Type) [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (_hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (S : Set (characterLattice T)) (n m : ℕ)
    (e : Z[n] ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν S))
    (b : Basis (Fin m) ℝ (relativeCentralDirections i)),
    ∃ (k : ℕ) (ν₁ : Measure Z[k]) (A : (Z[k] × Z[m]) ≃ₗ[ℝ] Z[n]),
      ν₁.IsAddHaarMeasure ∧ MeasurePreserving A (ν₁.prod ζ[m]) ζ[n] ∧
      ∀ u z r, pair T (restrictToTorus F i ν S (e (A (u, z)))) (b r : V T) = z r

/-- Split the central restriction, then transfer the product Haar scalar to the first block. -/
theorem wavePacketSpectralCoordinates : WavePacketSpectralCoordinatesStatement := by
  intro F _ G _ hG T i hi ν S n m e b
  let hT := hi.isSplitSubtorus.1
  let L := wavePacketCentralFrequency b
  let res := restrictToTorus F i ν S
  have hsurj : Function.Surjective (L.comp (res.comp e.toLinearMap)) := by
    intro z
    obtain ⟨t, ht⟩ := wavePacketCentralFrequency_surjective hT b z
    have hc := (relativeCharacterRootComplement F G hG T i hi).2
    have hmem : t ∈ relativeRootSpanReal i ⊔ (rationalCharacterRestrictReal i).range :=
      hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hmem
    have hzero : L a = 0 := by
      rw [← L.map_zero]
      exact (wavePacketCentralFrequency_eq_iff hT b a 0).mpr (by rwa [sub_zero])
    let p := Standard.parabolicHom i ν S
    have hr : res (rationalCharacterRestrictReal p x) = rationalCharacterRestrictReal i x := by
      change rationalCharacterRestrictReal (torusToParabolic F i ν S)
        (rationalCharacterRestrictReal (Standard.parabolicHom i ν S) x) = _
      rw [rationalCharacterRestrictReal_comp_apply, torusToParabolic_comp]
    refine ⟨e.symm (rationalCharacterRestrictReal p x), ?_⟩
    change L (res (e (e.symm (rationalCharacterRestrictReal p x)))) = z
    rw [LinearEquiv.apply_symm_apply, hr, ← ht, map_add, hzero, zero_add]
  obtain ⟨k, μRel, A, hμ, hA, hfreq⟩ := exists_product_coordinates _ hsurj
  exact ⟨k, μRel, A, hμ, hA, fun u z r => congrFun (hfreq u z) r⟩

end Langlands.Global

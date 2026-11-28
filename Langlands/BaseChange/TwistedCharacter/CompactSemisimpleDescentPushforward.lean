import Langlands.BaseChange.TwistedCharacter.RestrictedDescentPushforward
import Langlands.BaseChange.TwistedCharacter.SemisimpleDescentPushforward
import Langlands.BaseChange.TwistedCharacter.TranslatedCosetCharacter
import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialCongruenceHaar
import Langlands.Representation.Character.CompactTraceDescentWitness

/-! # The compact conjugation pushforward in a semisimple descent -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Set Function Metric _root_.Topology
open UnitConjugation

section Image

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  (K : OpenSubgroup G) (i : G →* H) (hi : IsOpenEmbedding i)

/-- The image of an open subgroup under an open group embedding. -/
def openSubgroupImage : OpenSubgroup H where
  toSubgroup := K.toSubgroup.map i
  isOpen' := hi.isOpenMap _ K.isOpen

/-- The original open subgroup and its image have the same topological group structure. -/
def openSubgroupImageEquiv : K ≃ₜ* openSubgroupImage K i hi := by
  let e : K ≃* openSubgroupImage K i hi := K.toSubgroup.equivMapOfInjective i hi.injective
  have he (k : K) : (e k).val = i k.val := rfl
  have hs (k : openSubgroupImage K i hi) : i (e.symm k).val = k.val := by
    rw [← he, e.apply_symm_apply]
  exact { toMulEquiv := e
          continuous_toFun := (hi.continuous.comp continuous_subtype_val).subtype_mk _
          continuous_invFun := continuous_induced_rng.mpr <|
            hi.isEmbedding.continuous_iff.mpr (continuous_subtype_val.congr (fun k => (hs k).symm)) }

@[simp]
theorem openSubgroupImageEquiv_apply_val (k : K) :
    (openSubgroupImageEquiv K i hi k).val = i k.val := rfl

variable [IsTopologicalGroup H] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace H] [BorelSpace H] (s : H)

include hi in
private theorem comap_translatedCosetEmbedding_eq (ν : Measure H) [ν.IsMulRightInvariant] :
    ν.comap (translatedCosetEmbedding i s) = ν.comap i := by
  let e := Homeomorph.mulRight s
  have h : ν.comap e = ν := by
    change ν.comap e.toMeasurableEquiv = ν
    rw [← e.toMeasurableEquiv.map_symm]
    exact map_mul_right_eq_self ν s⁻¹
  change ν.comap (e ∘ i) = ν.comap i
  rw [← Measure.comap_comap (fun _ hA => hi.measurableEmbedding.measurableSet_image.mpr hA)
    e.injective (fun _ hA => e.toMeasurableEquiv.measurableEmbedding.measurableSet_image.mpr hA), h]

end Image

section Coordinate

variable {F A : Type*} [NontriviallyNormedField F] [ProperSpace F]
  [NormedRing A] [NormedAlgebra F A] [CompleteSpace A] [FiniteDimensional F A]
  [IsUltrametricDist A] (α : A ≃ₐ[F] A)

local notation "S" => adjointFixedAlgebra α
local notation "U" => adjointConjugationDomain α

local instance : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : A => x ∈ S)
local instance : ProperSpace S := FiniteDimensional.proper F S

variable {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)

local notation "M" => normUnitCongruence (R := S) hr₀.le hr₁

variable (hrU : closedBall (0 : adjointFixedAlgebra α) r ⊆ adjointConjugationDomain α)

/-- The additive coordinate `m − 1` on a congruence subgroup inside the slice domain. -/
def adjointNormSlice (m : M) : U := by
  let y : S := normUnitCoordinate (A := S) hr₀.le hr₁ m
  have hy : ‖y‖ ≤ r := m.property
  exact ⟨y, hrU (Metric.mem_closedBall.mpr ((dist_zero_right y).le.trans hy))⟩

theorem isOpenEmbedding_adjointNormSlice : IsOpenEmbedding (adjointNormSlice α hr₀ hr₁ hrU) := by
  have h := (isOpen_adjointConjugationDomain α).isOpenEmbedding_subtypeVal
  apply IsOpenEmbedding.of_comp _ h
  change IsOpenEmbedding (normUnitCoordinate (A := S) hr₀.le hr₁)
  exact ((Homeomorph.subRight (1 : S)).isOpenEmbedding.comp Units.isOpenEmbedding_val).comp
    (isOpen_normUnitCongruence hr₀ hr₁).isOpenEmbedding_subtypeVal

/-- The homomorphism of the compact slice subgroup into the ambient group. -/
def adjointNormSliceHom {H : Type*} [Group H] (i : Aˣ →* H) : M →* H :=
  i.comp ((Units.map (adjointFixedAlgebra α).val.toMonoidHom).comp (M).subtype)

omit [ProperSpace F] [CompleteSpace A] [FiniteDimensional F A] in
theorem continuous_adjointNormSliceHom {H : Type*} [Group H] [TopologicalSpace H]
    (i : Aˣ →* H) (hi : Continuous i) : Continuous (adjointNormSliceHom α hr₀ hr₁ i) :=
  hi.comp ((continuous_subtype_val.units_map (adjointFixedAlgebra α).val.toMonoidHom).comp
    continuous_subtype_val)

end Coordinate

section Pushforward

variable {F A H : Type*} [NontriviallyNormedField F] [ProperSpace F]
  [NormedRing A] [NormedAlgebra F A] [CompleteSpace A] [FiniteDimensional F A] [IsUltrametricDist A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H]
  (α : A ≃ₐ[F] A) (K : OpenSubgroup Aˣ) (i : Aˣ →* H) (hi : IsOpenEmbedding i) (s : H)

local notation "S" => adjointFixedAlgebra α
local notation "U" => adjointConjugationDomain α
local notation "K'" => openSubgroupImage K i hi

local instance : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : A => x ∈ S)
local instance : ProperSpace S := FiniteDimensional.proper F S

variable [MeasurableSpace (adjointFixedAlgebra α)] [MeasurableSpace (adjointFixedAlgebra α)ˣ]
  {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)

local notation "M" => normUnitCongruence (R := S) hr₀.le hr₁

variable (hrU : closedBall (0 : adjointFixedAlgebra α) r ⊆ adjointConjugationDomain α)
local notation "b" => adjointNormSlice α hr₀ hr₁ hrU
local notation "hb" => isOpenEmbedding_adjointNormSlice α hr₀ hr₁ hrU
local notation "j" => translatedCosetEmbedding i s
local notation "hj" => isOpenEmbedding_translatedCoset i hi s

/-- The restriction of the normalized descent pushforward gives the actual
compact conjugation pushforward about `s` and its product evaluation formula. -/
def CompactSemisimpleDescentPushforwardStatement
    (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (ρ : Measure (adjointFixedAlgebra α)) [ρ.IsAddHaarMeasure]
    (P : SchwartzBruhat (Aˣ × U) →ₗ[ℂ] SchwartzBruhat Aˣ) (D : Distribution H) (T : Distribution U)
    [SecondCountableTopology A] [SecondCountableTopology Aˣ]
    [BorelSpace (adjointFixedAlgebra α)] [BorelSpace (adjointFixedAlgebra α)ˣ] : Prop :=
  (∀ g : Aˣ, i (Units.map α.toMonoidHom g) = s * i g * s⁻¹) →
  let μ := ν.comap j
  letI : IsFiniteMeasureOnCompacts μ := IsFiniteMeasureOnCompacts.comap' ν (hj).continuous (hj).measurableEmbedding
  SchwartzBruhat.IsTestPushforward (μ.prod (ρ.comap (Subtype.val : U → S))) μ (adjointConjugationOnUnits α) P →
  (translatedCosetDistribution i hi s D).comp P = Distribution.tensor (Distribution.ofMeasure μ) T →
  ∃ Q : SchwartzBruhat (K' × M) →ₗ[ℂ] SchwartzBruhat H,
    SchwartzBruhat.IsTestPushforward ((ν.comap ((K').toSubgroup.subtype)).prod
      (ρ.comap (normUnitCoordinate (A := S) hr₀.le hr₁))) ν
      (Character.compactSliceConjugation K' (adjointNormSliceHom α hr₀ hr₁ i) s) Q ∧
    ∀ (f : SchwartzBruhat K') (g : SchwartzBruhat M),
      D (Q (SchwartzBruhat.tensor f g)) =
        (∫ k, f k ∂(ν.comap ((K').toSubgroup.subtype))) * T (openEmbeddingTestExtension hb g)

theorem compactSemisimpleDescentPushforward (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (ρ : Measure (adjointFixedAlgebra α)) [ρ.IsAddHaarMeasure]
    (P : SchwartzBruhat (Aˣ × U) →ₗ[ℂ] SchwartzBruhat Aˣ) (D : Distribution H) (T : Distribution U)
    [SecondCountableTopology A] [SecondCountableTopology Aˣ]
    [BorelSpace (adjointFixedAlgebra α)] [BorelSpace (adjointFixedAlgebra α)ˣ] :
    CompactSemisimpleDescentPushforwardStatement α K i hi s hr₀ hr₁ hrU ν ρ P D T := by
  intro hα μ hP hT
  let : ProperSpace A := FiniteDimensional.proper F A
  let : LocallyCompactSpace Aˣ := (Units.isOpenEmbedding_val (R := A)).locallyCompactSpace
  let : IsFiniteMeasureOnCompacts μ := IsFiniteMeasureOnCompacts.comap' ν (hj).continuous (hj).measurableEmbedding
  let e := openSubgroupImageEquiv K i hi
  let a : K' → Aˣ := Subtype.val ∘ e.symm
  have ha_val (k : K') : i (a k) = k.val := by
    rw [show i (a k) = (e (e.symm k)).val from rfl, e.apply_symm_apply]
  have ha : IsOpenEmbedding a := (IsOpenEmbedding.of_comp_iff a hi).mp <| by
    rw [show i ∘ a = Subtype.val from funext ha_val]
    exact (K').isOpen.isOpenEmbedding_subtypeVal
  let ω := ρ.comap (Subtype.val : U → S)
  let hU := isOpen_adjointConjugationDomain α
  have hSub := hU.isOpenEmbedding_subtypeVal
  let : SecondCountableTopology S := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology U := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology K' := (ha.isEmbedding).secondCountableTopology
  let : SecondCountableTopology M := (hb).isEmbedding.secondCountableTopology
  let : CompactSpace M := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence hr₀.le hr₁)
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : IsFiniteMeasureOnCompacts ω := IsFiniteMeasureOnCompacts.comap' ρ hSub.continuous hSub.measurableEmbedding
  let : IsFiniteMeasureOnCompacts (ω.comap b) := IsFiniteMeasureOnCompacts.comap' ω (hb).continuous (hb).measurableEmbedding
  have hjClosed : IsClosed (range j) := by
    let t := Homeomorph.mulRight s
    rw [show range j = t '' range i from Set.range_comp t i]
    exact t.isClosedMap _ (i.range.isClosed_of_isOpen hi.isOpen_range)
  obtain ⟨Q, hQ, hEval⟩ := restrictedDescentPushforward ha hb hj μ ω ν
    (adjointConjugationOnUnits α) P D T hjClosed hP hT
  have haμ : μ.comap a = ν.comap (Subtype.val : K' → H) := by
    change (ν.comap j).comap a = _
    rw [comap_translatedCosetEmbedding_eq i hi s ν,
      Measure.comap_comap (fun _ hA => ha.measurableEmbedding.measurableSet_image.mpr hA)
        hi.injective (fun _ hA => hi.measurableEmbedding.measurableSet_image.mpr hA)]
    exact congrArg (ν.comap ·) (funext ha_val)
  have hbρ : ω.comap b = ρ.comap (normUnitCoordinate (A := S) hr₀.le hr₁) :=
    Measure.comap_comap (fun _ hA => (hb).measurableEmbedding.measurableSet_image.mpr hA)
      Subtype.val_injective (fun _ hA => hSub.measurableEmbedding.measurableSet_image.mpr hA) ρ
  have hMap : j ∘ adjointConjugationOnUnits α ∘ Prod.map a b =
      Character.compactSliceConjugation K' (adjointNormSliceHom α hr₀ hr₁ i) s := by
    funext z
    let g := a z.1
    let m : Sˣ := z.2.val
    let v := Units.map (adjointFixedAlgebra α).val.toMonoidHom m
    have hm : (b z.2).property.1.unit = m := by
      apply Units.ext
      rw [IsUnit.unit_spec]
      change 1 + (m.val - 1) = m.val
      abel
    have hv : Units.map α.toMonoidHom v = v := Units.ext m.val.property
    have heq : i v = s * i v * s⁻¹ := by simpa only [hv] using hα v
    have hcomm : i v * s = s * i v := calc
      _ = (s * i v * s⁻¹) * s := congrArg (· * s) heq
      _ = _ := by group
    change i (g * Units.map (adjointFixedAlgebra α).val.toMonoidHom (b z.2).property.1.unit *
      (Units.map α.toMonoidHom g)⁻¹) * s = z.1.val * (s * i v) * z.1.val⁻¹
    rw [hm, map_mul, map_mul, map_inv, hα, ← ha_val z.1]
    change i g * i v * (s * i g * s⁻¹)⁻¹ * s = i g * (s * i v) * (i g)⁻¹
    rw [← hcomm]
    group
  rw [hMap, haμ, hbρ] at hQ
  refine ⟨Q, hQ, fun f g => ?_⟩
  have h := hEval f g
  rw [haμ] at h
  exact h

end Pushforward

end Langlands.BaseChange

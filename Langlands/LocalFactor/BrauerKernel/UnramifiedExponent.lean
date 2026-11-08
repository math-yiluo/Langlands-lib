import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.ClassFieldTheory.Local.GradedUnitCoordinates
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.ClassFieldTheory.Local.UnitNormProof
import Langlands.HarmonicAnalysis.Conductor
import Langlands.LocalField.DVRTraceIdealsProof
import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof
import Langlands.LocalField.RelativeIdealPowers
import Mathlib.RingTheory.DedekindDomain.Different
import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.LocalFactor.BrauerKernel.UnramifiedKernel
import Langlands.LocalFactor.CommonClosureRankOneSpectral

/-! # Conductors under norms and traces of unramified extensions -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe u v

open scoped WithZero

section Comparison

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

end Comparison

section Norm

attribute [local instance] Ideal.Quotient.field

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier] (T : F.TopologicalData) (S : E.TopologicalData)

/-- For equal absolute ramification indices the norm maps each principal-unit group onto
the corresponding one. -/
theorem map_normUnits_principalUnits (he : T.ramificationIndex = S.ramificationIndex)
    (n : ℕ) :
    (S.principalUnits n).map (LocalClassField.normUnits F.Carrier E.Carrier) =
      T.principalUnits n := by
  rw [← S.unitFiltration_eq_principalUnits, ← T.unitFiltration_eq_principalUnits]
  exact LocalClassField.unramifiedUnitNorms p F E T S he n

/-- For equal absolute ramification indices the norm pullback of a quasicharacter has the
same conductor. -/
theorem multiplicativeConductor_eq_of_comp_normUnits
    (he : T.ramificationIndex = S.ramificationIndex)
    (α : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology)
    (β : @HarmonicAnalysis.Quasicharacter E.Carrier _ S.topology)
    (hβ : ∀ x, β x = α (LocalClassField.normUnits F.Carrier E.Carrier x)) :
    S.multiplicativeConductor β = T.multiplicativeConductor α := by
  have key : ∀ n, S.MultiplicativeTrivialAt β n ↔ T.MultiplicativeTrivialAt α n := by
    intro n
    have hmap := T.map_normUnits_principalUnits S he n
    constructor
    · intro hb u hu
      rw [← hmap] at hu
      obtain ⟨x, hx, rfl⟩ := hu
      rw [← hβ]
      exact hb x hx
    · intro ha x hx
      rw [hβ]
      apply ha
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
  apply le_antisymm
  · rw [← S.multiplicativeTrivialAt_iff_conductor_le, key,
      T.multiplicativeTrivialAt_iff_conductor_le]
  · rw [← T.multiplicativeTrivialAt_iff_conductor_le, ← key,
      S.multiplicativeTrivialAt_iff_conductor_le]

/-- For equal absolute ramification indices the field trace maps the integers of the
extension onto the integers of the base. -/
theorem exists_trace_eq_of_ramificationIndex_eq
    (he : T.ramificationIndex = S.ramificationIndex) (a : F.Carrier) (ha : a ∈ T.Integers) :
    ∃ x ∈ S.Integers, Algebra.trace F.Carrier E.Carrier x = a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let := relativeIntegerAlgebra T S
  let := relativeIntegerFieldAlgebra (E := E) T
  have := relativeIntegerFieldTower (E := E) T
  have := relativeIntegerTower T S
  obtain ⟨hclosure, hmodule⟩ := LocalClassField.NYLL.relativeIntegerStructure p F E T S
  have := hclosure
  have := hmodule
  have := LocalField.isTorsionFree_of_isFractionRing_tower T.Integers S.Integers
    F.Carrier E.Carrier
  have hmap := map_maximalIdeal_algebraMap_of_ramificationIndex_eq_mul T S 1
    (by rw [he, one_mul])
  rw [pow_one] at hmap
  let P := IsLocalRing.maximalIdeal T.Integers
  have hPmax : (P.map (algebraMap T.Integers S.Integers)).IsMaximal := by
    rw [hmap]
    infer_instance
  have : Finite (T.Integers ⧸ P) := T.finite_residueField
  have : Module.Finite (T.Integers ⧸ P)
      (S.Integers ⧸ P.map (algebraMap T.Integers S.Integers)) :=
    Module.Finite.of_restrictScalars_finite T.Integers _ _
  have : Finite (S.Integers ⧸ P.map (algebraMap T.Integers S.Integers)) :=
    Module.finite_of_finite (T.Integers ⧸ P)
  obtain ⟨y, hy⟩ : ∃ y, Algebra.trace (T.Integers ⧸ P)
      (S.Integers ⧸ P.map (algebraMap T.Integers S.Integers)) y ≠ 0 := by
    simpa [LinearMap.ext_iff] using
      Algebra.trace_ne_zero (T.Integers ⧸ P) (S.Integers ⧸ P.map (algebraMap T.Integers S.Integers))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Algebra.trace_quotient_eq_of_isDedekindDomain] at hy
  have hunit : IsUnit (Algebra.intTrace T.Integers S.Integers x) := by
    by_contra hnu
    apply hy
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
  obtain ⟨u, hu⟩ := hunit
  let b : T.Integers := ⟨a, ha⟩
  refine ⟨algebraMap S.Integers E.Carrier ((b * ↑u⁻¹) • x), ((b * ↑u⁻¹) • x).property, ?_⟩
  rw [← Algebra.algebraMap_intTrace (A := T.Integers) (B := S.Integers) (K := F.Carrier)
    (L := E.Carrier), map_smul, ← hu, smul_eq_mul, mul_assoc,
    Units.inv_mul, mul_one]
  rfl

/-- Field traces of integers are integers. -/
theorem trace_mem_integers_of_mem (x : E.Carrier) (hx : x ∈ S.Integers) :
    Algebra.trace F.Carrier E.Carrier x ∈ T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let := relativeIntegerAlgebra T S
  let := relativeIntegerFieldAlgebra (E := E) T
  have := relativeIntegerFieldTower (E := E) T
  have := relativeIntegerTower T S
  obtain ⟨hclosure, hmodule⟩ := LocalClassField.NYLL.relativeIntegerStructure p F E T S
  have := hclosure
  have := hmodule
  have := LocalField.isTorsionFree_of_isFractionRing_tower T.Integers S.Integers
    F.Carrier E.Carrier
  have h := Algebra.algebraMap_intTrace (A := T.Integers) (B := S.Integers) (K := F.Carrier)
    (L := E.Carrier) ⟨x, hx⟩
  change ((Algebra.intTrace T.Integers S.Integers ⟨x, hx⟩ : T.Integers) : F.Carrier) =
    Algebra.trace F.Carrier E.Carrier x at h
  rw [← h]
  exact Subtype.property _

/-- For equal absolute ramification indices the order of a base element is unchanged. -/
theorem ord_algebraMap_of_ramificationIndex_eq
    (he : T.ramificationIndex = S.ramificationIndex) (x : F.Carrier) :
    S.ord (algebraMap F.Carrier E.Carrier x) = T.ord x := by
  have key := LocalClassField.ramificationIndex_mul_ord_relative_algebraMap F E T S x
  rw [← he] at key
  exact mul_left_cancel₀ (show (T.ramificationIndex : ℤ) ≠ 0 by
    exact_mod_cast T.ramificationIndex_pos.ne') key

/-- For equal absolute ramification indices the trace pullback has the same additive
conductor. -/
theorem additiveConductor_traceCharacter_of_ramificationIndex_eq
    (he : T.ramificationIndex = S.ramificationIndex)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    S.additiveConductor (T.traceCharacter S ψ) = T.additiveConductor ψ := by
  let u := T.uniformizer
  have huord : T.ord u = 1 := T.ord_uniformizer
  have hu0 : u ≠ 0 := T.coordinateUniformizer_ne_zero u huord
  let π := algebraMap F.Carrier E.Carrier u
  have hπ0 : π ≠ 0 := (map_ne_zero _).mpr hu0
  have hπord : S.ord π = 1 := by rw [T.ord_algebraMap_of_ramificationIndex_eq S he, huord]
  have hT (k : ℤ) (x : F.Carrier) : x ∈ T.additiveLattice k ↔ u ^ k * x ∈ T.Integers := by
    rw [← T.mem_additiveLattice_zero, T.mul_mem_additiveLattice_iff (zpow_ne_zero k hu0),
      T.ord_zpow, huord, mul_one, zero_add]
  have hS (k : ℤ) (x : E.Carrier) : x ∈ S.additiveLattice k ↔ π ^ k * x ∈ S.Integers := by
    rw [← S.mem_additiveLattice_zero, S.mul_mem_additiveLattice_iff (zpow_ne_zero k hπ0),
      S.ord_zpow, hπord, mul_one, zero_add]
  have key (k : ℤ) : S.AdditiveTrivialAt (T.traceCharacter S ψ) k ↔ T.AdditiveTrivialAt ψ k := by
    constructor
    · intro h a ha
      have ha' := (hT k a).mp ha
      obtain ⟨y, hy, hya⟩ := T.exists_trace_eq_of_ramificationIndex_eq S he _ ha'
      have hmem : π ^ (-k) * y ∈ S.additiveLattice k := by
        rw [hS, ← mul_assoc, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero, one_mul]
        exact hy
      have := h _ hmem
      rw [traceCharacter_apply] at this
      rwa [show π ^ (-k) * y = algebraMap F.Carrier E.Carrier (u ^ (-k)) * y by
          simp [π, map_zpow₀], ← Algebra.smul_def, map_smul, hya, smul_eq_mul,
        ← mul_assoc, ← zpow_add₀ hu0, neg_add_cancel, zpow_zero, one_mul] at this
    · intro h x hx
      have hx' := (hS k x).mp hx
      rw [traceCharacter_apply]
      apply h
      rw [hT]
      have htr := T.trace_mem_integers_of_mem S _ hx'
      rwa [show π ^ k * x = algebraMap F.Carrier E.Carrier (u ^ k) * x by
          simp [π, map_zpow₀], ← Algebra.smul_def, map_smul, smul_eq_mul] at htr
  apply le_antisymm
  · rw [← T.additiveTrivialAt_iff_le_conductor, ← key, S.additiveTrivialAt_iff_le_conductor]
  · rw [← S.additiveTrivialAt_iff_le_conductor, key, T.additiveTrivialAt_iff_le_conductor]

end Norm

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The field character of `L` whose Weil character is the restriction of the Weil
character of `α`. For normalized reciprocity it is `α ∘ N_{L/E}`. -/
def normPullback (e : ReciprocityFamily F) (E L : Extension F) (h : E.field ≤ L.field)
    (α : FieldCharacter F E) : FieldCharacter F L :=
  CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L
    ((weilCharacter F e E α).comp (E.weilInclusion L h (Weil.Local.localResidueDegree F)))

/-- For normalized reciprocity the norm pullback is the composite with the field norm. -/
theorem normPullback_apply (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (E L : Extension F) (h : E.field ≤ L.field) (α : FieldCharacter F E) (x : L.fieldˣ) :
    normPullback F e E L h α x = α (E.unitsNorm L h x) := by
  let := (fieldData F E).topology
  let := (fieldData F L).topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  obtain ⟨v, rfl⟩ := CommonClosureSpectralAnalytic.reciprocityUnits_surjective F e L x
  have hw := CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv F e L
    ((weilCharacter F e E α).comp (E.weilInclusion L h (Weil.Local.localResidueDegree F)))
  have hv := DFunLike.congr_fun hw v
  change (normPullback F e E L h α) (reciprocityUnits F e L v) =
    ((weilCharacter F e E α).comp (E.weilInclusion L h (Weil.Local.localResidueDegree F))) v at hv
  rw [hv]
  have hnorm := DFunLike.congr_fun (he.1.1 E L h)
    (LocalClassField.abelianizationProjection (weilSubgroup F L) v)
  change α (reciprocityUnits F e E (E.weilInclusion L h (Weil.Local.localResidueDegree F) v)) = _
  congr 1

/-- **Unramified Brauer relations for a common base twist.** Let every generator of an
actual relation lie over a field of the base absolute ramification index, with characters
`χ₀ · (α ∘ N)` and `χ₀' · (α ∘ N)` for unramified `χ₀, χ₀'` and one character `α` of `E`.
Then the abelian epsilon evaluation of the relation is trivial. -/
theorem evaluationMap_eq_zero_of_unramified_normPullback (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (z : Presentation F E)
    (hz : presentationMap.{uF, uV} F e E z = 0) (α : FieldCharacter F E)
    (hgen : ∀ g ∈ z.support,
      (fieldData F g.extension).ramificationIndex = (fieldData F E).ramificationIndex ∧
      ∃ χ₀ χ₀' : FieldCharacter F g.extension,
        (fieldData F g.extension).IsUnramifiedQuasicharacter χ₀ ∧
        (fieldData F g.extension).IsUnramifiedQuasicharacter χ₀' ∧
        g.first = χ₀ * normPullback F e E g.extension g.inclusion α ∧
        g.second = χ₀' * normPullback F e E g.extension g.inclusion α) :
    evaluationMap F E ψ measures z = 0 := by
  refine evaluationMap_eq_zero_of_unramifiedTwist.{uF, uV} F e he E ψ measures z hz
    ((fieldData F E).additiveConductor ψ + ((fieldData F E).multiplicativeConductor α : ℤ)) ?_
  intro g hg
  obtain ⟨hram, χ₀, χ₀', h₀, h₀', h₁, h₂⟩ := hgen g hg
  refine ⟨hram, normPullback F e E g.extension g.inclusion α, χ₀, χ₀', h₀, h₀', h₁, h₂, ?_⟩
  let : Algebra E.field g.extension.field := (IntermediateField.inclusion g.inclusion).toAlgebra
  let : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
  let : Algebra (Padic p) g.extension.field := (g.extension.asPadicField (p := p)).algebra
  have : IsScalarTower (Padic p) E.field g.extension.field := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional E.field g.extension.field :=
    FiniteDimensional.right F.Carrier E.field g.extension.field
  have hc := PadicField.TopologicalData.additiveConductor_traceCharacter_of_ramificationIndex_eq
    (F := E.asPadicField (p := p)) (E := g.extension.asPadicField (p := p))
    (fieldData F E) (fieldData F g.extension) hram.symm ψ
  have hm := PadicField.TopologicalData.multiplicativeConductor_eq_of_comp_normUnits
    (F := E.asPadicField (p := p)) (E := g.extension.asPadicField (p := p))
    (fieldData F E) (fieldData F g.extension) hram.symm α
    (normPullback F e E g.extension g.inclusion α)
    (fun x => normPullback_apply F e he E g.extension g.inclusion α x)
  change (fieldData F g.extension).additiveConductor
      ((fieldData F E).traceCharacter (fieldData F g.extension) ψ) + _ = _
  rw [hc, hm]

end Langlands.LocalFactor.NonabelianBrauer

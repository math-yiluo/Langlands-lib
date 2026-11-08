import Langlands.LocalFactor.DeligneHenniartInductionStep
import Langlands.LocalFactor.Ramification.Herbrand.SlopeProof
import Langlands.LocalFactor.CommonClosureIntermediateWeil

/-!
# Upper groups of intermediate Weil groups and the half-break comparison

The relative inverse Herbrand function `ψ_{E/F}` has slope at most `e(E/F)` on `[0, ∞)`, and
exactly `e(E/F)` past any upper index whose group fixes `E`; both are stated multiplied out
by `e_F`. The upper filtration of the Weil group of a finite intermediate field `L` is
transported to the actual subgroup `W_L` of the base Weil group. Herbrand's theorem identifies
`W_F^v ∩ W_L` with `W_L^{ψ_{L/F}(v)}`, and convexity gives `W_L^{ψ(a)/2} ⊆ W_F^{a/2} ∩ W_L`.
With the induction step this passes relative witnesses from `L` to the base field.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Herbrand

universe u uK uE uL

section Orders

open _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (K : Type uK) [Field K] [Algebra (Padic p) K]
  (E : Type uE) [Field E] [Algebra (Padic p) E] {L : PadicField.{uL} p}
  [Algebra K E] [Algebra E L.Carrier] [Algebra K L.Carrier]
  [IsScalarTower K E L.Carrier]
  [IsScalarTower (Padic p) K L.Carrier] [IsScalarTower (Padic p) E L.Carrier]
  (T : L.TopologicalData)

/-- The lower group orders over `E` are at most those over `K`. -/
theorem lowerGroupOrder_subfield_le (i : ℕ) :
    Padic.lowerGroupOrder T E i ≤ Padic.lowerGroupOrder T K i := by
  have h := lowerGroupOrder_subfield_mul_relIndex K E T i
  have hpos := lowerGroupOrder_pos T K i
  rw [← h] at hpos ⊢
  exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left hpos)

/-- On `[0, ∞)`, `φ_{L/E} ≤ [G_0 : G_0 ∩ Gal(L/E)] · φ_{L/K}`. -/
theorem herbrandPhi_le_mul {y : ℝ} (hy : 0 ≤ y) :
    Padic.herbrandPhi T E y ≤
      ((AlgEquiv.restrictScalarsHom K :
        (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range.relIndex
          (Padic.lowerRamificationGroup T K 0) : ℝ) * Padic.herbrandPhi T K y := by
  set H := (AlgEquiv.restrictScalarsHom K :
    (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range
  set B := max (ramificationCutoff T K) (max (ramificationCutoff T E) ⌈y⌉₊)
  have hBK : ramificationCutoff T K ≤ B := le_max_left _ _
  have hBE : ramificationCutoff T E ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hyB : y ≤ B := (Nat.le_ceil y).trans (by exact_mod_cast
    (le_max_right _ _ : ⌈y⌉₊ ≤ max (ramificationCutoff T E) ⌈y⌉₊).trans (le_max_right _ _))
  rw [herbrandPhi_eq_sum T K hBK hy hyB, herbrandPhi_eq_sum T E hBE hy hyB]
  have h0 : (Padic.lowerGroupOrder T K 0 : ℝ) =
      Padic.lowerGroupOrder T E 0 * H.relIndex (Padic.lowerRamificationGroup T K 0) := by
    exact_mod_cast (lowerGroupOrder_subfield_mul_relIndex K E T 0).symm
  have hh0 : (0 : ℝ) < Padic.lowerGroupOrder T E 0 := by
    exact_mod_cast lowerGroupOrder_pos T E 0
  have hr : (0 : ℝ) < H.relIndex (Padic.lowerRamificationGroup T K 0) := by
    have hg0 : (0 : ℝ) < Padic.lowerGroupOrder T K 0 := by
      exact_mod_cast lowerGroupOrder_pos T K 0
    rw [h0] at hg0
    exact pos_of_mul_pos_right hg0 hh0.le
  have hsum : rampSum (fun i => (Padic.lowerGroupOrder T E i : ℝ)) B y ≤
      rampSum (fun i => (Padic.lowerGroupOrder T K i : ℝ)) B y := by
    unfold rampSum
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right
      (by dsimp only; exact_mod_cast lowerGroupOrder_subfield_le K E T (i + 1))
      (ramp_nonneg i y)
  rw [h0, mul_div_assoc', le_div_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ hh0]
  nlinarith [hsum]

/-- `φ_{L/E}(ψ_{L/K}(s)) ≤ [G_0 : G_0 ∩ Gal(L/E)] · s` for `s ≥ 0`. -/
theorem herbrandPhi_herbrandPsi_le_mul {s : ℝ} (hs : 0 ≤ s) :
    Padic.herbrandPhi T E (Padic.herbrandPsi T K s) ≤
      ((AlgEquiv.restrictScalarsHom K :
        (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range.relIndex
          (Padic.lowerRamificationGroup T K 0) : ℝ) * s := by
  have hy : 0 ≤ Padic.herbrandPsi T K s := by
    have h := (Padic.herbrandPsi_strictMono T K).monotone hs
    rwa [Padic.herbrandPsi_zero] at h
  have h := herbrandPhi_le_mul K E T hy
  rwa [Padic.herbrandPhi_herbrandPsi] at h

end Orders

section AbsoluteSlope

open LocalClassField _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {K : PadicField.{uE} p}
  [Algebra K.Carrier (AlgebraicClosure F.Carrier)] [Algebra F.Carrier K.Carrier]
  [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower (Padic p) K.Carrier (AlgebraicClosure F.Carrier)]

attribute [local instance] extension_padicScalarTower

variable {M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)}
  (h : ∀ x : K.Carrier, algebraMap K.Carrier (AlgebraicClosure F.Carrier) x ∈
    M.toIntermediateField)

/-- The index of the image of `Gal(M/K)` in inertia is the absolute index of `I_F ∩ G_K`
in `I_F`. -/
theorem relativeSubgroup_relIndex_eq :
    (relativeSubgroup F h).relIndex (Padic.lowerRamificationGroup
        (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData F.Carrier 0) =
      ((relativeSubgroup F h).comap (absoluteRelativeRestriction F h)).relIndex
        (F.absoluteInertia F.canonicalTopologicalData) := by
  set T := (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData
  have hlow0 : Padic.lowerRamificationGroup T F.Carrier 0 =
      Padic.upperRamificationGroup T F.Carrier 0 := by
    rw [Padic.upperRamificationGroup_zero, ← Padic.lowerRamificationGroupReal_nat, Nat.cast_zero,
      Padic.lowerRamificationGroupReal_zero]
  rw [hlow0, ← map_absoluteRelativeRestriction_upper F h (by norm_num),
    ← Subgroup.relIndex_comap, absoluteUpperCanonicalInertia F]

/-- `ψ_{K/F}(s) ≤ [I_F : I_F ∩ G_K] · s` for `s ≥ 0`, computed in `M`. -/
theorem relativeIndex_le_relIndex_mul {s : ℝ} (hs : 0 ≤ s) :
    relativeIndex F M h s ≤
      (((relativeSubgroup F h).comap (absoluteRelativeRestriction F h)).relIndex
        (F.absoluteInertia F.canonicalTopologicalData) : ℝ) * s := by
  have key := herbrandPhi_herbrandPsi_le_mul F.Carrier K.Carrier
    (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData hs
  rw [relativeSubgroup_relIndex_eq F h] at key
  exact key

end AbsoluteSlope

section Intermediate

open LocalClassField Weil.Local _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (E : FiniteIntermediateExtension F.Carrier)

attribute [local instance] asPadicField_isScalarTower

/-- `ψ_{E/F}(s) ≤ [I_F : I_F ∩ G_E] · s` for `s ≥ 0`. -/
theorem relativeHerbrandPsi_le_relIndex_mul {s : ℝ} (hs : 0 ≤ s) :
    relativeHerbrandPsi E s ≤
      (E.field.fixingSubgroup.relIndex (F.absoluteInertia F.canonicalTopologicalData) : ℝ) * s := by
  have key := relativeIndex_le_relIndex_mul F (algebraMap_mem_galoisClosure E) hs
  rw [comap_absoluteRelativeRestriction_galoisClosure] at key
  exact key

end Intermediate

section Slope

open LocalClassField Weil.Local _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (E : FiniteIntermediateExtension F.Carrier)

/-- The canonical ramification index of `E` is `[I_F : I_F ∩ G_E] · e_F`, as a real number. -/
theorem fieldData_ramificationIndex_eq :
    ((LocalFactor.CommonClosure.fieldData F E).ramificationIndex : ℝ) =
      (E.field.fixingSubgroup.relIndex (F.absoluteInertia F.canonicalTopologicalData) : ℝ) *
        F.canonicalTopologicalData.ramificationIndex := by
  exact_mod_cast (fixingSubgroup_relIndex_absoluteInertia_mul F E).symm

/-- The slope of `ψ_{E/F}` is at most `e(E/F)`: `e_F ψ_{E/F}(s) ≤ e_E s` for `s ≥ 0`. -/
theorem ramificationIndex_mul_relativeHerbrandPsi_le {s : ℝ} (hs : 0 ≤ s) :
    (F.canonicalTopologicalData.ramificationIndex : ℝ) * relativeHerbrandPsi E s ≤
      (LocalFactor.CommonClosure.fieldData F E).ramificationIndex * s := by
  have h := relativeHerbrandPsi_le_relIndex_mul E hs
  have heF : (0 : ℝ) ≤ F.canonicalTopologicalData.ramificationIndex := Nat.cast_nonneg _
  rw [fieldData_ramificationIndex_eq E]
  calc (F.canonicalTopologicalData.ramificationIndex : ℝ) * relativeHerbrandPsi E s
      ≤ (F.canonicalTopologicalData.ramificationIndex : ℝ) *
          ((E.field.fixingSubgroup.relIndex (F.absoluteInertia F.canonicalTopologicalData) : ℝ) *
            s) := mul_le_mul_of_nonneg_left h heF
    _ = _ := by ring

/-- DH81 3.2(iii), multiplied form: if `G_F^{v₀} ⊆ G_E` with `v₀ ≥ 0`, then
`e_F (ψ_{E/F}(t) - ψ_{E/F}(s)) = e_E (t - s)` for `v₀ ≤ s ≤ t`. -/
theorem ramificationIndex_mul_relativeHerbrandPsi_sub {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hG : absoluteUpperRamificationGroup F v₀ ≤ E.field.fixingSubgroup)
    {s t : ℝ} (hs : v₀ ≤ s) (hst : s ≤ t) :
    (F.canonicalTopologicalData.ramificationIndex : ℝ) *
        (relativeHerbrandPsi E t - relativeHerbrandPsi E s) =
      (LocalFactor.CommonClosure.fieldData F E).ramificationIndex * (t - s) := by
  rw [relativeHerbrandPsi_sub_eq_relIndex E hv₀ hG hs hst, fieldData_ramificationIndex_eq E]
  ring

/-- The same, with the hypothesis on the actual Weil upper groups. -/
theorem ramificationIndex_mul_relativeHerbrandPsi_sub_of_upperGroup_le {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hW : VirtualRepresentation.LocalWeil.Ramification.upperGroup F v₀ ≤
      LocalFactor.CommonClosure.weilSubgroup F E)
    {s t : ℝ} (hs : v₀ ≤ s) (hst : s ≤ t) :
    (F.canonicalTopologicalData.ramificationIndex : ℝ) *
        (relativeHerbrandPsi E t - relativeHerbrandPsi E s) =
      (LocalFactor.CommonClosure.fieldData F E).ramificationIndex * (t - s) := by
  have hF : (0 : ℝ) < F.canonicalTopologicalData.ramificationIndex := by
    exact_mod_cast F.canonicalTopologicalData.ramificationIndex_pos
  rw [relativeHerbrandPsi_sub_eq_of_upperGroup_le E hv₀ hW hs hst]
  field_simp

end Slope

end Langlands.Ramification.HerbrandBridge

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure Weil.Local VirtualRepresentation.LocalWeil.Ramification
open Ramification.HerbrandBridge Ramification.Padic LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The upper group of index `s` of the Weil group of `L`, as a subgroup of `W_L`. -/
def weilUpperSubgroup (L : Extension F) (s : ℝ) : Subgroup (weilSubgroup F L) :=
  (upperGroup (L.asPadicField (p := p)) s).comap
    ((standaloneWeilEquiv F L).symm : weilSubgroup F L →* localWeilGroup (L.asPadicField (p := p)))

theorem mem_weilUpperSubgroup (L : Extension F) (s : ℝ) (x : weilSubgroup F L) :
    x ∈ weilUpperSubgroup F L s ↔
      (standaloneWeilEquiv F L).symm x ∈ upperGroup (L.asPadicField (p := p)) s :=
  Iff.rfl

theorem weilUpperSubgroup_antitone (L : Extension F) : Antitone (weilUpperSubgroup F L) :=
  fun _ _ hst _ hx => upperGroup_antitone _ hst hx

theorem weilUpperSubgroup_normal (L : Extension F) (s : ℝ) :
    (weilUpperSubgroup F L s).Normal :=
  Subgroup.Normal.comap (upperGroup_normal _ s) _

/-- Upper groups of nonnegative index lie in inertia. -/
theorem weilUpperSubgroup_le_inertia (L : Extension F) {s : ℝ} (hs : 0 ≤ s) :
    weilUpperSubgroup F L s ≤ CommonClosureWeilDeligne.inertia F L := by
  intro x hx
  rw [← standaloneWeilEquiv_symm_mem_inertia, localInertia_eq_comap]
  have h0 := upperGroup_antitone _ hs hx
  change localProjection _ ((standaloneWeilEquiv F L).symm x) ∈
    absoluteUpperRamificationGroup _ 0 at h0
  rw [absoluteUpperCanonicalInertia] at h0
  exact h0

/-- Herbrand's theorem on `W_L`: `W_F^v ∩ W_L = W_L^{ψ_{L/F}(v)}` for `v ≥ -1`. -/
theorem coe_mem_upperGroup_iff (L : Extension F) {v : ℝ} (hv : -1 ≤ v) (x : weilSubgroup F L) :
    (x : localWeilGroup F) ∈ upperGroup F v ↔
      x ∈ weilUpperSubgroup F L (relativeHerbrandPsi L v) := by
  have h := intermediateWeilEquiv_mem_upperGroup_iff L hv ((standaloneWeilEquiv F L).symm x)
  have hx : ((intermediateWeilEquiv F L ((standaloneWeilEquiv F L).symm x) :
      weilSubgroup F L) : localWeilGroup F) = x := by
    change ((standaloneWeilEquiv F L ((standaloneWeilEquiv F L).symm x) :
      weilSubgroup F L) : localWeilGroup F) = x
    rw [ContinuousMulEquiv.apply_symm_apply]
  rw [hx] at h
  exact h

/-- `W_L^{ψ_{L/F}(a)} = W_F^a ∩ W_L` for `a ≥ -1`, as subgroups of `W_L`. -/
theorem weilUpperSubgroup_eq_restrictSubgroup (L : Extension F)
    (hL : (baseExtension F).field ≤ L.field) {a : ℝ} (ha : -1 ≤ a) :
    weilUpperSubgroup F L (relativeHerbrandPsi L a) =
      restrictSubgroup F (baseExtension F) L hL (baseUpperGroup F a) := by
  ext x
  exact (coe_mem_upperGroup_iff F L ha x).symm

/-- DH81 4.8: `W_L^{ψ_{L/F}(a)/2} ⊆ W_F^{a/2} ∩ W_L` for `a ≥ 0`, as subgroups of `W_L`. -/
theorem weilUpperSubgroup_half_le_restrictSubgroup (L : Extension F)
    (hL : (baseExtension F).field ≤ L.field) {a : ℝ} (ha : 0 ≤ a) :
    weilUpperSubgroup F L (relativeHerbrandPsi L a / 2) ≤
      restrictSubgroup F (baseExtension F) L hL (baseUpperGroup F (a / 2)) := by
  intro x hx
  change (x : localWeilGroup F) ∈ upperGroup F (a / 2)
  rw [coe_mem_upperGroup_iff F L (by linarith)]
  exact weilUpperSubgroup_antitone F L (relativeHerbrandPsi_half_le L ha) hx

variable {F}

/-- DH81 4.8, exact case: a witness over `L` relative to `W_L^{ψ_{L/F}(a)/2}` has norm a
witness over the base field for the induced class, relative to `W_F^{a/2}`. -/
theorem exactWitnessOn_induce_upper {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F}
    (hsys : IsSystem F e ε) (L : Extension F) (hL : (baseExtension F).field ≤ L.field)
    {a : ℝ} (ha : 0 ≤ a) (ψ : AdditiveCharacter F (baseExtension F))
    (x : Virtual.{uF, uV} F L) (γ : L.fieldˣ)
    (hx : ExactWitnessOn F e ε L (weilUpperSubgroup F L (relativeHerbrandPsi L a / 2))
      (traceCharacter F (baseExtension F) L hL ψ) x γ) :
    ExactWitnessOn F e ε (baseExtension F) (baseUpperGroup F (a / 2)) ψ
      (induce F (baseExtension F) L hL x) ((baseExtension F).unitsNorm L hL γ) :=
  exactWitnessOn_induce hsys _ L hL _ ψ x γ
    (exactWitnessOn_mono (weilUpperSubgroup_half_le_restrictSubgroup F L hL ha) hx)

/-- DH81 4.5, approximate case: a witness over `L` relative to `W_L^{ψ_{L/F}(a)}` has norm a
witness over the base field for the induced class, relative to `W_F^a`. -/
theorem approximateWitnessOn_induce_upper {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hsys : IsSystem F e ε) (L : Extension F)
    (hL : (baseExtension F).field ≤ L.field) {a : ℝ} (ha : -1 ≤ a)
    (ψ : AdditiveCharacter F (baseExtension F)) (x : Virtual.{uF, uV} F L) (γ : L.fieldˣ)
    (hx : ApproximateWitnessOn F e ε L (weilUpperSubgroup F L (relativeHerbrandPsi L a))
      (traceCharacter F (baseExtension F) L hL ψ) x γ) :
    ApproximateWitnessOn F e ε (baseExtension F) (baseUpperGroup F a) ψ
      (induce F (baseExtension F) L hL x) ((baseExtension F).unitsNorm L hL γ) :=
  approximateWitnessOn_induce hsys _ L hL _ ψ x γ
    (approximateWitnessOn_mono (weilUpperSubgroup_eq_restrictSubgroup F L hL ha).le hx)

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

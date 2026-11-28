import Langlands.TraceFormula.TwistedOrbital
import Langlands.Analysis.Local.QuotientNormalizingFunction
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure

/-!
# Twisted orbital integrals that vanish along an abelian fibre

Let `G` be a locally compact, second countable Hausdorff group, `θ : G →* G` a continuous
endomorphism, `δ ∈ G` and `H = twistedCentralizer θ δ`. Suppose that `U` is a closed abelian
subgroup of `G` with `θ(U) ⊆ U`, that a closed subgroup `P` contains `δ`, `U` and `H`, and that a
continuous homomorphism `π : P →* G` has kernel `U` and is the identity on `H`
(`TwistedFibreData`). Suppose further that `u ↦ δ⁻¹ u δ θ(u)⁻¹` maps `U` onto `U`.

`TwistedFibreData.twistedOrbitalIntegral_eq_zero`: if a continuous `φ : G → ℂ` satisfies
`∫_U φ(x u y) dμ(u) = 0` for every Haar measure `μ` on `U` and all `x, y`, then the twisted
orbital integral `∫ φ(x⁻¹ δ θ(x)) dν(x)` over `H \ G` vanishes for every right Haar measure on
`H` and every compatible quotient measure `ν`.

The proof: `S = U H` is a closed subgroup, the image of `μ_H × μ_U` under `(h, u) ↦ u h` is a
right-invariant measure on `S`, and the `U`-average `ρ'(g) = ∫_U ρ(u g) du` of a normalizing
function `ρ` for `S` is a normalizing function for `H`. Weil's formula
(`IsCompatible.integral_descend_eq`) writes the orbital integral as `∫_G ρ'(g) φ(g⁻¹ δ θ(g)) dg`;
Fubini on `U × G` and the shear `(u, g) ↦ (u, u⁻¹ g)` turn it into
`∫_G ρ(g) ∫_U φ(g⁻¹ δ T(u) θ(g)) du dg`, with `T(u) = δ⁻¹ u δ θ(u)⁻¹`. The map `T` is a
topological group automorphism of `U` (it is injective since `H ∩ U = 1`, and open by the open
mapping theorem), so the inner integral is an integral against the Haar measure `T_* du` and
vanishes.

This is the fibre argument behind the vanishing of (twisted) orbital integrals of cusp forms
off the elliptic set (Henniart–Lemaire 2011, II.4.5 and II.5.14).
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Langlands.QuotientIntegration
open scoped ENNReal NNReal

universe u

variable {G : Type u} [Group G]

/-- The data of an abelian fibre for the twisted conjugation `x ↦ x⁻¹ δ θ(x)`: a closed abelian
subgroup `U` stable under `θ`, a closed subgroup `P` containing `δ`, `U` and the twisted
centralizer `H` of `δ`, and a continuous homomorphism `π : P →* G` with kernel `U` that is the
identity on `H`. -/
structure TwistedFibreData [TopologicalSpace G] (θ : G →* G) (δ : G) where
  /-- The abelian fibre. -/
  U : Subgroup G
  isClosed_U : IsClosed (U : Set G)
  comm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  map_mem : ∀ a ∈ U, θ a ∈ U
  /-- The ambient subgroup on which the projection is defined. -/
  P : Subgroup G
  isClosed_P : IsClosed (P : Set G)
  /-- The projection with kernel `U`. -/
  π : P →* G
  continuous_π : Continuous π
  π_eq_one_iff : ∀ p : P, π p = 1 ↔ (p : G) ∈ U
  U_le_P : U ≤ P
  centralizer_le_P : twistedCentralizer θ δ ≤ P
  π_eq_self : ∀ p : P, (p : G) ∈ twistedCentralizer θ δ → π p = p
  mem_P : δ ∈ P

namespace TwistedFibreData

section Algebra

variable [TopologicalSpace G] {θ : G →* G} {δ : G} (D : TwistedFibreData θ δ)

local notation "H" => twistedCentralizer θ δ

/-- `π` takes the value `1` on `U`. -/
theorem π_of_mem_U {a : G} (ha : a ∈ D.U) : D.π ⟨a, D.U_le_P ha⟩ = 1 :=
  (D.π_eq_one_iff _).2 ha

/-- An element of `P` lies in `U` when `π` sends it to `1`. -/
theorem mem_U_of_π {a : G} (ha : a ∈ D.P) (h : D.π ⟨a, ha⟩ = 1) : a ∈ D.U :=
  (D.π_eq_one_iff ⟨a, ha⟩).1 h

/-- Conjugation by an element of `P` whose image commutes appropriately preserves `U`:
`p⁻¹ a p ∈ U` for `p ∈ P` and `a ∈ U`. -/
theorem inv_mul_mul_mem {p a : G} (hp : p ∈ D.P) (ha : a ∈ D.U) : p⁻¹ * a * p ∈ D.U := by
  have hm : p⁻¹ * a * p ∈ D.P := D.P.mul_mem (D.P.mul_mem (D.P.inv_mem hp) (D.U_le_P ha)) hp
  refine D.mem_U_of_π hm ?_
  have he : (⟨p⁻¹ * a * p, hm⟩ : D.P) = (⟨p, hp⟩ : D.P)⁻¹ * ⟨a, D.U_le_P ha⟩ * ⟨p, hp⟩ := rfl
  rw [he, map_mul, map_mul, map_inv, D.π_of_mem_U ha, mul_one, inv_mul_cancel]

/-- `p a p⁻¹ ∈ U` for `p ∈ P` and `a ∈ U`. -/
theorem mul_mul_inv_mem {p a : G} (hp : p ∈ D.P) (ha : a ∈ D.U) : p * a * p⁻¹ ∈ D.U := by
  simpa only [inv_inv] using D.inv_mul_mul_mem (D.P.inv_mem hp) ha

/-- `H ∩ U = 1`. -/
theorem eq_one_of_mem_U_of_mem_centralizer {a : G} (ha : a ∈ D.U) (hH : a ∈ H) : a = 1 := by
  have h1 := D.π_of_mem_U ha
  rwa [D.π_eq_self ⟨a, D.U_le_P ha⟩ hH] at h1

/-- The subgroup `S = U H`: the elements of `P` whose image under `π` lies in `H`. -/
def S : Subgroup G := ((twistedCentralizer θ δ).comap D.π).map D.P.subtype

theorem S_le_P : D.S ≤ D.P := Subgroup.map_subtype_le _

/-- The `H`-component `π(s)` of an element `s ∈ S`. -/
def retract (s : D.S) : G := D.π ⟨s.val, D.S_le_P s.2⟩

theorem retract_mem (s : D.S) : D.retract s ∈ H := by
  obtain ⟨p, hp, hps⟩ := Subgroup.mem_map.1 s.2
  have : (⟨s.val, D.S_le_P s.2⟩ : D.P) = p := Subtype.ext hps.symm
  rw [retract, this]
  exact hp

theorem mul_mem_S {a h : G} (ha : a ∈ D.U) (hh : h ∈ H) : a * h ∈ D.S := by
  refine Subgroup.mem_map.2 ⟨⟨a * h, D.P.mul_mem (D.U_le_P ha) (D.centralizer_le_P hh)⟩, ?_, rfl⟩
  change D.π (⟨a, D.U_le_P ha⟩ * ⟨h, D.centralizer_le_P hh⟩) ∈ H
  rw [map_mul, D.π_of_mem_U ha, one_mul, D.π_eq_self _ hh]
  exact hh

theorem retract_mul (a h : G) (ha : a ∈ D.U) (hh : h ∈ H) :
    D.retract ⟨a * h, D.mul_mem_S ha hh⟩ = h := by
  change D.π (⟨a, D.U_le_P ha⟩ * ⟨h, D.centralizer_le_P hh⟩) = h
  rw [map_mul, D.π_of_mem_U ha, one_mul, D.π_eq_self _ hh]

theorem mul_retract_inv_mem (s : D.S) : s.val * (D.retract s)⁻¹ ∈ D.U := by
  have hr := D.retract_mem s
  have hm : s.val * (D.retract s)⁻¹ ∈ D.P :=
    D.P.mul_mem (D.S_le_P s.2) (D.P.inv_mem (D.centralizer_le_P hr))
  refine D.mem_U_of_π hm ?_
  change D.π (⟨s.val, D.S_le_P s.2⟩ * (⟨D.retract s, D.centralizer_le_P hr⟩ : D.P)⁻¹) = 1
  rw [map_mul, map_inv, D.π_eq_self ⟨D.retract s, D.centralizer_le_P hr⟩ hr]
  exact mul_inv_cancel _

/-- The twisted conjugation `T(a) = δ⁻¹ a δ θ(a)⁻¹` on `U`. -/
def twist : D.U →* D.U where
  toFun a := ⟨δ⁻¹ * a.val * δ * (θ a.val)⁻¹,
    D.U.mul_mem (D.inv_mul_mul_mem D.mem_P a.2) (D.U.inv_mem (D.map_mem _ a.2))⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    have ha := D.inv_mul_mul_mem D.mem_P a.2
    have hb := D.inv_mul_mul_mem D.mem_P b.2
    have hc := D.U.inv_mem (D.map_mem _ a.2)
    have hd := D.U.inv_mem (D.map_mem _ b.2)
    change δ⁻¹ * (a.val * b.val) * δ * (θ (a.val * b.val))⁻¹ =
      δ⁻¹ * a.val * δ * (θ a.val)⁻¹ * (δ⁻¹ * b.val * δ * (θ b.val)⁻¹)
    have e1 : δ⁻¹ * (a.val * b.val) * δ * (θ (a.val * b.val))⁻¹ =
        (δ⁻¹ * a.val * δ) * ((δ⁻¹ * b.val * δ) * ((θ b.val)⁻¹ * (θ a.val)⁻¹)) := by
      rw [map_mul, mul_inv_rev]
      group
    have e2 : (δ⁻¹ * b.val * δ) * ((θ b.val)⁻¹ * (θ a.val)⁻¹) =
        (θ a.val)⁻¹ * ((δ⁻¹ * b.val * δ) * (θ b.val)⁻¹) := by
      rw [D.comm _ hd _ hc, ← mul_assoc, D.comm _ hb _ hc, mul_assoc]
    rw [e1, e2]
    group

@[simp] theorem twist_apply_coe (a : D.U) :
    (D.twist a : G) = δ⁻¹ * a.val * δ * (θ a.val)⁻¹ := rfl

theorem twist_injective : Function.Injective D.twist := by
  refine (injective_iff_map_eq_one D.twist).2 fun a ha => ?_
  have h : δ⁻¹ * a.val * δ * (θ a.val)⁻¹ = 1 := congrArg Subtype.val ha
  have hH : a.val ∈ H := by
    change a.val⁻¹ * δ * θ a.val = δ
    have h' : a.val * δ = δ * θ a.val := by
      have := congrArg (fun x => δ * x * θ a.val) h
      simpa [mul_assoc] using this
    calc a.val⁻¹ * δ * θ a.val = a.val⁻¹ * (δ * θ a.val) := mul_assoc _ _ _
      _ = a.val⁻¹ * (a.val * δ) := by rw [h']
      _ = δ := by group
  exact Subtype.ext (D.eq_one_of_mem_U_of_mem_centralizer a.2 hH)

end Algebra

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G] {θ : G →* G} {δ : G}
  (D : TwistedFibreData θ δ)

local notation "H" => twistedCentralizer θ δ

/-- The twisted centralizer of `δ` is closed when `θ` is continuous. -/
theorem isClosed_centralizer [T2Space G] (hθ : Continuous θ) : IsClosed (H : Set G) :=
  isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const

omit [IsTopologicalGroup G] in
theorem continuous_retract : Continuous D.retract :=
  D.continuous_π.comp (continuous_subtype_val.subtype_mk _)

/-- `S = U H` is closed. -/
theorem isClosed_S [T2Space G] (hθ : Continuous θ) : IsClosed (D.S : Set G) := by
  have h1 : IsClosed (((twistedCentralizer θ δ).comap D.π : Subgroup D.P) : Set D.P) :=
    (isClosed_centralizer hθ).preimage D.continuous_π
  have h2 := D.isClosed_P.isClosedMap_subtype_val _ h1
  rw [S, Subgroup.coe_map]
  exact h2

/-- The factorization `H × U ≃ₜ S`, `(h, a) ↦ a h`. -/
def prodHomeomorph : H × D.U ≃ₜ D.S where
  toFun z := ⟨z.2.val * z.1.val, D.mul_mem_S z.2.2 z.1.2⟩
  invFun s := (⟨D.retract s, D.retract_mem s⟩, ⟨s.val * (D.retract s)⁻¹, D.mul_retract_inv_mem s⟩)
  left_inv z := by
    rcases z with ⟨h, a⟩
    have hr := D.retract_mul a.val h.val a.2 h.2
    refine Prod.ext (Subtype.ext hr) (Subtype.ext ?_)
    change a.val * h.val * (D.retract ⟨a.val * h.val, _⟩)⁻¹ = a.val
    rw [hr, mul_inv_cancel_right]
  right_inv s := Subtype.ext (inv_mul_cancel_right s.val (D.retract s))
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_snd).mul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  continuous_invFun :=
    (D.continuous_retract.subtype_mk _).prodMk
      ((continuous_subtype_val.mul D.continuous_retract.inv).subtype_mk _)

@[simp] theorem prodHomeomorph_apply_coe (z : H × D.U) :
    (D.prodHomeomorph z : G) = z.2.val * z.1.val := rfl

theorem continuous_twist (hθ : Continuous θ) : Continuous D.twist :=
  ((((continuous_const.mul continuous_subtype_val).mul continuous_const).mul
    (hθ.comp continuous_subtype_val).inv)).subtype_mk _

/-- The twisted conjugation `T` as a topological group automorphism of `U`, by the open mapping
theorem for the σ-compact locally compact group `U`. -/
def twistEquiv [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (hθ : Continuous θ) (hsurj : Function.Surjective D.twist) : D.U ≃ₜ* D.U :=
  haveI : LocallyCompactSpace D.U := D.isClosed_U.locallyCompactSpace
  haveI : SecondCountableTopology D.U :=
    TopologicalSpace.Subtype.secondCountableTopology (D.U : Set G)
  let e : D.U ≃* D.U := MulEquiv.ofBijective D.twist ⟨D.twist_injective, hsurj⟩
  let h : D.U ≃ₜ D.U := e.toEquiv.toHomeomorphOfContinuousOpen (D.continuous_twist hθ)
    (MonoidHom.isOpenMap_of_sigmaCompact D.twist hsurj (D.continuous_twist hθ))
  { toMulEquiv := e
    continuous_toFun := h.continuous
    continuous_invFun := h.symm.continuous }

@[simp] theorem twistEquiv_apply [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (hθ : Continuous θ) (hsurj : Function.Surjective D.twist) (a : D.U) :
    D.twistEquiv hθ hsurj a = D.twist a := rfl

end Topology

end TwistedFibreData

section Fubini

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Averaging along a fibre.** Let `U` be a subgroup of `G` with an s-finite measure `μU`, `μG`
a left-invariant measure on `G`, `ρ : G → ℝ≥0` continuous and `ρ'(g) = ∫⁻_U ρ(a g) dμU(a)`,
finite `μG`-almost everywhere. If a continuous `Φ` satisfies `∫_U Φ(a⁻¹ g) dμU(a) = 0` for every
`g`, then `∫_G ρ'(g) Φ(g) dμG(g) = 0`: by Fubini on `U × G` and the measure-preserving shear
`(a, g) ↦ (a, a⁻¹ g)`. -/
theorem integral_fibreAverage_smul_eq_zero (U : Subgroup G) (μU : Measure U) [SFinite μU]
    (μG : Measure G) [SFinite μG] [μG.IsMulLeftInvariant] {ρ : G → ℝ≥0} (hρ : Continuous ρ)
    (hfin : ∀ᵐ g ∂μG, ∫⁻ a : U, (ρ (a.val * g) : ℝ≥0∞) ∂μU < ⊤)
    {Φ : G → ℂ} (hΦ : Continuous Φ) (hinner : ∀ g, ∫ a : U, Φ (a.val⁻¹ * g) ∂μU = 0) :
    ∫ g, (∫⁻ a : U, (ρ (a.val * g) : ℝ≥0∞) ∂μU).toReal • Φ g ∂μG = 0 := by
  have : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  set ρ' : G → ℝ≥0∞ := fun g => ∫⁻ a : U, (ρ (a.val * g) : ℝ≥0∞) ∂μU with hρ'
  by_cases hint : Integrable (fun g => (ρ' g).toReal • Φ g) μG
  swap
  · exact integral_undef hint
  have hcρ : ∀ g, Continuous fun a : U => (ρ (a.val * g) : ℝ) :=
    fun g => NNReal.continuous_coe.comp (hρ.comp (continuous_subtype_val.mul continuous_const))
  have hρint : ∀ g, ∫ a : U, (ρ (a.val * g) : ℝ) ∂μU = (ρ' g).toReal := by
    intro g
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun a => NNReal.coe_nonneg _)
      (hcρ g).aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun a => ?_
    rw [ENNReal.ofReal_coe_nnreal]
  let K : U × G → ℂ := fun z => (ρ (z.1.val * z.2) : ℝ) • Φ z.2
  have hKc : Continuous K :=
    (NNReal.continuous_coe.comp (hρ.comp ((continuous_subtype_val.comp continuous_fst).mul
      continuous_snd))).smul (hΦ.comp continuous_snd)
  have hK : Integrable K (μU.prod μG) := by
    rw [integrable_prod_iff' hKc.aestronglyMeasurable]
    constructor
    · filter_upwards [hfin] with g hg
      have hm : Measurable fun a : U => (ρ (a.val * g) : ℝ≥0∞) :=
        (ENNReal.continuous_coe.comp (hρ.comp (continuous_subtype_val.mul continuous_const))).measurable
      have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hg.ne
      simp only [ENNReal.coe_toReal] at hi
      exact hi.smul_const (Φ g)
    · refine hint.norm.congr (Filter.Eventually.of_forall fun g => ?_)
      simp only [K, norm_smul, Real.norm_eq_abs, NNReal.abs_eq]
      rw [integral_mul_const, hρint, abs_of_nonneg ENNReal.toReal_nonneg]
  have h1 : ∫ z, K z ∂(μU.prod μG) = ∫ g, (ρ' g).toReal • Φ g ∂μG := by
    rw [integral_prod_symm K hK]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [K]
    rw [integral_smul_const, hρint]
  let τ : U × G ≃ᵐ U × G :=
    { toFun := fun z => (z.1, z.1.val⁻¹ * z.2)
      invFun := fun z => (z.1, z.1.val * z.2)
      left_inv := fun z => by simp
      right_inv := fun z => by simp
      measurable_toFun := (continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd)).measurable
      measurable_invFun := (continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).measurable }
  have hτ : MeasurePreserving τ (μU.prod μG) (μU.prod μG) :=
    (MeasurePreserving.id μU).skew_product (g := fun (a : U) (x : G) => a.val⁻¹ * x)
      ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd).measurable
      (Filter.Eventually.of_forall fun a => map_mul_left_eq_self μG _)
  have hKτ : Integrable (fun z => K (τ z)) (μU.prod μG) :=
    (hτ.integrable_comp_emb τ.measurableEmbedding).2 hK
  have h2 : ∫ z, K (τ z) ∂(μU.prod μG) = ∫ z, K z ∂(μU.prod μG) := hτ.integral_comp' K
  have h3 : ∫ z, K (τ z) ∂(μU.prod μG) = 0 := by
    rw [integral_prod_symm _ hKτ]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)).trans (integral_zero G ℂ)
    change ∫ a : U, (ρ (a.val * (a.val⁻¹ * g)) : ℝ) • Φ (a.val⁻¹ * g) ∂μU = 0
    simp only [mul_inv_cancel_left]
    rw [integral_smul, hinner g, smul_zero]
  rw [← h1, ← h2, h3]

end Fubini

namespace TwistedFibreData

section Measure

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {θ : G →* G} {δ : G}
  (D : TwistedFibreData θ δ)

local notation "H" => twistedCentralizer θ δ

omit [T2Space G] [LocallyCompactSpace G] in
/-- The image of `μH × μU` under `(h, a) ↦ a h` is a right-invariant measure on `S = U H`. -/
theorem isMulRightInvariant_map_prodHomeomorph (μH : Measure H) [μH.IsMulRightInvariant]
    [SFinite μH] (μU : Measure D.U) [μU.IsMulLeftInvariant] [SFinite μU] :
    (Measure.map D.prodHomeomorph (μH.prod μU)).IsMulRightInvariant := by
  have : SecondCountableTopology D.U :=
    TopologicalSpace.Subtype.secondCountableTopology (D.U : Set G)
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have : SecondCountableTopology D.S :=
    TopologicalSpace.Subtype.secondCountableTopology (D.S : Set G)
  refine ⟨fun s => ?_⟩
  obtain ⟨⟨h', a'⟩, rfl⟩ := D.prodHomeomorph.surjective s
  let c : H → D.U := fun h =>
    ⟨h.val * a'.val * h.val⁻¹, D.mul_mul_inv_mem (D.centralizer_le_P h.2) a'.2⟩
  have hc : Continuous c :=
    (((continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.inv)).subtype_mk _
  have hτ : MeasurePreserving (fun z : H × D.U => (z.1 * h', z.2 * c z.1))
      (μH.prod μU) (μH.prod μU) :=
    (measurePreserving_mul_right μH h').skew_product (g := fun h a => a * c h)
      ((continuous_snd.mul (hc.comp continuous_fst))).measurable
      (Filter.Eventually.of_forall fun h => by
        have hfun : (fun a : D.U => a * c h) = fun a => c h * a := by
          funext a
          exact Subtype.ext (D.comm _ a.2 _ (c h).2)
        rw [hfun]
        exact map_mul_left_eq_self μU _)
  have hcomm : (fun x : D.S => x * D.prodHomeomorph (h', a')) ∘ D.prodHomeomorph =
      D.prodHomeomorph ∘ fun z : H × D.U => (z.1 * h', z.2 * c z.1) := by
    funext z
    apply Subtype.ext
    change z.2.val * z.1.val * (a'.val * h'.val) =
      z.2.val * (z.1.val * a'.val * z.1.val⁻¹) * (z.1.val * h'.val)
    group
  rw [Measure.map_map (measurable_mul_const _) D.prodHomeomorph.continuous.measurable, hcomm,
    ← Measure.map_map D.prodHomeomorph.continuous.measurable hτ.measurable, hτ.map_eq]

/-- **Vanishing along an abelian fibre.** If `∫_U φ(x a y) dμ(a) = 0` for every Haar measure `μ`
on `U` and all `x, y`, then the twisted orbital integral of `φ` at `δ` vanishes for every right
Haar measure on the twisted centralizer and every compatible quotient measure. -/
theorem twistedOrbitalIntegral_eq_zero (hθ : Continuous θ) (hsurj : Function.Surjective D.twist)
    {φ : G → ℂ} (hφc : Continuous φ)
    (hφ : ∀ μ : Measure D.U, μ.IsHaarMeasure → ∀ x y : G, ∫ a : D.U, φ (x * a.val * y) ∂μ = 0)
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μG μH ν) :
    twistedOrbitalIntegral θ δ ν φ = 0 := by
  have : LocallyCompactSpace D.U := D.isClosed_U.locallyCompactSpace
  have : SecondCountableTopology D.U :=
    TopologicalSpace.Subtype.secondCountableTopology (D.U : Set G)
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have : SecondCountableTopology D.S :=
    TopologicalSpace.Subtype.secondCountableTopology (D.S : Set G)
  have hHc : IsClosed (H : Set G) := isClosed_centralizer hθ
  have : LocallyCompactSpace H := hHc.locallyCompactSpace
  let μU : Measure D.U := Measure.haar
  let μS : Measure D.S := Measure.map D.prodHomeomorph (μH.prod μU)
  have : μS.IsMulRightInvariant := D.isMulRightInvariant_map_prodHomeomorph μH μU
  have : IsFiniteMeasureOnCompacts μS := IsFiniteMeasureOnCompacts.map _ _
  have : μS.IsOpenPosMeasure :=
    D.prodHomeomorph.continuous.isOpenPosMeasure_map D.prodHomeomorph.surjective
  obtain ⟨ρ, hρc, hρ, -⟩ := exists_continuous_isNormalizingFunction D.S (D.isClosed_S hθ) μS
  let ρ' : G → ℝ≥0∞ := fun g => ∫⁻ a : D.U, (ρ (a.val * g) : ℝ≥0∞) ∂μU
  have hρm : Measurable fun z : D.U × G => (ρ (z.1.val * z.2) : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp (hρc.comp ((continuous_subtype_val.comp continuous_fst).mul
      continuous_snd))).measurable
  have hρ' : IsNormalizingFunction H μH ρ' := by
    refine ⟨hρm.lintegral_prod_left', fun g => ?_⟩
    have h1 := hρ.lintegral_eq_one g
    have hm : Measurable fun s : D.S => (ρ (s.val * g) : ℝ≥0∞) :=
      (ENNReal.continuous_coe.comp (hρc.comp (continuous_subtype_val.mul continuous_const))).measurable
    rw [lintegral_map hm D.prodHomeomorph.continuous.measurable] at h1
    rw [lintegral_prod (fun z => (ρ ((D.prodHomeomorph z : G) * g) : ℝ≥0∞))
      (hm.comp D.prodHomeomorph.continuous.measurable).aemeasurable] at h1
    refine Eq.trans ?_ h1
    refine lintegral_congr fun h => lintegral_congr fun a => ?_
    simp only [prodHomeomorph_apply_coe, mul_assoc]
  let Φ : G → ℂ := fun x => φ (x⁻¹ * δ * θ x)
  have hΦc : Continuous Φ := hφc.comp ((continuous_inv.mul continuous_const).mul hθ)
  have hdesc := hν.integral_descend_eq hHc hρ' Φ hΦc.measurable
    (fun c x => congrArg φ (twistedConj_left_mul θ δ c x))
  refine hdesc.trans ?_
  refine integral_fibreAverage_smul_eq_zero D.U μU μG hρc (hρ'.ae_lt_top hHc hν) hΦc fun g => ?_
  let T := D.twistEquiv hθ hsurj
  have hT : (Measure.map T μU).IsHaarMeasure := inferInstance
  have h0 := hφ _ hT (g⁻¹ * δ) (θ g)
  rw [show Measure.map T μU = Measure.map T.toHomeomorph.toMeasurableEquiv μU from rfl,
    integral_map_equiv] at h0
  refine Eq.trans ?_ h0
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  change φ ((a.val⁻¹ * g)⁻¹ * δ * θ (a.val⁻¹ * g)) =
    φ (g⁻¹ * δ * (δ⁻¹ * a.val * δ * (θ a.val)⁻¹) * θ g)
  congr 1
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
  group

end Measure

end TwistedFibreData

end Langlands.TraceFormula

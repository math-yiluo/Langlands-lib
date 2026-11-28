import Langlands.Geometry.Building.KPMoyPrasadIsomorphismStatement

/-!
# Assembling abstract quotient isomorphisms

Two abstract tools for assembling `HasMoyPrasadQuotientIso` from component data.

* If `H₂ ≤ H₁` and `⁅H₁, H₁⁆ ≤ H₂`, then `H₂` is normal in `H₁` and `H₁ / H₂` is commutative.
  Two surjective homomorphisms out of one group, onto `H₁ / H₂` and onto `g₁ / g₂`, with the
  same kernel give `HasMoyPrasadQuotientIso H₁ H₂ g₁ g₂`.
* An additive map sending `A₁` into `B₁` and `A₂` into `B₂` induces `A₁ / A₂ → B₁ / B₂`.
* Grouping an independent family of elements of a modular compactly generated lattice along
  pairwise disjoint sets of indices gives an independent family.
-/

noncomputable section

open scoped Function

namespace Langlands.Geometry.Building

section Quotient

variable {Γ M : Type*} [Group Γ] [AddCommGroup M]

/-- If `⁅H₁, H₁⁆ ≤ H₂`, then `H₂ ∩ H₁` is normal in `H₁`. -/
theorem subgroupOf_normal_of_commutator_le {H₁ H₂ : Subgroup Γ}
    (hcomm : ⁅H₁, H₁⁆ ≤ H₂) : (H₂.subgroupOf H₁).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 : (g : Γ) * n * (g : Γ)⁻¹ * (n : Γ)⁻¹ ∈ H₂ :=
    hcomm (Subgroup.commutator_mem_commutator g.2 n.2)
  have h2 := H₂.mul_mem h1 hn
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] using h2

/-- If `⁅H₁, H₁⁆ ≤ H₂`, the quotient of `H₁` by `H₂ ∩ H₁` is commutative. -/
theorem quotient_mul_comm_of_commutator_le {H₁ H₂ : Subgroup Γ} [(H₂.subgroupOf H₁).Normal]
    (hcomm : ⁅H₁, H₁⁆ ≤ H₂) (a b : H₁ ⧸ H₂.subgroupOf H₁) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h := hcomm (Subgroup.commutator_mem_commutator (H₁.inv_mem b.2) (H₁.inv_mem a.2))
  rw [commutatorElement_def] at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc] using h

/-- The commutative group structure on `H₁ / (H₂ ∩ H₁)` when `⁅H₁, H₁⁆ ≤ H₂`. -/
abbrev quotientCommGroupOfCommutatorLE {H₁ H₂ : Subgroup Γ} [(H₂.subgroupOf H₁).Normal]
    (hcomm : ⁅H₁, H₁⁆ ≤ H₂) : CommGroup (H₁ ⧸ H₂.subgroupOf H₁) :=
  { (inferInstance : Group (H₁ ⧸ H₂.subgroupOf H₁)) with
    mul_comm := quotient_mul_comm_of_commutator_le hcomm }

/-- Two surjective homomorphisms out of one group `K`, onto `H₁ / (H₂ ∩ H₁)` and onto
`g₁ / g₂`, with equal kernels, give `HasMoyPrasadQuotientIso H₁ H₂ g₁ g₂`. -/
theorem hasMoyPrasadQuotientIso_of_ker_eq {H₁ H₂ : Subgroup Γ} {g₁ g₂ : AddSubgroup M}
    [(H₂.subgroupOf H₁).Normal] {K : Type*} [Group K]
    (Θ : K →* H₁ ⧸ H₂.subgroupOf H₁) (hΘ : Function.Surjective Θ)
    (Λ : K →* Multiplicative (g₁ ⧸ g₂.addSubgroupOf g₁)) (hΛ : Function.Surjective Λ)
    (hker : Θ.ker = Λ.ker) : HasMoyPrasadQuotientIso H₁ H₂ g₁ g₂ := by
  let e : (H₁ ⧸ H₂.subgroupOf H₁) ≃* Multiplicative (g₁ ⧸ g₂.addSubgroupOf g₁) :=
    (QuotientGroup.quotientKerEquivOfSurjective Θ hΘ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective Λ hΛ))
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

/-- The map `A₁ / A₂ → B₁ / B₂` induced by an additive map `f` sending `A₁` into `B₁` and `A₂`
into `B₂`, for additive subgroups `A₂, A₁` of `M` and `B₂, B₁` of `N`. -/
def addSubgroupQuotientMap {N : Type*} [AddCommGroup N] (f : M →+ N)
    {A₁ A₂ : AddSubgroup M} {B₁ B₂ : AddSubgroup N} (h₁ : ∀ X ∈ A₁, f X ∈ B₁)
    (h₂ : ∀ X ∈ A₂, f X ∈ B₂) :
    A₁ ⧸ A₂.addSubgroupOf A₁ →+ B₁ ⧸ B₂.addSubgroupOf B₁ :=
  QuotientAddGroup.map _ _
    { toFun := fun X => ⟨f X, h₁ X X.2⟩
      map_zero' := Subtype.ext f.map_zero
      map_add' := fun X Y => Subtype.ext (f.map_add X Y) }
    (fun X hX => h₂ X hX)

theorem addSubgroupQuotientMap_mk {N : Type*} [AddCommGroup N] (f : M →+ N)
    {A₁ A₂ : AddSubgroup M} {B₁ B₂ : AddSubgroup N} (h₁ : ∀ X ∈ A₁, f X ∈ B₁)
    (h₂ : ∀ X ∈ A₂, f X ∈ B₂) (X : A₁) :
    addSubgroupQuotientMap f h₁ h₂ (X : A₁ ⧸ A₂.addSubgroupOf A₁) =
      ((⟨f X, h₁ X X.2⟩ : B₁) : B₁ ⧸ B₂.addSubgroupOf B₁) :=
  rfl

end Quotient

section Independence

variable {α ι κ : Type*} [CompleteLattice α] [IsModularLattice α] [IsCompactlyGenerated α]

/-- Grouping an independent family along pairwise disjoint index sets keeps it independent. -/
theorem iSupIndep_biSup_of_pairwise_disjoint {f : ι → α} (hf : iSupIndep f)
    (T : κ → Set ι) (hT : Pairwise (Disjoint on T)) :
    iSupIndep fun k => ⨆ i ∈ T k, f i := by
  rw [iSupIndep_def]
  intro k
  refine (hf.disjoint_biSup_biSup (s := T k) (t := ⋃ (k' : κ) (_ : k' ≠ k), T k') ?_).mono_right
    ?_
  · simp only [Set.disjoint_iUnion_right]
    intro k' hk'
    exact hT (Ne.symm hk')
  · exact iSup₂_le fun k' hk' => biSup_mono fun i hi => Set.mem_iUnion₂.2 ⟨k', hk', hi⟩

end Independence

end Langlands.Geometry.Building

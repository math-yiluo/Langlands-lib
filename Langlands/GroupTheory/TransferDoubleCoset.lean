import Langlands.ClassField.Global.RelativeWeilTransfer

/-! # The double-coset formula for the transfer along a homomorphism

For a finite-index subgroup `H` of `G`, a homomorphism `ψ : L →* G` and elements
`t i` of `G` representing the double cosets `ψ(L) \ G / H`, the transfer of
`ϕ : H →* A` evaluated at `ψ y` is the product over `i` of the transfers to the
stabilizers `{l | (t i)⁻¹ * ψ l * t i ∈ H}` of the conjugated homomorphisms. -/

noncomputable section

namespace Langlands.GroupTheory.Transfer

open Subgroup Subgroup.leftTransversals MulAction

variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]

/-- For a section `τ` of `G → G ⧸ H`, the transfer factor of `g` at the coset `q`
lies in `H`. -/
theorem section_factor_mem {τ : G ⧸ H → G} (hτ : ∀ q, (τ q : G ⧸ H) = q) (g : G)
    (q : G ⧸ H) : (τ q)⁻¹ * g * τ (g⁻¹ • q) ∈ H := by
  have h : ((g * τ (g⁻¹ • q) : G) : G ⧸ H) = q := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, hτ, smul_inv_smul]
  rw [mul_assoc]
  exact QuotientGroup.eq.mp ((hτ q).trans h.symm)

/-- The transfer computed with an arbitrary section `τ` of `G → G ⧸ H`. -/
theorem transfer_eq_prod_section [H.FiniteIndex] [Fintype (G ⧸ H)] (ϕ : H →* A)
    {τ : G ⧸ H → G} (hτ : ∀ q, (τ q : G ⧸ H) = q) (g : G) :
    MonoidHom.transfer ϕ g =
      ∏ q : G ⧸ H, ϕ ⟨(τ q)⁻¹ * g * τ (g⁻¹ • q), section_factor_mem hτ g q⟩ := by
  let T : H.LeftTransversal := ⟨Set.range τ, isComplement_range_left hτ⟩
  rw [MonoidHom.transfer_def ϕ T g, diff]
  congr 1
  · exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
  · funext q
    congr 1
    apply Subtype.ext
    simp only
    rw [smul_apply_eq_smul_apply_inv_smul]
    have h₁ : ((T.2.leftQuotientEquiv q : G)) = τ q :=
      IsComplement.leftQuotientEquiv_apply hτ q
    have h₂ : ((T.2.leftQuotientEquiv (g⁻¹ • q) : G)) = τ (g⁻¹ • q) :=
      IsComplement.leftQuotientEquiv_apply hτ _
    rw [h₁, h₂, smul_eq_mul, mul_assoc]

section DoubleCoset

variable {L : Type*} [Group L] (ψ : L →* G) {ι : Type*} (t : ι → G) (K : ι → Subgroup L)
  (hK : ∀ i l, l ∈ K i ↔ (t i)⁻¹ * ψ l * t i ∈ H)

/-- The map `(i, l K_i) ↦ ψ l t_i H` from the stabilizer cosets to `G ⧸ H`. -/
def doubleCosetMap : (Σ i, L ⧸ K i) → G ⧸ H := fun p =>
  Quotient.liftOn' p.2 (fun l => ((ψ l * t p.1 : G) : G ⧸ H)) fun a b hab => by
    have h := (hK p.1 _).1 (QuotientGroup.leftRel_apply.mp hab)
    refine QuotientGroup.eq.mpr ?_
    simpa [mul_assoc] using h

variable {ψ t K hK}

theorem doubleCosetMap_mk (i : ι) (l : L) :
    doubleCosetMap ψ t K hK ⟨i, (l : L ⧸ K i)⟩ = ((ψ l * t i : G) : G ⧸ H) := rfl

theorem doubleCosetMap_eq_out (p : Σ i, L ⧸ K i) :
    doubleCosetMap ψ t K hK p = ((ψ p.2.out * t p.1 : G) : G ⧸ H) := by
  obtain ⟨i, β⟩ := p
  conv_lhs => rw [← QuotientGroup.out_eq' β]
  rfl

theorem doubleCosetMap_smul (y : L) (i : ι) (β : L ⧸ K i) :
    doubleCosetMap ψ t K hK ⟨i, y • β⟩ = ψ y • doubleCosetMap ψ t K hK ⟨i, β⟩ := by
  induction β using QuotientGroup.induction_on with
  | H l =>
    rw [MulAction.Quotient.smul_mk, doubleCosetMap_mk, doubleCosetMap_mk,
      MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul, map_mul, mul_assoc]

theorem doubleCosetMap_bijective
    (hcover : ∀ g : G, ∃ i l, ∃ h ∈ H, g = ψ l * t i * h)
    (hdisj : ∀ i j (l : L), ∀ h ∈ H, t j = ψ l * t i * h → i = j) :
    Function.Bijective (doubleCosetMap ψ t K hK) := by
  constructor
  · rintro ⟨i, β⟩ ⟨j, γ⟩ hβγ
    induction β using QuotientGroup.induction_on with
    | H l =>
    induction γ using QuotientGroup.induction_on with
    | H l' =>
    rw [doubleCosetMap_mk, doubleCosetMap_mk] at hβγ
    have hmem := QuotientGroup.eq.mp hβγ
    have hij : i = j := by
      refine hdisj i j (l'⁻¹ * l) _ hmem ?_
      simp [mul_assoc]
    subst hij
    have hl : l⁻¹ * l' ∈ K i := by
      refine (hK i _).2 ?_
      simpa [mul_assoc] using hmem
    exact Sigma.ext rfl (heq_of_eq (QuotientGroup.eq.mpr hl))
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
    obtain ⟨i, l, h, hh, rfl⟩ := hcover g
    exact ⟨⟨i, (l : L ⧸ K i)⟩, (QuotientGroup.mk_mul_of_mem _ hh).symm⟩

/-- The double-coset formula for the transfer along `ψ : L →* G`: if the elements `t i`
represent the double cosets `ψ(L) \ G / H` and `K i` is the subgroup of `l` with
`(t i)⁻¹ * ψ l * t i ∈ H`, then the transfer of `ϕ` at `ψ y` is the product of the
transfers of the conjugated homomorphisms `ϕ' i : K i →* A`. -/
theorem transfer_comp_eq_prod_of_conj [H.FiniteIndex] [Fintype ι] [∀ i, (K i).FiniteIndex]
    (ϕ : H →* A) (ϕ' : ∀ i, K i →* A)
    (hϕ' : ∀ i (k : K i), ϕ' i k = ϕ ⟨(t i)⁻¹ * ψ k * t i, (hK i k).1 k.2⟩)
    (hcover : ∀ g : G, ∃ i l, ∃ h ∈ H, g = ψ l * t i * h)
    (hdisj : ∀ i j (l : L), ∀ h ∈ H, t j = ψ l * t i * h → i = j) (y : L) :
    MonoidHom.transfer ϕ (ψ y) = ∏ i, MonoidHom.transfer (ϕ' i) y := by
  classical
  let := H.fintypeQuotientOfFiniteIndex
  let : ∀ i, Fintype (L ⧸ K i) := fun i => (K i).fintypeQuotientOfFiniteIndex
  let e : (Σ i, L ⧸ K i) ≃ G ⧸ H :=
    Equiv.ofBijective (doubleCosetMap ψ t K hK) (doubleCosetMap_bijective hcover hdisj)
  have he : ∀ p, e p = doubleCosetMap ψ t K hK p := fun _ => rfl
  let τ : G ⧸ H → G := fun q => ψ (e.symm q).2.out * t (e.symm q).1
  have hτ : ∀ q, (τ q : G ⧸ H) = q := by
    intro q
    rw [← doubleCosetMap_eq_out (hK := hK), ← he, e.apply_symm_apply]
  have hτe : ∀ p, τ (e p) = ψ p.2.out * t p.1 := by
    intro p
    show ψ (e.symm (e p)).2.out * t (e.symm (e p)).1 = _
    rw [e.symm_apply_apply]
  rw [transfer_eq_prod_section ϕ hτ (ψ y), ← e.prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [transfer_eq_prod_section (ϕ' i) (τ := Quotient.out) QuotientGroup.out_eq' y]
  refine Finset.prod_congr rfl fun β _ => ?_
  have hsmul : (ψ y)⁻¹ • e ⟨i, β⟩ = e ⟨i, y⁻¹ • β⟩ := by
    rw [he, he, doubleCosetMap_smul, map_inv]
  rw [hϕ']
  congr 1
  apply Subtype.ext
  show (τ (e ⟨i, β⟩))⁻¹ * ψ y * τ ((ψ y)⁻¹ • e ⟨i, β⟩) =
    (t i)⁻¹ * ψ ((β.out)⁻¹ * y * (y⁻¹ • β).out) * t i
  rw [hsmul, hτe, hτe]
  simp [mul_assoc]

/-- The double-coset formula with the stabilizers written as comaps: the transfer of
`ϕ` at `ψ y` is the product over the double-coset representatives `t i` of the
transfers of `ϕ` composed with conjugation by `t i`. -/
theorem transfer_comp_eq_prod [H.FiniteIndex] [Fintype ι] (ϕ : H →* A)
    (hcover : ∀ g : G, ∃ i l, ∃ h ∈ H, g = ψ l * t i * h)
    (hdisj : ∀ i j (l : L), ∀ h ∈ H, t j = ψ l * t i * h → i = j) (y : L) :
    MonoidHom.transfer ϕ (ψ y) =
      ∏ i, MonoidHom.transfer
        (ϕ.comp (((MulAut.conj (t i)⁻¹).toMonoidHom.comp ψ).subgroupComap H)) y :=
  transfer_comp_eq_prod_of_conj
    (K := fun i => H.comap ((MulAut.conj (t i)⁻¹).toMonoidHom.comp ψ))
    (hK := fun i l => by simp) ϕ _ (fun i k => by
      rw [MonoidHom.comp_apply]
      congr 1
      apply Subtype.ext
      show (MulAut.conj (t i)⁻¹) (ψ k) = _
      simp) hcover hdisj y

/-- The double-coset formula for a normal subgroup `H`: every stabilizer is `H.comap ψ`,
and the conjugated homomorphisms are `ϕ ∘ conjInv (t i)`. -/
theorem transfer_comp_eq_prod_of_normal [hH : H.Normal] [H.FiniteIndex] [Fintype ι]
    (ϕ : H →* A)
    (hcover : ∀ g : G, ∃ i l, ∃ h ∈ H, g = ψ l * t i * h)
    (hdisj : ∀ i j (l : L), ∀ h ∈ H, t j = ψ l * t i * h → i = j) (y : L) :
    MonoidHom.transfer ϕ (ψ y) =
      ∏ i, MonoidHom.transfer ((ϕ.comp (conjInv (t i))).comp (ψ.subgroupComap H)) y := by
  refine transfer_comp_eq_prod_of_conj (K := fun _ => H.comap ψ) (hK := fun i l => ?_) ϕ _
    (fun i k => rfl) hcover hdisj y
  rw [Subgroup.mem_comap]
  constructor
  · intro h
    simpa using hH.conj_mem _ h (t i)⁻¹
  · intro h
    simpa [mul_assoc] using hH.conj_mem _ h (t i)

end DoubleCoset

end Langlands.GroupTheory.Transfer

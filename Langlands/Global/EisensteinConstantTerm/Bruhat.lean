import Langlands.Global.AdelicParabolicQuotient

/-! # Coset combinatorics of the geometric lemma

Pure group theory behind the unfolding in Bernstein–Lapid §6.10 (proof of (6.17)). Inside a
group `H`, let `Gr` be a subgroup containing subgroups `P`, `Q` and points `w i` such that
every `z ∈ Gr` lies in `Q w_i P` for exactly one `i`. Let `V ≤ Q` be normalized by `Q`, put
`Δ_i = V ∩ w_i P w_i⁻¹` and let `Q'_i = (Q ∩ w_i P w_i⁻¹) V`. Then
`(i, c, ν) ↦ P · w_i⁻¹ ν c` is a bijection from triples with `c ∈ Q'_i \ Q` and `ν ∈ Δ_i \ V`
(evaluated at chosen representatives) onto `P \ Gr`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.EisensteinConstantTerm

open scoped Pointwise

section Bruhat

variable {H : Type*} [Group H]

/-- Membership in the conjugate `w P w⁻¹`, written as the image of `P` under `MulAut.conj w`. -/
theorem mem_map_conj_iff (P : Subgroup H) (w x : H) :
    x ∈ P.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * x * w ∈ P := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- If `V` is normalized by `A`, every element of `A ⊔ V` is a product `a * v`. -/
theorem exists_mul_of_mem_sup {A V : Subgroup H}
    (hN : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V) {x : H} (hx : x ∈ A ⊔ V) :
    ∃ a ∈ A, ∃ v ∈ V, x = a * v := by
  have hle : A ≤ Subgroup.normalizer (V : Set H) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact hN a ha v
    · intro hv
      have h := hN a⁻¹ (A.inv_mem ha) _ hv
      simpa [mul_assoc] using h
  have hx' : x⁻¹ ∈ V ⊔ A := by
    rw [sup_comm]
    exact (A ⊔ V).inv_mem hx
  obtain ⟨n, hn, γ, hγ, h⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hle).mp hx'
  refine ⟨γ⁻¹, A.inv_mem hγ, n⁻¹, V.inv_mem hn, ?_⟩
  rw [← inv_inv x, ← h]
  group

/-- The hypotheses of the coset decomposition: `P, Q ≤ Gr`, `V ≤ Q` normalized by `Q`, the
points `w i` lie in `Gr`, and every `z ∈ Gr` lies in exactly one double coset `Q w_i P`. -/
structure BruhatData (Gr P Q V : Subgroup H) {I : Type*} (w : I → H) : Prop where
  P_le : P ≤ Gr
  Q_le : Q ≤ Gr
  V_le : V ≤ Q
  w_mem : ∀ i, w i ∈ Gr
  normal : ∀ g ∈ Q, ∀ v ∈ V, g * v * g⁻¹ ∈ V
  unique : ∀ z ∈ Gr, ∃! i, ∃ x ∈ Q, ∃ y ∈ P, z = x * w i * y

variable {Gr P Q V : Subgroup H} {I : Type*} {w : I → H}

/-- The subgroup `Δ_i = V ∩ w_i P w_i⁻¹`. -/
def bruhatStabilizer (P V : Subgroup H) (w : H) : Subgroup H :=
  V ⊓ P.map (MulAut.conj w).toMonoidHom

theorem mem_bruhatStabilizer_iff (P V : Subgroup H) (w x : H) :
    x ∈ bruhatStabilizer P V w ↔ x ∈ V ∧ w⁻¹ * x * w ∈ P := by
  rw [bruhatStabilizer, Subgroup.mem_inf, mem_map_conj_iff]

/-- Right cosets `Q'_i \ Q`. -/
abbrev OuterCosets (Q Q' : Subgroup H) := Quotient (QuotientGroup.rightRel (Q'.subgroupOf Q))

/-- Right cosets `Δ_i \ V`. -/
abbrev InnerCosets (P V : Subgroup H) (w : H) :=
  Quotient (QuotientGroup.rightRel ((bruhatStabilizer P V w).subgroupOf V))

/-- Right cosets `P \ Gr`. -/
abbrev AmbientCosets (Gr P : Subgroup H) := Quotient (QuotientGroup.rightRel (P.subgroupOf Gr))

/-- The outer index type `Σ i, Q'_i \ Q`. -/
abbrev OuterIndex (Q : Subgroup H) (Q' : I → Subgroup H) := Σ i : I, OuterCosets Q (Q' i)

/-- The index type `Σ (i, c), Δ_i \ V` with `c ∈ Q'_i \ Q`. -/
abbrev BruhatIndex (P Q V : Subgroup H) (Q' : I → Subgroup H) (w : I → H) :=
  Σ j : OuterIndex Q Q', InnerCosets P V (w j.1)

/-- The point `w_i⁻¹ ν γ` attached to an index, at the chosen representatives. -/
def bruhatPoint (Q' : I → Subgroup H) (t : BruhatIndex P Q V Q' w) : H :=
  (w t.1.1)⁻¹ * ((t.2.out : V) : H) * ((t.1.2.out : Q) : H)

theorem bruhatPoint_mem (hB : BruhatData Gr P Q V w) (Q' : I → Subgroup H)
    (t : BruhatIndex P Q V Q' w) : bruhatPoint Q' t ∈ Gr :=
  Gr.mul_mem (Gr.mul_mem (Gr.inv_mem (hB.w_mem t.1.1)) (hB.Q_le (hB.V_le (t.2.out).2)))
    (hB.Q_le (t.1.2.out).2)

/-- The class of `w_i⁻¹ ν γ` in `P \ Gr`. -/
def bruhatClass (hB : BruhatData Gr P Q V w) (Q' : I → Subgroup H)
    (t : BruhatIndex P Q V Q' w) : AmbientCosets Gr P :=
  Quotient.mk _ ⟨bruhatPoint Q' t, bruhatPoint_mem hB Q' t⟩

/-- Two points of `Gr` have the same class in `P \ Gr` exactly when they differ on the left by
an element of `P`. -/
theorem ambient_mk_eq_iff {x y : Gr} :
    (Quotient.mk _ x : AmbientCosets Gr P) = Quotient.mk _ y ↔ (y : H) * (x : H)⁻¹ ∈ P := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp

theorem bruhatClass_injective (hB : BruhatData Gr P Q V w) (Q' : I → Subgroup H)
    (hQ' : ∀ i, Q' i = (Q ⊓ P.map (MulAut.conj (w i)).toMonoidHom) ⊔ V) :
    Function.Injective (bruhatClass hB Q') := by
  rintro ⟨⟨i, c⟩, ν⟩ ⟨⟨j, c'⟩, ν'⟩ h
  rw [bruhatClass, bruhatClass, ambient_mk_eq_iff] at h
  simp only [bruhatPoint] at h
  set γ : H := ((c.out : Q) : H) with hγ
  set ρ : H := ((ν.out : V) : H) with hρ
  set γ' : H := ((c'.out : Q) : H) with hγ'
  set ρ' : H := ((ν'.out : V) : H) with hρ'
  have hγQ : γ ∈ Q := (c.out).2
  have hγ'Q : γ' ∈ Q := (c'.out).2
  have hρV : ρ ∈ V := (ν.out).2
  have hρ'V : ρ' ∈ V := (ν'.out).2
  set π : H := (w j)⁻¹ * ρ' * γ' * ((w i)⁻¹ * ρ * γ)⁻¹ with hπ
  have hπP : π ∈ P := h
  -- the indices agree
  have hij : i = j := by
    have hz : γ⁻¹ * ρ⁻¹ * w i * π⁻¹ ∈ Gr :=
      Gr.mul_mem (Gr.mul_mem (Gr.mul_mem (Gr.inv_mem (hB.Q_le hγQ))
        (Gr.inv_mem (hB.Q_le (hB.V_le hρV)))) (hB.w_mem i)) (Gr.inv_mem (hB.P_le hπP))
    obtain ⟨k, -, hk⟩ := hB.unique _ hz
    have h1 := hk i ⟨γ⁻¹ * ρ⁻¹, Q.mul_mem (Q.inv_mem hγQ) (Q.inv_mem (hB.V_le hρV)),
      π⁻¹, P.inv_mem hπP, rfl⟩
    have h2 := hk j ⟨γ'⁻¹ * ρ'⁻¹, Q.mul_mem (Q.inv_mem hγ'Q) (Q.inv_mem (hB.V_le hρ'V)),
      1, P.one_mem, by rw [hπ]; group⟩
    exact h1.trans h2.symm
  subst hij
  -- the outer cosets agree
  have hA : ρ' * γ' * (ρ * γ)⁻¹ ∈ Q ⊓ P.map (MulAut.conj (w i)).toMonoidHom := by
    refine Subgroup.mem_inf.mpr ⟨Q.mul_mem (Q.mul_mem (hB.V_le hρ'V) hγ'Q)
      (Q.inv_mem (Q.mul_mem (hB.V_le hρV) hγQ)), ?_⟩
    rw [mem_map_conj_iff]
    have : (w i)⁻¹ * (ρ' * γ' * (ρ * γ)⁻¹) * w i = π := by rw [hπ]; group
    rw [this]
    exact hπP
  have hcc : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c', Quotient.eq, QuotientGroup.rightRel_apply,
      Subgroup.mem_subgroupOf]
    have hmem : γ' * γ⁻¹ ∈ Q' i := by
      rw [hQ' i]
      have : γ' * γ⁻¹ = ρ'⁻¹ * (ρ' * γ' * (ρ * γ)⁻¹) * ρ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (V.inv_mem hρ'V))
        (Subgroup.mem_sup_left hA)) (Subgroup.mem_sup_right hρV)
    simpa [hγ, hγ'] using hmem
  subst hcc
  -- the inner cosets agree
  have hνν : ν = ν' := by
    rw [← Quotient.out_eq ν, ← Quotient.out_eq ν', Quotient.eq, QuotientGroup.rightRel_apply,
      Subgroup.mem_subgroupOf]
    have hmem : ρ' * ρ⁻¹ ∈ bruhatStabilizer P V (w i) := by
      rw [mem_bruhatStabilizer_iff]
      refine ⟨V.mul_mem hρ'V (V.inv_mem hρV), ?_⟩
      have : (w i)⁻¹ * (ρ' * ρ⁻¹) * w i = π := by
        rw [hπ, show γ' = γ from hγ'.trans hγ.symm]; group
      rw [this]
      exact hπP
    simpa [hρ, hρ'] using hmem
  subst hνν
  rfl

theorem bruhatClass_surjective (hB : BruhatData Gr P Q V w) (Q' : I → Subgroup H)
    (hQ' : ∀ i, Q' i = (Q ⊓ P.map (MulAut.conj (w i)).toMonoidHom) ⊔ V) :
    Function.Surjective (bruhatClass hB Q') := by
  intro c₀
  induction c₀ using Quotient.inductionOn with
  | h z =>
  obtain ⟨i, ⟨x, hx, y, hy, hxy⟩, -⟩ := hB.unique _ (Gr.inv_mem z.2)
  -- the outer coset of `x⁻¹`
  let c : OuterCosets Q (Q' i) := Quotient.mk _ ⟨x⁻¹, Q.inv_mem hx⟩
  set γ : H := ((c.out : Q) : H) with hγ
  have hγx : γ * x ∈ Q' i := by
    have h := Quotient.mk_out (s := QuotientGroup.rightRel ((Q' i).subgroupOf Q))
      (⟨x⁻¹, Q.inv_mem hx⟩ : Q)
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h
    have h' := (Q' i).inv_mem h
    simpa [c, hγ, mul_inv_rev] using h'
  have hq' : (γ * x)⁻¹ ∈ (Q ⊓ P.map (MulAut.conj (w i)).toMonoidHom) ⊔ V := by
    rw [← hQ' i]
    exact (Q' i).inv_mem hγx
  obtain ⟨a, ha, v, hv, hav⟩ := exists_mul_of_mem_sup
    (fun a ha v hv => hB.normal a (Subgroup.mem_inf.mp ha).1 v hv) hq'
  -- the inner coset of `v`
  let ν : InnerCosets P V (w i) := Quotient.mk _ ⟨v, hv⟩
  set ρ : H := ((ν.out : V) : H) with hρ
  have hρv : ρ * v⁻¹ ∈ bruhatStabilizer P V (w i) := by
    have h := Quotient.mk_out (s := QuotientGroup.rightRel
      ((bruhatStabilizer P V (w i)).subgroupOf V)) (⟨v, hv⟩ : V)
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h
    have h' := (bruhatStabilizer P V (w i)).inv_mem h
    simpa [ν, hρ, mul_inv_rev] using h'
  refine ⟨⟨⟨i, c⟩, ν⟩, ?_⟩
  rw [bruhatClass, ambient_mk_eq_iff]
  simp only [bruhatPoint]
  rw [← hγ, ← hρ]
  have hz : (z : H) = y⁻¹ * (w i)⁻¹ * x⁻¹ := by
    rw [← inv_inv (z : H), hxy]
    group
  have hx' : x⁻¹ = (γ * x)⁻¹ * γ := by group
  have hkey : (z : H) * ((w i)⁻¹ * ρ * γ)⁻¹ =
      y⁻¹ * ((w i)⁻¹ * a * w i) * ((w i)⁻¹ * (ρ * v⁻¹)⁻¹ * w i) := by
    rw [hz, hx', hav]
    group
  rw [hkey]
  refine P.mul_mem (P.mul_mem (P.inv_mem hy) ((mem_map_conj_iff P (w i) a).mp (Subgroup.mem_inf.mp ha).2)) ?_
  exact ((mem_bruhatStabilizer_iff P V (w i) _).mp
    ((bruhatStabilizer P V (w i)).inv_mem hρv)).2

/-- The coset decomposition `P \ Gr ≃ Σ i, (Q'_i \ Q) × (Δ_i \ V)`. -/
def bruhatEquiv (hB : BruhatData Gr P Q V w) (Q' : I → Subgroup H)
    (hQ' : ∀ i, Q' i = (Q ⊓ P.map (MulAut.conj (w i)).toMonoidHom) ⊔ V) :
    BruhatIndex P Q V Q' w ≃ AmbientCosets Gr P :=
  Equiv.ofBijective (bruhatClass hB Q')
    ⟨bruhatClass_injective hB Q' hQ', bruhatClass_surjective hB Q' hQ'⟩

theorem bruhatEquiv_apply (hB : BruhatData Gr P Q V w) (Q' : I → Subgroup H)
    (hQ' : ∀ i, Q' i = (Q ⊓ P.map (MulAut.conj (w i)).toMonoidHom) ⊔ V)
    (t : BruhatIndex P Q V Q' w) : bruhatEquiv hB Q' hQ' t = bruhatClass hB Q' t := rfl

/-- The chosen representative of the class of `z ∈ Gr` differs from `z` on the left by an element
of `P`. -/
theorem exists_out_eq_mul (z : Gr) :
    ∃ π ∈ P, (((Quotient.mk _ z : AmbientCosets Gr P).out : Gr) : H) = π * z := by
  have h := Quotient.mk_out (s := QuotientGroup.rightRel (P.subgroupOf Gr)) z
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h
  refine ⟨_, P.inv_mem h, ?_⟩
  simp

/-- The chosen representative of `bruhatClass t` is `π w_i⁻¹ ν γ` with `π ∈ P`. -/
theorem exists_out_bruhatClass (hB : BruhatData Gr P Q V w) (Q' : I → Subgroup H)
    (t : BruhatIndex P Q V Q' w) :
    ∃ π ∈ P, (((bruhatClass hB Q' t).out : Gr) : H) = π * bruhatPoint Q' t :=
  exists_out_eq_mul _


section Series

variable {Gr P : Subgroup H}

/-- Right translation of `P \ Gr` by `δ ∈ Gr`. -/
def ambientRight (δ : Gr) : AmbientCosets Gr P ≃ AmbientCosets Gr P where
  toFun := Quotient.map' (fun x => x * δ) (fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    have : b * δ * (a * δ)⁻¹ = b * a⁻¹ := by group
    rw [this]
    exact h)
  invFun := Quotient.map' (fun x => x * δ⁻¹) (fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    have : b * δ⁻¹ * (a * δ⁻¹)⁻¹ = b * a⁻¹ := by group
    rw [this]
    exact h)
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h x =>
      change Quotient.mk'' (x * δ * δ⁻¹) = Quotient.mk'' x
      rw [mul_inv_cancel_right]
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h x =>
      change Quotient.mk'' (x * δ⁻¹ * δ) = Quotient.mk'' x
      rw [inv_mul_cancel_right]

theorem exists_out_ambientRight (δ : Gr) (c : AmbientCosets Gr P) :
    ∃ π ∈ P, (((ambientRight δ c).out : Gr) : H) = π * ((c.out : Gr) : H) * δ := by
  have hc : ambientRight δ c = Quotient.mk _ (c.out * δ) := by
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  obtain ⟨π, hπ, h⟩ := exists_out_eq_mul (P := P) (c.out * δ)
  refine ⟨π, hπ, ?_⟩
  rw [hc, h]
  simp [mul_assoc]

/-- A sum over `P \ Gr` of a left `P`-invariant function is invariant under left translation of
the argument by `Gr`. -/
theorem tsum_out_mul_left {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {g : H → E}
    (hg : ∀ z ∈ P, ∀ x, g (z * x) = g x) {δ : H} (hδ : δ ∈ Gr) (x : H) :
    ∑' c : AmbientCosets Gr P, g (((c.out : Gr) : H) * (δ * x)) =
      ∑' c : AmbientCosets Gr P, g (((c.out : Gr) : H) * x) := by
  conv_rhs => rw [← (ambientRight (P := P) ⟨δ, hδ⟩).tsum_eq]
  congr 1
  funext c
  obtain ⟨π, hπ, h⟩ := exists_out_ambientRight (P := P) ⟨δ, hδ⟩ c
  rw [h]
  have : π * ((c.out : Gr) : H) * ((⟨δ, hδ⟩ : Gr) : H) * x =
      π * (((c.out : Gr) : H) * (δ * x)) := by simp [mul_assoc]
  rw [this, hg π hπ]

/-- The coset decomposition of a sum over `P \ Gr` of a left `P`-invariant function. -/
theorem tsum_out_eq_tsum_bruhat {Q V : Subgroup H} {I : Type*} {w : I → H}
    (hB : BruhatData Gr P Q V w) (Q' : I → Subgroup H)
    (hQ' : ∀ i, Q' i = (Q ⊓ P.map (MulAut.conj (w i)).toMonoidHom) ⊔ V)
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {g : H → E}
    (hg : ∀ z ∈ P, ∀ x, g (z * x) = g x) (x : H) :
    ∑' c : AmbientCosets Gr P, g (((c.out : Gr) : H) * x) =
      ∑' t : BruhatIndex P Q V Q' w, g (bruhatPoint Q' t * x) := by
  rw [← (bruhatEquiv hB Q' hQ').tsum_eq]
  congr 1
  funext t
  obtain ⟨π, hπ, h⟩ := exists_out_bruhatClass hB Q' t
  rw [bruhatEquiv_apply, h, mul_assoc, hg π hπ]

end Series

end Bruhat

end Langlands.Global.EisensteinConstantTerm

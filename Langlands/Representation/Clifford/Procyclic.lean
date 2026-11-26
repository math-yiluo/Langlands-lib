import Langlands.Representation.Clifford.Extension
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Groups with procyclic quotient by a normal subgroup
-/

noncomputable section

namespace Langlands.Clifford

universe uG

section Commutator

variable {G : Type uG} [Group G] (N : Subgroup G)

/-- Every commutator lies in `N`, so `G / N` is abelian. -/
def CommutatorsIn : Prop := ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N

variable {N}

/-- Every subgroup containing `N` is normal when every commutator lies in `N`. -/
theorem normal_of_le (hab : CommutatorsIn N) {U : Subgroup G} (hU : N ≤ U) : U.Normal :=
  ⟨fun u hu g => by
    have h1 : g * u * g⁻¹ * u⁻¹ ∈ N := hab g u
    have h2 : g * u * g⁻¹ = (g * u * g⁻¹ * u⁻¹) * u := by group
    rw [h2]
    exact U.mul_mem (hU h1) hu⟩

/-- Powers are multiplicative modulo `N` when every commutator lies in `N`. -/
theorem mul_zpow_mem (hab : CommutatorsIn N) (x y : G) (n : ℤ) :
    (x * y) ^ n * (x ^ n * y ^ n)⁻¹ ∈ N := by
  have : N.Normal := normal_of_le hab le_rfl
  have hc : Commute (QuotientGroup.mk x : G ⧸ N) (QuotientGroup.mk y) := by
    change (QuotientGroup.mk (x * y) : G ⧸ N) = QuotientGroup.mk (y * x)
    rw [QuotientGroup.eq]
    have h := hab y⁻¹ x⁻¹
    simpa [mul_assoc] using h
  have h : (QuotientGroup.mk ((x * y) ^ n) : G ⧸ N) = QuotientGroup.mk (x ^ n * y ^ n) := by
    simp only [QuotientGroup.mk_zpow, QuotientGroup.mk_mul]
    exact hc.mul_zpow n
  rw [QuotientGroup.eq] at h
  have h' := N.inv_mem (this.mem_comm h)
  simpa using h'

end Commutator

section Index

variable {G : Type uG} [Group G]

/-- If every element is congruent to a power of `g` modulo a subgroup contained in the normal
subgroup `V`, then `g ^ i ∈ V` exactly when the index of `V` divides `i`. -/
theorem zpow_mem_iff_dvd {U V : Subgroup G} [V.Normal] (hUV : U ≤ V) {g : G}
    (hg : ∀ x : G, ∃ i : ℤ, x * (g ^ i)⁻¹ ∈ U) (i : ℤ) :
    g ^ i ∈ V ↔ (V.index : ℤ) ∣ i := by
  have hgen : ∀ y : G ⧸ V, y ∈ Subgroup.zpowers (QuotientGroup.mk g : G ⧸ V) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨j, hj⟩ := hg x
    refine ⟨j, ?_⟩
    change (QuotientGroup.mk g : G ⧸ V) ^ j = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    exact ‹V.Normal›.mem_comm (hUV hj)
  have hord : orderOf (QuotientGroup.mk g : G ⧸ V) = V.index :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (Subgroup.index_eq_card V).symm
  rw [← hord, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow,
    QuotientGroup.eq_one_iff]

end Index

section Tame

variable {G : Type uG} [Group G] [TopologicalSpace G] (N : Subgroup G)

/-- For every open subgroup `U` containing `N` there is one element some power of which lies in
every right coset of `U`. When `U` is normal, the class of that element generates `G / U`. -/
def CyclicOpenQuotients : Prop :=
  ∀ U : Subgroup G, N ≤ U → IsOpen (U : Set G) → ∃ g : G, ∀ x : G, ∃ i : ℤ, x * (g ^ i)⁻¹ ∈ U

/-- Characters of a subgroup `H` that are trivial on `N ∩ H` and have open kernel. -/
def tameCharacters (H : Subgroup G) : Set (H →* ℂˣ) :=
  {χ | N.subgroupOf H ≤ χ.ker ∧ IsOpen (χ.ker : Set H)}

/-- Characters of `G` that are trivial on `N` and have open kernel. -/
def tameCharactersTop : Set (G →* ℂˣ) :=
  {χ | N ≤ χ.ker ∧ IsOpen (χ.ker : Set G)}

variable {N}

/-- When every commutator lies in `N` and `CyclicOpenQuotients N` holds, inclusion of open
subgroups containing `N` is reverse divisibility of their indices. -/
theorem le_iff_index_dvd [IsTopologicalGroup G] (hab : CommutatorsIn N)
    (hcyc : CyclicOpenQuotients N) {U V : Subgroup G} (hU : N ≤ U) (hV : N ≤ V)
    (hUo : IsOpen (U : Set G)) (hVo : IsOpen (V : Set G)) :
    U ≤ V ↔ V.index ∣ U.index := by
  have : U.Normal := normal_of_le hab hU
  have : V.Normal := normal_of_le hab hV
  obtain ⟨g, hg⟩ := hcyc (U ⊓ V) (le_inf hU hV) (hUo.inter hVo)
  have hgU := zpow_mem_iff_dvd (V := U) inf_le_left hg
  have hgV := zpow_mem_iff_dvd (V := V) inf_le_right hg
  constructor
  · intro hle
    have h1 : g ^ (U.index : ℤ) ∈ U := (hgU _).mpr dvd_rfl
    exact Int.natCast_dvd_natCast.mp ((hgV _).mp (hle h1))
  · intro hdvd x hx
    obtain ⟨i, hi⟩ := hg x
    have hgi : g ^ i ∈ U := by
      have h := U.mul_mem (U.inv_mem (Subgroup.mem_inf.mp hi).1) hx
      simpa using h
    have hgi' : g ^ i ∈ V :=
      (hgV i).mpr ((Int.natCast_dvd_natCast.mpr hdvd).trans ((hgU i).mp hgi))
    have h := V.mul_mem (Subgroup.mem_inf.mp hi).2 hgi'
    simpa using h

variable (hab : CommutatorsIn N) {H : Subgroup G} (hNH : N ≤ H)

omit [TopologicalSpace G] in
include hab hNH in
theorem pow_index_mem' (x : G) : x ^ H.index ∈ H :=
  have : H.Normal := normal_of_le hab hNH
  H.pow_index_mem x

include hab hNH in
/-- For `N ≤ H` with every commutator in `N`, a character of `H` trivial on `N`, composed with
the power map `x ↦ x ^ [G : H]`. -/
def powChar (χ : H →* ℂˣ) (hχ : N.subgroupOf H ≤ χ.ker) : G →* ℂˣ where
  toFun x := χ ⟨x ^ H.index, pow_index_mem' hab hNH x⟩
  map_one' := by
    have h : (⟨(1 : G) ^ H.index, pow_index_mem' hab hNH 1⟩ : H) = 1 := by
      apply Subtype.ext
      simp
    rw [h, map_one]
  map_mul' x y := by
    have hn := mul_zpow_mem hab x y (H.index : ℤ)
    simp only [zpow_natCast] at hn
    have hsplit : (⟨(x * y) ^ H.index, pow_index_mem' hab hNH (x * y)⟩ : H) =
        ⟨_, hNH hn⟩ * ⟨x ^ H.index, pow_index_mem' hab hNH x⟩ *
          ⟨y ^ H.index, pow_index_mem' hab hNH y⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [hsplit, map_mul, map_mul, hχ (show (⟨_, hNH hn⟩ : H) ∈ N.subgroupOf H from hn), one_mul]

omit [TopologicalSpace G] in
theorem powChar_apply (χ : H →* ℂˣ) (hχ : N.subgroupOf H ≤ χ.ker) (x : G) :
    powChar hab hNH χ hχ x = χ ⟨x ^ H.index, pow_index_mem' hab hNH x⟩ := rfl

omit [TopologicalSpace G] in
/-- Power characters are compatible with automorphisms preserving `H`. -/
theorem powChar_comp_restrictAut (α : G ≃* G) (hα : ∀ x, x ∈ H ↔ α x ∈ H)
    {χ : H →* ℂˣ} (hχ : N.subgroupOf H ≤ χ.ker) (hχ' : N.subgroupOf H ≤ (χ.comp (restrictAut α hα)).ker) :
    powChar hab hNH (χ.comp (restrictAut α hα)) hχ' = (powChar hab hNH χ hχ).comp α.toMonoidHom := by
  ext1 x
  change χ (restrictAut α hα ⟨x ^ H.index, _⟩) = χ ⟨(α x) ^ H.index, _⟩
  congr 1
  apply Subtype.ext
  simp [restrictAut]

omit [TopologicalSpace G] in
theorem powChar_congr {χ χ' : H →* ℂˣ} (h : χ = χ') (hχ : N.subgroupOf H ≤ χ.ker)
    (hχ' : N.subgroupOf H ≤ χ'.ker) : powChar hab hNH χ hχ = powChar hab hNH χ' hχ' := by
  subst h
  rfl

/-- Power characters of tame characters are tame. -/
theorem powChar_mem_tameCharactersTop [IsTopologicalGroup G] {χ : H →* ℂˣ}
    (hχ : χ ∈ tameCharacters N H) : powChar hab hNH χ hχ.1 ∈ tameCharactersTop N := by
  refine ⟨fun n hn => ?_, ?_⟩
  · change χ ⟨n ^ H.index, pow_index_mem' hab hNH n⟩ = 1
    exact hχ.1 (show (⟨n ^ H.index, _⟩ : H) ∈ N.subgroupOf H from N.pow_mem hn _)
  · change IsOpen ((fun x : G => (⟨x ^ H.index, pow_index_mem' hab hNH x⟩ : H)) ⁻¹'
      (χ.ker : Set H))
    exact hχ.2.preimage ((continuous_pow H.index).subtype_mk _)

variable (hcyc : CyclicOpenQuotients N)

include hcyc in
/-- When `CyclicOpenQuotients N` holds, power characters determine tame characters of an open
subgroup `H ⊇ N`. -/
theorem powChar_injective (hHo : IsOpen (H : Set G)) {χ χ' : H →* ℂˣ}
    (hχ : χ ∈ tameCharacters N H) (hχ' : χ' ∈ tameCharacters N H)
    (h : powChar hab hNH χ hχ.1 = powChar hab hNH χ' hχ'.1) : χ = χ' := by
  have : H.Normal := normal_of_le hab hNH
  let U : Subgroup G := (χ.ker ⊓ χ'.ker).map H.subtype
  have hUH : U ≤ H := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hNU : N ≤ U := by
    intro n hn
    refine ⟨⟨n, hNH hn⟩, ⟨hχ.1 (show (⟨n, hNH hn⟩ : H) ∈ N.subgroupOf H from hn),
      hχ'.1 (show (⟨n, hNH hn⟩ : H) ∈ N.subgroupOf H from hn)⟩, rfl⟩
  have hUo : IsOpen (U : Set G) := by
    have h1 : IsOpen ((χ.ker ⊓ χ'.ker : Subgroup H) : Set H) := hχ.2.inter hχ'.2
    exact hHo.isOpenMap_subtype_val _ h1
  obtain ⟨g, hg⟩ := hcyc U hNU hUo
  ext1 x
  obtain ⟨i, hi⟩ := hg x
  have hgi : g ^ i ∈ H := by
    have h1 := H.mul_mem (H.inv_mem (hUH hi)) x.2
    simpa using h1
  obtain ⟨t, rfl⟩ := (zpow_mem_iff_dvd hUH hg i).mp hgi
  obtain ⟨u, ⟨hu, hu'⟩, hux⟩ := hi
  have hx : x = u * ⟨(g ^ t) ^ H.index, pow_index_mem' hab hNH _⟩ := by
    apply Subtype.ext
    have h1 : (u : G) = x * (g ^ ((H.index : ℤ) * t))⁻¹ := hux
    change (x : G) = (u : G) * (g ^ t) ^ H.index
    rw [h1, ← zpow_natCast, ← zpow_mul, mul_comm t]
    group
  have e1 := congrArg (fun f : G →* ℂˣ => f (g ^ t)) h
  simp only [powChar_apply] at e1
  rw [hx, map_mul, map_mul, MonoidHom.mem_ker.mp hu, MonoidHom.mem_ker.mp hu', e1]

include hcyc in
/-- Let every commutator lie in `N`, let `CyclicOpenQuotients N` hold, and let `p ≠ 1` be such that
every open subgroup containing `N` has index prime to `p` and every `d` prime to `p` is the index of
such a subgroup. Then every tame character of `G` is the power character of a tame character of an
open subgroup `H ⊇ N`. -/
theorem exists_powChar_eq [IsTopologicalGroup G] {p : ℕ} (hp : p ≠ 1)
    (hcop : ∀ U : Subgroup G, N ≤ U → IsOpen (U : Set G) → Nat.Coprime U.index p)
    (hexists : ∀ d : ℕ, Nat.Coprime d p →
      ∃ U : Subgroup G, N ≤ U ∧ IsOpen (U : Set G) ∧ U.index = d)
    (hHo : IsOpen (H : Set G)) {ψ : G →* ℂˣ} (hψ : ψ ∈ tameCharactersTop N) :
    ∃ (χ : H →* ℂˣ) (hχ : χ ∈ tameCharacters N H), powChar hab hNH χ hχ.1 = ψ := by
  classical
  have : H.Normal := normal_of_le hab hNH
  let K := ψ.ker
  have hNK : N ≤ K := hψ.1
  have hKo : IsOpen (K : Set G) := hψ.2
  have : K.Normal := normal_of_le hab hNK
  obtain ⟨U, hNU, hUo, hUi⟩ := hexists (H.index * K.index)
    (Nat.Coprime.mul_left (hcop H hNH hHo) (hcop K hNK hKo))
  have hUH : U ≤ H := (le_iff_index_dvd hab hcyc hNU hNH hUo hHo).mpr
    (hUi ▸ Dvd.intro _ rfl)
  have hUK : U ≤ K := (le_iff_index_dvd hab hcyc hNU hNK hUo hKo).mpr
    (hUi ▸ Dvd.intro_left _ rfl)
  have : U.Normal := normal_of_le hab hNU
  obtain ⟨g, hg⟩ := hcyc U hNU hUo
  have hgH := zpow_mem_iff_dvd hUH hg
  have hgK := zpow_mem_iff_dvd hUK hg
  have hgU := zpow_mem_iff_dvd (le_refl U) hg
  have he0 : H.index ≠ 0 := by
    intro h0
    have h1 := hcop H hNH hHo
    rw [h0, Nat.coprime_zero_left] at h1
    exact hp h1
  have hpowH : ∀ (h : H) (i : ℤ), (h : G) * (g ^ i)⁻¹ ∈ U → (H.index : ℤ) ∣ i := by
    intro h i hi
    apply (hgH i).mp
    have h1 := H.mul_mem (H.inv_mem (hUH hi)) h.2
    simpa using h1
  let idx : H → ℤ := fun h => Classical.choose (hg h)
  have hidx : ∀ h : H, (h : G) * (g ^ idx h)⁻¹ ∈ U := fun h => Classical.choose_spec (hg h)
  let χf : H → ℂˣ := fun h => ψ (g ^ (idx h / H.index))
  have hwd : ∀ (h : H) (i : ℤ), (h : G) * (g ^ i)⁻¹ ∈ U → χf h = ψ (g ^ (i / H.index)) := by
    intro h i hi
    have hdiff : g ^ (idx h - i) ∈ U := by
      have h1 := U.mul_mem (U.inv_mem (hidx h)) hi
      convert h1 using 1
      group
    obtain ⟨a, ha⟩ := hpowH h _ (hidx h)
    obtain ⟨b, hb⟩ := hpowH h _ hi
    have hdvd := (hgU _).mp hdiff
    rw [hUi, ha, hb, ← mul_sub, Nat.cast_mul] at hdvd
    have hdvd' : (K.index : ℤ) ∣ a - b :=
      (mul_dvd_mul_iff_left (by exact_mod_cast he0)).mp hdvd
    have hK := (hgK _).mpr hdvd'
    have he0' : (H.index : ℤ) ≠ 0 := by exact_mod_cast he0
    change ψ (g ^ (idx h / H.index)) = ψ (g ^ (i / H.index))
    rw [ha, hb, Int.mul_ediv_cancel_left _ he0', Int.mul_ediv_cancel_left _ he0',
      show a = (a - b) + b by ring, zpow_add, map_mul, MonoidHom.mem_ker.mp hK, one_mul]
  let χ : H →* ℂˣ :=
    { toFun := χf
      map_one' := by
        rw [hwd 1 0 (by simp)]
        simp
      map_mul' := fun h₁ h₂ => by
        have hmem : ((h₁ * h₂ : H) : G) * (g ^ (idx h₁ + idx h₂))⁻¹ ∈ U := by
          have h1 := U.mul_mem (hidx h₁)
            (‹U.Normal›.conj_mem _ (hidx h₂) (g ^ idx h₁))
          convert h1 using 1
          simp only [Subgroup.coe_mul]
          group
        rw [hwd _ _ hmem]
        obtain ⟨a, ha⟩ := hpowH h₁ _ (hidx h₁)
        obtain ⟨b, hb⟩ := hpowH h₂ _ (hidx h₂)
        have he0' : (H.index : ℤ) ≠ 0 := by exact_mod_cast he0
        change ψ (g ^ ((idx h₁ + idx h₂) / H.index)) =
          ψ (g ^ (idx h₁ / H.index)) * ψ (g ^ (idx h₂ / H.index))
        rw [ha, hb, ← mul_add, Int.mul_ediv_cancel_left _ he0',
          Int.mul_ediv_cancel_left _ he0', Int.mul_ediv_cancel_left _ he0', zpow_add,
          map_mul] }
  have hχU : U.subgroupOf H ≤ χ.ker := by
    intro u hu
    change χf u = 1
    rw [hwd u 0 (by simpa [Subgroup.mem_subgroupOf] using hu)]
    simp
  have hχ : χ ∈ tameCharacters N H := by
    refine ⟨fun n hn => hχU (hNU hn), ?_⟩
    apply Subgroup.isOpen_mono hχU
    exact hUo.preimage continuous_subtype_val
  refine ⟨χ, hχ, ?_⟩
  ext1 x
  obtain ⟨j, hj⟩ := hg x
  have hxe : x ^ H.index * (g ^ (j * H.index))⁻¹ ∈ U := by
    have hn := mul_zpow_mem hab (x * (g ^ j)⁻¹) (g ^ j) (H.index : ℤ)
    have h1 := U.mul_mem (hNU hn) (U.zpow_mem hj (H.index : ℤ))
    convert h1 using 1
    simp only [zpow_natCast, inv_mul_cancel_right]
    rw [zpow_mul]
    group
  rw [powChar_apply]
  change χf _ = ψ x
  rw [hwd _ _ hxe]
  have he0' : (H.index : ℤ) ≠ 0 := by exact_mod_cast he0
  rw [Int.mul_ediv_cancel _ he0']
  have hx : x = (x * (g ^ j)⁻¹) * g ^ j := by group
  conv_rhs => rw [hx]
  rw [map_mul, MonoidHom.mem_ker.mp (hUK hj), one_mul]

end Tame

end Langlands.Clifford

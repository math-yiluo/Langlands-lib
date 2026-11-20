import Langlands.BushnellKutzko.RefinementConstruction
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.RefinementChainTransport
import Langlands.BushnellKutzko.RefinementStatement

/-! # Proof of the refinement theorem (BK93 (2.2.8), printed p. 56; T6) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uE uO uK

/-! ### Critical index sets -/

section CriticalSets

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

local notation "P" => 𝓛.endFiltration

/-- A critical index is detected by any set of elements that approximates the centralizer
lattice of `γ` modulo `𝔓` in both directions. -/
theorem mem_criticalIndexSet_iff_of_approx {γ : Module.End K V} {Z : Module.End K V → Prop}
    (hZ1 : ∀ x ∈ centralizerLattice 𝓛 γ 0, ∃ y, Z y ∧ x - y ∈ P 1)
    (hZ2 : ∀ y ∈ P 0, Z y → ∃ z ∈ P 0, Commute z γ ∧ y - z ∈ P 1) (k : ℤ) :
    k ∈ criticalIndexSet 𝓛 γ ↔ ¬ ∀ x ∈ adjointLattice 𝓛 γ k, ∃ y, Z y ∧ x - y ∈ P 1 := by
  change ¬ (adjointLattice 𝓛 γ k ≤ centralizerLattice 𝓛 γ 0 ⊔ 𝓛.endFiltration 1) ↔ _
  apply not_congr
  constructor
  · intro hle x hx
    obtain ⟨q, hq, p, hp, rfl⟩ := Submodule.mem_sup.mp (hle hx)
    obtain ⟨y, hy, hqy⟩ := hZ1 q hq
    refine ⟨y, hy, ?_⟩
    have heq : q + p - y = (q - y) + p := by abel
    rw [heq]
    exact add_mem hqy hp
  · intro hall x hx
    obtain ⟨y, hy, hxy⟩ := hall x hx
    have hx0 : x ∈ P 0 := hx.1
    have hy0 : y ∈ P 0 := by
      have := sub_mem hx0 (𝓛.endFiltration_antitone (by omega) hxy)
      rwa [sub_sub_cancel] at this
    obtain ⟨z, hz0, hzγ, hyz⟩ := hZ2 y hy0 hy
    refine Submodule.mem_sup.mpr ⟨z, ⟨hz0, ?_⟩, x - z, ?_, by abel⟩
    · change γ * z - z * γ = 0
      rw [hzγ.eq, sub_self]
    · have heq : x - z = (x - y) + (y - z) := by abel
      rw [heq]
      exact add_mem hxy hyz

/-- The critical index set of `β` described through elements commuting with `β`. -/
theorem mem_criticalIndexSet_iff_commute (β : Module.End K V) (k : ℤ) :
    k ∈ criticalIndexSet 𝓛 β ↔
      ¬ ∀ x ∈ adjointLattice 𝓛 β k, ∃ y, Commute y β ∧ x - y ∈ P 1 := by
  refine mem_criticalIndexSet_iff_of_approx 𝓛 (fun x hx => ⟨x, ?_, ?_⟩)
    (fun y hy hyβ => ⟨y, hy, hyβ, by rw [sub_self]; exact zero_mem _⟩) k
  · have h := LinearMap.mem_ker.mp hx.2
    change β * x - x * β = 0 at h
    exact (sub_eq_zero.mp h).symm
  · rw [sub_self]
    exact zero_mem _

/-- Perturbing `β` by an element of `𝔓^{-r}` does not change `𝔑_k` for `k ≤ -r`. -/
theorem mem_adjointLattice_iff_of_sub_mem {β γ : Module.End K V} {r k : ℤ}
    (h : γ - β ∈ P (-r)) (hk : k ≤ -r) (x : Module.End K V) :
    x ∈ adjointLattice 𝓛 γ k ↔ x ∈ adjointLattice 𝓛 β k := by
  change x ∈ P 0 ∧ γ * x - x * γ ∈ P k ↔ x ∈ P 0 ∧ β * x - x * β ∈ P k
  refine and_congr_right fun hx => ?_
  have h1 := 𝓛.mul_mem_endFiltration h hx
  have h2 := 𝓛.mul_mem_endFiltration hx h
  rw [add_zero] at h1
  rw [zero_add] at h2
  have hd : (γ * x - x * γ) - (β * x - x * β) ∈ P k := by
    have heq : (γ * x - x * γ) - (β * x - x * β) = (γ - β) * x - x * (γ - β) := by noncomm_ring
    rw [heq]
    exact 𝓛.endFiltration_antitone hk (sub_mem h1 h2)
  constructor
  · intro hγ
    have := sub_mem hγ hd
    rwa [sub_sub_cancel] at this
  · intro hβ
    have := add_mem hd hβ
    rwa [sub_add_cancel] at this

/-- A scalar has no critical indices. -/
theorem criticalIndexSet_eq_empty_of_eq_bot {γ : Module.End K V}
    (h : Algebra.adjoin K ({γ} : Set (Module.End K V)) = ⊥) : criticalIndexSet 𝓛 γ = ∅ := by
  have hγ : γ ∈ (⊥ : Subalgebra K (Module.End K V)) := h ▸ Algebra.self_mem_adjoin_singleton K γ
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp hγ
  refine Set.eq_empty_of_forall_notMem fun k hk => hk ?_
  intro x hx
  refine Submodule.mem_sup_left ⟨hx.1, ?_⟩
  change algebraMap K (Module.End K V) a * x - x * algebraMap K (Module.End K V) a = 0
  rw [Algebra.commutes, sub_self]

/-- `𝔔^m 𝔑_k ⊆ 𝔓^m`. -/
theorem centralizerLattice_mul_adjointLattice_le (β : Module.End K V) (m k : ℤ) :
    centralizerLattice 𝓛 β m * adjointLattice 𝓛 β k ≤ P m := by
  rw [Submodule.mul_le]
  intro q hq n hn
  simpa only [add_zero] using 𝓛.mul_mem_endFiltration hq.1 hn.1

/-- The valuation of an element of exact depth `s` is `s`. -/
theorem valuation_eq_of_depth {x : Module.End K V} {s : ℤ} (hs : x ∈ P s)
    (hs1 : x ∉ P (s + 1)) : 𝓛.valuation x = (s : WithTop ℤ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hs1 (zero_mem _)
  have hset : {n : ℤ | x ∈ 𝓛.endFiltration n} = Set.Iic s := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    constructor
    · intro hn
      by_contra hlt
      push Not at hlt
      exact hs1 (𝓛.endFiltration_antitone (by omega) hn)
    · intro hn
      exact 𝓛.endFiltration_antitone hn hs
  rw [LatticeChain.valuation, if_neg hx0, hset, csSup_Iic]

end CriticalSets

theorem withBot_le_sub_one_of_lt {x : WithBot ℤ} {n : ℤ} (h : x < (n : WithBot ℤ)) :
    x ≤ ((n - 1 : ℤ) : WithBot ℤ) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    have := WithBot.coe_lt_coe.mp h
    exact WithBot.coe_le_coe.mpr (by omega)

/-! ### Exactness for the derived element, through a local-field structure on `E` -/

section Transported

variable {E : Type uE} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {V : Type uV} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {O : Type uO} [CommRing O] [Algebra O E] [Module O V] [IsScalarTower O E V]
  (𝓒 : LatticeChain O E V) (φ : O ≃+* 𝒪[E])
  (hφ : ∀ a, algebraMap 𝒪[E] E (φ a) = algebraMap O E a)
  (c : Module.End E V) (hfield : IsField (elementAlgebra c))
  (hnorm : letI := hfield.toField
    ∀ a : (elementAlgebra c)ˣ, subfieldUnits E (elementAlgebra c) V a ∈ 𝓒.stabilizer)

include φ hφ hnorm in
theorem transported_exists_commute_sub_mem {k : ℤ}
    (hk : criticalExponent 𝓒 c ≤ (k : WithBot ℤ))
    (m : ℤ) (γ : Module.End E V) (hγ : c * γ - γ * c ∈ 𝓒.endFiltration (m + k)) :
    ∃ γ₁ : Module.End E V, c * γ₁ - γ₁ * c = 0 ∧ γ - γ₁ ∈ 𝓒.endFiltration m := by
  have h : ∀ i, (𝓒.lattice i : Set V) = (𝓒.transfer φ hφ).lattice i :=
    fun i => (𝓒.transfer_lattice φ hφ i).symm
  have hnorm' : letI := hfield.toField
      ∀ a : (elementAlgebra c)ˣ,
        subfieldUnits E (elementAlgebra c) V a ∈ (𝓒.transfer φ hφ).stabilizer := by
    letI := hfield.toField
    exact fun a => (LatticeChain.mem_stabilizer_congr h).mp (hnorm a)
  rw [LatticeChain.criticalExponent_congr h c] at hk
  rw [LatticeChain.mem_endFiltration_congr h] at hγ
  obtain ⟨γ₁, h1, h2⟩ := exists_commute_sub_mem (𝓒.transfer φ hφ) c hfield hnorm' hk m γ hγ
  exact ⟨γ₁, h1, (LatticeChain.mem_endFiltration_congr h).mpr h2⟩

include φ hφ hnorm in
theorem transported_mem_criticalIndexSet_of_mem (hbot : elementAlgebra c ≠ ⊥) {r : ℤ}
    (hc : c ∈ 𝓒.endFiltration r) : r ∈ criticalIndexSet 𝓒 c := by
  have h : ∀ i, (𝓒.lattice i : Set V) = (𝓒.transfer φ hφ).lattice i :=
    fun i => (𝓒.transfer_lattice φ hφ i).symm
  have hnorm' : letI := hfield.toField
      ∀ a : (elementAlgebra c)ˣ,
        subfieldUnits E (elementAlgebra c) V a ∈ (𝓒.transfer φ hφ).stabilizer := by
    letI := hfield.toField
    exact fun a => (LatticeChain.mem_stabilizer_congr h).mp (hnorm a)
  rw [LatticeChain.criticalIndexSet_congr h c]
  rw [LatticeChain.mem_endFiltration_congr h] at hc
  exact mem_criticalIndexSet_of_mem (𝓒.transfer φ hφ) c hfield hnorm' hbot hc

include φ hφ hnorm in
theorem transported_exists_isGreatest_criticalIndexSet (hbot : elementAlgebra c ≠ ⊥) :
    ∃ k₀ : ℤ, IsGreatest (criticalIndexSet 𝓒 c) k₀ ∧
      criticalExponent 𝓒 c = (k₀ : WithBot ℤ) := by
  have h : ∀ i, (𝓒.lattice i : Set V) = (𝓒.transfer φ hφ).lattice i :=
    fun i => (𝓒.transfer_lattice φ hφ i).symm
  have hnorm' : letI := hfield.toField
      ∀ a : (elementAlgebra c)ˣ,
        subfieldUnits E (elementAlgebra c) V a ∈ (𝓒.transfer φ hφ).stabilizer := by
    letI := hfield.toField
    exact fun a => (LatticeChain.mem_stabilizer_congr h).mp (hnorm a)
  rw [LatticeChain.criticalIndexSet_congr h c, LatticeChain.criticalExponent_congr h c]
  exact exists_isGreatest_criticalIndexSet (𝓒.transfer φ hφ) c hfield hnorm' hbot

end Transported

section Derived

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
  [FiniteDimensional F V]
  (𝓒 : LatticeChain (subfieldIntegers F E) E V) (c : Module.End E V)
  (hfield : IsField (elementAlgebra c))
  (hnorm : letI := hfield.toField
    ∀ a : (elementAlgebra c)ˣ, subfieldUnits E (elementAlgebra c) V a ∈ 𝓒.stabilizer)

include hnorm in
/-- Middle exactness of the third sequence for a simple element over `E`. -/
theorem derived_exists_commute_sub_mem {k : ℤ} (hk : criticalExponent 𝓒 c ≤ (k : WithBot ℤ))
    (m : ℤ) (γ : Module.End E V) (hγ : c * γ - γ * c ∈ 𝓒.endFiltration (m + k)) :
    ∃ γ₁ : Module.End E V, c * γ₁ - γ₁ * c = 0 ∧ γ - γ₁ ∈ 𝓒.endFiltration m := by
  letI := LocalField.FiniteExtension.normedField F E
  letI := LocalField.FiniteExtension.valuativeRel F E
  haveI := LocalField.FiniteExtension.isLocalField F E
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  exact transported_exists_commute_sub_mem 𝓒 (subfieldIntegerEquiv F E) (fun _ => rfl) c hfield
    hnorm hk m γ hγ

include hnorm in
theorem derived_mem_criticalIndexSet_of_mem (hbot : elementAlgebra c ≠ ⊥) {r : ℤ}
    (hc : c ∈ 𝓒.endFiltration r) : r ∈ criticalIndexSet 𝓒 c := by
  letI := LocalField.FiniteExtension.normedField F E
  letI := LocalField.FiniteExtension.valuativeRel F E
  haveI := LocalField.FiniteExtension.isLocalField F E
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  exact transported_mem_criticalIndexSet_of_mem 𝓒 (subfieldIntegerEquiv F E) (fun _ => rfl) c
    hfield hnorm hbot hc

include hnorm in
theorem derived_exists_isGreatest_criticalIndexSet (hbot : elementAlgebra c ≠ ⊥) :
    ∃ k₀ : ℤ, IsGreatest (criticalIndexSet 𝓒 c) k₀ ∧
      criticalExponent 𝓒 c = (k₀ : WithBot ℤ) := by
  letI := LocalField.FiniteExtension.normedField F E
  letI := LocalField.FiniteExtension.valuativeRel F E
  haveI := LocalField.FiniteExtension.isLocalField F E
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  exact transported_exists_isGreatest_criticalIndexSet 𝓒 (subfieldIntegerEquiv F E)
    (fun _ => rfl) c hfield hnorm hbot

end Derived

/-! ### Restriction of scalars from `E` to `F` -/

section Restrict

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

/-- An `E`-linear map commutes with the action of `E`. -/
theorem restrictScalars_commute (Y : Module.End E V) (e : E) :
    Commute (Y.restrictScalars F) (subfieldEmbedding F E V e) := by
  change Y.restrictScalars F * subfieldEmbedding F E V e =
    subfieldEmbedding F E V e * Y.restrictScalars F
  ext v
  change Y (e • v) = e • Y v
  exact Y.map_smul e v

/-- An endomorphism commuting with a generator of `E` is `E`-linear. -/
theorem exists_restrictScalars_of_commute {β : E} (hβ : Algebra.adjoin F ({β} : Set E) = ⊤)
    {X : Module.End F V} (hX : Commute X (subfieldEmbedding F E V β)) :
    ∃ Y : Module.End E V, Y.restrictScalars F = X := by
  have hmem : X ∈ LinearMap.ker (adjointMap F (subfieldEmbedding F E V β)) := by
    rw [LinearMap.mem_ker]
    change subfieldEmbedding F E V β * X - X * subfieldEmbedding F E V β = 0
    rw [hX.eq, sub_self]
  rw [ker_adjointMap_eq_range_restrictScalars (V := V) β hβ] at hmem
  obtain ⟨Y, hY⟩ := hmem
  exact ⟨Y, hY⟩

/-- `F[β, c]` is the restriction of scalars of `E[c]`. -/
theorem exists_restrictScalars_of_mem_adjoin {β : E} {c : Module.End E V} {X : Module.End F V}
    (hX : X ∈ Algebra.adjoin F
      ({subfieldEmbedding F E V β, c.restrictScalars F} : Set (Module.End F V))) :
    ∃ Y ∈ elementAlgebra c, Y.restrictScalars F = X := by
  induction hX using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨algebraMap E (Module.End E V) β, Subalgebra.algebraMap_mem _ _, rfl⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨c, Algebra.self_mem_adjoin_singleton E c, rfl⟩
  | algebraMap a =>
    refine ⟨algebraMap E (Module.End E V) (algebraMap F E a), Subalgebra.algebraMap_mem _ _, ?_⟩
    ext v
    change (algebraMap F E a) • v = a • v
    exact algebraMap_smul E a v
  | add x x' _ _ hx hx' =>
    obtain ⟨Y, hY, rfl⟩ := hx
    obtain ⟨Y', hY', rfl⟩ := hx'
    exact ⟨Y + Y', add_mem hY hY', rfl⟩
  | mul x x' _ _ hx hx' =>
    obtain ⟨Y, hY, rfl⟩ := hx
    obtain ⟨Y', hY', rfl⟩ := hx'
    exact ⟨Y * Y', mul_mem hY hY', rfl⟩

/-- The restriction of scalars of a unit. -/
def restrictUnit (g : (Module.End E V)ˣ) : (Module.End F V)ˣ where
  val := (g : Module.End E V).restrictScalars F
  inv := ((g⁻¹ : (Module.End E V)ˣ) : Module.End E V).restrictScalars F
  val_inv := by
    ext v
    exact LinearMap.congr_fun g.mul_inv v
  inv_val := by
    ext v
    exact LinearMap.congr_fun g.inv_mul v

variable [ValuativeRel F] {O : Type uO} [CommRing O] [Algebra O E] [Module O V]
  [IsScalarTower O E V] {𝓛 : LatticeChain 𝒪[F] F V} {𝓒 : LatticeChain O E V}
  (h : ∀ i, (𝓒.lattice i : Set V) = 𝓛.lattice i)
include h

theorem mem_endFiltration_restrictScalars {x : Module.End E V} {k : ℤ} :
    x ∈ 𝓒.endFiltration k ↔ x.restrictScalars F ∈ 𝓛.endFiltration k := by
  rw [LatticeChain.mem_endFiltration, LatticeChain.mem_endFiltration]
  refine forall_congr' fun i => forall_congr' fun v => ?_
  rw [← SetLike.mem_coe, h, ← SetLike.mem_coe (x := x v), h]
  rfl

theorem restrictUnit_mem_stabilizer {g : (Module.End E V)ˣ} (hg : g ∈ 𝓒.stabilizer) :
    restrictUnit g ∈ 𝓛.stabilizer := by
  refine 𝓛.mem_stabilizer.mpr fun i => ?_
  obtain ⟨j, hj⟩ := 𝓒.mem_stabilizer.mp hg i
  refine ⟨j, SetLike.coe_injective ?_⟩
  rw [Submodule.map_coe, ← h, ← h]
  have := congrArg (fun p : Submodule O V => (p : Set V)) hj
  rw [Submodule.map_coe] at this
  exact this

end Restrict

/-! ### Subalgebras of `End_F(V)` that are fields -/

section FieldSubalgebra

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

theorem normalizingUnits_of_isField {R : Subalgebra F (Module.End F V)} (hR : IsField R)
    (hn : letI := hR.toField
      ∀ a : Rˣ, subfieldUnits F R V a ∈ 𝓛.stabilizer) : NormalizingUnits 𝓛 R := by
  letI := hR.toField
  intro X hX hX0
  have hne : (⟨X, hX⟩ : R) ≠ 0 := fun h => hX0 (congrArg Subtype.val h)
  refine ⟨subfieldUnits F R V (Units.mk0 ⟨X, hX⟩ hne), ?_, hn _⟩
  rw [coe_subfieldUnits]
  ext v
  rfl

theorem isField_of_normalizingUnits_of_comm {R : Subalgebra F (Module.End F V)}
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (h : NormalizingUnits 𝓛 R) :
    ∃ hf : IsField R,
      letI := hf.toField
      ∀ a : Rˣ, subfieldUnits F R V a ∈ 𝓛.stabilizer := by
  haveI := 𝓛.finiteDimensional
  haveI := 𝓛.nontrivial_space
  have hf : IsField R :=
    isField_of_forall_ne_zero_isUnit R hcomm
      (fun X hX hX0 => by
        obtain ⟨g, hg, -⟩ := h X hX hX0
        exact hg ▸ g.isUnit)
  refine ⟨hf, ?_⟩
  letI := hf.toField
  intro a
  have ha : ((a : R) : Module.End F V) ≠ 0 := fun h0 => a.ne_zero (Subtype.ext h0)
  obtain ⟨g, hg, hgs⟩ := h _ (a : R).2 ha
  have heq : subfieldUnits F R V a = g := by
    apply Units.ext
    rw [coe_subfieldUnits, hg]
    ext v
    rfl
  rw [heq]
  exact hgs

theorem range_subfieldEmbedding_subalgebra (R : Subalgebra F (Module.End F V)) (hR : IsField R) :
    letI := hR.toField
    Set.range (subfieldEmbedding F R V) = (R : Set (Module.End F V)) := by
  letI := hR.toField
  ext X
  constructor
  · rintro ⟨a, rfl⟩
    have : subfieldEmbedding F R V a = (a : Module.End F V) := LinearMap.ext fun v => rfl
    rw [this]
    exact a.2
  · intro hX
    exact ⟨⟨X, hX⟩, LinearMap.ext fun v => rfl⟩

end FieldSubalgebra

/-! ### The main argument -/

section Main

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  {S : Stratum 𝒪[F] F V} {b : Module.End F V} {s : TameCorestriction 𝒪[F] F E V}
  {D C : Stratum (subfieldIntegers F E) E V}

set_option maxHeartbeats 1000000 in
theorem refinement_aux (hD : S.IsDerivedStratum E b s D)
    (hCD : C.chain = D.chain) (hCr : C.r = D.r) (hDC : D.Equivalent C) (hC : C.IsSimple)
    (E₁ : Subalgebra F (Module.End F V))
    (hE₁ : E₁ = Algebra.adjoin F ({S.b, C.b.restrictScalars F} : Set (Module.End F V))) :
    ∃ T : Stratum 𝒪[F] F V,
      T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r - 1 ∧ T.IsSimple ∧
      T.coset = {x | x - (S.b + b) ∈ S.chain.endFiltration (1 - S.r)} ∧
      elementRamificationIndex F T.b = subalgebraRamificationIndex F E₁ ∧
      elementResidueDegree F T.b = subalgebraResidueDegree F E₁ ∧
      criticalExponent T.chain T.b =
        max (criticalExponent S.chain S.b) (criticalExponent C.chain C.b) := by
  obtain ⟨hS, ⟨βE, hβES, hβE⟩, hb, hDlat, -, hDr, hDb⟩ := hD
  obtain ⟨⟨hSfield, hSnorm⟩, hSval⟩ := hS.1
  have hSk := hS.2
  obtain ⟨⟨hCfield, hCnorm⟩, -⟩ := hC.1
  have hCk := hC.2
  have hlat : ∀ i, (C.chain.lattice i : Set V) = S.chain.lattice i := fun i => by
    rw [hCD]
    exact hDlat i
  have := S.chain.nontrivial_space
  -- `E` normalizes the chain
  have hSN : NormalizingUnits S.chain (elementAlgebra S.b) :=
    normalizingUnits_of_isField S.chain hSfield hSnorm
  have hℓinj : Function.Injective (subfieldEmbedding F E V) :=
    (subfieldEmbedding F E V).toRingHom.injective
  have hEmem : ∀ e : E, subfieldEmbedding F E V e ∈ elementAlgebra S.b := by
    intro e
    have h1 : subfieldEmbedding F E V e ∈
        (Algebra.adjoin F ({βE} : Set E)).map (subfieldEmbedding F E V) :=
      Subalgebra.mem_map.mpr ⟨e, by rw [hβE]; exact Algebra.mem_top, rfl⟩
    rw [AlgHom.map_adjoin_singleton, hβES] at h1
    exact h1
  have hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ S.chain.stabilizer := by
    intro a
    obtain ⟨g, hg, hgs⟩ := hSN _ (hEmem a)
      (fun h0 => a.ne_zero (hℓinj (h0.trans (map_zero _).symm)))
    have heq : subfieldUnits F E V a = g := Units.ext ((coe_subfieldUnits F E V a).trans hg.symm)
    rw [heq]
    exact hgs
  have hFE : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
  -- the field `E₁ = F[β, c]`
  have hrep : ∀ X ∈ E₁, ∃ Y ∈ elementAlgebra C.b, Y.restrictScalars F = X := by
    intro X hX
    rw [hE₁, ← hβES] at hX
    exact exists_restrictScalars_of_mem_adjoin hX
  have hE₁comm : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    intro x hx y hy
    obtain ⟨X, hX, rfl⟩ := hrep x hx
    obtain ⟨Y, hY, rfl⟩ := hrep y hy
    have hXY : X * Y = Y * X :=
      (Algebra.commute_of_mem_adjoin_singleton_of_commute hY
        (Algebra.commute_of_mem_adjoin_self hX).symm).eq
    exact congrArg (fun Z : Module.End E V => Z.restrictScalars F) hXY
  have hE₁N : NormalizingUnits S.chain E₁ := by
    intro X hX hX0
    obtain ⟨Y, hY, rfl⟩ := hrep X hX
    letI := hCfield.toField
    have hne : (⟨Y, hY⟩ : elementAlgebra C.b) ≠ 0 := fun h => hX0 (by
      rw [show Y = 0 from congrArg Subtype.val h]
      rfl)
    let u := subfieldUnits E (elementAlgebra C.b) V (Units.mk0 ⟨Y, hY⟩ hne)
    have hu : (u : Module.End E V) = Y := by
      rw [coe_subfieldUnits]
      ext v
      rfl
    refine ⟨restrictUnit u, ?_, restrictUnit_mem_stabilizer hlat (hCnorm _)⟩
    change (u : Module.End E V).restrictScalars F = Y.restrictScalars F
    rw [hu]
  obtain ⟨hE₁field, hE₁norm⟩ := isField_of_normalizingUnits_of_comm S.chain hE₁comm hE₁N
  -- the corestriction `s' = restrictScalars ∘ s`
  let s' : Module.End F V →+ Module.End F V :=
    { toFun := fun x => (s x).restrictScalars F
      map_zero' := by
        change (s.toAddMonoidHom 0).restrictScalars F = 0
        rw [map_zero]
        rfl
      map_add' := fun x y => by
        change (s.toAddMonoidHom (x + y)).restrictScalars F = _
        rw [map_add]
        rfl }
  have hs'_apply : ∀ x, s' x = (s x).restrictScalars F := fun _ => rfl
  have hT1 := (tameCorestriction F V E).2.2 s S.chain hE
  have hs_mem : ∀ (m : ℤ) (z : Module.End F V), z ∈ S.chain.endFiltration m →
      s' z ∈ S.chain.endFiltration m := by
    intro m z hz
    have h1 : s z ∈ s '' (S.chain.endFiltration m : Set (Module.End F V)) := ⟨z, hz, rfl⟩
    rw [hT1 m] at h1
    exact h1
  have hs_adj : ∀ X, s' (S.b * X - X * S.b) = 0 := by
    intro X
    have h0 := s.adjointMap_eq_zero βE X
    rw [hβES] at h0
    rw [hs'_apply, show S.b * X - X * S.b = adjointMap F S.b X from rfl, h0]
    rfl
  have hs_left : ∀ Y z, Commute Y S.b → s' (Y * z) = Y * s' z := by
    intro Y z hY
    obtain ⟨Y', rfl⟩ := exists_restrictScalars_of_commute (X := Y) hβE (by rw [hβES]; exact hY)
    have hl : s (Y'.restrictScalars F * z) = Y' * s z := s.map_mul_left Y' z
    rw [hs'_apply, hs'_apply, hl]
    rfl
  have hs_right : ∀ Y z, Commute Y S.b → s' (z * Y) = s' z * Y := by
    intro Y z hY
    obtain ⟨Y', rfl⟩ := exists_restrictScalars_of_commute (X := Y) hβE (by rw [hβES]; exact hY)
    have hr : s (z * Y'.restrictScalars F) = s z * Y' := s.map_mul_right z Y'
    rw [hs'_apply, hs'_apply, hr]
    rfl
  -- exactness inputs
  have hkβ : criticalExponent S.chain S.b ≤ ((-S.r - 1 : ℤ) : WithBot ℤ) :=
    withBot_le_sub_one_of_lt hSk
  have hkc : criticalExponent C.chain C.b ≤ ((-S.r : ℤ) : WithBot ℤ) := by
    have h1 := withBot_le_sub_one_of_lt hCk
    rwa [hCr, hDr, show -(S.r - 1) - 1 = -S.r by ring] at h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hscalar : (∃ a : F, algebraMap F E a = βE) →
      ∃ a : F, S.b = algebraMap F (Module.End F V) a := by
    rintro ⟨a, ha⟩
    exact ⟨a, by rw [← hβES, ← ha, AlgHom.commutes]⟩
  have hU1 : ∀ (t : ℤ) (X : Module.End F V), X ∈ S.chain.endFiltration t →
      S.b * X - X * S.b ∈ S.chain.endFiltration (t - S.r) →
      ∃ x ∈ S.chain.endFiltration (t + 1), Commute (X - x) S.b := by
    intro t X hX hXc
    by_cases hns : ∃ a : F, algebraMap F E a = βE
    · obtain ⟨a, ha⟩ := hscalar hns
      refine ⟨0, zero_mem _, ?_⟩
      rw [sub_zero, ha]
      exact (Algebra.commutes a X).symm
    · have h := adjointExactness F V E S.chain βE hβE hns hE
      rw [hβES] at h
      have h3 := (h.2.2.2.2 s (t + 1) (-S.r - 1) 1 hkβ le_rfl).2.2.1
      obtain ⟨-, -, -, -, -, -, -, -, -, hmid⟩ := h3
      have hy : adjointMap 𝒪[F] S.b X ∈
          (S.chain.endFiltration (t + 1 + (-S.r - 1))).toAddSubgroup := by
        rw [show t + 1 + (-S.r - 1) = t - S.r by ring]
        exact hXc
      have hs0 : (s (adjointMap 𝒪[F] S.b X)).restrictScalars F ∈
          (⊥ : Submodule 𝒪[F] (Module.End F V)).toAddSubgroup := by
        have h0 := hs_adj X
        rw [hs'_apply] at h0
        change (s (adjointMap 𝒪[F] S.b X)).restrictScalars F = 0
        exact h0
      obtain ⟨x, hx, hax⟩ := (hmid _ hy).mp hs0
      have hax' : S.b * X - X * S.b - (S.b * x - x * S.b) = 0 := hax
      refine ⟨x, centralizerLattice_mul_adjointLattice_le S.chain S.b _ _ hx, ?_⟩
      have h0 : S.b * (X - x) - (X - x) * S.b = 0 := by
        rw [← hax']
        noncomm_ring
      exact (sub_eq_zero.mp h0).symm
  have hV1 : ∀ (t : ℤ) (γ : Module.End F V), Commute γ S.b → γ ∈ S.chain.endFiltration t →
      C.b.restrictScalars F * γ - γ * C.b.restrictScalars F ∈
        S.chain.endFiltration (t + 1 - S.r) →
      ∃ γ₁, Commute γ₁ S.b ∧ Commute γ₁ (C.b.restrictScalars F) ∧
        γ - γ₁ ∈ S.chain.endFiltration (t + 1) := by
    intro t γ hγβ hγ hγc
    obtain ⟨γ', rfl⟩ := exists_restrictScalars_of_commute (X := γ) hβE (by rw [hβES]; exact hγβ)
    have hγc' : C.b * γ' - γ' * C.b ∈ C.chain.endFiltration (t + 1 + -S.r) := by
      rw [mem_endFiltration_restrictScalars hlat, show t + 1 + -S.r = t + 1 - S.r by ring]
      exact hγc
    obtain ⟨γ₁, h1, h2⟩ :=
      derived_exists_commute_sub_mem C.chain C.b hCfield hCnorm hkc (t + 1) γ' hγc'
    refine ⟨γ₁.restrictScalars F, ?_, ?_, (mem_endFiltration_restrictScalars hlat).mp h2⟩
    · rw [← hβES]
      exact restrictScalars_commute γ₁ βE
    · exact congrArg (fun Z : Module.End E V => Z.restrictScalars F) (sub_eq_zero.mp h1).symm
  have hU2 : ∀ z ∈ S.chain.endFiltration (-S.r), s' z ∈ S.chain.endFiltration (1 - S.r) →
      ∃ y ∈ S.chain.endFiltration 1,
        z - (S.b * y - y * S.b) ∈ S.chain.endFiltration (1 - S.r) := by
    intro z hz hsz
    by_cases hns : ∃ a : F, algebraMap F E a = βE
    · refine ⟨0, zero_mem _, ?_⟩
      rw [mul_zero, zero_mul, sub_zero, sub_zero]
      have h1 : s z ∈ s '' (S.chain.endFiltration (1 - S.r) : Set (Module.End F V)) := by
        rw [hT1]
        exact hsz
      obtain ⟨z', hz', hzz'⟩ := h1
      have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
      have hsurj := s.surjective_of_clearing S.chain hE hϖ0
        (fun x => S.chain.exists_uniformizer_pow_mem_endFiltration hϖ x 0)
      have hker : z' - z ∈ LinearMap.ker s.toLinearMap := by
        rw [LinearMap.mem_ker, map_sub, s.toLinearMap_apply, s.toLinearMap_apply, hzz', sub_self]
      rw [← s.range_adjointMap_eq_ker βE hβE hsurj] at hker
      obtain ⟨x, hx⟩ := hker
      obtain ⟨a, ha⟩ := hscalar hns
      have h0 : adjointMap F (subfieldEmbedding F E V βE) x = 0 := by
        rw [hβES, ha]
        change algebraMap F (Module.End F V) a * x - x * algebraMap F (Module.End F V) a = 0
        rw [Algebra.commutes, sub_self]
      rw [h0, eq_comm, sub_eq_zero] at hx
      rw [← hx]
      exact hz'
    · have h := adjointExactness F V E S.chain βE hβE hns hE
      rw [hβES] at h
      have h4 := (h.2.2.2.2 s 1 (-S.r - 1) 1 hkβ le_rfl).2.2.2
      obtain ⟨-, -, -, -, -, -, -, -, -, hmid⟩ := h4
      have hzm : z ∈ (S.chain.endFiltration (1 + (-S.r - 1))).toAddSubgroup := by
        rw [show (1 : ℤ) + (-S.r - 1) = -S.r by ring]
        exact hz
      have hsz' : (s z).restrictScalars F ∈
          (centralizerLattice S.chain S.b (1 + (-S.r - 1) + 1)).toAddSubgroup := by
        rw [show (1 : ℤ) + (-S.r - 1) + 1 = 1 - S.r by ring]
        refine ⟨hsz, ?_⟩
        change S.b * (s z).restrictScalars F - (s z).restrictScalars F * S.b = 0
        rw [← hβES, sub_eq_zero]
        exact (restrictScalars_commute (s z) βE).eq.symm
      obtain ⟨x, hx, hzx⟩ := (hmid z hzm).mp hsz'
      refine ⟨x, centralizerLattice_mul_adjointLattice_le S.chain S.b _ _ hx, ?_⟩
      have hzx' : z - (S.b * x - x * S.b) ∈ S.chain.endFiltration (1 + (-S.r - 1) + 1) := hzx
      rwa [show (1 : ℤ) + (-S.r - 1) + 1 = 1 - S.r by ring] at hzx'
  have hDbmem : D.b ∈ C.coset := by
    rw [← hDC]
    change D.b - D.b ∈ D.chain.endFiltration (-D.r)
    rw [sub_self]
    exact zero_mem _
  have hsb : s' b - C.b.restrictScalars F ∈ S.chain.endFiltration (1 - S.r) := by
    have h1 : D.b - C.b ∈ C.chain.endFiltration (-C.r) := hDbmem
    rw [hDb, hCr, hDr, show -(S.r - 1) = 1 - S.r by ring,
      mem_endFiltration_restrictScalars hlat] at h1
    exact h1
  -- generators of `E₁`
  letI := hE₁field.toField
  have hℓE₁ : ∀ a : E₁, subfieldEmbedding F E₁ V a = (a : Module.End F V) :=
    fun a => LinearMap.ext fun v => rfl
  have hβmem : S.b ∈ E₁ := by
    rw [hE₁]
    exact Algebra.subset_adjoin (Set.mem_insert _ _)
  have hcmem : C.b.restrictScalars F ∈ E₁ := by
    rw [hE₁]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hβL : ∃ a : E₁, subfieldEmbedding F E₁ V a = S.b := ⟨⟨S.b, hβmem⟩, hℓE₁ _⟩
  have hcL : ∃ a : E₁, subfieldEmbedding F E₁ V a = C.b.restrictScalars F :=
    ⟨⟨_, hcmem⟩, hℓE₁ _⟩
  have hgen : ∀ γ : Module.End F V, Commute γ S.b → Commute γ (C.b.restrictScalars F) →
      ∀ a : E₁, γ * subfieldEmbedding F E₁ V a = subfieldEmbedding F E₁ V a * γ := by
    intro γ h1 h2 a
    rw [hℓE₁]
    have key : ∀ x ∈ E₁, Commute γ x := by
      rw [hE₁]
      intro x hx
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_
      rintro y (rfl | hy)
      · exact h1
      · rw [Set.mem_singleton_iff.mp hy]
        exact h2
    exact (key _ a.2).eq
  obtain ⟨γ, hγ, hNγ, hA, hA', hX, hbot⟩ :=
    exists_refined_element S.chain hE₁norm hβL hcL hgen s' hs_mem hs_adj hs_left hs_right
      hU1 hV1 hU2 hb hsb
  -- basic properties of `γ`
  have hγβ : γ - S.b ∈ S.chain.endFiltration (-S.r) := by
    have h1 := add_mem (S.chain.endFiltration_antitone (by omega) hγ :
      γ - (S.b + b) ∈ S.chain.endFiltration (-S.r)) hb
    rwa [show γ - (S.b + b) + b = γ - S.b by abel] at h1
  have hβ0 : S.b ≠ 0 := by
    intro h0
    rw [h0, LatticeChain.valuation_zero] at hSval
    exact WithTop.top_ne_coe hSval
  obtain ⟨d, hd, hd1⟩ := exists_depth S.chain hϖ hβ0
  have hdn : d = -S.n := by
    have h1 := valuation_eq_of_depth S.chain hd hd1
    rw [hSval] at h1
    exact_mod_cast h1.symm
  have hγd : γ ∈ S.chain.endFiltration d := by
    have h1 := add_mem hd (S.chain.endFiltration_antitone
      (show d ≤ -S.r by have := S.r_lt_n; omega) hγβ)
    rwa [add_sub_cancel] at h1
  have hγd1 : γ ∉ S.chain.endFiltration (d + 1) := by
    intro h1
    apply hd1
    have h2 := sub_mem h1 (S.chain.endFiltration_antitone
      (show d + 1 ≤ -S.r by have := S.r_lt_n; omega) hγβ)
    rwa [sub_sub_cancel] at h2
  have hγval : S.chain.valuation γ = S.chain.valuation S.b := by
    rw [valuation_eq_of_depth S.chain hγd hγd1, valuation_eq_of_depth S.chain hd hd1]
  -- the core property for `γ` and its consequences for critical indices
  have hsγ : s' (γ - S.b) - C.b.restrictScalars F ∈ S.chain.endFiltration (1 - S.r) := by
    have e1 : γ - S.b = (γ - (S.b + b)) + b := by abel
    rw [e1, map_add, add_sub_assoc]
    exact add_mem (hs_mem _ _ hγ) hsb
  have hI : ∀ x ∈ adjointLattice S.chain γ (1 - S.r), ∃ y,
      (Commute y S.b ∧ Commute y (C.b.restrictScalars F)) ∧ x - y ∈ S.chain.endFiltration 1 := by
    intro x hx
    have hγeq : S.b + (γ - S.b) = γ := by abel
    have hXc : (S.b + (γ - S.b)) * x - x * (S.b + (γ - S.b)) ∈
        S.chain.endFiltration (0 + 1 - S.r) := by
      rw [hγeq, zero_add]
      exact hx.2
    obtain ⟨y, h1, h2, h3⟩ :=
      refinement_core S.chain s' hs_mem hs_adj hs_left hs_right hU1 hV1 hγβ hsγ hx.1 hXc
    exact ⟨y, ⟨h1, h2⟩, by simpa using h3⟩
  have hZ1 : ∀ x ∈ centralizerLattice S.chain γ 0, ∃ y,
      (Commute y S.b ∧ Commute y (C.b.restrictScalars F)) ∧ x - y ∈ S.chain.endFiltration 1 := by
    intro x hx
    refine hI x ⟨hx.1, ?_⟩
    change adjointMap 𝒪[F] γ x ∈ S.chain.endFiltration (1 - S.r)
    rw [LinearMap.mem_ker.mp hx.2]
    exact zero_mem _
  have hγcrit := mem_criticalIndexSet_iff_of_approx S.chain hZ1
    (fun y hy hZ => hX y hy hZ.1 hZ.2)
  have hhigh : ∀ k : ℤ, 1 - S.r ≤ k → k ∉ criticalIndexSet S.chain γ := by
    intro k hk hmem
    rw [hγcrit] at hmem
    exact hmem fun x hx => hI x ⟨hx.1, S.chain.endFiltration_antitone hk hx.2⟩
  have hlow : ∀ k : ℤ, k ≤ -S.r → (k ∈ criticalIndexSet S.chain γ ↔
      ¬ ∀ x ∈ adjointLattice S.chain S.b k, ∃ y,
        (Commute y S.b ∧ Commute y (C.b.restrictScalars F)) ∧
          x - y ∈ S.chain.endFiltration 1) := by
    intro k hk
    rw [hγcrit]
    refine not_congr (forall_congr' fun x => ?_)
    rw [mem_adjointLattice_iff_of_sub_mem S.chain hγβ hk x]
  -- `γ` normalizes, and the invariants
  obtain ⟨hγfield, hγnorm⟩ := isField_of_normalizingUnits S.chain hNγ
  have hrγ : (letI := hγfield.toField
      Set.range (subfieldEmbedding F (elementAlgebra γ) V)) =
        (elementAlgebra γ : Set (Module.End F V)) :=
    range_subfieldEmbedding_subalgebra (elementAlgebra γ) hγfield
  have hrE₁ : Set.range (subfieldEmbedding F E₁ V) = (E₁ : Set (Module.End F V)) :=
    range_subfieldEmbedding_subalgebra E₁ hE₁field
  -- the critical exponent
  have hk₀ : criticalExponent S.chain γ =
      max (criticalExponent S.chain S.b) (criticalExponent C.chain C.b) ∧
      criticalExponent S.chain γ < ((-(S.r - 1) : ℤ) : WithBot ℤ) := by
    by_cases hc : elementAlgebra C.b = ⊥
    · -- `c ∈ E`
      have hcbot : criticalExponent C.chain C.b = ⊥ := by
        rw [criticalExponent, if_pos hc]
      rw [hcbot, max_bot_right]
      have hcmem' : C.b ∈ (⊥ : Subalgebra E (Module.End E V)) :=
        hc ▸ Algebra.self_mem_adjoin_singleton E C.b
      obtain ⟨e', he'⟩ := Algebra.mem_bot.mp hcmem'
      have hcF : C.b.restrictScalars F = subfieldEmbedding F E V e' := by
        rw [← he']
        rfl
      have hZβ : ∀ y : Module.End F V, Commute y S.b → Commute y (C.b.restrictScalars F) := by
        intro y hy
        obtain ⟨y', rfl⟩ := exists_restrictScalars_of_commute (X := y) hβE (by rw [hβES]; exact hy)
        rw [hcF]
        exact restrictScalars_commute y' e'
      by_cases hns : ∃ a : F, algebraMap F E a = βE
      · -- `β ∈ F`
        obtain ⟨a, ha⟩ := hscalar hns
        have hβbot : Algebra.adjoin F ({S.b} : Set (Module.End F V)) = ⊥ := by
          rw [ha]
          exact le_bot_iff.mp (Algebra.adjoin_le
            (Set.singleton_subset_iff.mpr (Subalgebra.algebraMap_mem _ a)))
        have hEbot : ∀ e : E, ∃ a' : F, algebraMap F E a' = e := by
          intro e
          have he : e ∈ Algebra.adjoin F ({βE} : Set E) := by
            rw [hβE]
            exact Algebra.mem_top
          obtain ⟨b', hb'⟩ := hns
          rw [← hb'] at he
          have hle : Algebra.adjoin F ({algebraMap F E b'} : Set E) ≤ ⊥ :=
            Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Subalgebra.algebraMap_mem _ b'))
          exact Algebra.mem_bot.mp (hle he)
        obtain ⟨a'', ha''⟩ := hEbot e'
        have hcF' : C.b.restrictScalars F = algebraMap F (Module.End F V) a'' := by
          rw [hcF, ← ha'', AlgHom.commutes]
        have hE₁bot : E₁ = ⊥ := by
          rw [hE₁, ha, hcF']
          refine le_bot_iff.mp (Algebra.adjoin_le ?_)
          rintro x (rfl | hx)
          · exact Subalgebra.algebraMap_mem _ a
          · rw [Set.mem_singleton_iff.mp hx]
            exact Subalgebra.algebraMap_mem _ a''
        have hfin : Module.finrank F E₁ = 1 := Subalgebra.finrank_eq_one_iff.mpr hE₁bot
        have hγbot := hbot hfin
        have h1 : criticalExponent S.chain γ = ⊥ := by
          rw [criticalExponent, if_pos hγbot]
        have h2 : criticalExponent S.chain S.b = ⊥ := by
          rw [criticalExponent, if_pos hβbot]
        rw [h1, h2]
        exact ⟨rfl, WithBot.bot_lt_coe _⟩
      · -- `β ∉ F`
        have h := adjointExactness F V E S.chain βE hβE hns hE
        rw [hβES] at h
        obtain ⟨k₀, hk₀, hk₀eq⟩ := h.2.2.2.1
        have hk₀r : k₀ < -S.r := by
          have := hSk
          rw [hk₀eq] at this
          exact_mod_cast this
        have hsets : criticalIndexSet S.chain γ = criticalIndexSet S.chain S.b := by
          ext k
          by_cases hk : k ≤ -S.r
          · rw [hlow k hk, mem_criticalIndexSet_iff_commute S.chain S.b k]
            refine not_congr (forall_congr' fun x => forall_congr' fun _ => ?_)
            constructor
            · rintro ⟨y, hy, hxy⟩
              exact ⟨y, hy.1, hxy⟩
            · rintro ⟨y, hy, hxy⟩
              exact ⟨y, ⟨hy, hZβ y hy⟩, hxy⟩
          · push Not at hk
            constructor
            · intro hmem
              exact absurd hmem (hhigh k (by omega))
            · intro hmem
              have := hk₀.2 hmem
              omega
        have hγbot : Algebra.adjoin F ({γ} : Set (Module.End F V)) ≠ ⊥ := by
          intro hγb
          have hempty := criticalIndexSet_eq_empty_of_eq_bot S.chain hγb
          rw [hsets] at hempty
          rw [hempty] at hk₀
          exact hk₀.1
        have hβnb : Algebra.adjoin F ({S.b} : Set (Module.End F V)) ≠ ⊥ := by
          rw [← hβES]
          exact adjoin_subfieldEmbedding_ne_bot S.chain βE hns
        have h1 : criticalExponent S.chain γ = criticalExponent S.chain S.b := by
          rw [criticalExponent, if_neg hγbot, criticalExponent, if_neg hβnb, hsets]
        refine ⟨h1, ?_⟩
        rw [h1, hk₀eq]
        exact WithBot.coe_lt_coe.mpr (by omega)
    · -- `c ∉ E`
      have hsbQ : s b ∈ C.chain.endFiltration (-S.r) := by
        rw [mem_endFiltration_restrictScalars hlat]
        exact hs_mem _ _ hb
      have hsbcQ : s b - C.b ∈ C.chain.endFiltration (-S.r) := by
        rw [mem_endFiltration_restrictScalars hlat]
        exact S.chain.endFiltration_antitone (by omega) hsb
      have hcQ : C.b ∈ C.chain.endFiltration (-S.r) := by
        have := sub_mem hsbQ hsbcQ
        rwa [sub_sub_cancel] at this
      have hcrit_c := derived_mem_criticalIndexSet_of_mem C.chain C.b hCfield hCnorm hc hcQ
      obtain ⟨k₀, hk₀, hk₀eq⟩ :=
        derived_exists_isGreatest_criticalIndexSet C.chain C.b hCfield hCnorm hc
      have hk₀r : k₀ = -S.r := by
        have h1 := hk₀.2 hcrit_c
        have h2 := hkc
        rw [hk₀eq] at h2
        have h3 : k₀ ≤ -S.r := by exact_mod_cast h2
        omega
      have hγr : -S.r ∈ criticalIndexSet S.chain γ := by
        rw [hlow (-S.r) le_rfl]
        intro hall
        apply hcrit_c
        intro x' hx'
        have hx'0 : x' ∈ C.chain.endFiltration 0 := hx'.1
        have hx0 : x'.restrictScalars F ∈ S.chain.endFiltration 0 :=
          (mem_endFiltration_restrictScalars hlat).mp hx'0
        have hxN : x'.restrictScalars F ∈ adjointLattice S.chain S.b (-S.r) := by
          refine ⟨hx0, ?_⟩
          change S.b * x'.restrictScalars F - x'.restrictScalars F * S.b ∈
            S.chain.endFiltration (-S.r)
          rw [← hβES, (restrictScalars_commute x' βE).eq, sub_self]
          exact zero_mem _
        obtain ⟨y, ⟨hyβ, hyc⟩, hxy⟩ := hall _ hxN
        obtain ⟨y', rfl⟩ := exists_restrictScalars_of_commute (X := y) hβE (by rw [hβES]; exact hyβ)
        have hxy' : x' - y' ∈ C.chain.endFiltration 1 :=
          (mem_endFiltration_restrictScalars hlat).mpr hxy
        have hy'0 : y' ∈ C.chain.endFiltration 0 := by
          have := sub_mem hx'0 (C.chain.endFiltration_antitone (by omega) hxy')
          rwa [sub_sub_cancel] at this
        have hyc' : y' * C.b = C.b * y' := LinearMap.restrictScalars_injective F hyc
        refine Submodule.mem_sup.mpr ⟨y', ⟨hy'0, ?_⟩, x' - y', hxy', by abel⟩
        change C.b * y' - y' * C.b = 0
        rw [hyc', sub_self]
      have hgreat : IsGreatest (criticalIndexSet S.chain γ) (-S.r) := by
        refine ⟨hγr, fun k hk => ?_⟩
        by_contra hlt
        push Not at hlt
        exact hhigh k (by omega) hk
      have hγbot : Algebra.adjoin F ({γ} : Set (Module.End F V)) ≠ ⊥ := by
        intro hγb
        have hempty := criticalIndexSet_eq_empty_of_eq_bot S.chain hγb
        rw [hempty] at hγr
        exact hγr
      have h1 : criticalExponent S.chain γ = ((-S.r : ℤ) : WithBot ℤ) := by
        rw [criticalExponent, if_neg hγbot, hgreat.csSup_eq]
      rw [h1, hk₀eq, hk₀r, max_eq_right (le_of_lt hSk)]
      exact ⟨rfl, WithBot.coe_lt_coe.mpr (by omega)⟩
  refine ⟨⟨S.chain, S.n, S.r - 1, γ, by have := S.r_lt_n; omega, hγval ▸ S.valuation_ge⟩,
    rfl, rfl, rfl, ⟨⟨⟨hγfield, hγnorm⟩, ?_⟩, ?_⟩, ?_, ?_, ?_, hk₀.1⟩
  · exact hγval.trans hSval
  · exact hk₀.2
  · ext x
    change x - γ ∈ S.chain.endFiltration (-(S.r - 1)) ↔
      x - (S.b + b) ∈ S.chain.endFiltration (1 - S.r)
    rw [show -(S.r - 1) = 1 - S.r by ring]
    constructor
    · intro h
      have := add_mem h hγ
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h hγ
      rwa [sub_sub_sub_cancel_right] at this
  · change elementRamificationIndex F γ = subalgebraRamificationIndex F E₁
    unfold elementRamificationIndex subalgebraRamificationIndex
    rw [dif_pos hγfield, dif_pos hE₁field]
    letI := hγfield.toField
    exact subfieldRamificationIndex_eq_of_approx S.chain hγnorm hE₁norm
      (by rw [hrγ]; exact hA) (by rw [hrγ]; exact hA')
  · change elementResidueDegree F γ = subalgebraResidueDegree F E₁
    unfold elementResidueDegree subalgebraResidueDegree
    rw [dif_pos hγfield, dif_pos hE₁field]
    letI := hγfield.toField
    exact subfieldResidueDegree_eq_of_approx S.chain hγnorm hE₁norm
      (by rw [hrγ]; exact hA) (by rw [hrγ]; exact hA')

end Main

/-- **BK93 (2.2.8), printed p. 56 (T6).** -/
theorem refinement : RefinementStatement.{uF, uV, uE} := by
  intro F _ _ _ _ V _ _ _ E _ _ _ _ S b s D C hD _ hCD _ hCr hDC hC
  exact refinement_aux hD hCD hCr hDC hC _ rfl

end Langlands.BushnellKutzko

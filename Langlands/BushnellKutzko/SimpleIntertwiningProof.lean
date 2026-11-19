import Langlands.BushnellKutzko.SimpleIntertwiningStatement
import Langlands.BushnellKutzko.RadicalFiltrationProof
import Langlands.BushnellKutzko.RelativeLatticeChain
import Langlands.BushnellKutzko.MixedAdjointLifting

/-! # Formal intertwining of a simple stratum -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

local notation "A" => Module.End K V

private theorem adjointMap_apply (β x : A) : adjointMap O β x = β * x - x * β := rfl

private theorem adjointMap_mul (β x y : A) :
    adjointMap O β (x * y) = adjointMap O β x * y + x * adjointMap O β y := by
  simp only [adjointMap_apply]
  noncomm_ring

private theorem adjointMap_eq_zero_iff (β x : A) :
    adjointMap O β x = 0 ↔ β * x = x * β := by
  rw [adjointMap_apply, sub_eq_zero]

private theorem adjointMap_one (β : A) : adjointMap O β 1 = 0 := by
  simp [adjointMap_apply]

private theorem beta_mem_coset (S : Stratum O K V) : S.b ∈ S.coset := by
  change S.b - S.b ∈ S.chain.endFiltration (-S.r)
  simp

private theorem centralizerUnits_subset_formalSelfIntertwining (S : Stratum O K V) :
    centralizerUnits S.b ⊆ S.formalSelfIntertwining := by
  intro g hg
  refine ⟨S.b, beta_mem_coset S, ?_⟩
  change S.b * (g : A) = (g : A) * S.b at hg
  rw [mul_assoc, hg, ← mul_assoc, Units.inv_mul, one_mul]
  exact beta_mem_coset S

private theorem simpleIntertwining_of_criticalExponent_eq_bot (S : Stratum O K V)
    (h : criticalExponent S.chain S.b = ⊥) :
    S.formalSelfIntertwining = S.simpleIntertwiningNeighborhood * centralizerUnits S.b *
      S.simpleIntertwiningNeighborhood := by
  have hb : elementAlgebra S.b = ⊥ := by
    unfold criticalExponent at h
    split at h
    · assumption
    · simp at h
  have hmem : S.b ∈ elementAlgebra S.b := Algebra.subset_adjoin (Set.mem_singleton _)
  rw [hb] at hmem
  obtain ⟨c, hc⟩ := (show S.b ∈ Set.range (algebraMap K A) from hmem)
  have hB : centralizerUnits S.b = Set.univ := by
    ext g
    simp only [Set.mem_univ, iff_true]
    change S.b * (g : A) = (g : A) * S.b
    rw [← hc]
    exact Algebra.commutes c _
  have hN : S.simpleIntertwiningNeighborhood = 1 := by
    ext g
    simp [Stratum.simpleIntertwiningNeighborhood, h]
  have hI := centralizerUnits_subset_formalSelfIntertwining S
  rw [hB] at hI
  simpa [hN, hB] using (Set.eq_univ_of_univ_subset hI)

private theorem mul_adjointLattice_le (L : LatticeChain O K V) (β : A) (m k : ℤ) :
    centralizerLattice L β m * adjointLattice L β k ≤
      L.endFiltration m ⊓ (L.endFiltration (m + k)).comap (adjointMap O β) := by
  rw [Submodule.mul_le]
  intro p hp q hq
  change p ∈ L.endFiltration m ∧ adjointMap O β p = 0 at hp
  change q ∈ L.endFiltration 0 ∧ adjointMap O β q ∈ L.endFiltration k at hq
  change p * q ∈ L.endFiltration m ∧ adjointMap O β (p * q) ∈ L.endFiltration (m + k)
  refine ⟨by simpa using L.mul_mem_endFiltration hp.1 hq.1, ?_⟩
  simpa [adjointMap_mul, hp.2] using L.mul_mem_endFiltration hp.1 hq.2

private theorem coset_conjugate_mem (S : Stratum O K V) {g : Aˣ}
    (hg : g ∈ S.chain.unitFiltration 0)
    (hgb : adjointMap O S.b (g : A) ∈ S.chain.endFiltration (-S.r))
    {z : A} (hz : z ∈ S.coset) : (↑g⁻¹ : A) * z * (g : A) ∈ S.coset := by
  change z - S.b ∈ S.chain.endFiltration (-S.r) at hz
  change (↑g⁻¹ : A) * z * (g : A) - S.b ∈ S.chain.endFiltration (-S.r)
  rw [show (↑g⁻¹ : A) * z * (g : A) - S.b =
      (↑g⁻¹ : A) * (z - S.b) * (g : A) + (↑g⁻¹ : A) * adjointMap O S.b (g : A) by
    rw [adjointMap_apply, mul_sub, mul_sub, sub_mul, ← mul_assoc (↑g⁻¹ : A) (g : A),
      Units.inv_mul, one_mul, mul_assoc (↑g⁻¹ : A) S.b (g : A)]
    abel]
  have hz' : (↑g⁻¹ : A) * (z - S.b) ∈ S.chain.endFiltration (-S.r) := by
    simpa using S.chain.mul_mem_endFiltration (m := 0) hg.2.1 hz
  exact add_mem (by simpa using S.chain.mul_mem_endFiltration (n := 0) hz' hg.1)
    (by simpa using S.chain.mul_mem_endFiltration (m := 0) hg.2.1 hgb)

private theorem adjointMap_inv_mem_endFiltration (S : Stratum O K V) {g : Aˣ}
    (hg : g ∈ S.chain.unitFiltration 0)
    (hgb : adjointMap O S.b (g : A) ∈ S.chain.endFiltration (-S.r)) :
    adjointMap O S.b (↑g⁻¹ : A) ∈ S.chain.endFiltration (-S.r) := by
  have h : adjointMap O S.b (↑g⁻¹ : A) =
      -((↑g⁻¹ : A) * adjointMap O S.b (g : A) * (↑g⁻¹ : A)) := by
    simp only [adjointMap_apply, mul_sub, sub_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [← mul_assoc (↑g⁻¹ : A) (g : A), Units.inv_mul, one_mul, neg_sub]
  rw [h]
  have hg' : (↑g⁻¹ : A) * adjointMap O S.b (g : A) ∈ S.chain.endFiltration (-S.r) := by
    simpa using S.chain.mul_mem_endFiltration (m := 0) hg.2.1 hgb
  exact neg_mem (by simpa using S.chain.mul_mem_endFiltration (n := 0) hg' hg.2.1)

private theorem unitFiltration_zero_of_sub_one_mem (L : LatticeChain O K V) {d : ℤ}
    (hd : 0 < d) {g : Aˣ} (hg : (g : A) - 1 ∈ L.endFiltration d) :
    g ∈ L.unitFiltration 0 := by
  obtain ⟨u, hu, he⟩ := L.exists_mem_unitFiltration (n := d.toNat) (by omega)
    (by simpa [Int.toNat_of_nonneg hd.le] using hg)
  have hug : u = g := Units.ext (by rw [he]; abel)
  exact (L.unitFiltration_antitone (Nat.zero_le _)) (hug ▸ hu)

private theorem unitFiltration_zero_and_adjointMap_mem_of_neighborhood (S : Stratum O K V)
    {k : ℤ} (hk : criticalExponent S.chain S.b = (k : WithBot ℤ)) (hd : 0 < -(S.r + k))
    {g : Aˣ} (hg : g ∈ S.simpleIntertwiningNeighborhood) :
    g ∈ S.chain.unitFiltration 0 ∧ adjointMap O S.b (g : A) ∈ S.chain.endFiltration (-S.r) := by
  rcases hg with ⟨h, _⟩ | ⟨j, hj, hgj⟩
  · simp [hk] at h
  · have h : k = j := WithBot.coe_injective (hk.symm.trans hj)
    subst j
    have hm := mul_adjointLattice_le S.chain S.b (-(S.r + k)) k hgj
    change (g : A) - 1 ∈ S.chain.endFiltration (-(S.r + k)) ∧
      adjointMap O S.b ((g : A) - 1) ∈ S.chain.endFiltration (-(S.r + k) + k) at hm
    refine ⟨unitFiltration_zero_of_sub_one_mem S.chain hd hm.1, ?_⟩
    simpa [map_sub, adjointMap_one, show -(S.r + k) + k = -S.r by omega] using hm.2

private theorem left_mul_mem_formalSelfIntertwining (S : Stratum O K V) {u g : Aˣ}
    (hu : u ∈ S.chain.unitFiltration 0)
    (hub : adjointMap O S.b (u : A) ∈ S.chain.endFiltration (-S.r))
    (hg : g ∈ S.formalSelfIntertwining) : u * g ∈ S.formalSelfIntertwining := by
  obtain ⟨z, hz, hz'⟩ := hg
  refine ⟨(u : A) * z * (↑u⁻¹ : A), ?_, ?_⟩
  · simpa using coset_conjugate_mem S ((S.chain.unitFiltration 0).inv_mem hu)
      (adjointMap_inv_mem_endFiltration S hu hub) hz
  · simpa [mul_inv_rev, mul_assoc] using hz'

private theorem right_mul_mem_formalSelfIntertwining (S : Stratum O K V) {u g : Aˣ}
    (hu : u ∈ S.chain.unitFiltration 0)
    (hub : adjointMap O S.b (u : A) ∈ S.chain.endFiltration (-S.r))
    (hg : g ∈ S.formalSelfIntertwining) : g * u ∈ S.formalSelfIntertwining := by
  obtain ⟨z, hz, hz'⟩ := hg
  refine ⟨z, hz, ?_⟩
  simpa [mul_inv_rev, mul_assoc] using coset_conjugate_mem S hu hub hz'

private theorem doubleCoset_subset_formalSelfIntertwining (S : Stratum O K V)
    {k : ℤ} (hk : criticalExponent S.chain S.b = (k : WithBot ℤ)) (hd : 0 < -(S.r + k)) :
    S.simpleIntertwiningNeighborhood * centralizerUnits S.b * S.simpleIntertwiningNeighborhood ⊆
      S.formalSelfIntertwining := by
  intro g hg
  obtain ⟨u₁b, hx, u₂, hu₂, rfl⟩ := Set.mem_mul.mp hg
  obtain ⟨u₁, hu₁, b, hb, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨hu₁, h₁⟩ := unitFiltration_zero_and_adjointMap_mem_of_neighborhood S hk hd hu₁
  obtain ⟨hu₂, h₂⟩ := unitFiltration_zero_and_adjointMap_mem_of_neighborhood S hk hd hu₂
  exact right_mul_mem_formalSelfIntertwining S hu₂ h₂
    (left_mul_mem_formalSelfIntertwining S hu₁ h₁ (centralizerUnits_subset_formalSelfIntertwining S hb))

private abbrev shiftedAdjointLattice (S : Stratum O K V) (k m : ℤ) : Submodule O A :=
  S.chain.endFiltration m ⊓ (S.chain.endFiltration (m + k)).comap (adjointMap O S.b)

private theorem shiftedAdjointLattice_antitone (S : Stratum O K V) (k : ℤ) :
    Antitone (shiftedAdjointLattice S k) := by
  intro m n h x hx
  refine ⟨S.chain.endFiltration_antitone h hx.1, ?_⟩
  change adjointMap O S.b x ∈ S.chain.endFiltration (m + k)
  exact S.chain.endFiltration_antitone (show m + k ≤ n + k by omega) hx.2

private theorem mul_mem_shiftedAdjointLattice {S : Stratum O K V} {k m n : ℤ}
    {x y : A} (hx : x ∈ shiftedAdjointLattice S k m) (hy : y ∈ shiftedAdjointLattice S k n) :
    x * y ∈ shiftedAdjointLattice S k (m + n) := by
  refine ⟨S.chain.mul_mem_endFiltration hx.1 hy.1, ?_⟩
  change adjointMap O S.b (x * y) ∈ S.chain.endFiltration (m + n + k)
  rw [adjointMap_mul]
  have hx' := S.chain.mul_mem_endFiltration hx.2 hy.1
  rw [show m + k + n = m + n + k by ring] at hx'
  exact add_mem hx' (by simpa only [add_assoc] using S.chain.mul_mem_endFiltration hx.1 hy.2)

private theorem centralizerLattice_le_shiftedAdjointLattice (S : Stratum O K V) (k m : ℤ) :
    centralizerLattice S.chain S.b m ≤ shiftedAdjointLattice S k m := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  change adjointMap O S.b x ∈ S.chain.endFiltration (m + k)
  rw [show adjointMap O S.b x = 0 from hx.2]
  exact zero_mem _

private theorem adjointMap_mem_of_shifted_sub_one {S : Stratum O K V} {k d : ℤ}
    {g : Aˣ} (hd : d + k = -S.r)
    (hg : (g : A) - 1 ∈ shiftedAdjointLattice S k d) :
    adjointMap O S.b (g : A) ∈ S.chain.endFiltration (-S.r) := by
  have h : adjointMap O S.b ((g : A) - 1) ∈ S.chain.endFiltration (d + k) := hg.2
  simpa only [map_sub, adjointMap_one, sub_zero, hd] using h

private def intertwiningSubgroup (S : Stratum O K V) (d : ℤ) : Subgroup Aˣ where
  carrier := {g | g ∈ S.chain.unitFiltration d.toNat ∧
    adjointMap O S.b (g : A) ∈ S.chain.endFiltration (-S.r)}
  one_mem' := ⟨Subgroup.one_mem _, by simp [adjointMap_one]⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨Subgroup.mul_mem _ hg hh, ?_⟩
    rw [Units.val_mul, adjointMap_mul]
    exact add_mem (by simpa using S.chain.mul_mem_endFiltration (n := 0) hg' hh.1)
      (by simpa using S.chain.mul_mem_endFiltration (m := 0) hg.1 hh')
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    exact ⟨Subgroup.inv_mem _ hg, adjointMap_inv_mem_endFiltration S
      (S.chain.unitFiltration_antitone (Nat.zero_le _) hg) hg'⟩

private theorem mem_intertwiningSubgroup {S : Stratum O K V} {k d : ℤ}
    (hd : 0 < d) (hdk : d + k = -S.r) {g : Aˣ} :
    g ∈ intertwiningSubgroup S d ↔ (g : A) - 1 ∈ shiftedAdjointLattice S k d := by
  constructor
  · rintro ⟨hg, hg'⟩
    refine ⟨by simpa [Int.toNat_of_nonneg hd.le] using hg.2.2, ?_⟩
    change adjointMap O S.b ((g : A) - 1) ∈ S.chain.endFiltration (d + k)
    simpa only [hdk, map_sub, adjointMap_one, sub_zero] using hg'
  · intro hg
    obtain ⟨h, hh, he⟩ := S.chain.exists_mem_unitFiltration (n := d.toNat) (by omega)
      (by simpa [Int.toNat_of_nonneg hd.le] using hg.1)
    have hhg : h = g := Units.ext (by rw [he]; abel)
    exact ⟨hhg ▸ hh, adjointMap_mem_of_shifted_sub_one hdk hg⟩

private theorem mul_intertwiningSubgroup_mem_shifted {S : Stratum O K V} {k d m : ℤ}
    (hd : 0 < d) (hdk : d + k = -S.r) {x : A} (hx : x ∈ shiftedAdjointLattice S k m)
    {g : Aˣ} (hg : g ∈ intertwiningSubgroup S d) :
    x * (g : A) ∈ shiftedAdjointLattice S k m := by
  have hg' := (mem_intertwiningSubgroup (g := g) hd hdk).1 hg
  have hmul := shiftedAdjointLattice_antitone S k (show m ≤ m + d by omega)
    (mul_mem_shiftedAdjointLattice hx hg')
  simpa only [mul_sub, mul_one, sub_add_cancel] using add_mem hmul hx

private theorem exists_mem_intertwiningSubgroup_of_add {S : Stratum O K V} {k d : ℤ}
    (hd : 0 < d) (hdk : d + k = -S.r) {x : A} (hx : x ∈ shiftedAdjointLattice S k d) :
    ∃ g ∈ intertwiningSubgroup S d, (g : A) = 1 + x := by
  obtain ⟨g, hg, he⟩ := S.chain.exists_mem_unitFiltration (n := d.toNat) (by omega)
    (by simpa [Int.toNat_of_nonneg hd.le] using hx.1)
  refine ⟨g, (mem_intertwiningSubgroup (k := k) hd hdk).2 ?_, he⟩
  simpa only [he, add_sub_cancel_left] using hx

private theorem intertwiningNeighborhood_eq (S : Stratum O K V) {k d : ℤ}
    (hk : criticalExponent S.chain S.b = (k : WithBot ℤ)) (hd : 0 < d)
    (hdk : d + k = -S.r)
    (hD : centralizerLattice S.chain S.b d * adjointLattice S.chain S.b k =
      shiftedAdjointLattice S k d) :
    S.simpleIntertwiningNeighborhood = (intertwiningSubgroup S d : Set Aˣ) := by
  ext g
  rw [SetLike.mem_coe, mem_intertwiningSubgroup hd hdk]
  have hd' : -(S.r + k) = d := by omega
  constructor
  · rintro (⟨h, _⟩ | ⟨j, hj, hg⟩)
    · simp [hk] at h
    · obtain rfl : k = j := WithBot.coe_injective (hk.symm.trans hj)
      rwa [hd', hD] at hg
  · intro hg
    exact Or.inr ⟨k, hk, by rwa [hd', hD]⟩

private theorem adjointMap_eq_of_formalSelfIntertwining (S : Stratum O K V)
    {g : Aˣ} (hg : g ∈ S.formalSelfIntertwining) :
    ∃ p ∈ S.chain.endFiltration (-S.r), ∃ q ∈ S.chain.endFiltration (-S.r),
      adjointMap O S.b (g : A) = (g : A) * p + q * (g : A) := by
  obtain ⟨z, hz, hz'⟩ := hg
  change z - S.b ∈ S.chain.endFiltration (-S.r) at hz
  change (↑g⁻¹ : A) * z * (g : A) - S.b ∈ S.chain.endFiltration (-S.r) at hz'
  refine ⟨_, hz', S.b - z, by simpa only [neg_sub] using neg_mem hz, ?_⟩
  rw [adjointMap_apply, mul_sub, ← mul_assoc (g : A) ((↑g⁻¹ : A) * z) (g : A),
    ← mul_assoc (g : A) (↑g⁻¹ : A) z, Units.mul_inv, one_mul]
  noncomm_ring

private def CentralizerApproximation (S : Stratum O K V) : Prop :=
  ∀ (m : ℤ) (x : A), adjointMap O S.b x = 0 →
    ∃ γ ∈ centralizerUnits S.b, (γ : A) - x ∈ centralizerLattice S.chain S.b m

private def SingleAdjointLift (S : Stratum O K V) (k : ℤ) : Prop :=
  ∀ (m : ℤ) (x : A), adjointMap O S.b x ∈ S.chain.endFiltration (m + k) →
    ∃ z ∈ shiftedAdjointLattice S k m, adjointMap O S.b z = adjointMap O S.b x

private def MixedAdjointLift (S : Stratum O K V) (k d : ℤ) : Prop :=
  ∀ (s : ℤ) (γ : Aˣ), γ ∈ centralizerUnits S.b →
    ∀ (y : A), y ∈ shiftedAdjointLattice S k s →
    (∃ p ∈ S.chain.endFiltration (-S.r), ∃ q ∈ S.chain.endFiltration (-S.r),
      ∃ w ∈ S.chain.endFiltration (s - S.r),
        adjointMap O S.b y = (γ : A) * p + q * (γ : A) + w) →
    ∃ a ∈ shiftedAdjointLattice S k d, ∃ c ∈ shiftedAdjointLattice S k d,
      ∃ e ∈ shiftedAdjointLattice S k (s + d),
        let z := (γ : A) * a + c * (γ : A) + e
        z ∈ shiftedAdjointLattice S k s ∧ adjointMap O S.b z = adjointMap O S.b y

private theorem adjointMap_eq_zero_of_centralizerUnit {β : A} {γ : Aˣ}
    (hγ : γ ∈ centralizerUnits β) : adjointMap O β (γ : A) = 0 :=
  (adjointMap_eq_zero_iff β _).2 hγ

private theorem adjointMap_mem_of_mul_sub (S : Stratum O K V) {g : Aˣ}
    (hg : g ∈ S.formalSelfIntertwining) {t : ℤ} (hgt : (g : A) ∈ S.chain.endFiltration t) :
    adjointMap O S.b (g : A) ∈ S.chain.endFiltration (t - S.r) := by
  obtain ⟨p, hp, q, hq, h⟩ := adjointMap_eq_of_formalSelfIntertwining S hg
  rw [h, sub_eq_add_neg]
  exact add_mem (S.chain.mul_mem_endFiltration hgt hp)
    (by simpa only [add_comm] using S.chain.mul_mem_endFiltration hq hgt)

private theorem exists_centralizerUnit_approximation (S : Stratum O K V) {k d : ℤ}
    (hdk : d + k = -S.r)
    (hApprox : CentralizerApproximation S) (hLift : SingleAdjointLift S k)
    {g : Aˣ} (hg : g ∈ S.formalSelfIntertwining) {t : ℤ} (ht : (g : A) ∈ S.chain.endFiltration t) :
    ∃ γ ∈ centralizerUnits S.b, (g : A) - (γ : A) ∈ shiftedAdjointLattice S k (t + d) := by
  obtain ⟨z, hz, he⟩ := hLift (t + d) (g : A)
    (by simpa only [add_assoc, hdk, ← sub_eq_add_neg] using adjointMap_mem_of_mul_sub S hg ht)
  obtain ⟨γ, hγ, hγ'⟩ := hApprox (t + d) ((g : A) - z) (by simp [map_sub, he])
  refine ⟨γ, hγ, ?_⟩
  convert (shiftedAdjointLattice S k (t + d)).sub_mem hz
    (centralizerLattice_le_shiftedAdjointLattice S k _ hγ') using 1
  abel

private theorem exists_deeper_centralizerUnit_approximation (S : Stratum O K V) {k d : ℤ}
    (hd : 0 < d) (hdk : d + k = -S.r)
    (hApprox : CentralizerApproximation S) (hMixed : MixedAdjointLift S k d)
    {g γ : Aˣ} (hg : g ∈ S.formalSelfIntertwining) (hγ : γ ∈ centralizerUnits S.b)
    {s : ℤ} (hy : (g : A) - (γ : A) ∈ shiftedAdjointLattice S k s) :
    ∃ u ∈ intertwiningSubgroup S d, ∃ v ∈ intertwiningSubgroup S d,
      ∃ γ' ∈ centralizerUnits S.b,
        ((u * g * v : Aˣ) : A) - (γ' : A) ∈ shiftedAdjointLattice S k (s + d) := by
  let y := (g : A) - (γ : A)
  have hγa := adjointMap_eq_zero_of_centralizerUnit (O := O) hγ
  have hya : adjointMap O S.b y = adjointMap O S.b (g : A) := by simp [y, map_sub, hγa]
  obtain ⟨p, hp, q, hq, heq⟩ := adjointMap_eq_of_formalSelfIntertwining S hg
  have hw : y * p + q * y ∈ S.chain.endFiltration (s - S.r) := by
    rw [sub_eq_add_neg]
    exact add_mem (S.chain.mul_mem_endFiltration hy.1 hp)
      (by simpa only [add_comm] using S.chain.mul_mem_endFiltration hq hy.1)
  obtain ⟨a, ha, c, hc, e, he, hz, hza⟩ := hMixed s γ hγ y hy
    ⟨p, hp, q, hq, _, hw, by rw [hya, heq]; dsimp [y]; noncomm_ring⟩
  let z := (γ : A) * a + c * (γ : A) + e
  change z ∈ shiftedAdjointLattice S k s at hz
  change adjointMap O S.b z = adjointMap O S.b y at hza
  let δ := y - z
  have hδa : adjointMap O S.b δ = 0 := by simp [δ, map_sub, hza]
  have hδ : δ ∈ centralizerLattice S.chain S.b s :=
    ⟨((shiftedAdjointLattice S k s).sub_mem hy hz).1, hδa⟩
  obtain ⟨γ', hγ', hη⟩ := hApprox (s + d) ((γ : A) + δ) (by simp [map_add, hγa, hδa])
  let η := (γ' : A) - ((γ : A) + δ)
  let b := (γ' : A) - (γ : A)
  have hη' := centralizerLattice_le_shiftedAdjointLattice S k (s + d) hη
  have hb : b ∈ shiftedAdjointLattice S k s := by
    have hb' := add_mem (centralizerLattice_le_shiftedAdjointLattice S k s hδ)
      (shiftedAdjointLattice_antitone S k (show s ≤ s + d by omega) hη')
    change δ + η ∈ shiftedAdjointLattice S k s at hb'
    convert hb' using 1
    dsimp [b, η]
    abel
  have hy' : (g : A) - (γ' : A) ∈ shiftedAdjointLattice S k s := by
    convert (shiftedAdjointLattice S k s).sub_mem hy hb using 1
    dsimp [b]
    abel
  obtain ⟨u, hu, huval⟩ := exists_mem_intertwiningSubgroup_of_add hd hdk
    ((shiftedAdjointLattice S k d).neg_mem hc)
  obtain ⟨v, hv, hvval⟩ := exists_mem_intertwiningSubgroup_of_add hd hdk ha
  have hleft : (u : A) * (g : A) - (γ' : A) * (v : A) ∈
      shiftedAdjointLattice S k (s + d) := by
    have hca := mul_mem_shiftedAdjointLattice hc hb
    have hcy := mul_mem_shiftedAdjointLattice hc hy'
    rw [add_comm d s] at hca hcy
    have herr := sub_mem (sub_mem (sub_mem (sub_mem he hη') (mul_mem_shiftedAdjointLattice hb ha))
      hca) hcy
    convert herr using 1
    rw [huval, hvval]
    dsimp [b, η, δ, y, z]
    noncomm_ring
  refine ⟨u, hu, v⁻¹, (intertwiningSubgroup S d).inv_mem hv, γ', hγ', ?_⟩
  simpa only [sub_mul, mul_assoc, Units.mul_inv, mul_one, Units.val_mul] using
    mul_intertwiningSubgroup_mem_shifted hd hdk hleft ((intertwiningSubgroup S d).inv_mem hv)

private theorem mul_intertwiningSubgroup_mem_formalSelfIntertwining (S : Stratum O K V) {d : ℤ}
    {u v x : Aˣ} (hu : u ∈ intertwiningSubgroup S d) (hv : v ∈ intertwiningSubgroup S d)
    (hx : x ∈ S.formalSelfIntertwining) : u * x * v ∈ S.formalSelfIntertwining :=
  right_mul_mem_formalSelfIntertwining S (S.chain.unitFiltration_antitone (Nat.zero_le _) hv.1)
    hv.2 (left_mul_mem_formalSelfIntertwining S
      (S.chain.unitFiltration_antitone (Nat.zero_le _) hu.1) hu.2 hx)

private theorem inv_mem_endFiltration_of_doubleCoset (S : Stratum O K V) {d t : ℤ}
    {u v x : Aˣ} (hu : u ∈ intertwiningSubgroup S d) (hv : v ∈ intertwiningSubgroup S d)
    (hx : (↑x⁻¹ : A) ∈ S.chain.endFiltration t) :
    (↑((u * x * v)⁻¹) : A) ∈ S.chain.endFiltration t := by
  have hu' := (S.chain.unitFiltration_antitone (Nat.zero_le _) hu.1).2.1
  have hv' := (S.chain.unitFiltration_antitone (Nat.zero_le _) hv.1).2.1
  have h := S.chain.mul_mem_endFiltration hv' (S.chain.mul_mem_endFiltration hx hu')
  simpa only [mul_inv_rev, Units.val_mul, zero_add, add_zero] using h

private theorem exists_mem_intertwiningSubgroup_of_deep_approximation (S : Stratum O K V)
    {k d t v s : ℤ} (hd : 0 < d) (hdk : d + k = -S.r)
    {x γ : Aˣ} (hx : (↑x⁻¹ : A) ∈ S.chain.endFiltration t)
    (hβ : S.b ∈ S.chain.endFiltration v)
    (hy : (x : A) - (γ : A) ∈ shiftedAdjointLattice S k s)
    (hs : d ≤ t + s) (hs' : d + k ≤ t + s + min k v) :
    x⁻¹ * γ ∈ intertwiningSubgroup S d := by
  let y := (x : A) - (γ : A)
  have hax : adjointMap O S.b (↑x⁻¹ : A) ∈ S.chain.endFiltration (t + v) := by
    rw [adjointMap_apply]
    exact sub_mem (by simpa only [add_comm] using S.chain.mul_mem_endFiltration hβ hx)
      (S.chain.mul_mem_endFiltration hx hβ)
  apply (mem_intertwiningSubgroup hd hdk).2
  have hh : (((x⁻¹ * γ : Aˣ) : A) - 1) = (↑x⁻¹ : A) * -y := by
    simp [y, mul_sub]
  rw [hh]
  refine ⟨S.chain.endFiltration_antitone hs (S.chain.mul_mem_endFiltration hx (neg_mem hy.1)), ?_⟩
  change adjointMap O S.b ((↑x⁻¹ : A) * -y) ∈ S.chain.endFiltration (d + k)
  rw [adjointMap_mul, map_neg]
  have hlo : d + k ≤ t + v + s := by omega
  have hhi : d + k ≤ t + (s + k) := by omega
  exact add_mem (S.chain.endFiltration_antitone hlo (S.chain.mul_mem_endFiltration hax (neg_mem hy.1)))
    (S.chain.endFiltration_antitone hhi (S.chain.mul_mem_endFiltration hx (neg_mem hy.2)))

private theorem formalSelfIntertwining_subset_doubleCoset (S : Stratum O K V) {k d : ℤ}
    (hd : 0 < d) (hdk : d + k = -S.r)
    (hExhaust : ∀ x : A, ∃ t : ℤ, x ∈ S.chain.endFiltration t)
    (hApprox : CentralizerApproximation S) (hLift : SingleAdjointLift S k)
    (hMixed : MixedAdjointLift S k d) :
    S.formalSelfIntertwining ⊆ (intertwiningSubgroup S d : Set Aˣ) * centralizerUnits S.b *
      (intertwiningSubgroup S d : Set Aˣ) := by
  intro x hx
  obtain ⟨t₀, ht₀⟩ := hExhaust (x : A)
  obtain ⟨t, ht⟩ := hExhaust (↑x⁻¹ : A)
  obtain ⟨v, hv⟩ := hExhaust S.b
  let H := intertwiningSubgroup S d
  have hIter (j : ℕ) : ∃ l ∈ H, ∃ r ∈ H, ∃ γ ∈ centralizerUnits S.b,
      ((l * x * r : Aˣ) : A) - (γ : A) ∈ shiftedAdjointLattice S k (t₀ + d + j) := by
    induction j with
    | zero =>
      obtain ⟨γ, hγ, h⟩ := exists_centralizerUnit_approximation S hdk hApprox hLift hx ht₀
      exact ⟨1, H.one_mem, 1, H.one_mem, γ, hγ, by simpa using h⟩
    | succ j ih =>
      obtain ⟨l, hl, r, hr, γ, hγ, h⟩ := ih
      obtain ⟨l', hl', r', hr', γ', hγ', h'⟩ := exists_deeper_centralizerUnit_approximation S
        hd hdk hApprox hMixed (mul_intertwiningSubgroup_mem_formalSelfIntertwining S hl hr hx) hγ h
      refine ⟨l' * l, H.mul_mem hl' hl, r * r', H.mul_mem hr hr', γ', hγ', ?_⟩
      have hstep : t₀ + d + ((j + 1 : ℕ) : ℤ) ≤ t₀ + d + (j : ℤ) + d := by omega
      simpa only [mul_assoc] using shiftedAdjointLattice_antitone S k hstep h'
  let j := (max (d - t) (d + k - t - min k v) - (t₀ + d)).toNat
  obtain ⟨l, hl, r, hr, γ, hγ, hy⟩ := hIter j
  have hInv := inv_mem_endFiltration_of_doubleCoset S hl hr ht
  have h := exists_mem_intertwiningSubgroup_of_deep_approximation S hd hdk hInv hv hy
    (by dsimp [j]; omega) (by dsimp [j]; omega)
  let r' := (l * x * r)⁻¹ * γ
  have hr' : r' ∈ H := h
  refine Set.mem_mul.mpr ⟨l⁻¹ * γ, Set.mem_mul.mpr ⟨l⁻¹, H.inv_mem hl, γ, hγ, rfl⟩,
    r'⁻¹ * r⁻¹, H.mul_mem (H.inv_mem hr') (H.inv_mem hr), ?_⟩
  simp [r', mul_inv_rev, mul_assoc]

private theorem mem_mul_centralizerLattice_span_singleton (S : Stratum O K V)
    (hQ : ∀ m : ℤ, (1 : A) ∈ centralizerLattice S.chain S.b m * centralizerLattice S.chain S.b (-m))
    (m : ℤ) (x : A) :
    x ∈ centralizerLattice S.chain S.b m *
      (centralizerLattice S.chain S.b (-m) * Submodule.span O {x}) := by
  rw [← mul_assoc]
  exact Submodule.mem_mul_span_singleton.mpr ⟨1, hQ m, one_mul x⟩

private theorem centralizerLattice_mul_adjointLattice_eq (S : Stratum O K V)
    (hQ : ∀ m : ℤ, (1 : A) ∈ centralizerLattice S.chain S.b m * centralizerLattice S.chain S.b (-m))
    (m k : ℤ) :
    centralizerLattice S.chain S.b m * adjointLattice S.chain S.b k = shiftedAdjointLattice S k m := by
  refine le_antisymm (mul_adjointLattice_le S.chain S.b m k) ?_
  intro x hx
  have h : centralizerLattice S.chain S.b (-m) * Submodule.span O {x} ≤ adjointLattice S.chain S.b k := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_mul_span_singleton.mp hy
    change p ∈ S.chain.endFiltration (-m) ∧ adjointMap O S.b p = 0 at hp
    refine ⟨by simpa using S.chain.mul_mem_endFiltration hp.1 hx.1, ?_⟩
    change adjointMap O S.b (p * x) ∈ S.chain.endFiltration k
    simpa [adjointMap_mul, hp.2] using S.chain.mul_mem_endFiltration hp.1 hx.2
  exact mul_le_mul' le_rfl h (mem_mul_centralizerLattice_span_singleton S hQ m x)

private theorem exists_add_centralizerLattice_of_large_adjoint (S : Stratum O K V)
    (hQ : ∀ m : ℤ, (1 : A) ∈ centralizerLattice S.chain S.b m * centralizerLattice S.chain S.b (-m))
    {k t : ℤ} (hk : adjointLattice S.chain S.b (k + 1) ≤
      centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1)
    {x : A} (hx : x ∈ S.chain.endFiltration t)
    (hax : adjointMap O S.b x ∈ S.chain.endFiltration (t + (k + 1))) :
    x ∈ centralizerLattice S.chain S.b t ⊔ S.chain.endFiltration (t + 1) := by
  let Q := centralizerLattice S.chain S.b
  have h : Q (-t) * Submodule.span O {x} ≤ Q 0 ⊔ S.chain.endFiltration 1 := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_mul_span_singleton.mp hy
    change p ∈ S.chain.endFiltration (-t) ∧ adjointMap O S.b p = 0 at hp
    apply hk
    refine ⟨by simpa using S.chain.mul_mem_endFiltration hp.1 hx, ?_⟩
    change adjointMap O S.b (p * x) ∈ S.chain.endFiltration (k + 1)
    simpa [adjointMap_mul, hp.2] using S.chain.mul_mem_endFiltration hp.1 hax
  have hmul : Q t * (Q 0 ⊔ S.chain.endFiltration 1) ≤ Q t ⊔ S.chain.endFiltration (t + 1) := by
    rw [Submodule.mul_sup]
    refine sup_le (le_sup_of_le_left ?_) (le_sup_of_le_right ?_)
    · rw [Submodule.mul_le]
      intro x hx y hy
      change x ∈ S.chain.endFiltration t ∧ adjointMap O S.b x = 0 at hx
      change y ∈ S.chain.endFiltration 0 ∧ adjointMap O S.b y = 0 at hy
      refine ⟨by simpa using S.chain.mul_mem_endFiltration hx.1 hy.1, ?_⟩
      change adjointMap O S.b (x * y) = 0
      simp [adjointMap_mul, hx.2, hy.2]
    · rw [Submodule.mul_le]
      exact fun x hx y hy => S.chain.mul_mem_endFiltration hx.1 hy
  exact hmul (mul_le_mul' le_rfl h (mem_mul_centralizerLattice_span_singleton S hQ t x))

private theorem adjointLattice_le_of_criticalExponent_eq (S : Stratum O K V) {k : ℤ}
    (hk : criticalExponent S.chain S.b = (k : WithBot ℤ))
    (hBound : BddAbove (criticalIndexSet S.chain S.b)) :
    adjointLattice S.chain S.b (k + 1) ≤ centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1 := by
  have hk' : sSup (criticalIndexSet S.chain S.b) = k := by
    unfold criticalExponent at hk
    split at hk
    · simp at hk
    · exact WithBot.coe_injective hk
  by_contra hn
  have h := le_csSup hBound (show k + 1 ∈ criticalIndexSet S.chain S.b from hn)
  omega

private theorem singleAdjointLift_of_criticalExponent_eq (S : Stratum O K V)
    (hQ : ∀ m : ℤ, (1 : A) ∈ centralizerLattice S.chain S.b m * centralizerLattice S.chain S.b (-m))
    (hExhaust : ∀ x : A, ∃ t : ℤ, x ∈ S.chain.endFiltration t)
    {k : ℤ} (hk : criticalExponent S.chain S.b = (k : WithBot ℤ))
    (hBound : BddAbove (criticalIndexSet S.chain S.b)) : SingleAdjointLift S k := by
  intro m x hax
  have hstep := adjointLattice_le_of_criticalExponent_eq S hk hBound
  have hLift (j : ℕ) (t : ℤ) (q : A) (hq : q ∈ S.chain.endFiltration t)
      (haq : adjointMap O S.b q ∈ S.chain.endFiltration (t + (j : ℤ) + k)) :
      ∃ z ∈ shiftedAdjointLattice S k (t + (j : ℤ)),
        adjointMap O S.b z = adjointMap O S.b q := by
    induction j generalizing t q with
    | zero =>
      exact ⟨q, by simpa using (show q ∈ shiftedAdjointLattice S k t from
        ⟨hq, by simpa using haq⟩), rfl⟩
    | succ j ih =>
      have hadd := exists_add_centralizerLattice_of_large_adjoint S hQ hstep hq
        (S.chain.endFiltration_antitone (show t + (k + 1) ≤ t + (j + 1 : ℕ) + k by omega) haq)
      obtain ⟨c, hc, q', hq', rfl⟩ := Submodule.mem_sup.mp hadd
      have hca : adjointMap O S.b c = 0 := hc.2
      rw [map_add, hca, zero_add] at haq ⊢
      have h : t + (↑(j + 1) : ℤ) = (t + 1) + (j : ℤ) := by omega
      rw [h] at haq ⊢
      exact ih _ _ hq' haq
  obtain ⟨t, ht⟩ := hExhaust x
  by_cases hmt : m ≤ t
  · exact ⟨x, ⟨S.chain.endFiltration_antitone hmt ht, hax⟩, rfl⟩
  have h : t + ((m - t).toNat : ℤ) = m := by omega
  have hh := hLift (m - t).toNat t x ht (by rwa [h])
  rwa [h] at hh

private theorem commutes_with_elementAlgebra {β x : A} (hx : adjointMap O β x = 0)
    (a : elementAlgebra β) : (a : A) * x = x * (a : A) := by
  refine Algebra.adjoin_induction (p := fun z _ => z * x = x * z) ?_ ?_ ?_ ?_ a.prop
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (adjointMap_eq_zero_iff β x).mp hx
  · exact fun r => Algebra.commutes r x
  · intro a b _ _ ha hb
    rw [add_mul, mul_add, ha, hb]
  · intro a b _ _ ha hb
    rw [mul_assoc, hb, ← mul_assoc a, ha, mul_assoc]

section LocalField

variable {F : Type uK} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {W : Type uV} [AddCommGroup W] [Module F W]
  [FiniteDimensional F W]

local notation "EndF" => Module.End F W

omit [FiniteDimensional F W] in
private theorem endFiltration_exhaustive (L : LatticeChain 𝒪[F] F W) (x : EndF) :
    ∃ t : ℤ, x ∈ L.endFiltration t := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ zero_mem _⟩
  · exact ((radicalFiltration F W L).2.2.2.2 x hx).1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] in
private theorem one_mem_centralizerLattice_mul_opposite (S : Stratum 𝒪[F] F W)
    {E : Type*} [Field E] [Algebra F E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Module E W] [IsScalarTower F E W]
    (C : LatticeChain 𝒪[E] E W) (hC : ∀ i v, v ∈ C.lattice i ↔ v ∈ S.chain.lattice i)
    (a : E) (ha : subfieldEmbedding F E W a = S.b) (m : ℤ) :
    (1 : EndF) ∈ centralizerLattice S.chain S.b m * centralizerLattice S.chain S.b (-m) := by
  have hmem : (1 : Module.End E W) ∈ C.endFiltration m * C.endFiltration (-m) := by
    rw [(radicalFiltration E W C).1, add_neg_cancel]
    exact C.mem_order_iff_mem_endFiltration.mp (one_mem C.order)
  have hrestrict {n : ℤ} {x : Module.End E W} (hx : x ∈ C.endFiltration n) :
      x.restrictScalars F ∈ centralizerLattice S.chain S.b n := by
    refine ⟨fun i v hv => (hC _ _).mp (hx i v ((hC _ _).mpr hv)), ?_⟩
    apply (adjointMap_eq_zero_iff S.b _).mpr
    rw [← ha]
    ext v
    exact (x.map_smul a v).symm
  change (1 : Module.End E W).restrictScalars F ∈
    centralizerLattice S.chain S.b m * centralizerLattice S.chain S.b (-m)
  refine Submodule.mul_induction_on hmem (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · exact Submodule.mul_mem_mul (hrestrict hx) (hrestrict hy)
  · exact add_mem hx hy

omit [FiniteDimensional F W] in
private theorem endFiltration_zero_fg (L : LatticeChain 𝒪[F] F W) : (L.endFiltration 0).FG := by
  let M := L.lattice 0
  have : M.IsLattice F := L.isLattice 0
  let f : L.endFiltration 0 →ₗ[𝒪[F]] Module.End 𝒪[F] M :=
    { toFun := fun x => (x.val.restrictScalars 𝒪[F]).restrict fun v hv => by
        simpa using x.prop 0 v hv
      map_add' := fun x y => by ext v; rfl
      map_smul' := fun c x => by ext v; rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply LinearMap.ext_on (L.isLattice 0).span_eq_top
    intro v hv
    exact congrArg (fun g : Module.End 𝒪[F] M => (g ⟨v, hv⟩ : W)) h
  exact Module.Finite.iff_fg.mp (Module.Finite.of_injective f hf)

omit [FiniteDimensional F W] in
private theorem exists_endFiltration_mapsTo_one (L : LatticeChain 𝒪[F] F W)
    (f : EndF →ₗ[F] EndF) :
    ∃ n : ℤ, Set.MapsTo f (L.endFiltration n) (L.endFiltration 1) := by
  classical
  obtain ⟨s, hs⟩ := endFiltration_zero_fg L
  choose depth hdepth using fun x => endFiltration_exhaustive L (f x)
  obtain ⟨t, ht⟩ := (s.finite_toSet.image depth).bddBelow
  have hbase : Set.MapsTo f (L.endFiltration 0) (L.endFiltration t) := by
    have hspan : Submodule.span 𝒪[F] (s : Set EndF) ≤
        (L.endFiltration t).comap (f.restrictScalars 𝒪[F]) := by
      refine Submodule.span_le.mpr fun x hx => ?_
      exact L.endFiltration_antitone (ht ⟨x, hx, rfl⟩) (hdepth x)
    exact fun x hx => hspan (hs ▸ hx)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hπ0 : (π : F) ≠ 0 := coe_uniformizer_ne_zero hπ
  have hshift (j : ℕ) : Set.MapsTo f
      (L.endFiltration ((j : ℤ) * L.period)) (L.endFiltration (t + j * L.period)) := by
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      intro x hx
      change x ∈ L.endFiltration ((↑(j + 1) : ℤ) * L.period) at hx
      change f x ∈ L.endFiltration (t + (↑(j + 1) : ℤ) * L.period)
      let y := (π : F)⁻¹ • x
      have hxy : (π : F) • y = x := by simp [y, smul_smul, hπ0]
      have hy : y ∈ L.endFiltration ((j : ℤ) * L.period) :=
        (L.uniformizer_smul_mem_endFiltration_iff hπ y _).mp (by
          simpa only [hxy, Nat.cast_succ, add_mul, one_mul] using hx)
      have hfy := (L.uniformizer_smul_mem_endFiltration_iff hπ (f y) _).mpr (ih hy)
      simpa only [← f.map_smul, hxy, Nat.cast_succ, add_mul, one_mul, ← add_assoc] using hfy
  let j := (1 - t).toNat
  refine ⟨(j : ℤ) * L.period, fun x hx => L.endFiltration_antitone ?_ (hshift j hx)⟩
  have hper : (1 : ℤ) ≤ L.period := by exact_mod_cast L.period_pos
  have hmul : (j : ℤ) * 1 ≤ (j : ℤ) * L.period := mul_le_mul_of_nonneg_left hper (by positivity)
  dsimp [j] at hmul ⊢
  omega

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] in
private theorem exists_adjoint_section (b : EndF) :
    ∃ f : EndF →ₗ[F] EndF, ∀ x, adjointMap F b (f (adjointMap F b x)) = adjointMap F b x := by
  let a := adjointMap F b
  obtain ⟨g, hg⟩ := a.range.subtype.exists_leftInverse_of_injective a.range.ker_subtype
  obtain ⟨r, hr⟩ := a.rangeRestrict.exists_rightInverse_of_surjective a.range_rangeRestrict
  refine ⟨r.comp g, fun x => ?_⟩
  have h₁ : g (a x) = a.rangeRestrict x := LinearMap.congr_fun hg (a.rangeRestrict x)
  have h₂ : a (r (a.rangeRestrict x)) = a x :=
    congrArg Subtype.val (LinearMap.congr_fun hr (a.rangeRestrict x))
  change a (r (g (a x))) = a x
  rwa [h₁]

omit [FiniteDimensional F W] in
private theorem bddAbove_criticalIndexSet (S : Stratum 𝒪[F] F W) :
    BddAbove (criticalIndexSet S.chain S.b) := by
  obtain ⟨f, hf⟩ := exists_adjoint_section S.b
  obtain ⟨n, hn⟩ := exists_endFiltration_mapsTo_one S.chain f
  have hle : adjointLattice S.chain S.b n ≤ centralizerLattice S.chain S.b 0 ⊔
      S.chain.endFiltration 1 := by
    intro x hx
    obtain ⟨hx₀, hx₁⟩ : x ∈ S.chain.endFiltration 0 ∧
        adjointMap F S.b x ∈ S.chain.endFiltration n := hx
    have hy := hn hx₁
    have hy₀ := S.chain.endFiltration_antitone (show (0 : ℤ) ≤ 1 by omega) hy
    refine Submodule.mem_sup.mpr ⟨x - f (adjointMap F S.b x), ⟨sub_mem hx₀ hy₀, ?_⟩,
      _, hy, sub_add_cancel _ _⟩
    change adjointMap F S.b (x - f (adjointMap F S.b x)) = 0
    rw [map_sub, hf, sub_self]
  refine ⟨n, fun m hm => ?_⟩
  by_contra hmn
  apply hm
  intro x hx
  exact hle ⟨hx.1, S.chain.endFiltration_antitone (le_of_not_ge hmn) hx.2⟩

private theorem centralizerApproximation (S : Stratum 𝒪[F] F W) : CentralizerApproximation S := by
  intro m x hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let q : F := π
  have hπ0 : q ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hp : algebraMap F (Module.End F W) q ∈ S.chain.endFiltration 1 := by
    apply S.chain.endFiltration_antitone (show (1 : ℤ) ≤ S.chain.period by
      exact_mod_cast S.chain.period_pos)
    intro i v hv
    rw [S.chain.lattice_add_period, jacobson_integer_eq_maximalIdeal, hπ.maximalIdeal_eq,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨v, hv, rfl⟩
  have hPow (j : ℕ) : algebraMap F (Module.End F W) (q ^ j) ∈ S.chain.endFiltration j := by
    induction j with
    | zero => simpa using S.chain.mem_order_iff_mem_endFiltration.mp (one_mem S.chain.order)
    | succ j ih =>
      simpa only [Nat.cast_succ, pow_succ, map_mul] using S.chain.mul_mem_endFiltration ih hp
  have hinj : Function.Injective (fun j : ℕ => q ^ j) := by
    suffices hn : ∀ j l : ℕ, j ≤ l → q ^ j = q ^ l → j = l by
      intro j l heq
      rcases le_total j l with h | h
      · exact hn j l h heq
      · exact (hn l j h heq.symm).symm
    intro j l h heq
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h
    have he : 1 = q ^ a := mul_left_cancel₀ (pow_ne_zero _ hπ0) (by rwa [mul_one, ← pow_add])
    by_contra hne
    have ha0 : a ≠ 0 := by omega
    have hunit : IsUnit (π ^ a) := by
      have hpa : π ^ a = 1 := Subtype.ext (by simpa [q] using he.symm)
      rw [hpa]
      exact isUnit_one
    exact hπ.not_isUnit ((isUnit_pow_iff ha0).mp hunit)
  have hinf : (Set.range (fun j : ℕ => q ^ (m.toNat + j))).Infinite :=
    Set.infinite_range_of_injective (hinj.comp (fun _ _ h => Nat.add_left_cancel h))
  have hfinite := Polynomial.finite_setOfPred_isRoot (LinearMap.charpoly_monic (-x)).ne_zero
  obtain ⟨c, ⟨j, rfl⟩, hc⟩ := hinf.exists_notMem_finite hfinite
  let z : Module.End F W := algebraMap F (Module.End F W) (q ^ (m.toNat + j))
  have hdet : (z + x).det ≠ 0 := by
    change (-x).charpoly.eval (q ^ (m.toNat + j)) ≠ 0 at hc
    simpa only [LinearMap.eval_charpoly, sub_neg_eq_add, z] using hc
  have hunit : IsUnit (z + x) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hz : z ∈ centralizerLattice S.chain S.b m := by
    refine ⟨S.chain.endFiltration_antitone (show m ≤ ((m.toNat + j : ℕ) : ℤ) by omega)
      (hPow (m.toNat + j)), ?_⟩
    change adjointMap 𝒪[F] S.b z = 0
    rw [adjointMap_apply, (Algebra.commutes (q ^ (m.toNat + j)) S.b).symm, sub_self]
  refine ⟨hunit.unit, ?_, ?_⟩
  · apply (adjointMap_eq_zero_iff (O := 𝒪[F]) S.b _).mp
    rw [hunit.unit_spec, map_add, (show adjointMap 𝒪[F] S.b z = 0 from hz.2), hx, zero_add]
  · simpa only [hunit.unit_spec, add_sub_cancel_right] using hz

private theorem simpleIntertwining_of_criticalExponent_eq (S : Stratum 𝒪[F] F W)
    (hS : S.IsSimple) {k : ℤ} (hk : criticalExponent S.chain S.b = (k : WithBot ℤ)) :
    S.formalSelfIntertwining = S.simpleIntertwiningNeighborhood * centralizerUnits S.b *
      S.simpleIntertwiningNeighborhood := by
  have hkr : k < -S.r := WithBot.coe_lt_coe.mp (hk ▸ hS.2)
  let d := -(S.r + k)
  have hd : 0 < d := by dsimp [d]; omega
  have hdk : d + k = -S.r := by dsimp [d]; omega
  obtain ⟨hField, hE⟩ := hS.1.1
  let E := elementAlgebra S.b
  let : Field E := hField.toField
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra S.b))
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  have hE' : ∀ a : Eˣ, subfieldUnits F E W a ∈ S.chain.stabilizer := hE
  have hInt : ∀ a : E, IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[E] := isIntegral_iff_mem_spectralInteger F E
  let C := S.chain.relativeLatticeChain hE' hInt
  have hC : ∀ i v, v ∈ C.lattice i ↔ v ∈ S.chain.lattice i :=
    S.chain.mem_relativeLatticeChain hE' hInt
  let β : E := ⟨S.b, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  have hβ : subfieldEmbedding F E W β = S.b := rfl
  have hker {x : EndF} (hx : adjointMap 𝒪[F] S.b x = 0) (a : E) (v : W) :
      x (a • v) = a • x v :=
    (LinearMap.congr_fun (commutes_with_elementAlgebra hx a) v).symm
  have hQ := one_mem_centralizerLattice_mul_opposite S C hC β hβ
  have hLift := singleAdjointLift_of_criticalExponent_eq S hQ
    (endFiltration_exhaustive S.chain) hk (bddAbove_criticalIndexSet S)
  have hMixed : MixedAdjointLift S k d := by
    intro s γ hγ y hy hsum
    obtain ⟨p, hp, q, hq, w, hw, hsum⟩ := hsum
    let g : W ≃ₗ[E] W :=
      { toFun := fun v => (γ : EndF) v
        invFun := fun v => (↑γ⁻¹ : EndF) v
        left_inv := fun v => LinearMap.congr_fun (Units.inv_mul γ) v
        right_inv := fun v => LinearMap.congr_fun (Units.mul_inv γ) v
        map_add' := map_add (γ : EndF)
        map_smul' := hker (adjointMap_eq_zero_of_centralizerUnit hγ) }
    have hg : g.toLinearMap.restrictScalars F = (γ : EndF) := rfl
    have hLift' (m : ℤ) (x : EndF)
        (hx : adjointMap 𝒪[F] (subfieldEmbedding F E W β) x ∈ S.chain.endFiltration (m + k)) :
        ∃ z ∈ S.chain.endFiltration m,
          adjointMap 𝒪[F] (subfieldEmbedding F E W β) z =
            adjointMap 𝒪[F] (subfieldEmbedding F E W β) x := by
      rw [hβ] at hx ⊢
      obtain ⟨z, hz, heq⟩ := hLift m x hx
      exact ⟨z, hz.1, heq⟩
    obtain ⟨a, ha, c, hc, e, he, haa, hca, hea, hz, hza⟩ := exists_mixed_adjoint_lift
      β C S.chain hC (fun {_} hx => hker (by simpa only [hβ] using hx)) k hLift' g g
      (i := s) (j := d) (m := d) (n := s + d) hy.1
      (by simpa only [hdk] using hp) (by simpa only [hdk] using hq)
      (by simpa only [add_assoc, hdk, ← sub_eq_add_neg] using hw)
      (by simpa only [hβ, hg] using hsum)
    simp only [hβ] at haa hca hea
    simp only [hβ, hg] at hz hza
    refine ⟨a, ⟨ha, haa⟩, c, ⟨hc, hca⟩, e, ⟨he, hea⟩, ⟨hz, ?_⟩, hza⟩
    change adjointMap 𝒪[F] S.b ((γ : EndF) * a + c * (γ : EndF) + e) ∈
      S.chain.endFiltration (s + k)
    rw [hza]
    exact hy.2
  apply le_antisymm ?_ (doubleCoset_subset_formalSelfIntertwining S hk hd)
  rw [intertwiningNeighborhood_eq S hk hd hdk (centralizerLattice_mul_adjointLattice_eq S hQ d k)]
  exact formalSelfIntertwining_subset_doubleCoset S hd hdk (endFiltration_exhaustive S.chain)
    (centralizerApproximation S) hLift hMixed

end LocalField

/-- Bushnell–Kutzko (1.5.8), including the scalar convention (1.4.6). -/
theorem simpleIntertwining : SimpleIntertwiningStatement := by
  intro F _ _ _ _ V _ _ _ S hS
  cases h : criticalExponent S.chain S.b using WithBot.recBotCoe with
  | bot => exact simpleIntertwining_of_criticalExponent_eq_bot S h
  | coe k => exact simpleIntertwining_of_criticalExponent_eq S hS h

end Langlands.BushnellKutzko

import Langlands.Representation.Jacquet.IwahoriContraction
import Langlands.Representation.Jacquet.StablePairingProof

/-! # Stable pairing group data from opposite Iwahori contractions -/

noncomputable section

namespace Langlands.Jacquet

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace IsIwahoriContraction

/-- Conjugating an open subgroup preserves its Iwahori contraction conditions
when the conjugating element normalizes all three subgroups and commutes with
the fixed contracting element. -/
theorem conj_of_normalizes {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}
    (h : IsIwahoriContraction K N M Nbar g) (m : G)
    (hN : m ∈ Subgroup.normalizer N) (hM : m ∈ Subgroup.normalizer M)
    (hNbar : m ∈ Subgroup.normalizer Nbar) (hc : Commute m g) :
    IsIwahoriContraction (conjOpenSubgroup m K) N M Nbar g := by
  let f : MulAut G := MulAut.conj m
  let b : MulAut G := MulAut.conj m⁻¹
  have hfb (x : G) : f (b x) = x := by
    simp [f, b, MulAut.conj_apply, mul_assoc]
  have hfg : f g = g := hc.mul_inv_cancel
  have forward (H : Subgroup G) (hH : m ∈ Subgroup.normalizer H) {x : G}
      (hx : x ∈ K.toSubgroup ⊓ H) :
      f x ∈ (conjOpenSubgroup m K).toSubgroup ⊓ H := by
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hH x).mp hx.2⟩
    change f x ∈ conjOpenSubgroup m K
    rw [mem_conjOpenSubgroup]
    simpa [f, MulAut.conj_apply, mul_assoc] using hx.1
  have back (H : Subgroup G) (hH : m ∈ Subgroup.normalizer H) {x : G}
      (hx : x ∈ (conjOpenSubgroup m K).toSubgroup ⊓ H) :
      b x ∈ K.toSubgroup ⊓ H := by
    refine ⟨?_, ?_⟩
    · simpa [b, MulAut.conj_apply] using (mem_conjOpenSubgroup m K x).mp hx.1
    · simpa [b, MulAut.conj_apply] using
        (Subgroup.mem_normalizer_iff''.mp hH x).mp hx.2
  refine
    { mem_levi := h.mem_levi
      factor := ?_
      upper := ?_
      levi := ?_
      lower := ?_
      exhaust := ?_
      contract := ?_ }
  · intro k hk
    have hk' : b k ∈ K := by
      simpa [b, MulAut.conj_apply] using (mem_conjOpenSubgroup m K k).mp hk
    obtain ⟨l, hl, a, ha, u, hu, heq⟩ := h.factor (b k) hk'
    refine ⟨f l, forward Nbar hNbar hl, f a, forward M hM ha,
      f u, forward N hN hu, ?_⟩
    calc k = f (b k) := (hfb k).symm
      _ = f (l * a * u) := congrArg f heq
      _ = f l * f a * f u := by simp only [map_mul]
  · intro u hu
    have h' := forward N hN (h.upper (b u) (back N hN hu))
    simpa only [map_mul, map_inv, hfg, hfb] using h'
  · intro a ha
    have h' := forward M hM (h.levi (b a) (back M hM ha))
    simpa only [map_mul, map_inv, hfg, hfb] using h'
  · intro l hl
    have h' := forward Nbar hNbar (h.lower (b l) (back Nbar hNbar hl))
    simpa only [map_mul, map_inv, hfg, hfb] using h'
  · intro x hx
    have hx' : b x ∈ N := by
      simpa [b, MulAut.conj_apply] using
        (Subgroup.mem_normalizer_iff''.mp hN x).mp hx
    obtain ⟨r, hr⟩ := h.exhaust (b x) hx'
    refine ⟨r, ?_⟩
    have h' : f (g ^ r * b x * (g ^ r)⁻¹) ∈ conjOpenSubgroup m K := by
      rw [mem_conjOpenSubgroup]
      simpa [f, MulAut.conj_apply, mul_assoc] using hr
    simpa only [map_mul, map_pow, map_inv, hfg, hfb] using h'
  · intro L
    obtain ⟨s, hs⟩ := h.contract (conjOpenSubgroup m⁻¹ L)
    refine ⟨s, fun l hl => ?_⟩
    have h' : f ((g ^ s)⁻¹ * b l * g ^ s) ∈ L := by
      have h'' := hs (b l) (back Nbar hNbar hl)
      simpa [mem_conjOpenSubgroup, f, MulAut.conj_apply] using h''
    simpa only [map_mul, map_pow, map_inv, hfg, hfb] using h'

end IsIwahoriContraction

/-- Every identity neighborhood contains a compact open subgroup admitting
Iwahori contractions in both orders, for one fixed element and its inverse. -/
def HasOppositeIwahoriContractionBasis (N M Nbar : Subgroup G) (g : G) : Prop :=
  ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O ∧
      IsIwahoriContraction K N M Nbar g ∧ IsIwahoriContraction K Nbar M N g⁻¹

/-- The structural part of the stable evaluation pairing follows from
normalization, centrality, and a cofinal family with opposite contractions for
the same fixed element. -/
def stablePairingDataOfIwahoriContractions (N M Nbar : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (g : G) (hc : ∀ m ∈ M, m * g = g * m)
    (hBasis : HasOppositeIwahoriContractionBasis N M Nbar g) : StablePairingData G :=
  { N := N
    Nbar := Nbar
    M := M
    hMN := hMN
    hMNbar := hMNbar
    g := g
    commute := hc
    Good := fun K => IsCompact (K : Set G) ∧ IsIwahoriContraction K N M Nbar g ∧
      IsIwahoriContraction K Nbar M N g⁻¹
    isCompact := fun _ hK => hK.1
    exists_good_subset := fun O hO h1 => by
      obtain ⟨K, hK, hKO, hUpper, hLower⟩ := hBasis O hO h1
      exact ⟨K, ⟨hK, hUpper, hLower⟩, hKO⟩
    good_conj := fun m hm K hK =>
      ⟨isCompact_conjOpenSubgroup m K hK.1,
        hK.2.1.conj_of_normalizes m (hMN hm) (M.le_normalizer hm) (hMNbar hm) (hc m hm),
        hK.2.2.conj_of_normalizes m (hMNbar hm) (M.le_normalizer hm) (hMN hm)
          (Commute.inv_right (hc m hm))⟩
    factor := fun K hK k hk => by
      obtain ⟨l, hl, a, ha, u, hu, heq⟩ := hK.2.1.factor k hk
      exact ⟨l, hl.1, hl.2, a, ha.1, ha.2, u, hu.1, hu.2, heq⟩
    lower_conj := fun _ hK l hl hlN => (hK.2.1.lower l ⟨hl, hlN⟩).1
    upper_conj := fun _ hK u hu huN r => (hK.2.1.upper_pow r u ⟨hu, huN⟩).1
    deep := fun K₀ K₁ hK₀ _ => by
      obtain ⟨r, hr⟩ := hK₀.2.2.contract K₁
      refine ⟨r, fun u hu huN => ?_⟩
      simpa only [inv_pow, inv_inv] using hr u ⟨hu, huN⟩ }

end Langlands.Jacquet

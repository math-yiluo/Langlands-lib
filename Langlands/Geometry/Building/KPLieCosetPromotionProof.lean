import Langlands.Geometry.Building.KPLieCosetPromotionStatement

/-!
# Proof of the apartment coset promotion statement

Proves `LieCosetPromotionOfPositiveRootSupportStatement`: finite generation of the strict
denominator is used twice as compactness in the submodule lattice, first to choose one
translation radius and then one deeper depth for the whole coset.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open ParahoricBuildingData.LieFiltrationData

private theorem shiftRightWindow (r : ℝ) :
    ∃ b : ℝ, r < b ∧ ∀ s : ℝ, r ≤ s → s < b → indexShift s = indexShift r := by
  by_cases hn : indexShift r = 0
  · refine ⟨r + 1, lt_add_one r, fun s hrs _ => ?_⟩
    exact Nat.le_antisymm (Nat.ceil_mono (neg_le_neg hrs)) (by rw [hn]; exact Nat.zero_le _)
  · have h := (Nat.ceil_eq_iff hn).1 (show ⌈-r⌉₊ = indexShift r from rfl)
    refine ⟨-((indexShift r - 1 : ℕ) : ℝ), by linarith [h.1], fun s hrs hs => ?_⟩
    exact (Nat.ceil_eq_iff hn).2 ⟨by linarith, (neg_le_neg hrs).trans h.2⟩

private theorem exists_le_of_fg_le_iSup {R M ι : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Nonempty ι] {S : Submodule R M} (hS : S.FG) (f : ι → Submodule R M)
    (hD : Directed (· ≤ ·) f) (h : S ≤ ⨆ i, f i) : ∃ i, S ≤ f i := by
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := (isCompactElement_iff_le_of_directed_sSup_le S).1
    ((Submodule.fg_iff_compact S).1 hS) (Set.range f) (Set.range_nonempty f)
    hD.directedOn_range (by rwa [sSup_range])
  exact ⟨i, hi⟩

private theorem eventually_affine_lt {V A : Type*} [AddCommGroup V] [Module ℝ V]
    [AddTorsor V A] (ψ : A →ᵃ[ℝ] ℝ) (x : A) (v : V) (t : ℝ)
    (hψ : t < ψ x ∨ (t = ψ x ∧ 0 < ψ.linear v)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → t < ψ (ε • v +ᵥ x) := by
  rcases hψ with hψ | ⟨heq, hpos⟩
  · let m : ℝ := |ψ.linear v|
    have hm : 0 < 1 + m := by linarith [abs_nonneg (ψ.linear v)]
    refine ⟨(ψ x - t) / (1 + m), div_pos (sub_pos.2 hψ) hm, fun ε hε hεδ => ?_⟩
    rw [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
    have hA := (lt_div_iff₀ hm).1 hεδ
    have hB := mul_le_mul_of_nonneg_left (neg_abs_le (ψ.linear v)) hε.le
    change ε * (-m) ≤ ε * ψ.linear v at hB
    nlinarith
  · refine ⟨1, zero_lt_one, fun ε hε _ => ?_⟩
    rw [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
    linarith [mul_pos hε hpos]

set_option maxHeartbeats 1000000 in
/-- Proof of `LieCosetPromotionOfPositiveRootSupportStatement`. -/
theorem lieCosetPromotionOfPositiveRootSupport :
    LieCosetPromotionOfPositiveRootSupportStatement.{u} := by
  intro F _ _ _ _ G _ P L hper x v r X hfg hX
  let t : NNReal := shiftedIndex r
  let I : Ideal 𝒪[F] := 𝓂[F] ^ indexShift r
  let a : 𝒪[F] := Submodule.IsPrincipal.generator I
  have ha : a ∈ I := Submodule.IsPrincipal.generator_mem I
  have ha_gen : Ideal.span {a} = I := Ideal.span_singleton_generator I
  let m : GenericLie 𝒪[F] G →ₗ[𝒪[F]] GenericLie 𝒪[F] G := a • LinearMap.id
  let S : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
    Submodule.span 𝒪[F] {a • X} ⊔ (L.lieFiltrationPlusReal x r).map m
  have hS : S.FG := (Submodule.fg_span_singleton _).sup (hfg.map m)
  obtain ⟨b, hrb, hb⟩ := shiftRightWindow r
  have hindex {q : ℝ} (hq : r ≤ q) (hqb : q < b) :
      (shiftedIndex q : ℝ) = q + indexShift r := by
    change q + (indexShift q : ℝ) = _
    rw [hb q hq hqb]
  let Q (δ : {d : ℝ // 0 < d}) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
    ⨅ (ε : ℝ) (_ : 0 < ε) (_ : ε < δ.1), L.lieFiltrationPlus (ε • v +ᵥ x) t
  have mem_Q {δ : {d : ℝ // 0 < d}} {Z : GenericLie 𝒪[F] G} : Z ∈ Q δ ↔
      ∀ ε : ℝ, 0 < ε → ε < δ.1 → Z ∈ L.lieFiltrationPlus (ε • v +ᵥ x) t := by
    simp only [Q, Submodule.mem_iInf]
  let U := ⨆ δ, Q δ
  have hroot (ψ : P.affineRoots)
      (hψ : (t : ℝ) < ψ.1 x ∨ ((t : ℝ) = ψ.1 x ∧ 0 < ψ.1.linear v)) :
      L.affineRootLie ψ ≤ U := by
    obtain ⟨δ, hδ, he⟩ := eventually_affine_lt ψ.1 x v t hψ
    refine le_trans ?_ (le_iSup Q ⟨δ, hδ⟩)
    intro Z hZ
    apply mem_Q.2
    intro ε hε hεδ
    have hval := he ε hε hεδ
    let q : NNReal := ⟨ψ.1 (ε • v +ᵥ x), t.2.trans hval.le⟩
    exact L.lieFiltration_le_lieFiltrationPlus _ (show t < q from hval)
      (L.affineRootLie_le_lieFiltration ψ (show (q : ℝ) ≤ ψ.1 (ε • v +ᵥ x) from le_rfl) hZ)
  have hbase (q : NNReal) (hq : t < q) : L.lieFiltration x q ≤ U := by
    rw [lieFiltration]
    apply sup_le
    · refine le_trans ?_ (le_iSup Q ⟨1, zero_lt_one⟩)
      intro Z hZ
      exact mem_Q.2 (fun ε _ _ =>
        L.lieFiltration_le_lieFiltrationPlus _ hq (L.centralizerLieImage_le_lieFiltration _ q hZ))
    · exact iSup₂_le fun ψ hψ => hroot ψ (.inl ((show (t : ℝ) < q from hq).trans_le hψ))
  have hSU : S ≤ U := by
    apply sup_le
    · apply Submodule.span_le.2
      intro Z hZ
      rw [Set.mem_singleton_iff] at hZ
      subst Z
      exact (iSup₂_le hroot) (hX a ha)
    · rintro _ ⟨Z, hZ, rfl⟩
      obtain ⟨q, hrq, hq⟩ := (L.mem_lieFiltrationPlusReal hper).1 hZ
      obtain ⟨q', hrq', hq'⟩ := exists_between (lt_min hrq hrb)
      have hq'b := hq'.trans_le (min_le_right q b)
      have hz := L.lieFiltrationReal_antitone hper x (hq'.le.trans (min_le_left q b)) hq
      have hm := (L.mem_lieFiltrationReal.1 hz) a (by rwa [hb q' hrq'.le hq'b])
      have htq' : (t : ℝ) < shiftedIndex q' := by
        rw [hindex hrq'.le hq'b]
        change r + (indexShift r : ℝ) < _
        linarith
      exact hbase (shiftedIndex q') htq' hm
  have : Nonempty {d : ℝ // 0 < d} := ⟨⟨1, zero_lt_one⟩⟩
  have hDQ : Directed (· ≤ ·) Q := by
    intro d d'
    refine ⟨⟨min d.1 d'.1, lt_min d.2 d'.2⟩, ?_, ?_⟩
    · intro Z hZ
      exact mem_Q.2 (fun ε hε he => mem_Q.1 hZ ε hε (he.trans_le (min_le_left _ _)))
    · intro Z hZ
      exact mem_Q.2 (fun ε hε he => mem_Q.1 hZ ε hε (he.trans_le (min_le_right _ _)))
  obtain ⟨δ, hδ⟩ := exists_le_of_fg_le_iSup hS Q hDQ hSU
  refine ⟨δ.1, δ.2, fun ε hε hεδ => ?_⟩
  let y := ε • v +ᵥ x
  have hy : S ≤ L.lieFiltrationPlus y t := fun Z hZ => mem_Q.1 (hδ hZ) ε hε hεδ
  have : Nonempty {q : NNReal // t < q} := ⟨⟨t + 1, lt_add_one t⟩⟩
  let D (q : {q : NNReal // t < q}) := L.lieFiltration y q.1
  have hD : Directed (· ≤ ·) D := by
    intro q q'
    exact ⟨⟨min q.1 q'.1, lt_min q.2 q'.2⟩,
      L.lieFiltration_antitone y (min_le_left _ _), L.lieFiltration_antitone y (min_le_right _ _)⟩
  have hy' : S ≤ ⨆ q, D q := by
    rw [lieFiltrationPlus, iSup_subtype'] at hy
    exact hy
  obtain ⟨q, hq⟩ := exists_le_of_fg_le_iSup hS D hD hy'
  have htq : (t : ℝ) < (q.1 : ℝ) := q.2
  have hrs' : r < (q.1 : ℝ) - indexShift r := by
    change r + (indexShift r : ℝ) < (q.1 : ℝ) at htq
    linarith
  obtain ⟨s, hrs, hsb⟩ := exists_between (lt_min hrb hrs')
  have hs_b := hsb.trans_le (min_le_left b _)
  have hs_q := hsb.trans_le (min_le_right b _)
  have hle : shiftedIndex s ≤ q.1 := by
    change (shiftedIndex s : ℝ) ≤ (q.1 : ℝ)
    rw [hindex hrs.le hs_b]
    linarith
  have hscaled {Z : GenericLie 𝒪[F] G} (hZ : a • Z ∈ S) : Z ∈ L.lieFiltrationReal y s := by
    rw [L.mem_lieFiltrationReal, hb s hrs.le hs_b]
    intro c hc
    change c ∈ I at hc
    rw [← ha_gen] at hc
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    rw [mul_smul]
    exact Submodule.smul_mem _ _ (L.lieFiltration_antitone y hle (hq hZ))
  refine ⟨s, hrs, fun Y hY => ?_⟩
  have hxx : X ∈ L.lieFiltrationReal y s := hscaled
    ((show Submodule.span 𝒪[F] {a • X} ≤ S from le_sup_left)
      (Submodule.subset_span (Set.mem_singleton _)))
  have hdiff : Y - X ∈ L.lieFiltrationReal y s := hscaled
    ((show (L.lieFiltrationPlusReal x r).map m ≤ S from le_sup_right)
      (Submodule.mem_map.2 ⟨_, hY, rfl⟩))
  simpa only [sub_add_cancel] using add_mem hdiff hxx

end Langlands.Geometry.Building

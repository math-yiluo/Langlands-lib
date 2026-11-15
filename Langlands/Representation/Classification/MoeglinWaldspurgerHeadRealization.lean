import Langlands.Representation.Classification.MoeglinWaldspurgerListCut

/-!
# Langlands heads inside products of segment heads along lists

Regrouping products of heads along lists, commuting cuspidal powers past heads of intervals
ending well below the cuspidal, the Langlands subrepresentation realization for the datum of a
list of intervals, finiteness and left reducedness of such products, and the head version of
the derivative-data wrapper.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear
open Langlands.Classification.LeftCuspidalDerivative Aubert.SegmentPolynomialSurjectivity

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

/-! ### Regrouping -/

theorem castIso_listProd_append :
    ∀ (l₁ l₂ : List Interval) {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      CastIso T (listProd F ρ x (l₁ ++ l₂) Y) (listProd F ρ x l₁ (listProd F ρ x l₂ Y))
  | [], _, _, _ => CastIso.refl _
  | I :: l₁, l₂, m, Y => by
    let := T.topology
    have h := castIso_listProd_append l₁ l₂ Y
    exact (CastIso.refl (segHead F ρ x I)).binary h

/-- `(L(l) × Y) × Z ≅ L(l) × (Y × Z)`, up to rank transport. -/
theorem castIso_listProd_binary :
    ∀ (l : List Interval) {m c : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier)),
      PosOrIrr T Y → PosOrIrr T Z →
      CastIso T (letI := T.topology;
          (T.binaryNormalizedProductFunctor (listRank ρ x l m) c).obj (listProd F ρ x l Y, Z))
        (listProd F ρ x l (letI := T.topology; (T.binaryNormalizedProductFunctor m c).obj (Y, Z)))
  | [], _, _, _, _, _, _ => CastIso.refl _
  | I :: l, m, c, Y, Z, hY, hZ => by
    let := T.topology
    have hW := posOrIrr_listProd.{uF, uV} ρ x l Y hY
    have h1 := castIso_assoc'' (realize_degree_pos.{uF, uV} ρ x I) (segHead F ρ x I)
      (listProd F ρ x l Y) Z hW hZ
    have h2 := (CastIso.refl (segHead F ρ x I)).binary (castIso_listProd_binary l Y Z hY hZ)
    exact h1.trans h2

/-- Cuspidal powers commute past heads of intervals ending below `c - 1`. -/
theorem castIso_listProd_iterProd (c : ℤ) (K : ℕ) :
    ∀ (l : List Interval), (∀ I ∈ l, I.ending + 1 < c) → ∀ {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      PosOrIrr T Y →
      CastIso T (listProd F ρ x l (iterProd T (cuspRep F T ρ x c).obj K Y))
        (iterProd T (cuspRep F T ρ x c).obj K (listProd F ρ x l Y))
  | [], _, _, _, _ => CastIso.refl _
  | I :: l, hl, m, Y, hY => by
    let := T.topology
    have hIc := hl I List.mem_cons_self
    have IH := castIso_listProd_iterProd c K l (fun J hJ => hl J (List.mem_cons_of_mem _ hJ)) Y hY
    have hsw := castIso_segHead_swap.{uF, uV} ρ x I c (by have := I.nonempty; omega)
    have h1 := (CastIso.refl (segHead F ρ x I)).binary IH
    have h2 := castIso_commute ρ.rank_pos (realize_degree_pos.{uF, uV} ρ x I) (cuspRep F T ρ x c).obj
      (segHead F ρ x I) hsw K (listProd F ρ x l Y) (posOrIrr_listProd.{uF, uV} ρ x l Y hY)
    exact h1.trans h2

/-! ### The empty datum -/

theorem empty_isIrreducible :
    letI := T.topology
    (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced.IsIrreducible := by
  let := T.topology
  exact ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one _
    (SegmentProductOrderedAssembly.finrank_zeroDatum _)

theorem empty_posOrIrr :
    PosOrIrr T (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced := by
  have h := empty_isIrreducible.{uF, uV} (T := T)
  exact Or.inr ⟨rfl, h⟩

theorem empty_nontrivial :
    letI := T.topology
    Nontrivial (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced := by
  let := T.topology
  have h := SegmentProductOrderedAssembly.finrank_zeroDatum
    (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0)
  exact Module.nontrivial_of_finrank_eq_succ h

theorem empty_hasFiniteLength :
    letI := T.topology
    (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced.HasFiniteLength := by
  let := T.topology
  have h := empty_isIrreducible.{uF, uV} (T := T)
  exact SmoothRep.hasFiniteLength_of_isIrreducible h

/-! ### Finiteness, nontriviality and reducedness -/

theorem listProd_hasFiniteLength :
    ∀ (l : List Interval) {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      (letI := T.topology; Y.HasFiniteLength) →
      (letI := T.topology; (listProd F ρ x l Y).HasFiniteLength)
  | [], _, _, h => h
  | I :: l, _, Y, h => by
    let := T.topology
    have hI := segHead_isIrreducible.{uF, uV} ρ x I
    have hIf := SmoothRep.hasFiniteLength_of_isIrreducible hI
    have hl := listProd_hasFiniteLength l Y h
    have h1 := Aubert.binaryProduct_preservesFiniteLength F T _ _ (segHead F ρ x I)
      (listProd F ρ x l Y) hIf hl
    exact h1

theorem segHead_nontrivial (I : Interval) :
    letI := T.topology; Nontrivial (segHead F ρ x I) := by
  let := T.topology
  have hI := segHead_isIrreducible.{uF, uV} ρ x I
  exact Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hI

theorem head_nontrivial {Δ : T.Segment.{max uF uV, uF}}
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hZ : T.IsSegmentHead Δ Z) : letI := T.topology; Nontrivial Z := by
  let := T.topology
  have hI := SegmentHeadSupport.isIrreducible_of_isSegmentHead T hZ
  exact Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hI

theorem binary_nontrivial_of {a b : ℕ}
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hX : letI := T.topology; Nontrivial X) (hY : letI := T.topology; Nontrivial Y) :
    letI := T.topology; Nontrivial ((T.binaryNormalizedProductFunctor a b).obj (X, Y)) := by
  let := T.topology
  exact Derivative.ProductVanishing.nontrivial_binary T (X, Y)

theorem listProd_nontrivial (l : List Interval) :
    ∀ {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      (letI := T.topology; Nontrivial Y) →
      (letI := T.topology; Nontrivial (listProd F ρ x l Y)) := by
  induction l with
  | nil => exact fun Y h => h
  | cons I l ih =>
    intro m Y h
    have h0 := head_nontrivial.{uF, uV} (segHead_isSegmentHead.{uF, uV} ρ x I)
    have h2 := ih Y h
    have h1 := binary_nontrivial_of.{uF, uV} _ _ h0 h2
    exact h1

/-- A segment head of a realized occurrence not ending at `y` is left reduced for
`ν^{x+y} ρ`. -/
theorem head_leftReduced (hL : LeftCuspidalDerivativeLemma.{uF, uV}) (y : ℤ) (J : Interval)
    (hJ : J.ending ≠ y)
    (π : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (J.realize ρ x).degree F.Carrier))
    (hπ : T.IsSegmentHead (J.realize ρ x) π) :
    LeftReduced F T (cuspRep F T ρ x y) π := by
  let := T.topology
  obtain ⟨-, -, -, -, hseg⟩ := hL p F T ρ.rank (cuspRep F T ρ x y)
  refine (hseg (ρ.twist (x + (y : ℝ))) rfl (cuspRep_represents F T ρ x y) _ π).1 hπ ?_
  rw [Interval.realize_last]
  intro h
  have := Langlands.Classification.cuspidalDatum_twist_injective ρ h
  have hJy : (J.ending : ℝ) = (y : ℝ) := by linarith
  exact hJ (by exact_mod_cast hJy)

theorem leftReduced_rankZero {d : ℕ} (hd : 0 < d)
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier)) :
    LeftReduced F T A Y := by
  intro Z _ _ k h
  exfalso
  omega

theorem listProd_leftReduced (hL : LeftCuspidalDerivativeLemma.{uF, uV}) (c : ℤ) :
    ∀ (l : List Interval), (∀ I ∈ l, I.ending ≠ c) → ∀ {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      (letI := T.topology; Y.HasFiniteLength) →
      LeftReduced F T (cuspRep F T ρ x c) Y →
      LeftReduced F T (cuspRep F T ρ x c) (listProd F ρ x l Y)
  | [], _, _, _, _, h => h
  | I :: l, hl, m, Y, hf, h => by
    let := T.topology
    obtain ⟨-, hprod, -, -, -⟩ := hL p F T ρ.rank (cuspRep F T ρ x c)
    have hI := segHead_isIrreducible.{uF, uV} ρ x I
    have hIf := SmoothRep.hasFiniteLength_of_isIrreducible hI
    have hlf := listProd_hasFiniteLength.{uF, uV} ρ x l Y hf
    have hIr := head_leftReduced.{uF, uV} ρ x hL c I (hl I List.mem_cons_self) _
      (segHead_isSegmentHead.{uF, uV} ρ x I)
    have hlr := listProd_leftReduced hL c l (fun J hJ => hl J (List.mem_cons_of_mem _ hJ)) Y hf h
    have h1 := hprod _ _ (segHead F ρ x I) (listProd F ρ x l Y) hIf hlf hIr hlr
    exact h1

/-! ### The Langlands subrepresentation realization along a list -/

/-- `J` does not precede `I` (in realized form, by `realize_precedes_iff`). -/
def NoPrec (I J : Interval) : Prop :=
  ¬ (J.beginning < I.beginning ∧ I.beginning ≤ J.ending + 1 ∧ J.ending < I.ending)

theorem lsub_listProd (hLS : LanglandsSubrepresentationRealization.{uF, uV})
    (l : List Interval) (hl : l.Pairwise NoPrec) :
    (∀ {n : ℕ} (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
        (realize ρ x (l : Multisegment)).IsLanglandsHead π →
        Embeds T π (listProd F ρ x l
          (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced)) ∧
    (∀ {k : ℕ} (W : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier)),
        (letI := T.topology; W.IsIrreducible) →
        Embeds T W (listProd F ρ x l
          (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced) →
        (realize ρ x (l : Multisegment)).IsLanglandsHead W) := by
  let := T.topology
  let d := consHeads F ρ x l
    (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0)
  have hd : d.HasSegmentHeads := consHeads_hasSegmentHeads.{uF, uV} ρ x l _ empty_hasSegmentHeads
  have hseg : List.ofFn d.segments = l.map (Interval.realize ρ x) := by
    rw [consHeads_segments, SegmentProductOrderedAssembly.empty_segments, List.append_nil]
  have hord : ∀ i j, i < j → ¬ (d.segments j).Precedes (d.segments i) := by
    have h : (List.ofFn d.segments).Pairwise (fun Δ Γ => ¬ Γ.Precedes Δ) := by
      rw [hseg, List.pairwise_map]
      refine hl.imp ?_
      intro I J hIJ hprec
      exact hIJ ((realize_precedes_iff F T ρ x J I).mp hprec)
    exact fun i j hij => List.pairwise_ofFn.mp h hij
  have hms : d.multisegment = realize ρ x (l : Multisegment) := by
    unfold SegmentProductDatum.multisegment
    rw [hseg]
    simp [realize]
  obtain ⟨h1, h2⟩ := hLS p F T _ d hd hord
  have hiso := consHeads_induced.{uF, uV} ρ x l
    (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0)
  refine ⟨fun {n} π hπ => ?_, fun {k} W hW hWe => ?_⟩
  · have hn : listRank ρ x l 0 = n := by
      rw [listRank_eq, add_zero, ← realize_degree]
      exact langlandsHead_degree hπ
    subst hn
    exact (embeds_of_isSubrepresentation (h1 π (hms ▸ hπ))).castIso_right hiso
  · obtain ⟨hk, hsub⟩ := hWe
    subst hk
    have hE0 : Embeds T W (listProd F ρ x l
        (SegmentProductOrderedAssembly.empty : T.SegmentProductDatum.{max uF uV, uF} 0).induced) :=
      ⟨rfl, hsub⟩
    have hE : Embeds T W d.induced := hE0.castIso_right hiso.symm
    have := h2 W hW (hE.isSubrepresentation_castRank rfl)
    rwa [hms] at this

/-! ### The head version of the derivative-data wrapper -/

theorem LDrel_of_embeds_head (hL : LeftCuspidalDerivativeLemma.{uF, uV}) (c : ℤ)
    (β : Multisegment) {K m' m n : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible)
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier))
    (hYf : letI := T.topology; Y.HasFiniteLength)
    (hYred : LeftReduced F T (cuspRep F T ρ x c) Y)
    (hex : letI := T.topology; ∃ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier)),
      D.IsIrreducible ∧ SmoothRep.IsSubrepresentation D Y)
    (hYhead : letI := T.topology;
      ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier)), W.IsIrreducible →
        SmoothRep.IsSubrepresentation W Y → (realize ρ x β).IsLanglandsHead W)
    (S : Label.{uF, uV} F T m) (hS : HeadClass F T ρ x β m S)
    (hemb : Embeds T π (iterProd T (cuspRep F T ρ x c).obj K Y)) :
    LDrel F T ρ x c (letI := T.topology; GeneralLinear.irreducibleIsoClass n F.Carrier π hπ) K S := by
  let := T.topology
  obtain ⟨D, hD, hDY⟩ := hex
  have hDc : HeadClass F T ρ x β m' (GeneralLinear.irreducibleIsoClass m' F.Carrier D hD) :=
    ⟨D, hD, rfl, hYhead D hD hDY⟩
  have hm' : m' = m := hDc.degree.symm.trans hS.degree
  subst hm'
  have hrank : powerRank ρ.rank K m' = n := hemb.choose.symm
  refine LDrel_of_embedding ρ x hL c hrank π hπ Y hYf hYred S ?_ ⟨D, hD, hDY⟩ ?_
  · intro Z hZ hZY
    exact headClass_unique F T ρ x ⟨Z, hZ, rfl, hYhead Z hZ hZY⟩ hS
  · rw [powerProduct_eq_iterProd]
    exact hemb.isSubrepresentation_castRank hrank

end Langlands.MoeglinWaldspurger.Derivation

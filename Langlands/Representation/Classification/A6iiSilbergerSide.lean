import Langlands.Representation.Classification.A6iiSegment
import Langlands.Representation.Classification.A6iiDatum
import Langlands.Representation.Classification.A6iiSilberger
import Langlands.Representation.Classification.TemperedQuotientAssembly

/-!
# The Silberger side of the head comparison

For a datum of segment heads merged by decreasing exponents, the cuspidal tensor
`⊠ ν^j A` in the merged fine order has the same positive count `m₀` in the
opposite Jacquet module of the merged standard module and at least `m₀` copies in
that of any irreducible quotient of it.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open CategoryTheory GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV

section Count

variable {G : Type*} [Monoid G]

theorem count_congr {A : Rep.{uF} ℂ G} {B : Rep.{uV} ℂ G} {τ υ : Rep.{uV} ℂ G}
    (φ : A.ρ.Equiv B.ρ) (ψ : τ.ρ.Equiv υ.ρ) {m : ℕ}
    (h : HasJordanHolderMultiplicity A τ m) : HasJordanHolderMultiplicity B υ m :=
  (equivJordanHolderMultiplicityTransport ℂ G A B τ υ φ ψ m).mp h

end Count

section Twist

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem realPowerTwist_conj (ν : G →* NNReal ˣ) (a b j : ℝ) (hab : a = b)
    (ρ : Representation ℂ G V) :
    realPowerTwist ν a (realPowerTwist ν j (realPowerTwist ν (-b) ρ)) =
      realPowerTwist ν j ρ := by
  subst hab
  rw [← realPowerTwist_add, ← realPowerTwist_add]
  congr 1
  ring

end Twist

variable {p : ℕ} [Fact p.Prime]

/-- Undoing a twist by `ν^(-b)` with `ν^a`, `a = b`, around a further twist `ν^j`. -/
theorem twistSC_conj (F : PadicField.{uF} p) (T : F.TopologicalData) {r : ℕ} (a b j : ℝ)
    (hab : a = b)
    (X : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    realPowerTwist (T.determinantNorm r) a (twistSC F T j (twistSC F T (-b) X)).obj.representation =
      (twistSC F T j X).obj.representation :=
  realPowerTwist_conj _ a b j hab _

variable {F : PadicField.{uF} p} {T : F.TopologicalData}

section Merged

variable {n : ℕ} (c : T.SegmentProductDatum.{max uF uV, uF} n) {ex : Fin c.length → ℝ}
  (m : MergeGrouping n (fun ℓ => (c.segments ℓ).degree) ex)

/-- The segment refinement of the merged shape: each segment block is cut into
its supercuspidal blocks. -/
abbrev segmentRefinement : BlockRefinement (m.shape.flatten (mergedRefinement c m)) :=
  fun k => BlockShape.uniform (c.segments (mergedLabel c m k)).length
    (c.segments (mergedLabel c m k)).rank (c.segments (mergedLabel c m k)).rank_pos

/-- The fine shape of all supercuspidal blocks, in merged order. -/
abbrev fineShape : BlockShape n :=
  (m.shape.flatten (mergedRefinement c m)).flatten (segmentRefinement c m)

end Merged

/-- The fine cuspidal test representation `⊠ ν^j A` in merged order. -/
abbrev fineAtoms (F : PadicField.{uF} p) (T : F.TopologicalData)
    {n : ℕ} (c : T.SegmentProductDatum.{max uF uV, uF} n) {ex : Fin c.length → ℝ}
    (m : MergeGrouping n (fun ℓ => (c.segments ℓ).degree) ex)
    (A : letI := T.topology
      ∀ l, SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := (c.segments l).rank)) :
    Rep.{max uF uV} ℂ ((fineShape c m).Levi F.Carrier) :=
  letI := T.topology
  Rep.of ((fineShape c m).blockTensor fun k =>
    (twistSC F T (((((m.shape.flatten (mergedRefinement c m)).flattenBlockEquiv
      (segmentRefinement c m)).symm k).2 : ℕ) : ℝ)
      (A (mergedLabel c m (((m.shape.flatten (mergedRefinement c m)).flattenBlockEquiv
        (segmentRefinement c m)).symm k).1))).obj.representation)

set_option maxHeartbeats 2000000 in
/-- The Silberger side: the cuspidal tensor `⊠ ν^j A` in merged order has a common
positive count `m₀` in the opposite Jacquet module of the merged standard module,
and at least `m₀` copies in that of every irreducible quotient of it. -/
theorem silbergerSide (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (hn : 0 < n)
    (c : T.SegmentProductDatum.{max uF uV, uF} n) {ex : Fin c.length → ℝ}
    (m : MergeGrouping n (fun ℓ => (c.segments ℓ).degree) ex)
    (A : letI := T.topology
      ∀ l, SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := (c.segments l).rank))
    (hA : letI := T.topology
      ∀ l, IsIrreducibleQuotient
        (T.segmentInduced (A l).obj (c.segments l).length (c.segments l).rank_pos).representation
        (c.blocks l).representation)
    (u : letI := T.topology
      ∀ l, UnitaryExponentData (T.determinantNorm (c.segments l).degree)
        (c.blocks l).representation)
    (hex : ∀ l, ex l = (u l).exponent)
    (hsq : letI := T.topology
      ∀ l, T.IsSquareIntegrable (T.segmentFactor (c.blocks l) (-(u l).exponent)).representation)
    (L : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hL : letI := T.topology; L.IsIrreducible)
    (qL : letI := T.topology; (merged c m).induced ⟶ L)
    (hqL : letI := T.topology; Function.Surjective (SmoothRep.hom qL)) :
    letI := T.topology
    ∃ m₀, 0 < m₀ ∧
      HasJordanHolderMultiplicity
        (CuspidalJacquetMultiplicity.oppositeJacquet T (fineShape c m) (merged c m).induced.obj)
        (fineAtoms F T c m A) m₀ ∧
      ∃ c', m₀ ≤ c' ∧ HasJordanHolderMultiplicity
        (CuspidalJacquetMultiplicity.oppositeJacquet T (fineShape c m) L.obj)
        (fineAtoms F T c m A) c' := by
  let := T.topology
  let Bc := m.shape
  let Q := mergedRefinement c m
  let D := Bc.flatten Q
  let R := segmentRefinement c m
  let fQ := Bc.flattenBlockEquiv Q
  let fR := D.flattenBlockEquiv R
  let S := Bc.composeRefinement Q R
  let fS := Bc.flattenBlockEquiv S
  let hS := Bc.flatten_composeRefinement Q R
  -- the twisted supercuspidal blocks and the normalized square-integrable blocks
  let Asc : ∀ q : (k : Fin D.length) × Fin (R k).length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := (R q.1).size q.2) :=
    fun q => twistSC F T (((q.2 : ℕ) : ℝ))
      (twistSC F T (-(u (mergedLabel c m q.1)).exponent) (A (mergedLabel c m q.1)))
  let Zs : ∀ q : (g : Fin Bc.length) × Fin (Q g).length,
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((Q q.1).size q.2) F.Carrier) :=
    fun q => T.segmentFactor (c.blocks (m.label q)) (-(u (m.label q)).exponent)
  have hZs : ∀ q, Representation.IsIrreducible (Zs q).representation ∧
      T.IsSquareIntegrable (Zs q).representation ∧ IsUnitarizable (Zs q).representation :=
    fun q => ⟨(isIrreducible_twist_iff _ _).mpr (hA _).1, hsq _, (u _).normalized_unitarizable⟩
  have hqb := fun k : Fin D.length =>
    (segment_twisted_quotient.{uF, uV} F T (c.segments (mergedLabel c m k)) (A _) (c.blocks _)
      (hA _) (-(u (mergedLabel c m k)).exponent)).2
  choose qb hqb using hqb
  let qblk : ∀ k : Fin D.length,
      (T.normalizedProductInductionFunctor (R k)).obj (fun j => (Asc ⟨k, j⟩).obj) ⟶
        Zs (fQ.symm k) := fun k => SmoothRep.ofHom (qb k)
  -- Silberger's count
  let π₀ : Rep.{max uF uV} ℂ (Bc.Levi F.Carrier) := Rep.of (Bc.blockTensor fun g =>
      ((T.normalizedProductInductionFunctor (Q g)).obj fun j => Zs ⟨g, j⟩).representation)
  let πt : Rep.{max uF uV} ℂ (Bc.Levi F.Carrier) :=
    Rep.of (T.leviRealPowerTwist Bc m.exponent π₀.ρ)
  let ω₀ : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier) :=
    Rep.of ((D.flatten R).blockTensor fun k => (Asc (fR.symm k)).obj.representation)
  let τ := fineTwist T Bc S (hS ▸ ω₀ : Rep.{max uF uV} ℂ ((Bc.flatten S).Levi F.Carrier)) 0
    m.exponent
  have key : ∃ m₀ : ℕ, 0 < m₀ ∧ HasJordanHolderMultiplicity (innerJacquet T Bc S πt) τ m₀ ∧
      HasJordanHolderMultiplicity (ambientJacquet T Bc S πt) τ m₀ ∧
      Classification.HasIrreducibleHead (CuspidalJacquetMultiplicity.induced T Bc πt).ρ ∧
      Representation.IsIrreducible πt.ρ ∧ IsAdmissible πt.ρ :=
    silbergerCount.{uF, uV} T hn Bc Q R Asc Zs hZs qblk hqb m.exponent m.strictAnti
  -- move the outer twist inside the blocks
  let I : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
    (T.normalizedProductInductionFunctor Bc).obj fun g =>
      T.segmentFactor ((T.normalizedProductInductionFunctor (Q g)).obj fun j => Zs ⟨g, j⟩)
        (m.exponent g)
  let πt' : Rep.{max uF uV} ℂ (Bc.Levi F.Carrier) := Rep.of (Bc.blockTensor fun g =>
    (T.segmentFactor ((T.normalizedProductInductionFunctor (Q g)).obj fun j => Zs ⟨g, j⟩)
      (m.exponent g)).representation)
  have hπt : πt = πt' := congrArg Rep.of (leviRealPowerTwist_blockTensor F T Bc _ _ _)
  obtain ⟨m₀, hm₀, hin, hout, -, hπi₀, hπa₀⟩ := key
  have hirr' : Representation.IsIrreducible πt'.ρ ∧ IsAdmissible πt'.ρ := by
    have gen : ∀ X : Rep.{max uF uV} ℂ (Bc.Levi F.Carrier), X = πt' →
        Representation.IsIrreducible X.ρ → IsAdmissible X.ρ →
        Representation.IsIrreducible πt'.ρ ∧ IsAdmissible πt'.ρ := by
      rintro X rfl h1 h2
      exact ⟨h1, h2⟩
    exact gen πt hπt hπi₀ hπa₀
  obtain ⟨hπi, hπa⟩ := hirr'
  rw [hπt] at hin hout
  -- the comparison of standard modules
  have eg (g : Fin Bc.length) :
      (T.normalizedProductInductionFunctor (Q g)).obj (fun j => c.blocks (m.label ⟨g, j⟩)) ≅
        T.segmentFactor ((T.normalizedProductInductionFunctor (Q g)).obj fun j => Zs ⟨g, j⟩)
          (m.exponent g) := by
    have hz : (fun j => T.segmentFactor (c.blocks (m.label ⟨g, j⟩)) (-(m.exponent g))) =
        fun j => Zs ⟨g, j⟩ := by
      funext j
      change _ = T.segmentFactor (c.blocks (m.label ⟨g, j⟩))
        (-(u (m.label ⟨g, j⟩)).exponent)
      rw [← hex, m.label_exponent]
    exact (commonExponentIso.{uF, max uF uV} F T (Bc.positive g) (Q g)
      (fun j => c.blocks (m.label ⟨g, j⟩)) (m.exponent g)).some ≪≫ eqToIso (congrArg (fun σ => T.segmentFactor
      ((T.normalizedProductInductionFunctor (Q g)).obj σ) (m.exponent g)) hz)
  obtain ⟨eflat⟩ := nonempty_flatten_iso.{uF, max uF uV} F T Bc Q
    (fun g j => c.blocks (m.label ⟨g, j⟩))
  let EI : (merged c m).induced ≅ I :=
    eflat ≪≫ (T.normalizedProductInductionFunctor Bc).mapIso (Pi.isoMk eg)
  -- the counts along the fine composed shape
  let fLE := flattenedLeviEquiv F.Carrier Bc S
  have hamb := count_flattened T Bc S (CuspidalJacquetMultiplicity.induced T Bc πt') τ hout
  have hquot := quotient_count_ge T hn Bc S τ πt' hπi hπa m₀ hin hout L hL
    (SmoothRep.hom (EI.inv ≫ qL)) (by
      intro w
      obtain ⟨v, rfl⟩ := hqL w
      exact ⟨SmoothRep.hom EI.hom v, by
        change SmoothRep.hom (EI.hom ≫ EI.inv ≫ qL) v = _
        rw [Iso.hom_inv_id_assoc]⟩)
  -- transport from the composed fine shape to the merged fine shape
  have conv : ∀ (X : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier)) (k : ℕ),
      HasJordanHolderMultiplicity (CuspidalJacquetMultiplicity.oppositeJacquet T (Bc.flatten S) X)
        (Rep.of (τ.ρ.comp fLE.toMonoidHom)) k →
      HasJordanHolderMultiplicity (CuspidalJacquetMultiplicity.oppositeJacquet T (D.flatten R) X)
        (fineAtoms F T c m A) k := by
    intro X k hk
    have h1 : HasJordanHolderMultiplicity
        (CuspidalJacquetMultiplicity.oppositeJacquet T (Bc.flatten S) X)
        (Rep.of (T.leviRealPowerTwist (Bc.flatten S)
          (fun k => -(0 : Fin (Bc.flatten S).length → ℝ) k + m.exponent (fS.symm k).1)
          (hS ▸ ω₀ : Rep.{max uF uV} ℂ ((Bc.flatten S).Levi F.Carrier)).ρ)) k :=
      count_congr (Representation.Equiv.refl _) (compSymmCompEquiv _ fLE) hk
    have h2 := count_cast T hS X ω₀ (fun k => m.exponent (fQ.symm (fR.symm k).1).1) _
      (fun k => by
        simp only [Pi.zero_apply, neg_zero, zero_add]
        exact congrArg m.exponent (outer_composeRefinement Bc Q R k)) h1
    have hatoms : (Rep.of (T.leviRealPowerTwist (D.flatten R)
        (fun k => m.exponent (fQ.symm (fR.symm k).1).1) ω₀.ρ) :
          Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier)) = fineAtoms F T c m A := by
      have e1 := leviRealPowerTwist_blockTensor F T (D.flatten R)
        (fun k => ((Asc (fR.symm k)).obj : Type (max uF uV)))
        (fun k => (Asc (fR.symm k)).obj.representation)
        (fun k => m.exponent (fQ.symm (fR.symm k).1).1)
      refine (congrArg Rep.of e1).trans ?_
      refine congrArg (fun ρs : ∀ k, Representation ℂ
          (GeneralLinear ((D.flatten R).size k) F.Carrier) ((Asc (fR.symm k)).obj) =>
        (Rep.of ((D.flatten R).blockTensor ρs) :
          Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier))) (funext fun k => ?_)
      exact twistSC_conj F T _ _ _
        ((m.label_exponent _ _).symm.trans (hex _)) _
    rw [hatoms] at h2
    exact h2
  refine ⟨m₀, hm₀, ?_, ?_⟩
  · have h := conv _ m₀ hamb
    have hIobj : CuspidalJacquetMultiplicity.induced T Bc πt' = I.obj :=
      induced_obj_eq.{uF, max uF uV} F T Bc _
    rw [hIobj, ← CuspidalJacquetMultiplicity.oppositeFunctor_obj] at h
    rw [← CuspidalJacquetMultiplicity.oppositeFunctor_obj]
    exact count_congr (Representation.equivOfIso
      ((CuspidalJacquetMultiplicity.oppositeFunctor T (D.flatten R)).mapIso EI.symm))
      (Representation.Equiv.refl _) h
  · obtain ⟨c', hc', hcount⟩ := hquot
    exact ⟨c', hc', conv _ c' hcount⟩

end Langlands.Classification.A6ii

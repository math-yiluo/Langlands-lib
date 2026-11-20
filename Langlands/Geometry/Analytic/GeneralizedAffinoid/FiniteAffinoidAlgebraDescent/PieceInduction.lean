import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceBaseCase
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceMatchingGenerationStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceMatchingGluingStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.LaurentInductionStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.BinaryLaurentSplitStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.SplitSquareGenerationStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.GlobalGenerationStatement

/-! # Generation of matching families by binary Laurent induction -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

open CategoryTheory

section Coefficients

variable {A B G : Type*} [CommRing A] [CommRing B] [FunLike G A B] [RingHomClass G A B]

/-- Linear combinations of linear combinations are linear combinations. -/
theorem exists_coeff_trans (f : G) {n m : ℕ} (x : Fin n → B) (y : Fin m → B)
    (hy : ∀ l, ∃ β : Fin n → A, ∑ k, f (β k) * x k = y l) {p : B}
    (hp : ∃ α : Fin m → A, ∑ l, f (α l) * y l = p) :
    ∃ a : Fin n → A, ∑ k, f (a k) * x k = p := by
  choose β hβ using hy
  obtain ⟨α, rfl⟩ := hp
  refine ⟨fun k => ∑ l, α l * β l k, ?_⟩
  simp only [map_sum, map_mul, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← hβ l, Finset.mul_sum]

end Coefficients

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K} {c : Domain.FiniteCover (Domain.whole K R)}

namespace LocalAlgebras

variable (F : LocalAlgebras c)

theorem restrict_localMap_apply (i : Fin c.size) {E D : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDi : D.locus ⊆ (c.obj i).locus) (y : F.algebra i) :
    F.restrict i hED hDi (F.localMap i D hDi y) = F.localMap i E (hED.trans hDi) y :=
  congrArg (fun q : BoundedAlgHom K (F.algebra i) (F.baseChange i E (hED.trans hDi)) => q y)
    (F.restrict_localMap i hED hDi)

theorem restrict_baseMap_apply (i : Fin c.size) {E D : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDi : D.locus ⊆ (c.obj i).locus) (a : D.algebra) :
    F.restrict i hED hDi (F.baseMap i D hDi a) =
      F.baseMap i E (hED.trans hDi) (restriction hED a) :=
  congrArg (fun q : BoundedAlgHom K D.algebra (F.baseChange i E (hED.trans hDi)) => q a)
    (F.restrict_baseMap i hED hDi)

/-- Images of norm-controlled generators of a local algebra generate every base
change over the algebra of the full domain. -/
theorem baseChange_generated (i : Fin c.size) {N : ℕ} (b : Fin N → F.algebra i) {C : ℝ}
    (hC : 0 < C) (hb : ∀ y, ∃ a, (F.map i).coefficientMap b a = y ∧ ‖a‖ ≤ C * ‖y‖)
    (E : Domain K R) (h : E.locus ⊆ (c.obj i).locus) (z : F.baseChange i E h) :
    ∃ a : Fin N → E.algebra, ∑ l, F.baseMap i E h (a l) * F.localMap i E h (b l) = z := by
  obtain ⟨D, -, hz⟩ :=
    AffinoidPushout.rightMap_coefficientMap_leftMap (F.map i) (restriction h) b hC hb
  obtain ⟨a, ha, -⟩ := hz z
  exact ⟨a, ha⟩

end LocalAlgebras

namespace PairTransitions

variable {F : LocalAlgebras c} (t : PairTransitions F)

theorem transition_baseMap_apply (i j : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) (hj : E.locus ⊆ (c.obj j).locus) (a : E.algebra) :
    t.transition i j E hi hj (F.baseMap i E hi a) = F.baseMap j E hj a :=
  congrArg (fun q : BoundedAlgHom K E.algebra (F.baseChange j E hj) => q a)
    (t.transition_baseMap i j E hi hj)

theorem matchingRestrict_comp {V'' V' V : Domain K R} (h' : V''.locus ⊆ V'.locus)
    (h : V'.locus ⊆ V.locus) (m : t.pieceMatching V) :
    t.matchingRestrict h' (t.matchingRestrict h m) = t.matchingRestrict (h'.trans h) m :=
  Subtype.ext (funext fun i => F.restrict_restrict i (inter_subset_inter h' i)
    (inter_subset_inter h i) (inter_subset_member V i) (m.val i))

theorem matchingRestrict_self {V : Domain K R} (h : V.locus ⊆ V.locus)
    (m : t.pieceMatching V) : t.matchingRestrict h m = m :=
  Subtype.ext (funext fun i => congrArg (fun q : BoundedAlgHom K (t.piece V i) (t.piece V i) =>
    q (m.val i)) (F.restrict_self i (V.inter (c.obj i)) (inter_subset_member V i)))

theorem matchingRestrict_structure {V' V : Domain K R} (h : V'.locus ⊆ V.locus)
    (a : V.algebra) :
    t.matchingRestrict h (t.matchingStructure V a) =
      t.matchingStructure V' (restriction h a) := by
  apply Subtype.ext
  funext i
  have h1 := F.restrict_baseMap_apply i (inter_subset_inter h i) (inter_subset_member V i)
    (restriction (Set.inter_subset_left : (V.inter (c.obj i)).locus ⊆ V.locus) a)
  have h2 := congrArg (fun q : BoundedAlgHom K V.algebra (V'.inter (c.obj i)).algebra => q a)
    ((restriction_comp (inter_subset_inter h i)
      (Set.inter_subset_left : (V.inter (c.obj i)).locus ⊆ V.locus)).trans
      (restriction_comp (Set.inter_subset_left : (V'.inter (c.obj i)).locus ⊆ V'.locus)
        h).symm)
  exact h1.trans (congrArg _ h2)

theorem val_sum_mul_apply {V : Domain K R} {m : ℕ} (f g : Fin m → t.pieceMatching V)
    (i : Fin c.size) : (∑ l, f l * g l).val i = ∑ l, (f l).val i * (g l).val i := by
  let π := (Pi.evalAlgHom K (fun i => t.piece V i) i).comp (t.pieceMatching V).val
  exact (map_sum π (fun l => f l * g l) Finset.univ).trans
    (Finset.sum_congr rfl fun l _ => map_mul π (f l) (g l))

theorem piecesGenerate_congr {V : Domain K R} {n : ℕ} {s s' : Fin n → t.pieceMatching V}
    (h : ∀ k, s k = s' k) (hs : t.PiecesGenerate V s) : t.PiecesGenerate V s' := by
  have : s = s' := funext h
  subst this
  exact hs

/-- Piece generation is inherited by restriction to smaller full domains. -/
theorem piecesGenerate_restrict {V' V : Domain K R} (h : V'.locus ⊆ V.locus) {n : ℕ}
    {s : Fin n → t.pieceMatching V} (hs : t.PiecesGenerate V s) :
    t.PiecesGenerate V' (fun k => t.matchingRestrict h (s k)) := by
  intro i p
  obtain ⟨N, b, C, hC, hb⟩ := F.finite i
  refine exists_coeff_trans
    (F.baseMap i (V'.inter (c.obj i)) (inter_subset_member V' i)).toAlgHom
    (fun k => (t.matchingRestrict h (s k)).val i)
    (fun l => F.localMap i (V'.inter (c.obj i)) (inter_subset_member V' i) (b l)) ?_
    (F.baseChange_generated i b hC hb _ _ p)
  intro l
  obtain ⟨β, hβ⟩ := hs i (F.localMap i (V.inter (c.obj i)) (inter_subset_member V i) (b l))
  refine ⟨fun k => restriction (inter_subset_inter h i) (β k), ?_⟩
  have h1 := congrArg (fun z => t.pieceRestrict h i z) hβ
  simp only [pieceRestrict, map_sum, map_mul, F.restrict_baseMap_apply,
    F.restrict_localMap_apply] at h1
  exact h1

/-- Piece generation passes to any family whose span contains a generating family. -/
theorem piecesGenerate_of_span {V : Domain K R} {n m : ℕ} {x : Fin n → t.pieceMatching V}
    {x' : Fin m → t.pieceMatching V}
    (hx : ∀ k, ∃ β : Fin m → V.algebra, ∑ l, t.matchingStructure V (β l) * x' l = x k)
    (hgen : t.PiecesGenerate V x) : t.PiecesGenerate V x' := by
  intro i p
  refine exists_coeff_trans
    (F.baseMap i (V.inter (c.obj i)) (inter_subset_member V i)).toAlgHom
    (fun l => (x' l).val i) (fun k => (x k).val i) ?_ (hgen i p)
  intro k
  obtain ⟨β, hβ⟩ := hx k
  refine ⟨fun l => restriction Set.inter_subset_left (β l), ?_⟩
  have h1 := congrArg (fun z : t.pieceMatching V => z.val i) hβ
  simp only [val_sum_mul_apply] at h1
  exact h1

end PairTransitions

open PairTransitions

namespace DescentData

variable {F : LocalAlgebras c} (d : DescentData F)

/-- Under descent data, restricted transitions in opposite directions are inverse. -/
theorem transition_transition_apply (i j : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) (hj : E.locus ⊆ (c.obj j).locus)
    (y : F.baseChange j E hj) :
    d.toPairTransitions.transition i j E hi hj
      (d.toPairTransitions.transition j i E hj hi y) = y := by
  have h := d.toPairTransitions.transition_cocycle_of_triple j i j (d.cocycle j i j) E hj hi hj
  rw [d.toPairTransitions.transition_self_of_identity (d.identity j)] at h
  exact congrArg (fun q : BoundedAlgHom K (F.baseChange j E hj) (F.baseChange j E hj) => q y) h

/-- Base case: over a full domain inside one cover member, finitely many matching
families generate every piece. -/
theorem piecesGenerate_base {U : Domain K R} (i₀ : Fin c.size)
    (hU : U.locus ⊆ (c.obj i₀).locus) :
    ∃ (n : ℕ) (s : Fin n → d.toPairTransitions.pieceMatching U),
      d.toPairTransitions.PiecesGenerate U s := by
  obtain ⟨N, b, C, hC, hb⟩ := F.finite i₀
  refine ⟨N, fun l => d.ofPiece i₀ hU
    (F.localMap i₀ (U.inter (c.obj i₀)) (inter_subset_member U i₀) (b l)), ?_⟩
  intro j p
  have hE₀ : (U.inter (c.obj j)).locus ⊆ (c.obj i₀).locus :=
    Set.Subset.trans (inter_subset_of_subset hU j) (inter_subset_member U i₀)
  obtain ⟨a, ha⟩ := F.baseChange_generated i₀ b hC hb (U.inter (c.obj j)) hE₀
    (d.toPairTransitions.transition j i₀ (U.inter (c.obj j)) (inter_subset_member U j) hE₀ p)
  refine ⟨a, ?_⟩
  have h1 := congrArg (d.toPairTransitions.transition i₀ j (U.inter (c.obj j)) hE₀
    (inter_subset_member U j)) ha
  rw [d.transition_transition_apply] at h1
  simp only [map_sum, map_mul, d.toPairTransitions.transition_baseMap_apply] at h1
  simp only [DescentData.ofPiece_apply, F.restrict_localMap_apply]
  exact h1

/-- If the restrictions of finitely many matching families over `V` generate the
matching families over `V ∩ cᵢ`, their `i`-th components generate the `i`-th piece. -/
theorem piece_of_generates {V : Domain K R} (i : Fin c.size) {n : ℕ}
    (s : Fin n → d.toPairTransitions.pieceMatching V)
    (hs : d.toPairTransitions.Generates (V.inter (c.obj i))
      (fun k => d.toPairTransitions.matchingRestrict Set.inter_subset_left (s k)))
    (p : d.toPairTransitions.piece V i) :
    ∃ a : Fin n → (V.inter (c.obj i)).algebra,
      ∑ k, F.baseMap i (V.inter (c.obj i)) (inter_subset_member V i) (a k) * (s k).val i =
        p := by
  have hV'i : (V.inter (c.obj i)).locus ⊆ (c.obj i).locus := inter_subset_member V i
  have hback : (V.inter (c.obj i)).locus ⊆ ((V.inter (c.obj i)).inter (c.obj i)).locus :=
    fun _ hx => ⟨hx, hV'i hx⟩
  have hid : ∀ x : F.baseChange i (V.inter (c.obj i)) (inter_subset_member V i),
      F.restrict i hback (inter_subset_member (V.inter (c.obj i)) i)
        (F.restrict i (Set.inter_subset_left :
          ((V.inter (c.obj i)).inter (c.obj i)).locus ⊆ (V.inter (c.obj i)).locus)
          (inter_subset_member V i) x) = x := by
    intro x
    exact (F.restrict_restrict i hback Set.inter_subset_left (inter_subset_member V i) x).trans
      (congrArg (fun q : BoundedAlgHom K _ _ => q x) (F.restrict_self i _ _))
  let p' : d.toPairTransitions.piece (V.inter (c.obj i)) i :=
    F.restrict i (Set.inter_subset_left :
      ((V.inter (c.obj i)).inter (c.obj i)).locus ⊆ (V.inter (c.obj i)).locus) hV'i p
  have hp' : (d.ofPiece i hV'i p').val i = p' := by
    rw [DescentData.ofPiece_apply,
      d.toPairTransitions.transition_self_of_identity (d.identity i)]
    exact congrArg (fun q : BoundedAlgHom K _ _ => q p') (F.restrict_self i _ _)
  obtain ⟨a, ha⟩ := hs (d.ofPiece i hV'i p')
  refine ⟨fun k => restriction hback (restriction Set.inter_subset_left (a k)), ?_⟩
  have h1 := congrArg (fun z : d.toPairTransitions.pieceMatching (V.inter (c.obj i)) =>
    z.val i) ha
  simp only [PairTransitions.val_sum_mul_apply] at h1
  have h2 := congrArg (fun z => F.restrict i hback
    (inter_subset_member (V.inter (c.obj i)) i) z) (h1.trans hp')
  simp only [map_sum, map_mul] at h2
  refine Eq.trans ?_ (h2.trans (hid p))
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg₂ (· * ·) (F.restrict_baseMap_apply i hback _ _).symm (hid _).symm

end DescentData

namespace PairTransitions

variable {F : LocalAlgebras c} (t : PairTransitions F)

/-- A full domain covered by two full subdomains. -/
def pairCover {V W₁ W₂ : Domain K R} (h₁ : W₁.locus ⊆ V.locus) (h₂ : W₂.locus ⊆ V.locus)
    (hcov : V.locus ⊆ W₁.locus ∪ W₂.locus) : Domain.FiniteCover V where
  size := 2
  obj := Fin.cons (α := fun _ => Domain K R) W₁ (fun _ => W₂)
  map a := Domain.inclusionOfSubset _ _ (by
    induction a using Fin.cases with
    | zero => exact h₁
    | succ _ => exact h₂)
  covers x hx := by
    rcases hcov hx with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

/-- Matching families over two covering full subdomains that agree on the
intersection glue to a matching family over the full domain. -/
theorem exists_pair_glue (hG3 : PieceMatchingGluingStatement.{u}) {V W₁ W₂ : Domain K R}
    (h₁ : W₁.locus ⊆ V.locus) (h₂ : W₂.locus ⊆ V.locus)
    (hcov : V.locus ⊆ W₁.locus ∪ W₂.locus) (x : t.pieceMatching W₁)
    (y : t.pieceMatching W₂)
    (hxy : t.matchingRestrict (V' := W₁.inter W₂) Set.inter_subset_left x =
      t.matchingRestrict (V' := W₁.inter W₂) Set.inter_subset_right y) :
    ∃ z : t.pieceMatching V, t.matchingRestrict h₁ z = x ∧ t.matchingRestrict h₂ z = y := by
  let e := pairCover h₁ h₂ hcov
  let m : ∀ a, t.pieceMatching (e.obj a) :=
    Fin.cons (α := fun a => t.pieceMatching (e.obj a)) x (fun _ => y)
  have hswap : (W₂.inter W₁).locus ⊆ (W₁.inter W₂).locus := fun _ hp => ⟨hp.2, hp.1⟩
  have hm : ∀ a b, t.matchingRestrict (V' := (e.obj a).inter (e.obj b))
      Set.inter_subset_left (m a) =
        t.matchingRestrict (V' := (e.obj a).inter (e.obj b)) Set.inter_subset_right (m b) := by
    intro a b
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ _ => exact hxy
    | succ _ =>
      induction b using Fin.cases with
      | zero =>
        exact ((t.matchingRestrict_comp hswap Set.inter_subset_right y).symm.trans
          (congrArg (t.matchingRestrict hswap) hxy.symm)).trans
          (t.matchingRestrict_comp hswap Set.inter_subset_left x)
      | succ _ => rfl
  obtain ⟨z, hz, -⟩ := hG3 K R c F t V e m hm
  exact ⟨z, hz (0 : Fin 2), hz (1 : Fin 2)⟩

/-- Piece generation implies generation of matching families (singleton cover). -/
theorem generates_of_piecesGenerate (hG2 : PieceMatchingLocalGenerationStatement.{u})
    {V : Domain K R} {n : ℕ} {s : Fin n → t.pieceMatching V} (hs : t.PiecesGenerate V s) :
    t.Generates V s :=
  hG2 K R c F t V (Domain.FiniteCover.singleton V) n s fun _ =>
    t.piecesGenerate_congr (fun k => (t.matchingRestrict_self _ (s k)).symm) hs

theorem piecesGenerate_restrict_restrict {E W V' V : Domain K R} (hEW : E.locus ⊆ W.locus)
    (hWV : W.locus ⊆ V.locus) (hEV' : E.locus ⊆ V'.locus) (hV'V : V'.locus ⊆ V.locus)
    {n : ℕ} {s : Fin n → t.pieceMatching V}
    (hs : t.PiecesGenerate W (fun k => t.matchingRestrict hWV (s k))) :
    t.PiecesGenerate E (fun k => t.matchingRestrict hEV' (t.matchingRestrict hV'V (s k))) :=
  t.piecesGenerate_congr (fun k => (t.matchingRestrict_comp hEW hWV (s k)).trans
    (t.matchingRestrict_comp hEV' hV'V (s k)).symm) (t.piecesGenerate_restrict hEW hs)

/-- If restrictions of matching families to two covering full subdomains generate
all pieces, then their restrictions to every smaller full domain generate the
matching families there. -/
theorem generates_of_pair (hG2 : PieceMatchingLocalGenerationStatement.{u})
    {V W₁ W₂ : Domain K R} (h₁ : W₁.locus ⊆ V.locus) (h₂ : W₂.locus ⊆ V.locus)
    (hcov : V.locus ⊆ W₁.locus ∪ W₂.locus) {n : ℕ} (s : Fin n → t.pieceMatching V)
    (hs₁ : t.PiecesGenerate W₁ (fun k => t.matchingRestrict h₁ (s k)))
    (hs₂ : t.PiecesGenerate W₂ (fun k => t.matchingRestrict h₂ (s k)))
    {V' : Domain K R} (hV' : V'.locus ⊆ V.locus) :
    t.Generates V' (fun k => t.matchingRestrict hV' (s k)) := by
  have hE₁ : (W₁.inter V').locus ⊆ V'.locus := Set.inter_subset_right
  have hE₂ : (W₂.inter V').locus ⊆ V'.locus := Set.inter_subset_right
  have hcov' : V'.locus ⊆ (W₁.inter V').locus ∪ (W₂.inter V').locus := by
    intro x hx
    rcases hcov (hV' hx) with h | h
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨h, hx⟩
  refine hG2 K R c F t V' (pairCover hE₁ hE₂ hcov') n _ ?_
  intro a
  induction a using Fin.cases with
  | zero => exact t.piecesGenerate_restrict_restrict Set.inter_subset_left h₁ _ hV' hs₁
  | succ _ => exact t.piecesGenerate_restrict_restrict Set.inter_subset_left h₂ _ hV' hs₂

/-- Generation in the sense of `Generates` gives spanning sets for any module
structure acting through `matchingStructure`. -/
theorem span_eq_top_of_generates {V : Domain K R} [Module V.algebra (t.pieceMatching V)]
    (hsmul : ∀ (a : V.algebra) (m : t.pieceMatching V), a • m = t.matchingStructure V a * m)
    {n : ℕ} {s : Fin n → t.pieceMatching V} {S : Set (t.pieceMatching V)}
    (hS : Set.range s ⊆ S) (hs : t.Generates V s) :
    Submodule.span V.algebra S = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun m => Submodule.span_mono hS ?_
  obtain ⟨a, ha⟩ := hs m
  refine (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨a, ?_⟩
  simp only [hsmul]
  exact ha

theorem exists_coeff_of_span {V : Domain K R} [Module V.algebra (t.pieceMatching V)]
    (hsmul : ∀ (a : V.algebra) (m : t.pieceMatching V), a • m = t.matchingStructure V a * m)
    {n : ℕ} {s : Fin n → t.pieceMatching V}
    (hs : Submodule.span V.algebra (Set.range s) = ⊤) (m : t.pieceMatching V) :
    ∃ β : Fin n → V.algebra, ∑ l, t.matchingStructure V (β l) * s l = m := by
  have hm : m ∈ Submodule.span V.algebra (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm
  refine ⟨β, ?_⟩
  simp only [hsmul] at hβ
  exact hβ

theorem locus_subset_of_split {U U₁ : Domain K R} {S : Set (BanachSpectrum U.algebra)}
    (hU₁ : U₁.locus = U.spectrumMap '' S) : U₁.locus ⊆ U.locus := by
  rw [hU₁]
  rintro _ ⟨y, -, rfl⟩
  exact U.represents.hasImageIn y

theorem locus_subset_union_of_split {U U₁ U₂ : Domain K R} (a : U.algebra) (ρ : ℝ)
    (hU₁ : U₁.locus = U.spectrumMap '' {y | y a ≤ ρ})
    (hU₂ : U₂.locus = U.spectrumMap '' {y | ρ ≤ y a}) :
    U.locus ⊆ U₁.locus ∪ U₂.locus := by
  intro x hx
  obtain ⟨y, hy⟩ := U.spectrumToLocus_surjective ⟨x, hx⟩
  have hyx : U.spectrumMap y = x := congrArg Subtype.val hy
  rcases le_total (y a) ρ with h | h
  · left
    rw [hU₁]
    exact ⟨y, h, hyx⟩
  · right
    rw [hU₂]
    exact ⟨y, h, hyx⟩

/-- Induction step: piece generation over both halves of a binary Laurent split
gives piece generation over the split domain, provided piece generation glues
along two-member covers. -/
theorem piecesGenerate_step (hG2 : PieceMatchingLocalGenerationStatement.{u})
    (hG3 : PieceMatchingGluingStatement.{u})
    (h4 : DomainBinaryLaurentSplitSquareStatement.{u})
    (h5 : BoundedAlgHom.SplitSquareModuleGenerationStatement.{u, u, u})
    (hpair : ∀ {V W₁ W₂ : Domain K R} (h₁ : W₁.locus ⊆ V.locus) (h₂ : W₂.locus ⊆ V.locus),
      V.locus ⊆ W₁.locus ∪ W₂.locus → ∀ {n : ℕ} (s : Fin n → t.pieceMatching V),
      t.PiecesGenerate W₁ (fun k => t.matchingRestrict h₁ (s k)) →
      t.PiecesGenerate W₂ (fun k => t.matchingRestrict h₂ (s k)) → t.PiecesGenerate V s)
    (U : Domain K R) (a : U.algebra) (ρ : ℝ) (hρ : 0 < ρ)
    (hP : ∀ U₁ U₂ : Domain K R, U₁.locus = U.spectrumMap '' {y | y a ≤ ρ} →
      U₂.locus = U.spectrumMap '' {y | ρ ≤ y a} →
      (∃ (n : ℕ) (s : Fin n → t.pieceMatching U₁), t.PiecesGenerate U₁ s) ∧
      (∃ (n : ℕ) (s : Fin n → t.pieceMatching U₂), t.PiecesGenerate U₂ s)) :
    ∃ (n : ℕ) (s : Fin n → t.pieceMatching U), t.PiecesGenerate U s := by
  obtain ⟨⟨U₁, U₂, hU₁, hU₂⟩, hsq⟩ := h4 K R U a ρ hρ
  obtain ⟨⟨n₁, x, hx⟩, ⟨n₂, y, hy⟩⟩ := hP U₁ U₂ hU₁ hU₂
  have h₁ : U₁.locus ⊆ U.locus := locus_subset_of_split hU₁
  have h₂ : U₂.locus ⊆ U.locus := locus_subset_of_split hU₂
  have hcov := locus_subset_union_of_split a ρ hU₁ hU₂
  have hW₁ : (U₁.inter U₂).locus ⊆ U₁.locus := Set.inter_subset_left
  have hW₂ : (U₁.inter U₂).locus ⊆ U₂.locus := Set.inter_subset_right
  obtain ⟨S⟩ := hsq U₁ U₂ (U₁.inter U₂) h₁ h₂ hW₁ hW₂ hU₁ hU₂ rfl
  let _ : Module U₁.algebra (t.pieceMatching U₁) :=
    Module.compHom _ (t.matchingStructure U₁).toRingHom
  let _ : Module U₂.algebra (t.pieceMatching U₂) :=
    Module.compHom _ (t.matchingStructure U₂).toRingHom
  let _ : Module (U₁.inter U₂).algebra (t.pieceMatching (U₁.inter U₂)) :=
    Module.compHom _ (t.matchingStructure (U₁.inter U₂)).toRingHom
  have hgx := t.generates_of_piecesGenerate hG2 hx
  have hgy := t.generates_of_piecesGenerate hG2 hy
  have hgx' := t.generates_of_piecesGenerate hG2 (t.piecesGenerate_restrict hW₁ hx)
  have hgy' := t.generates_of_piecesGenerate hG2 (t.piecesGenerate_restrict hW₂ hy)
  have hu₁ : ∀ (b : U₁.algebra) (m : t.pieceMatching U₁),
      (t.matchingRestrict hW₁).toRingHom.toAddMonoidHom (b • m) =
        restriction hW₁ b • (t.matchingRestrict hW₁).toRingHom.toAddMonoidHom m := fun b m =>
    (map_mul (t.matchingRestrict hW₁) (t.matchingStructure U₁ b) m).trans
      (congrArg (· * t.matchingRestrict hW₁ m) (t.matchingRestrict_structure hW₁ b))
  have hu₂ : ∀ (b : U₂.algebra) (m : t.pieceMatching U₂),
      (t.matchingRestrict hW₂).toRingHom.toAddMonoidHom (b • m) =
        restriction hW₂ b • (t.matchingRestrict hW₂).toRingHom.toAddMonoidHom m := fun b m =>
    (map_mul (t.matchingRestrict hW₂) (t.matchingStructure U₂ b) m).trans
      (congrArg (· * t.matchingRestrict hW₂ m) (t.matchingRestrict_structure hW₂ b))
  have hfin₁ : Module.Finite U₁.algebra (t.pieceMatching U₁) :=
    Module.finite_def.mpr (Submodule.fg_def.mpr ⟨Set.range x, Set.finite_range x,
      t.span_eq_top_of_generates (fun _ _ => rfl) subset_rfl hgx⟩)
  have hfin₂ : Module.Finite U₂.algebra (t.pieceMatching U₂) :=
    Module.finite_def.mpr (Submodule.fg_def.mpr ⟨Set.range y, Set.finite_range y,
      t.span_eq_top_of_generates (fun _ _ => rfl) subset_rfl hgy⟩)
  have hspan₁ : Submodule.span (U₁.inter U₂).algebra
      (Set.range (t.matchingRestrict hW₁).toRingHom.toAddMonoidHom) = ⊤ :=
    t.span_eq_top_of_generates (fun _ _ => rfl) (by rintro _ ⟨k, rfl⟩; exact ⟨x k, rfl⟩) hgx'
  have hspan₂ : Submodule.span (U₁.inter U₂).algebra
      (Set.range (t.matchingRestrict hW₂).toRingHom.toAddMonoidHom) = ⊤ :=
    t.span_eq_top_of_generates (fun _ _ => rfl) (by rintro _ ⟨k, rfl⟩; exact ⟨y k, rfl⟩) hgy'
  obtain ⟨m, x', y', hxy, hx', hy'⟩ := h5 K U.algebra U₁.algebra U₂.algebra
    (U₁.inter U₂).algebra (restriction h₁) (restriction h₂) (restriction hW₁)
    (restriction hW₂) ⟨S⟩ (t.pieceMatching U₁) (t.pieceMatching U₂)
    (t.pieceMatching (U₁.inter U₂)) (t.matchingRestrict hW₁).toRingHom.toAddMonoidHom
    (t.matchingRestrict hW₂).toRingHom.toAddMonoidHom hu₁ hu₂ hfin₁ hfin₂ hspan₁ hspan₂
  have hgx'' : t.PiecesGenerate U₁ x' :=
    t.piecesGenerate_of_span (fun k => t.exists_coeff_of_span (fun _ _ => rfl) hx' (x k)) hx
  have hgy'' : t.PiecesGenerate U₂ y' :=
    t.piecesGenerate_of_span (fun k => t.exists_coeff_of_span (fun _ _ => rfl) hy' (y k)) hy
  choose z hz₁ hz₂ using fun l => t.exists_pair_glue hG3 h₁ h₂ hcov (x' l) (y' l) (hxy l)
  exact ⟨m, z, hpair h₁ h₂ hcov z (t.piecesGenerate_congr (fun l => (hz₁ l).symm) hgx'')
    (t.piecesGenerate_congr (fun l => (hz₂ l).symm) hgy'')⟩

end PairTransitions

namespace DescentData

variable {F : LocalAlgebras c} (d : DescentData F)

/-- Under descent data, piece generation glues along two-member covers. -/
theorem piecesGenerate_of_pair (hG2 : PieceMatchingLocalGenerationStatement.{u})
    {V W₁ W₂ : Domain K R} (h₁ : W₁.locus ⊆ V.locus) (h₂ : W₂.locus ⊆ V.locus)
    (hcov : V.locus ⊆ W₁.locus ∪ W₂.locus) {n : ℕ}
    (s : Fin n → d.toPairTransitions.pieceMatching V)
    (hs₁ : d.toPairTransitions.PiecesGenerate W₁
      (fun k => d.toPairTransitions.matchingRestrict h₁ (s k)))
    (hs₂ : d.toPairTransitions.PiecesGenerate W₂
      (fun k => d.toPairTransitions.matchingRestrict h₂ (s k))) :
    d.toPairTransitions.PiecesGenerate V s := fun i p =>
  d.piece_of_generates i s
    (d.toPairTransitions.generates_of_pair hG2 h₁ h₂ hcov s hs₁ hs₂ Set.inter_subset_left) p

/-- Over the whole spectrum of a nonempty cover, finitely many matching families
generate every piece. -/
theorem exists_piecesGenerate_whole (hG2 : PieceMatchingLocalGenerationStatement.{u})
    (hG3 : PieceMatchingGluingStatement.{u})
    (h3 : FiniteCoverBinaryLaurentInductionStatement.{u})
    (h4 : DomainBinaryLaurentSplitSquareStatement.{u})
    (h5 : BoundedAlgHom.SplitSquareModuleGenerationStatement.{u, u, u}) (hc : 0 < c.size) :
    ∃ (n : ℕ) (s : Fin n → d.toPairTransitions.pieceMatching (Domain.whole K R)),
      d.toPairTransitions.PiecesGenerate (Domain.whole K R) s :=
  h3 K R c (fun U => ∃ (n : ℕ) (s : Fin n → d.toPairTransitions.pieceMatching U),
      d.toPairTransitions.PiecesGenerate U s) hc
    (fun _ ⟨i, hi⟩ => d.piecesGenerate_base i hi)
    (fun U ⟨a, ρ, hρ, hP⟩ => d.toPairTransitions.piecesGenerate_step hG2 hG3 h4 h5
      (fun h₁ h₂ hcov _ s hs₁ hs₂ => d.piecesGenerate_of_pair hG2 h₁ h₂ hcov s hs₁ hs₂)
      U a ρ hρ hP)

end DescentData

theorem member_subset_whole_inter (c : Domain.FiniteCover (Domain.whole K R))
    (i : Fin c.size) : (c.obj i).locus ⊆ ((Domain.whole K R).inter (c.obj i)).locus :=
  fun _ hx => ⟨Set.mem_univ _, hx⟩

namespace LocalAlgebras

variable (F : LocalAlgebras c)

/-- The inverse of the base change of a local algebra to `whole ∩ cᵢ`, whose
locus is the locus of `cᵢ`. -/
def wholeInverse (i : Fin c.size) :
    BoundedAlgHom K (F.baseChange i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i)) (F.algebra i) :=
  AffinoidPushout.lift (F.map i) (restriction (PairTransitions.inter_subset_member _ i))
    (F.algebra i) (BoundedAlgHom.id K (F.algebra i))
    ((F.map i).comp (restriction (member_subset_whole_inter c i))) (by
      rw [BoundedAlgHom.id_comp, BoundedAlgHom.comp_assoc, restriction_comp,
        restriction_self, BoundedAlgHom.comp_id])

theorem wholeInverse_comp_localMap (i : Fin c.size) :
    (F.wholeInverse i).comp (F.localMap i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i)) = BoundedAlgHom.id K (F.algebra i) :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem wholeInverse_comp_baseMap (i : Fin c.size) :
    (F.wholeInverse i).comp (F.baseMap i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i)) =
        (F.map i).comp (restriction (member_subset_whole_inter c i)) :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

theorem wholeInverse_localMap_apply (i : Fin c.size) (y : F.algebra i) :
    F.wholeInverse i (F.localMap i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i) y) = y :=
  congrArg (fun q : BoundedAlgHom K (F.algebra i) (F.algebra i) => q y)
    (F.wholeInverse_comp_localMap i)

theorem wholeInverse_baseMap_apply (i : Fin c.size)
    (a : ((Domain.whole K R).inter (c.obj i)).algebra) :
    F.wholeInverse i (F.baseMap i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i) a) =
        F.map i (restriction (member_subset_whole_inter c i) a) :=
  congrArg (fun q : BoundedAlgHom K ((Domain.whole K R).inter (c.obj i)).algebra
    (F.algebra i) => q a) (F.wholeInverse_comp_baseMap i)

theorem localMap_wholeInverse (i : Fin c.size) :
    (F.localMap i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i)).comp (F.wholeInverse i) =
        BoundedAlgHom.id K _ := by
  apply AffinoidPushout.hom_ext (F.map i)
    (restriction (PairTransitions.inter_subset_member (Domain.whole K R) i))
  · change ((F.localMap i _ _).comp (F.wholeInverse i)).comp (F.localMap i _ _) =
      (BoundedAlgHom.id K _).comp (F.localMap i _ _)
    rw [BoundedAlgHom.comp_assoc, F.wholeInverse_comp_localMap]
    exact (BoundedAlgHom.comp_id _).trans (BoundedAlgHom.id_comp _).symm
  · change ((F.localMap i _ _).comp (F.wholeInverse i)).comp (F.baseMap i _ _) =
      (BoundedAlgHom.id K _).comp (F.baseMap i _ _)
    rw [BoundedAlgHom.comp_assoc, F.wholeInverse_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, F.condition, BoundedAlgHom.comp_assoc, restriction_comp,
      restriction_self, BoundedAlgHom.comp_id, BoundedAlgHom.id_comp]

theorem localMap_wholeInverse_apply (i : Fin c.size)
    (p : F.baseChange i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i)) :
    F.localMap i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i) (F.wholeInverse i p) = p :=
  congrArg (fun q : BoundedAlgHom K (F.baseChange i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i))
    (F.baseChange i ((Domain.whole K R).inter (c.obj i))
      (PairTransitions.inter_subset_member _ i)) => q p) (F.localMap_wholeInverse i)

end LocalAlgebras

namespace PairTransitions

variable {F : LocalAlgebras c} (t : PairTransitions F)

/-- Matching families over the whole spectrum give elements of the matching
algebra, componentwise through `wholeInverse`. -/
def toMatchingAlgebra (s : t.pieceMatching (Domain.whole K R)) : t.MatchingAlgebra :=
  ⟨fun i => F.wholeInverse i (s.val i), fun i j => by
    have hi : (F.overlap i j).locus ⊆ ((Domain.whole K R).inter (c.obj i)).locus :=
      fun _ hx => ⟨Set.mem_univ _, hx.1⟩
    have hj : (F.overlap i j).locus ⊆ ((Domain.whole K R).inter (c.obj j)).locus :=
      fun _ hx => ⟨Set.mem_univ _, hx.2⟩
    have key : ∀ k (hk : (F.overlap i j).locus ⊆ ((Domain.whole K R).inter (c.obj k)).locus),
        F.restrict k hk (inter_subset_member _ k) (s.val k) =
          F.localMap k (F.overlap i j) (hk.trans (inter_subset_member _ k))
            (F.wholeInverse k (s.val k)) := fun k hk =>
      (congrArg (F.restrict k hk (inter_subset_member _ k))
        (F.localMap_wholeInverse_apply k (s.val k)).symm).trans
        (F.restrict_localMap_apply k hk (inter_subset_member _ k) _)
    have h1 := (congrArg (t.transition i j (F.overlap i j) _ _) (key i hi)).symm.trans
      ((s.property i j (F.overlap i j) hi hj).trans (key j hj))
    exact (congrArg (fun q : BoundedAlgHom K _ _ =>
      q (F.localMap i (F.overlap i j) (F.overlapLeft i j) (F.wholeInverse i (s.val i))))
        (t.transition_overlap i j)).symm.trans h1⟩

/-- Piece generation over the whole spectrum gives generators of every local
algebra over its cover algebra. -/
theorem surjective_of_piecesGenerate_whole {n : ℕ}
    {s : Fin n → t.pieceMatching (Domain.whole K R)}
    (hs : t.PiecesGenerate (Domain.whole K R) s) (i : Fin c.size) :
    Function.Surjective
      ((F.map i).coefficientMap fun k => t.projection i (t.toMatchingAlgebra (s k))) := by
  intro y
  obtain ⟨a, ha⟩ := hs i (F.localMap i _ (inter_subset_member _ i) y)
  refine ⟨fun k => restriction (member_subset_whole_inter c i) (a k), ?_⟩
  have h1 := congrArg (F.wholeInverse i) ha
  simp only [map_sum, map_mul, F.wholeInverse_baseMap_apply,
    F.wholeInverse_localMap_apply] at h1
  rw [BoundedAlgHom.coefficientMap_apply]
  exact h1

end PairTransitions

/-- Global generation follows from the local-to-global generation statement, the
gluing statement, binary Laurent induction, binary Laurent split squares, and
split-square generation of modules. -/
theorem globalGeneration_of_prerequisites (hG2 : PieceMatchingLocalGenerationStatement.{u})
    (hG3 : PieceMatchingGluingStatement.{u})
    (h3 : FiniteCoverBinaryLaurentInductionStatement.{u})
    (h4 : DomainBinaryLaurentSplitSquareStatement.{u})
    (h5 : BoundedAlgHom.SplitSquareModuleGenerationStatement.{u, u, u}) :
    FiniteAffinoidAlgebraGlobalGenerationStatement.{u} := by
  intro K' _ _ _ R' c' F' d'
  by_cases hc : c'.size = 0
  · exact ⟨0, Fin.elim0, fun i => absurd i.isLt (by omega)⟩
  · obtain ⟨n, s, hs⟩ := d'.exists_piecesGenerate_whole hG2 hG3 h3 h4 h5
      (Nat.pos_of_ne_zero hc)
    exact ⟨n, fun k => d'.toPairTransitions.toMatchingAlgebra (s k),
      d'.toPairTransitions.surjective_of_piecesGenerate_whole hs⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

import Langlands.GroupScheme.Reductive.LocalSplitCommutatorLaws
import Langlands.GroupScheme.Reductive.LocalSplitCommonTorus
import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismTheoremStatement
import Langlands.LinearAlgebra.RootDatumBaseExists

/-! # The local split Isomorphism Theorem from Weyl normalization and root relations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section Enumerations

/-- A finite type has an enumeration along which a given integer-valued function is
monotone. -/
theorem exists_equiv_monotone {α : Type*} [Fintype α] (f : α → ℤ) :
    ∃ e : Fin (Fintype.card α) ≃ α, ∀ p q, p ≤ q → f (e p) ≤ f (e q) := by
  classical
  let g : α → ℤ ×ₗ Fin (Fintype.card α) := fun x => toLex (f x, Fintype.equivFin α x)
  have hg : Function.Injective g := by
    intro x y h
    have h2 := congrArg (fun z => (ofLex z).2) h
    exact (Fintype.equivFin α).injective h2
  let _ : LinearOrder α := LinearOrder.lift' g hg
  let e := Fintype.orderIsoFinOfCardEq α rfl
  refine ⟨e.toEquiv, fun p q hpq => ?_⟩
  have h : g (e p) ≤ g (e q) := e.monotone hpq
  rcases Prod.Lex.le_iff.mp h with h' | ⟨h', -⟩
  · exact h'.le
  · exact h'.le

end Enumerations

section Words

variable {I : Type u} {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))

/-- **Simple words built by descending height.** The word of a simple root `a` starts at `a`
and is empty. The word of a positive non-simple root `α` is `c ::` (the word of `s_c α`), with
the same simple root, for some simple root `c` with `0 < ⟨α, c^∨⟩`; so `s_c α` has smaller
height. The word of a non-positive root `α` is the word of `-α` followed by its simple root.
Here `P.reflectionPerm c α` is the index of `s_c α`, and `P.reflectionPerm α α` that of
`-α`. -/
def IsDescendingWords (b : P.Base) (W : ∀ α, SimpleWord P b α) : Prop :=
  (∀ a ∈ b.support, (W a).simple = a ∧ (W a).word = []) ∧
  (∀ α, b.IsPos α → α ∉ b.support → ∃ c ∈ b.support, 0 < P.pairing α c ∧
    (W α).simple = (W (P.reflectionPerm c α)).simple ∧
    (W α).word = c :: (W (P.reflectionPerm c α)).word) ∧
  (∀ α, ¬ b.IsPos α → (W α).simple = (W (P.reflectionPerm α α)).simple ∧
    (W α).word = (W (P.reflectionPerm α α)).word ++ [(W (P.reflectionPerm α α)).simple])

open Classical in
/-- The recursion measure for `descWord`: twice the height of a positive root, and one more
than twice the absolute value of the height of a non-positive root. -/
def descMeasure (b : P.Base) (α : J) : ℕ :=
  if b.IsPos α then 2 * (b.height α).toNat else 2 * (-b.height α).toNat + 1

theorem height_reflectionPerm_of_mem {b : P.Base} {c : J} (hc : c ∈ b.support) (α : J) :
    b.height (P.reflectionPerm c α) = b.height α - P.pairing α c := by
  have h : P.root (P.reflectionPerm c α) = P.root α + (-P.pairing α c) • P.root c := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, neg_smul,
      sub_eq_add_neg]
  rw [b.height_add_zsmul h, RootPairing.Base.height_one_of_mem_support hc, smul_eq_mul,
    mul_one]
  ring

theorem descMeasure_lt_of_not_pos {b : P.Base} {α : J} (hα : ¬ b.IsPos α) :
    descMeasure P b (P.reflectionPerm α α) < descMeasure P b α := by
  have hneg : b.height (P.reflectionPerm α α) = -b.height α := b.height_reflectionPerm_self α
  have h0 := b.height_ne_zero α
  have hα' : ¬ 0 < b.height α := hα
  have hpos : b.IsPos (P.reflectionPerm α α) := by
    rw [RootPairing.Base.isPos_iff, hneg]
    omega
  simp only [descMeasure, hpos, hα, ↓reduceIte, hneg]
  omega

variable [Finite J] [P.IsReduced]

omit [P.IsReduced] in
theorem exists_mem_support_pos_pairing {b : P.Base} {α : J} (hp : b.IsPos α) :
    ∃ c ∈ b.support, 0 < P.pairing α c := by
  obtain ⟨c, hc, hpos⟩ := hp.exists_mem_support_pos_pairingIn
  refine ⟨c, hc, ?_⟩
  have h2 : 0 < P.pairingIn ℤ α c := (P.zero_lt_pairingIn_iff' ℤ (i := c) (j := α)).mp hpos
  have e : P.pairing α c = P.pairingIn ℤ α c := by
    rw [← P.algebraMap_pairingIn ℤ]
    simp
  rw [e]
  exact h2

theorem descMeasure_lt_of_pos {b : P.Base} {α c : J} (hα : b.IsPos α) (hs : α ∉ b.support)
    (hc : c ∈ b.support) (hpair : 0 < P.pairing α c) :
    descMeasure P b (P.reflectionPerm c α) < descMeasure P b α := by
  have hne : α ≠ c := fun h => hs (h ▸ hc)
  have hβ : b.IsPos (P.reflectionPerm c α) := hα.reflectionPerm hc hne
  have hh := height_reflectionPerm_of_mem P hc α
  have h1 : 0 < b.height α := hα
  have h2 : 0 < b.height (P.reflectionPerm c α) := hβ
  simp only [descMeasure, hβ, hα, ↓reduceIte, hh]
  rw [hh] at h2
  omega

open Classical in
/-- **Descending simple words**, by recursion on `descMeasure`. A simple root gets the empty
word. A positive non-simple root `α` gets `c ::` (the word of `s_c α`) for a chosen simple
root `c` with `0 < ⟨α, c^∨⟩`; such a `c` always exists, and the branch without it is never
used. A non-positive root gets the word of its negative followed by its simple root. -/
noncomputable def descWord (b : P.Base) (α : J) : SimpleWord P b α :=
  if hs : α ∈ b.support then ⟨α, hs, [], fun _ hj => absurd hj List.not_mem_nil, rfl⟩
  else if hp : b.IsPos α then
    if h : ∃ c ∈ b.support, 0 < P.pairing α c then
      let w := descWord b (P.reflectionPerm h.choose α)
      ⟨w.simple, w.simple_mem, h.choose :: w.word, fun j hj => by
          rcases List.mem_cons.mp hj with hj | hj
          · exact hj ▸ h.choose_spec.1
          · exact w.word_mem j hj,
        by
          change P.reflection h.choose (wordReflect P w.word (P.root w.simple)) = P.root α
          rw [w.root_eq, RootPairing.root_reflectionPerm, RootPairing.reflection_same]⟩
    else (nonempty_simpleWord P b α).some
  else
    let w := descWord b (P.reflectionPerm α α)
    ⟨w.simple, w.simple_mem, w.word ++ [w.simple], fun j hj => by
        rcases List.mem_append.mp hj with hj | hj
        · exact w.word_mem j hj
        · rw [List.mem_singleton.mp hj]
          exact w.simple_mem,
      by
        have h1 : P.root α = -P.root (P.reflectionPerm α α) := by
          rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, neg_neg]
        rw [h1, ← w.root_eq, ← wordReflect_neg, ← RootPairing.reflection_apply_self]
        simp only [wordReflect, List.foldr_append, List.foldr_cons, List.foldr_nil]⟩
termination_by descMeasure P b α
decreasing_by
  · exact descMeasure_lt_of_pos P hp hs h.choose_spec.1 h.choose_spec.2
  · exact descMeasure_lt_of_not_pos P hp

/-- The words `descWord` are descending. -/
theorem isDescendingWords_descWord (b : P.Base) : IsDescendingWords P b (descWord P b) := by
  refine ⟨fun a ha => ?_, fun α hp hs => ?_, fun α hp => ?_⟩
  · rw [descWord]
    simp only [ha, ↓reduceDIte, and_self]
  · have h := exists_mem_support_pos_pairing P hp
    refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2, ?_, ?_⟩
    · conv_lhs => rw [descWord]
      simp only [hs, hp, h, ↓reduceDIte]
    · conv_lhs => rw [descWord]
      simp only [hs, hp, h, ↓reduceDIte]
  · have hs : α ∉ b.support := fun h => hp (b.isPos_of_mem_support h)
    constructor
    · conv_lhs => rw [descWord]
      simp only [hs, hp, ↓reduceDIte]
    · conv_lhs => rw [descWord]
      simp only [hs, hp, ↓reduceDIte]

end Words

end LocalSplitCell

open LocalSplitCell

/-- **Weyl-normalized simple-root data over an arbitrary local ring.** The statement
`LocalSplitSimpleRootGroupStatement` without the reducedness hypothesis: for every base `b`
there are root parametrizations of the simple roots and their negatives whose Weyl points
`u_{-a}(-1) u_a(1) u_{-a}(-1)` act on the torus by the simple reflections. -/
def LocalSplitSimpleRootGroupLocalStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
      ∀ b : P.Base, ∃ u : J → (Ga R ⟶ G),
        (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
          IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))) ∧
        ∀ a ∈ b.support,
          IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a)

/-- **Commutator relations of Weyl families over a local ring.** For two reductive groups over
a local ring with fibrewise maximal coordinate split tori carrying the same fibrewise root
datum, and Weyl-normalized simple-root data for a base `b`, the positive cell factors of the
two Weyl families satisfy the same commutator relations (`CommutatorRelations`). Here the
words are descending (`IsDescendingWords`) and the positive roots are enumerated by
increasing height. -/
def LocalSplitWeylCommutatorStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I] [DecidableEq I]
    (J : Type u) (G H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom],
    IsReductive G → IsReductive H →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H),
      IsClosedSubgroup i → IsClosedSubgroup i' →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i' →
      ∀ (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P → IsFibrewiseRootDatumOf I H i' P →
      ∀ (b : P.Base) (W : ∀ α, SimpleWord P b α), IsDescendingWords P b W →
      ∀ (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)),
      (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
        IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))) →
      (∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a)) →
      (∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a) ∧
        IsRootParametrization i' (P.root (P.reflectionPerm a a)) (u' (P.reflectionPerm a a))) →
      (∀ a ∈ b.support, IsWeylPoint i' (rootWeylPoint P u' a) (P.reflection a)) →
      ∀ (n : ℕ) (pos : Fin n ≃ {α // b.IsPos α}),
      (∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) →
      CommutatorRelations b W u u' (fun k => (pos k : J))

/-- **Negative simple relations of Weyl families over a local ring.** In the setting of
`LocalSplitWeylCommutatorStatement`, right translation by the points `u_{-a}(-1)`, for simple
`a`, transfers relations between big-cell points of the two Weyl families
(`NegSimpleRelations`). -/
def LocalSplitWeylNegSimpleStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I] [DecidableEq I]
    (J : Type u) (G H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom],
    IsReductive G → IsReductive H →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H),
      IsClosedSubgroup i → IsClosedSubgroup i' →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i' →
      ∀ (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P → IsFibrewiseRootDatumOf I H i' P →
      ∀ (b : P.Base) (W : ∀ α, SimpleWord P b α), IsDescendingWords P b W →
      ∀ (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)),
      (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
        IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))) →
      (∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a)) →
      (∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a) ∧
        IsRootParametrization i' (P.root (P.reflectionPerm a a)) (u' (P.reflectionPerm a a))) →
      (∀ a ∈ b.support, IsWeylPoint i' (rootWeylPoint P u' a) (P.reflection a)) →
      ∀ (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α}),
      (∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) →
      NegSimpleRelations P
        (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
        (cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) b u u'

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- **The common-torus case.** -/
theorem nonempty_iso_of_commonTorus_local (h1 : LocalSplitSimpleRootGroupLocalStatement.{u})
    (h2 : LocalSplitWeylCommutatorStatement.{u}) (h3 : LocalSplitWeylNegSimpleStatement.{u})
    [IsLocalRing R] (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} (hi : IsClosedSubgroup i)
    (hi' : IsClosedSubgroup i')
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i')
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hP' : IsFibrewiseRootDatumOf I H i' P) : Nonempty (G ≅ H) := by
  classical
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  have : Fintype J := Fintype.ofFinite J
  obtain ⟨b⟩ := Langlands.LinearAlgebra.RootDatumBase.nonempty_base P
  obtain ⟨u, hu, hw⟩ := h1 R G hG I i hi hmax J P hP b
  obtain ⟨u', hu', hw'⟩ := h1 R H hH I i' hi' hmax' J P hP' b
  let W : ∀ α, SimpleWord P b α := descWord P b
  have hD : IsDescendingWords P b W := isDescendingWords_descWord P b
  have hW : ∀ a ∈ b.support, (W a).simple = a ∧ (W a).word = [] := hD.1
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  obtain ⟨pos, hmono⟩ := exists_equiv_monotone (fun α : {α // b.IsPos α} => b.height (α : J))
  have hru : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) := fun a ha => (hu a ha).1
  have hru' : ∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a) :=
    fun a ha => (hu' a ha).1
  obtain ⟨ψ, -⟩ := localSplitCommutatorLawIsomorphism R I J G H hG hH i i' hmax hmax' P hP hP' b
    W hW u u' hru hw hru' hw' _ _ neg pos hmono
    (h2 R I J G H hG hH i i' hi hi' hmax hmax' P hP hP' b W hD u u' hu hw hu' hw' _ pos hmono)
    (h3 R I J G H hG hH i i' hi hi' hmax hmax' P hP hP' b W hD u u' hu hw hu' hw' _ _ neg pos
      hmono)
  exact ⟨ψ⟩

end LocalSplitCell

/-- The local split Isomorphism Theorem follows from Weyl normalization over local rings, the
commutator relations and the negative simple relations of Weyl families. -/
def LocalSplitWeylRelationsReductionStatement : Prop :=
  LocalSplitSimpleRootGroupLocalStatement.{u} → LocalSplitWeylCommutatorStatement.{u} →
    LocalSplitWeylNegSimpleStatement.{u} → LocalSplitIsomorphismTheoremStatement.{u}

/-- **The Isomorphism Theorem over a local ring** from Weyl normalization, the commutator
relations and the negative simple relations of Weyl families. -/
theorem localSplitIsomorphismTheorem_of_weylRelations
    (h1 : LocalSplitSimpleRootGroupLocalStatement.{u})
    (h2 : LocalSplitWeylCommutatorStatement.{u}) (h3 : LocalSplitWeylNegSimpleStatement.{u}) :
    LocalSplitIsomorphismTheoremStatement.{u} := by
  intro R _ _ G H _ _ hG hH I I' _ _ i i' hi hi' hmax hmax' J J' P Q hP hQ ⟨e⟩
  classical
  exact nonempty_iso_of_commonTorus_local h1 h2 h3 hG hH hi
    (isClosedSubgroup_precompTorus e.weightEquiv hi') hmax
    (isFibrewiseMaximalTorus_precompTorus e.weightEquiv hmax') hP
    (isFibrewiseRootDatumOf_precompTorus hP hQ e)

/-- The reduction of the local split Isomorphism Theorem to the three statements. -/
theorem localSplitWeylRelationsReduction : LocalSplitWeylRelationsReductionStatement.{u} :=
  localSplitIsomorphismTheorem_of_weylRelations

end Langlands.GroupScheme

import Langlands.Representation.Aubert.General.SupportCategorySums
import Langlands.Representation.Aubert.General.InducedCuspidalSupportCategoryStatement
import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingStatement
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Category.FiniteGenerationExhaustion

/-! # Splitting a smooth representation along disjoint support categories -/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uG uV uK uK'

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The image of a composite is an actual quotient of the image of its first
factor. -/
theorem isSubquotient_image_comp {X Y Z : SmoothRep.{0, uG, uV} ℂ G}
    (h : X ⟶ Y) (g : Y ⟶ Z) : IsSubquotient (image (h ≫ g)) (image h) := by
  have hr : (hom (imageι h ≫ g)).range = (hom (h ≫ g)).range := by
    apply Subrepresentation.toSubmodule_injective
    ext z
    constructor
    · rintro ⟨⟨y, x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨hom h x, x, rfl⟩, rfl⟩
  have e : image (imageι h ≫ g) = image (h ≫ g) :=
    congrArg (fun S => subrepresentation Z S) hr
  rw [← e]
  exact (image_isQuotient (imageι h ≫ g)).isSubquotient

/-- An invariant submodule without irreducible actual subquotients is zero. -/
theorem eq_bot_of_forall_not_isSubquotient {E : SmoothRep.{0, uG, uV} ℂ G}
    (N : Subrepresentation E.representation)
    (hN : ∀ π : SmoothRep.{0, uG, uV} ℂ G, π.IsIrreducible →
      ¬ IsSubquotient π (subrepresentation E N)) : N = ⊥ := by
  by_contra hne
  have hne' : N.toSubmodule ≠ ⊥ := fun h' =>
    hne (Subrepresentation.toSubmodule_injective h')
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  have : Nontrivial (subrepresentation E N) :=
    ⟨⟨(⟨v, hv⟩ : N.toSubmodule), 0, fun h' => hv0 (congrArg Subtype.val h')⟩⟩
  obtain ⟨π, hπ, hπN⟩ :=
    exists_isIrreducible_isSubquotient_of_nontrivial (subrepresentation E N)
  exact hN π hπ hπN

/-- Renard, Lemme A.IX, in the form used in the proof of Théorème VI.7.2: let
`p` and `p'` be endomorphisms of `D` with `p + p' = 1`, such that no irreducible
object is a subquotient of both images in the sense of the two predicates.
Then the image of every intertwiner `f : E → D` is stable under `p`. -/
theorem mem_range_of_splitting {E D : SmoothRep.{0, uG, uV} ℂ G} (f : E ⟶ D)
    (p p' : D ⟶ D) (hpp' : ∀ d, hom p d + hom p' d = d)
    (𝒜 ℬ : SmoothRep.{0, uG, uV} ℂ G → Prop)
    (hA : ∀ π : SmoothRep.{0, uG, uV} ℂ G, π.IsIrreducible →
      IsSubquotient π (image p) → 𝒜 π)
    (hB : ∀ π : SmoothRep.{0, uG, uV} ℂ G, π.IsIrreducible →
      IsSubquotient π (image p') → ℬ π)
    (hAB : ∀ π : SmoothRep.{0, uG, uV} ℂ G, π.IsIrreducible → 𝒜 π → ℬ π → False)
    (v : E) : hom p (hom f v) ∈ (hom f).range := by
  let W := (hom f).range
  let q := mkQ D W
  have hq0 : ∀ x, hom q (hom f x) = 0 := fun x =>
    (Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr ⟨x, rfl⟩
  have hφ : ∀ x, hom ((f ≫ p) ≫ q) x = - hom ((f ≫ p') ≫ q) x := by
    intro x
    have h2 := congrArg (hom q) (hpp' (hom f x))
    rw [map_add, hq0] at h2
    exact eq_neg_of_add_eq_zero_left h2
  have hrange : (hom ((f ≫ p) ≫ q)).range = (hom ((f ≫ p') ≫ q)).range := by
    apply Subrepresentation.toSubmodule_injective
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      change hom ((f ≫ p') ≫ q) (-x) = hom ((f ≫ p) ≫ q) x
      rw [map_neg, hφ]
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      change hom ((f ≫ p) ≫ q) (-x) = hom ((f ≫ p') ≫ q) x
      rw [map_neg, hφ, neg_neg]
  by_contra hv
  have hne : hom ((f ≫ p) ≫ q) v ≠ 0 := by
    intro h0
    exact hv ((Submodule.Quotient.mk_eq_zero W.toSubmodule).mp h0)
  have : Nontrivial (image ((f ≫ p) ≫ q)) :=
    ⟨⟨⟨hom ((f ≫ p) ≫ q) v, v, rfl⟩, 0, fun h' => hne (congrArg Subtype.val h')⟩⟩
  obtain ⟨π, hπ, hπφ⟩ :=
    exists_isIrreducible_isSubquotient_of_nontrivial (image ((f ≫ p) ≫ q))
  have hle : ∀ p₀ : D ⟶ D, (hom (f ≫ p₀)).range ≤ (hom p₀).range := by
    rintro p₀ _ ⟨x, rfl⟩
    exact ⟨hom f x, rfl⟩
  have hA' : 𝒜 π := by
    apply hA π hπ
    exact smoothSubquotientTransitivity ℂ G _ _ _
      (smoothSubquotientTransitivity ℂ G _ _ _ hπφ (isSubquotient_image_comp (f ≫ p) q))
      (IsSubrepresentation.isSubquotient
        ⟨subrepresentationInclusion (hle p), subrepresentationInclusion_injective _⟩)
  have hπφ' : IsSubquotient π (image ((f ≫ p') ≫ q)) := by
    have e : image ((f ≫ p) ≫ q) = image ((f ≫ p') ≫ q) :=
      congrArg (fun S => subrepresentation (quotient D W) S) hrange
    rw [← e]
    exact hπφ
  have hB' : ℬ π := by
    apply hB π hπ
    exact smoothSubquotientTransitivity ℂ G _ _ _
      (smoothSubquotientTransitivity ℂ G _ _ _ hπφ' (isSubquotient_image_comp (f ≫ p') q))
      (IsSubrepresentation.isSubquotient
        ⟨subrepresentationInclusion (hle p'), subrepresentationInclusion_injective _⟩)
  exact hAB π hπ hA' hB'

section DirectSum

variable {κ : Type uK} [DecidableEq κ] (A : κ → SmoothRep.{0, uG, max uK uV} ℂ G)

omit [DecidableEq κ] in
private theorem filter_lmap (Q : κ → Prop) [DecidablePred Q] (g : G)
    (y : DirectSum κ fun K => A K) :
    DFinsupp.filter Q (DirectSum.lmap (fun i => (A i).representation g) y) =
      DirectSum.lmap (fun i => (A i).representation g) (DFinsupp.filter Q y) := by
  apply DFinsupp.ext
  intro K
  rw [DFinsupp.filter_apply, DirectSum.lmap_apply, DirectSum.lmap_apply,
    DFinsupp.filter_apply]
  split_ifs <;> simp

/-- The actual equivariant projection of a finite direct sum onto the summands
whose index satisfies `Q`, killing the other summands. -/
def directSumFilter (Q : κ → Prop) [DecidablePred Q] : directSum A ⟶ directSum A :=
  ofHom {
    toLinearMap := DFinsupp.filterLinearMap ℂ (fun K => A K) Q
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact filter_lmap A Q g x }

/-- The two complementary filters add up to the identity. -/
theorem directSumFilter_add_not (Q : κ → Prop) [DecidablePred Q] (x : directSum A) :
    hom (directSumFilter A Q) x + hom (directSumFilter A fun K => ¬ Q K) x = x :=
  DFinsupp.filter_add_filter_not (β := fun K => A K) x Q

/-- The filters along the fibres of a map whose values lie in `s` add up to the
identity. -/
theorem sum_directSumFilter_fiber {κ' : Type uK'} [DecidableEq κ'] (c : κ → κ')
    (s : Finset κ') (hs : ∀ K, c K ∈ s) (x : directSum A) :
    ∑ I ∈ s, hom (directSumFilter A fun K => c K = I) x = x := by
  have key : ∀ y : DirectSum κ (fun K => A K),
      ∑ I ∈ s, DFinsupp.filter (fun K => c K = I) y = y := by
    intro y
    apply DFinsupp.ext
    intro K
    rw [DFinsupp.finsetSum_apply]
    simp only [DFinsupp.filter_apply]
    rw [Finset.sum_ite_eq]
    simp [hs K]
  exact key x

/-- The direct-sum carrier read as the carrier of the smooth direct sum. -/
private def toCarrier (y : DirectSum κ fun K => A K) : directSum A := y

/-- The image of a filter lies in the invariant sum of the selected summands. -/
theorem range_directSumFilter_le (Q : κ → Prop) [DecidablePred Q] :
    (hom (directSumFilter A Q)).range ≤
      ⨆ K : {K : κ // Q K}, (hom (directSumι A K.val)).range := by
  have key : ∀ y : DirectSum κ (fun K => A K), toCarrier A (DFinsupp.filter Q y) ∈
      (⨆ K : {K : κ // Q K}, (hom (directSumι A K.val)).range).toSubmodule := by
    intro y
    rw [Langlands.Subrepresentation.toSubmodule_iSup]
    induction y using DirectSum.induction_on with
    | zero =>
      rw [DFinsupp.filter_zero]
      exact Submodule.zero_mem _
    | of K v =>
      by_cases hK : Q K
      · have e : (DFinsupp.filter Q (DirectSum.of (fun K => A K) K v) :
            DirectSum κ fun K => A K) = DirectSum.of (fun K => A K) K v :=
          DFinsupp.filter_single_pos (β := fun K => A K) K v hK
        rw [e]
        exact Submodule.mem_iSup_of_mem (⟨K, hK⟩ : {K : κ // Q K}) ⟨v, rfl⟩
      · have e : (DFinsupp.filter Q (DirectSum.of (fun K => A K) K v) :
            DirectSum κ fun K => A K) = 0 :=
          DFinsupp.filter_single_neg (β := fun K => A K) K v hK
        rw [e]
        exact Submodule.zero_mem _
    | add x y hx hy =>
      rw [DFinsupp.filter_add]
      exact Submodule.add_mem _ hx hy
  rintro _ ⟨x, rfl⟩
  exact key x

/-- An irreducible subquotient of the image of a filter is a subquotient of one
of the selected summands. -/
theorem exists_isSubquotient_of_isSubquotient_image_directSumFilter
    (Q : κ → Prop) [DecidablePred Q] {π : SmoothRep.{0, uG, max uK uV} ℂ G}
    (hπ : π.IsIrreducible) (h : IsSubquotient π (image (directSumFilter A Q))) :
    ∃ K, Q K ∧ IsSubquotient π (A K) := by
  have h1 : IsSubquotient π (subrepresentation (directSum A)
      (⨆ K : {K : κ // Q K}, (hom (directSumι A K.val)).range)) :=
    smoothSubquotientTransitivity ℂ G _ _ _ h
      (IsSubrepresentation.isSubquotient
        ⟨subrepresentationInclusion (range_directSumFilter_le A Q),
          subrepresentationInclusion_injective _⟩)
  obtain ⟨⟨K, hK⟩, hπK⟩ := irreducibleSubquotient_iSup hπ _ h1
  exact ⟨K, hK, smoothSubquotientTransitivity ℂ G _ _ _ hπK
    (image_isQuotient (directSumι A K)).isSubquotient⟩

end DirectSum

end Langlands.SmoothRep

namespace Langlands.Aubert.General

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {ι : Type uG} [Fintype ι]
  {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)} {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}

omit [Fintype ι] in
/-- Renard, Théorème VI.5.4, read on support categories: an irreducible object
lying in `Alg({I})` and in `Alg({J})` forces `I` and `J` to be associated. The
inputs are the association of cuspidal data, transport of inside-Levi
cuspidality along association, and inversion and composition of association
representatives. -/
theorem exists_isAssociate_of_isInSupportCategory
    (hassoc : CuspidalSupportAssociationTarget.{uG, uG, uV} P M U h hU hM hL IsAssociate)
    (hconjCusp : ∀ (I J : Finset ι) (n : G)
      (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n →
      ∀ σ : SmoothRep.{0, uG, max uG uV} ℂ (M I),
        IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
        IsLeviCuspidal P M U hU J (hM J) (hL J) ((conjugationFunctor n hn).obj σ))
    (hinv : ∀ (I J : Finset ι) (n : G), IsAssociate I J n → IsAssociate J I n⁻¹)
    (hcomp : ∀ (I K J : Finset ι) (n m : G),
      IsAssociate I K n → IsAssociate K J m → IsAssociate I J (m * n))
    {I J : Finset ι} {π : SmoothRep.{0, uG, max uG uV} ℂ G} (hπ : π.IsIrreducible)
    (hπI : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) π)
    (hπJ : IsInSupportCategory P M U h hU IsAssociate J (hM J) (hL J) π) :
    ∃ n, IsAssociate I J n := by
  have hππ : SmoothRep.IsSubquotient π π :=
    SmoothRep.isSubquotient_iff_exists.mpr
      ⟨π, 𝟙 π, 𝟙 π, fun _ _ hxy => hxy, fun x => ⟨x, rfl⟩⟩
  obtain ⟨J₁, n, hn, hIJ₁, σ, hσ, hcσ, hπσ⟩ := hπI π hπ hππ
  obtain ⟨J₂, m, hm, hJJ₂, σ', hσ', hcσ', hπσ'⟩ := hπJ π hπ hππ
  obtain ⟨l, -, hJ₁J₂, -⟩ := hassoc π hπ J₁ J₂ ((conjugationFunctor n hn).obj σ)
    ((conjugationFunctor m hm).obj σ')
    ((Langlands.isIrreducible_comp_continuousMulEquiv_iff σ.representation
      (conjugationEquiv n hn)).mpr hσ)
    (hconjCusp I J₁ n hn hIJ₁ σ hcσ)
    ((Langlands.isIrreducible_comp_continuousMulEquiv_iff σ'.representation
      (conjugationEquiv m hm)).mpr hσ')
    (hconjCusp J J₂ m hm hJJ₂ σ' hcσ')
    hπσ hπσ'
  exact ⟨m⁻¹ * (l * n),
    hcomp I J₂ J (l * n) m⁻¹ (hcomp I J₁ J₂ n l hIJ₁ hJ₁J₂) (hinv J J₂ m hJJ₂)⟩

/-- Renard, Théorème VI.7.2, grouped by an equivalence relation on the
standard index sets: if the support categories are invariant along the
relation, no irreducible object lies in two support categories of inequivalent
index sets, every normalized induction of an inside-Levi cuspidal object lies
in the support category of its index set, and every smooth object embeds into
a finite sum of such inductions, then every smooth object is the internal
direct sum of members of the support categories. -/
theorem supportCategoryDecomposition_of_inducedEmbedding (r : Setoid (Finset ι))
    (hInv : ∀ I J, r.r I J → ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
      IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E →
        IsInSupportCategory P M U h hU IsAssociate J (hM J) (hL J) E)
    (hDisj : ∀ I J (π : SmoothRep.{0, uG, max uG uV} ℂ G), π.IsIrreducible →
      IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) π →
      IsInSupportCategory P M U h hU IsAssociate J (hM J) (hL J) π → r.r I J)
    (hInd : InducedCuspidalSupportCategoryTarget.{uG, uG, uV} P M U h hU hM hL IsAssociate)
    (hEmb : FiniteCuspidalInducedEmbeddingTarget.{uG, uG, max uG uV} P M U h hU hM hL) :
    SupportCategoryDecompositionTarget.{uG, uG, uV} P M U h hU hM hL IsAssociate := by
  let : DecidableEq (Finset ι) := Classical.decEq _
  intro E
  obtain ⟨τ, hτ, f, hf⟩ := hEmb E
  let A : Finset ι → SmoothRep.{0, uG, max uG uV} ℂ G := fun K =>
    (normalizedInductionFunctor.{uG, max uG uV} (h K) (hU K)).obj (τ K)
  let F : E ⟶ SmoothRep.directSum A := SmoothRep.ofHom f
  -- representatives of the classes
  let rep : Finset ι → Finset ι := fun I => (Quotient.mk r I).out
  have hrep : ∀ I, r.r (rep I) I := fun I =>
    Quotient.exact (Quotient.out_eq (Quotient.mk r I))
  have hrep_eq : ∀ I J, r.r I J → rep I = rep J := fun I J hIJ =>
    congrArg Quotient.out (Quotient.sound hIJ)
  have hrep_rep : ∀ I, rep (rep I) = rep I := fun I => hrep_eq _ _ (hrep I)
  have hsep : ∀ (I J : Finset ι) (π : SmoothRep.{0, uG, max uG uV} ℂ G), π.IsIrreducible →
      rep I = I → rep J = J → J ≠ I →
      IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) π →
      IsInSupportCategory P M U h hU IsAssociate J (hM J) (hL J) π → False := by
    intro I J π hπ hI hJ hJI hπI hπJ
    apply hJI
    calc J = rep J := hJ.symm
      _ = rep I := (hrep_eq I J (hDisj I J π hπ hπI hπJ)).symm
      _ = I := hI
  -- the summands
  let S : Finset ι → Subrepresentation E.representation := fun I =>
    if rep I = I then supportSubrepresentationSum P M U h hU IsAssociate I (hM I) (hL I) E
    else ⊥
  have hSrep : ∀ I, rep I = I →
      S I = supportSubrepresentationSum P M U h hU IsAssociate I (hM I) (hL I) E :=
    fun I hI => ite_eq_left_of_eq_true _ _ (eq_true hI)
  have hSnon : ∀ I, ¬ rep I = I → S I = ⊥ := fun I hI =>
    ite_eq_right_of_eq_false _ _ (eq_false hI)
  have hS : ∀ I, IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I)
      (subrepresentation E (S I)) := by
    intro I
    by_cases hI : rep I = I
    · rw [hSrep I hI]
      exact isInSupportCategory_supportSubrepresentationSum
    · rw [hSnon I hI]
      intro π hπ hπS
      exact absurd hπS (not_irreducibleSubquotient_bot hπ)
  -- constituents of the filtered parts of the direct sum
  have hAlg : ∀ (Q : Finset ι → Prop) [DecidablePred Q]
      (π : SmoothRep.{0, uG, max uG uV} ℂ G), π.IsIrreducible →
      IsSubquotient π (image (directSumFilter A Q)) →
        ∃ K, Q K ∧ IsInSupportCategory P M U h hU IsAssociate (rep K) (hM (rep K))
          (hL (rep K)) π := by
    intro Q _ π hπ hπQ
    obtain ⟨K, hK, hπK⟩ :=
      exists_isSubquotient_of_isSubquotient_image_directSumFilter A Q hπ hπQ
    exact ⟨K, hK, hInv K (rep K) (r.iseqv.symm (hrep K)) π
      ((hInd K (τ K) (hτ K)).of_isSubquotient hπK)⟩
  refine ⟨S, hS, ?_⟩
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · -- independence, from disjointness of the support categories
    rw [iSupIndep_def]
    intro I
    rw [disjoint_iff]
    have key : S I ⊓ ⨆ J : {J : Finset ι // J ≠ I}, S J.val = ⊥ := by
      apply eq_bot_of_forall_not_isSubquotient
      intro π hπ hπN
      have hπI : IsSubquotient π (subrepresentation E (S I)) :=
        smoothSubquotientTransitivity ℂ G _ _ _ hπN
          (IsSubrepresentation.isSubquotient
            ⟨subrepresentationInclusion inf_le_left, subrepresentationInclusion_injective _⟩)
      have hπT : IsSubquotient π
          (subrepresentation E (⨆ J : {J : Finset ι // J ≠ I}, S J.val)) :=
        smoothSubquotientTransitivity ℂ G _ _ _ hπN
          (IsSubrepresentation.isSubquotient
            ⟨subrepresentationInclusion inf_le_right, subrepresentationInclusion_injective _⟩)
      obtain ⟨⟨J, hJI⟩, hπJ⟩ := irreducibleSubquotient_iSup hπ _ hπT
      by_cases hI : rep I = I
      · by_cases hJ : rep J = J
        · exact hsep I J π hπ hI hJ hJI ((hS I).of_isSubquotient hπI)
            ((hS J).of_isSubquotient hπJ)
        · rw [hSnon J hJ] at hπJ
          exact not_irreducibleSubquotient_bot hπ hπJ
      · rw [hSnon I hI] at hπI
        exact not_irreducibleSubquotient_bot hπ hπI
    have h2 : (⨆ (J : Finset ι) (_ : J ≠ I), (S J).toSubmodule) =
        (⨆ J : {J : Finset ι // J ≠ I}, S J.val).toSubmodule := by
      rw [Langlands.Subrepresentation.toSubmodule_iSup, iSup_subtype']
    rw [h2]
    exact congrArg Subrepresentation.toSubmodule key
  · -- spanning, from the embedding and the splitting lemma
    rw [eq_top_iff]
    intro v _
    let reps : Finset (Finset ι) := Finset.univ.filter fun I => rep I = I
    have hreps : ∀ K, rep K ∈ reps := fun K =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrep_rep K⟩
    have hcomp : ∀ I : Finset ι, ∃ e : E, e ∈ (S I).toSubmodule ∧
        (rep I = I → hom F e = hom (directSumFilter A fun K => rep K = I) (hom F v)) := by
      intro I
      by_cases hI : rep I = I
      · have hA : ∀ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible →
            IsSubquotient π (image (directSumFilter A fun K => rep K = I)) →
              IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) π := by
          intro π hπ hπQ
          obtain ⟨K, hK, hπK⟩ := hAlg _ π hπ hπQ
          rw [hK] at hπK
          exact hπK
        obtain ⟨e, he⟩ := mem_range_of_splitting F (directSumFilter A fun K => rep K = I)
          (directSumFilter A fun K => ¬ rep K = I) (directSumFilter_add_not A _)
          (fun π => IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) π)
          (fun π => ∃ K, ¬ rep K = I ∧
            IsInSupportCategory P M U h hU IsAssociate (rep K) (hM (rep K)) (hL (rep K)) π)
          hA (fun π hπ hπQ => hAlg _ π hπ hπQ)
          (fun π hπ hπI ⟨K, hK, hπK⟩ => hsep I (rep K) π hπ hI (hrep_rep K) hK hπI hπK) v
        refine ⟨e, ?_, fun _ => he⟩
        rw [hSrep I hI]
        have hX : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I)
            (subrepresentation E (subrepresentationPreimage F
              (hom (directSumFilter A fun K => rep K = I)).range)) := by
          intro π hπ hπX
          exact hA π hπ (smoothSubquotientTransitivity ℂ G _ _ _ hπX
            (IsSubrepresentation.isSubquotient
              ⟨subrepresentationPreimageMap F _,
                subrepresentationPreimageMap_injective F _ hf⟩)) π hπ
            (IsSubrepresentation.isSubquotient ⟨𝟙 π, fun _ _ hxy => hxy⟩)
        exact le_supportSubrepresentationSum hX ⟨hom F v, he.symm⟩
      · exact ⟨0, Submodule.zero_mem _, fun h' => absurd h' hI⟩
    choose e he using hcomp
    have hsum : hom F v = hom F (∑ I ∈ reps, e I) := by
      rw [map_sum]
      conv_lhs => rw [← sum_directSumFilter_fiber A rep reps hreps (hom F v)]
      apply Finset.sum_congr rfl
      intro I hI
      exact ((he I).2 (Finset.mem_filter.mp hI).2).symm
    have hv : v = ∑ I ∈ reps, e I := hf hsum
    rw [hv]
    exact Submodule.sum_mem _ fun I _ =>
      Submodule.mem_iSup_of_mem (p := fun I => (S I).toSubmodule) I (he I).1

end Langlands.Aubert.General

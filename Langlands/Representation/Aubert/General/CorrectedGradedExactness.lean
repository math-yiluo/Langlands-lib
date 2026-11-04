import Langlands.Representation.Aubert.General.CorrectedDegreeFiltration
import Langlands.Representation.Aubert.General.CorrectedFiltrationStatements
import Langlands.Representation.Aubert.General.CorrectedGradedContraction

/-!
# Exactness of the graded Jacquet pieces of the corrected filtration

Let `Lo` and `Up` be subdiagrams of the actual Jacquet diagram whose members are
the `i`-th and `(i+1)`-st steps of the corrected support filtration. Assuming
the two graded targets of `CorrectedFiltrationStatements` and the actual Levi
Weyl identification, the graded piece `Lo.quotientDiagram Up` is exact strictly
before `|S| - |I|`, and its degree-zero differential is injective when
`0 < |S| - |I|`. Specializing to the actual support steps and lifting through
the finite support filtration under a Bruhat cover gives the same exactness for
the actual Jacquet diagram, and, given cardinality and support invariance under
association, for every associated Jacquet diagram. The predicate
`Diagram.IsExactBefore D n` bundles the two conclusions: exactness strictly
before `n` and degree-zero injectivity when `0 < n`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.CutComplex.Diagram

universe uD uE

variable {κ : Type uD} [LinearOrder κ] [Fintype κ]

/-- A signed cut diagram is exact strictly before degree `n`: the image of the
degree-`k` differential is the kernel of the degree-`(k+1)` differential
whenever `k + 1 < n`, and the degree-zero differential is injective when
`0 < n`. -/
def IsExactBefore (D : Diagram.{uD, uE} κ) (n : ℕ) : Prop :=
  (∀ k, k + 1 < n →
    LinearMap.range (D.degreeDifferential k) = LinearMap.ker (D.degreeDifferential (k + 1))) ∧
  (0 < n → Function.Injective (D.degreeDifferential 0))

end Langlands.Aubert.CutComplex.Diagram

namespace Langlands.Aubert.General.JacquetComplex

open Langlands.Group.RelativeWeylIndexing
open Langlands.Aubert.CutComplex

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J)}
  {hclosed : ∀ J, IsClosed (U J : Set G)}
  {hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J)}
  {hP : Monotone P} {hU : Antitone U}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}
  {T : Subgroup G} [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} {cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T)}
  {A : SmoothRep.{0, uG, max uG uV} ℂ G} {I : Finset ι} {i : ℕ}
  {Lo Up : (jacquetDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU A I).Subdiagram}

/-- Case analysis of one graded piece. Either the two steps agree in every
coordinate, or the piece has a Boolean contraction over the survivors at the
`i`-th length-ordered element `w`, for a standard `K` with
`W_K = w W_I w⁻¹`, and some cut set survives. -/
theorem graded_cases {Φ : Prop}
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (hLo : ∀ s x, x ∈ Lo.obj s ↔
      x ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s i).toSubmodule)
    (hUp : ∀ s x, x ∈ Up.obj s ↔
      x ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s (i + 1)).toSubmodule)
    (caseA : (∀ s, ∀ x ∈ Up.obj s, x ∈ Lo.obj s) → Φ)
    (caseB : ∀ (K s₀ : Finset ι) (X : Type (max uG uV)) [AddCommGroup X] [Module ℂ X],
      (∀ a, a ∈ standardSubgroup cs K ↔
        (Support.rankOrderedElement cs.length i hi)⁻¹ * a *
          Support.rankOrderedElement cs.length i hi ∈ standardSubgroup cs I) →
      Diagram.Subdiagram.Survives cs I K (Support.rankOrderedElement cs.length i hi) s₀ →
      Lo.BooleanContraction Up
        (Diagram.Subdiagram.Survives cs I K (Support.rankOrderedElement cs.length i hi)) X →
      Φ) : Φ := by
  set w := Support.rankOrderedElement cs.length i hi with hw
  have hle_of_eq : ∀ s,
      CorrectedFiltration.step P M U h hclosed T cs A I s (i + 1) =
        CorrectedFiltration.step P M U h hclosed T cs A I s i →
      ∀ x ∈ Up.obj s, x ∈ Lo.obj s := by
    intro s heq x hx
    rw [hLo, ← heq]
    exact (hUp s x).mp hx
  by_cases hall : ∀ s, CorrectedFiltration.step P M U h hclosed T cs A I s (i + 1) =
      CorrectedFiltration.step P M U h hclosed T cs A I s i
  · exact caseA fun s => hle_of_eq s (hall s)
  push Not at hall
  obtain ⟨s₀, hs₀⟩ := hall
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (w⁻¹)
  obtain ⟨K, hKs₀, hK⟩ := hvan I A hA s₀ i hi hs₀ m hm
  have hconj := mem_standardSubgroup_iff_of_leviConj hLevi m hm hK
  have hmin₀ : IsMinimal cs (Finset.univ \ s₀) I w := by
    by_contra hn
    exact hs₀ (CorrectedFiltration.step_succ_eq A I s₀ i hi hn)
  obtain ⟨β, hsurj, hker, hnat⟩ := htrans I A hA i hi m hm K hK
  refine caseB K s₀ _ hconj ⟨hKs₀, hmin₀⟩
    { coeff := fun s hs =>
        (SmoothRep.hom (β s hs.1 hs.2)).toLinearMap.comp
          (Submodule.inclusion fun x hx => (hUp s x).mp hx)
      coeff_surjective := ?_
      coeff_eq_zero_iff := ?_
      coeff_natural := ?_
      inactive := ?_ }
  · intro s hs y
    obtain ⟨⟨x, hx⟩, rfl⟩ := hsurj s hs.1 hs.2 y
    exact ⟨⟨x, (hUp s x).mpr hx⟩, rfl⟩
  · intro s hs x
    exact (hker s hs.1 hs.2 ⟨x.1, (hUp s x.1).mp x.2⟩).trans (hLo s x.1).symm
  · intro s t hst hs ht x
    exact hnat s t hst hs.1 hs.2 ht.1 ht.2 x.1 ((hUp s x.1).mp x.2)
  · intro s hns
    by_cases hmin : IsMinimal cs (Finset.univ \ s) I w
    · have hKs : ¬ K ⊆ Finset.univ \ s := fun hKs => hns ⟨hKs, hmin⟩
      by_cases heq : CorrectedFiltration.step P M U h hclosed T cs A I s (i + 1) =
          CorrectedFiltration.step P M U h hclosed T cs A I s i
      · exact hle_of_eq s heq
      · obtain ⟨K', hK's, hK'⟩ := hvan I A hA s i hi heq m hm
        have hKK' : K = K' := eq_of_standardSubgroup_conj cs hconj
          (mem_standardSubgroup_iff_of_leviConj hLevi m hm hK')
        exact absurd (hKK' ▸ hK's) hKs
    · exact hle_of_eq s (CorrectedFiltration.step_succ_eq A I s i hi hmin)

/-- The graded piece is exact strictly before `|S| - |I|`. -/
theorem graded_range_eq_ker
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (hLo : ∀ s x, x ∈ Lo.obj s ↔
      x ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s i).toSubmodule)
    (hUp : ∀ s x, x ∈ Up.obj s ↔
      x ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s (i + 1)).toSubmodule)
    (k : ℕ) (hk : k + 1 < Fintype.card ι - I.card) :
    LinearMap.range ((Lo.quotientDiagram Up).degreeDifferential k) =
      LinearMap.ker ((Lo.quotientDiagram Up).degreeDifferential (k + 1)) :=
  graded_cases hvan htrans hLevi hA hi hLo hUp
    (fun hle => Lo.quotient_exact_of_le Up hle k)
    (fun _ _ _ _ _ hconj hs₀ C =>
      Diagram.Subdiagram.range_eq_ker_of_survives cs hconj hs₀ C k hk)

/-- The degree-zero differential of the graded piece is injective when
`0 < |S| - |I|`. -/
theorem graded_injective_zero
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (hLo : ∀ s x, x ∈ Lo.obj s ↔
      x ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s i).toSubmodule)
    (hUp : ∀ s x, x ∈ Up.obj s ↔
      x ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s (i + 1)).toSubmodule)
    (hpos : 0 < Fintype.card ι - I.card) :
    Function.Injective ((Lo.quotientDiagram Up).degreeDifferential 0) :=
  graded_cases hvan htrans hLevi hA hi hLo hUp
    (fun hle => Lo.quotient_injective_of_le Up hle 0)
    (fun _ _ _ _ _ hconj hs₀ C =>
      Diagram.Subdiagram.injective_zero_of_survives cs hconj hs₀ C hpos)

/-- Each actual graded piece of the corrected support filtration is exact
strictly before `|S| - |I|`. -/
theorem gradedDiagram_range_eq_ker
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (k : ℕ) (hk : k + 1 < Fintype.card ι - I.card) :
    LinearMap.range
        ((gradedDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i).degreeDifferential k) =
      LinearMap.ker
        ((gradedDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i).degreeDifferential
          (k + 1)) :=
  graded_range_eq_ker hvan htrans hLevi hA hi (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) k hk

/-- The degree-zero differential of each actual graded piece is injective when
`0 < |S| - |I|`. -/
theorem gradedDiagram_injective_zero
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (hpos : 0 < Fintype.card ι - I.card) :
    Function.Injective
      ((gradedDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i).degreeDifferential 0) :=
  graded_injective_zero hvan htrans hLevi hA hi (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) hpos

/-- Under a Bruhat cover, the actual Jacquet diagram is exact strictly before
`|S| - |I|`. -/
theorem degreeDifferential_exact_of_targets
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I))
    (k : ℕ) (hk : k + 1 < Fintype.card ι - I.card) :
    LinearMap.range
        ((jacquetDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU A I).degreeDifferential k) =
      LinearMap.ker
        ((jacquetDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU A I).degreeDifferential (k + 1)) :=
  degreeDifferential_exact_of_graded P M U h hclosed hδ hP hU T cs A I hcover k
    fun _ hi => gradedDiagram_range_eq_ker hvan htrans hLevi hA hi k hk

/-- Under a Bruhat cover, the degree-zero differential of the actual Jacquet
diagram is injective when `0 < |S| - |I|`. -/
theorem degreeDifferential_injective_zero_of_targets
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I))
    (hpos : 0 < Fintype.card ι - I.card) :
    Function.Injective
      ((jacquetDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU A I).degreeDifferential 0) :=
  degreeDifferential_injective_of_graded P M U h hclosed hδ hP hU T cs A I hcover 0
    fun _ hi => gradedDiagram_injective_zero hvan htrans hLevi hA hi hpos

/-- The associated graded map of the actual degree filtration, in the
`FiniteFiltered.gradedMap` form, is exact strictly before `|S| - |I|`. -/
theorem gradedDifferential_range_eq_ker
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (k : ℕ) (hk : k + 1 < Fintype.card ι - I.card) :
    LinearMap.range (gradedDifferential.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i k) =
      LinearMap.ker
        (gradedDifferential.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i (k + 1)) :=
  (gradedDifferential_exact_iff P M U h hclosed hδ hP hU T cs A I i k).mpr
    (gradedDiagram_range_eq_ker hvan htrans hLevi hA hi k hk)

/-- The degree-zero associated graded map of the actual degree filtration, in
the `FiniteFiltered.gradedMap` form, is injective when `0 < |S| - |I|`. -/
theorem gradedDifferential_injective_zero
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (hpos : 0 < Fintype.card ι - I.card) :
    Function.Injective
      (gradedDifferential.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i 0) :=
  (gradedDifferential_injective_iff P M U h hclosed hδ hP hU T cs A I i 0).mpr
    (gradedDiagram_injective_zero hvan htrans hLevi hA hi hpos)

/-- For every `J` associated to `I` with conjugate Levi, the actual Jacquet
diagram at `J` is exact strictly before the terminal degree of `I`, provided
association preserves cardinality and the support category, and the Bruhat
cover holds at each such `J`. -/
theorem associated_degreeDifferential_exact_of_targets
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hcard : ∀ (J : Finset ι) (n : G), IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) → J.card = I.card)
    (hsupp : ∀ (J : Finset ι) (n : G), IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
      IsInSupportCategory P M U h hclosed IsAssociate J (hM J) (hL J) A)
    (hcover : ∀ (J : Finset ι) (n : G), IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
      CorrectedFiltration.IsBruhatCover T (P ∅) (P J)) :
    ∀ k, k + 1 < Complex.terminalDegree I →
      ∀ (J : Finset ι) (n : G), IsAssociate I J n →
        (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
        LinearMap.range
            ((jacquetDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU A J).degreeDifferential k) =
          LinearMap.ker
            ((jacquetDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU A J).degreeDifferential
              (k + 1)) := by
  intro k hk J n hn hconj
  refine degreeDifferential_exact_of_targets hvan htrans hLevi (hsupp J n hn hconj)
    (hcover J n hn hconj) k ?_
  rw [hcard J n hn hconj]
  exact hk

/-- For every `J` associated to `I` with conjugate Levi, the degree-zero
differential of the actual Jacquet diagram at `J` is injective when the
terminal degree of `I` is positive, under the same premises. -/
theorem associated_degreeDifferential_injective_zero_of_targets
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hcard : ∀ (J : Finset ι) (n : G), IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) → J.card = I.card)
    (hsupp : ∀ (J : Finset ι) (n : G), IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
      IsInSupportCategory P M U h hclosed IsAssociate J (hM J) (hL J) A)
    (hcover : ∀ (J : Finset ι) (n : G), IsAssociate I J n →
      (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
      CorrectedFiltration.IsBruhatCover T (P ∅) (P J)) :
    0 < Complex.terminalDegree I →
      ∀ (J : Finset ι) (n : G), IsAssociate I J n →
        (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
        Function.Injective
          ((jacquetDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU A J).degreeDifferential 0) := by
  intro hpos J n hn hconj
  refine degreeDifferential_injective_zero_of_targets hvan htrans hLevi (hsupp J n hn hconj)
    (hcover J n hn hconj) ?_
  rw [hcard J n hn hconj]
  exact hpos

/-- Each actual graded piece of the corrected support filtration is exact
before `|S| - |I|` in the sense of `Diagram.IsExactBefore`. -/
theorem gradedDiagram_isExactBefore
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hi : i < (Support.rankOrderedList cs.length).length) :
    (gradedDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i).IsExactBefore
      (Fintype.card ι - I.card) :=
  ⟨fun k hk => gradedDiagram_range_eq_ker hvan htrans hLevi hA hi k hk,
    fun hpos => gradedDiagram_injective_zero hvan htrans hLevi hA hi hpos⟩

/-- Under a Bruhat cover, the actual Jacquet diagram is exact before
`|S| - |I|` in the sense of `Diagram.IsExactBefore`. -/
theorem jacquetDiagram_isExactBefore_of_targets
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I)) :
    (jacquetDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU A I).IsExactBefore
      (Fintype.card ι - I.card) :=
  ⟨fun k hk => degreeDifferential_exact_of_targets hvan htrans hLevi hA hcover k hk,
    fun hpos => degreeDifferential_injective_zero_of_targets hvan htrans hLevi hA hcover hpos⟩

end Langlands.Aubert.General.JacquetComplex

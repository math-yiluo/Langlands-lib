import Langlands.Representation.Aubert.General.CorrectedFiltration
import Langlands.Representation.Aubert.General.SupportCategory

/-!
# Graded targets for the corrected support filtration

Proposition targets for the two representation-theoretic assertions of the
corrected proof of Aubert's Theorem 3.6 (erratum 1996, pp. 4688–4690, with the
Ban–Jantzen 2016 Section 4 repair) about the support filtration `step` of the
normalized Jacquet modules `r_I(E_J)`:

* `CorrectedGradedVanishingTarget`: for `E ∈ Alg({I})`, a nonzero graded piece
  at the `i`-th length-ordered Weyl element `w` forces `w L_I w⁻¹ = L_K` for a
  standard `K ⊆ J`;
* `CorrectedGradedTransitionTarget`: on every surviving grade the graded piece
  is identified with `Ad(w⁻¹)(r_{L_K}(E))` by maps under which the actual
  Jacquet transitions `r_I(φ^J_{J'})` become identity maps.

Nothing is asserted here.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General.CorrectedFiltration

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)
  (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))

/-- Erratum, pp. 4688–4689 (with the Ban–Jantzen double-coset correction): for
`E ∈ Alg({I})`, if the graded piece of `r_I(E_J)` at the `i`-th length-ordered
Weyl element `w` is nonzero, then for every lift `m ∈ N_G(T)` of `w⁻¹` there is a
standard index set `K ⊆ J = S \ s` with `M K = m⁻¹ (M I) m`, that is
`w L_I w⁻¹ = L_K ⊆ L_J`. -/
def CorrectedGradedVanishingTarget : Prop :=
  ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uG uV} ℂ G),
    IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) E →
    ∀ (s : Finset ι) (i : ℕ) (hi : i < (Support.rankOrderedList cs.length).length),
      step P M U h hclosed T cs E I s (i + 1) ≠ step P M U h hclosed T cs E I s i →
      ∀ m : Group.RelativeWeyl.normalizer T,
        (QuotientGroup.mk m : Group.RelativeWeyl.Weyl T) =
          (Support.rankOrderedElement cs.length i hi)⁻¹ →
        ∃ K : Finset ι, K ⊆ Finset.univ \ s ∧
          ∀ x : G, x ∈ M I ↔ (m : G)⁻¹ * x * m ∈ M K

/-- Erratum, pp. 4688–4690 (with the Ban–Jantzen double-coset correction): let
`E ∈ Alg({I})`, let `w` be the `i`-th length-ordered Weyl element, `m ∈ N_G(T)` a
lift of `w⁻¹`, and `K` a standard index set with `M K = m⁻¹ (M I) m`. For every
surviving target `J = S \ s` (`K ⊆ J` and `w` minimal in `W_J w W_I`) there is a
surjective intertwiner `β_s` from the step `i + 1` of `r_I(E_J)` onto
`Ad(w⁻¹)(r_{L_K}(E)) = (conjugationFunctor m hK).obj (r_K E)` whose kernel is the
step `i`, and for surviving `s ⊆ t` the actual Jacquet transition
`r_I(φ^J_{J'})` satisfies `β_t ∘ r_I(φ^J_{J'}) = β_s` on the step `i + 1`. Thus
every surviving graded transition is the identity of `Ad(w⁻¹)(r_{L_K}(E))`. -/
def CorrectedGradedTransitionTarget : Prop :=
  ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uG uV} ℂ G),
    IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) E →
    ∀ (i : ℕ) (hi : i < (Support.rankOrderedList cs.length).length)
      (m : Group.RelativeWeyl.normalizer T),
      (QuotientGroup.mk m : Group.RelativeWeyl.Weyl T) =
        (Support.rankOrderedElement cs.length i hi)⁻¹ →
    ∀ (K : Finset ι) (hK : ∀ x : G, x ∈ M I ↔ (m : G)⁻¹ * x * m ∈ M K),
      ∃ β : ∀ s : Finset ι, K ⊆ Finset.univ \ s →
          Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I
            (Support.rankOrderedElement cs.length i hi) →
          (SmoothRep.subrepresentation
              ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj
                (term P M U h hclosed E s))
              (step P M U h hclosed T cs E I s (i + 1)) ⟶
            (conjugationFunctor (m : G) hK).obj
              ((jacquetFunctor.{uG, max uG uV} (h K) (hclosed K)).obj E)),
        (∀ s hKs hs, Function.Surjective (SmoothRep.hom (β s hKs hs))) ∧
        (∀ s hKs hs (x : SmoothRep.subrepresentation
            ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj
              (term P M U h hclosed E s))
            (step P M U h hclosed T cs E I s (i + 1))),
          SmoothRep.hom (β s hKs hs) x = 0 ↔
            x.1 ∈ (step P M U h hclosed T cs E I s i).toSubmodule) ∧
        (∀ (s t : Finset ι) (hst : s ⊆ t) hKs hs hKt ht
          (x : (jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj
            (term P M U h hclosed E s))
          (hx : x ∈ (step P M U h hclosed T cs E I s (i + 1)).toSubmodule),
          SmoothRep.hom (β t hKt ht)
              ⟨SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).map
                (transition P M U h hclosed hδ hP hU E hst)) x,
                transition_mem_step E I hst (i + 1) hx⟩ =
            SmoothRep.hom (β s hKs hs) ⟨x, hx⟩)

end Langlands.Aubert.General.CorrectedFiltration

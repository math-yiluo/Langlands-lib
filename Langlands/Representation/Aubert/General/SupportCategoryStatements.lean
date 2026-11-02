import Langlands.Representation.Aubert.General.SupportCategory

/-!
# Support-theory targets for the support categories `Alg({I})`

Proposition targets, stated over the generic standard families of
`Langlands.Aubert.General`, for the facts about cuspidal supports that Aubert's
corrected Theorem 3.6 (erratum 1996, p. 4687) and its consequences use:

* existence of a cuspidal support (Renard, Corollaire VI.2.1);
* uniqueness of the cuspidal support up to association (Renard, Théorème VI.5.4);
* invariance of `Alg({I})` under association (erratum, p. 4687);
* detection of irreducible members by a Jacquet module along an associated
  standard Levi (proof of Renard, Théorème VI.5.4);
* detection of zero and of exactness on `Alg({I})` by the Jacquet modules along
  the associated standard Levis (erratum, p. 4687);
* stability of `Alg({I})` under `i_K ∘ r_K` and vanishing of `r_K` when `L_K`
  contains no Levi associated to `L_I` (Renard, VI.5.3 and VI.7.2–VI.7.3);
* the decomposition of every smooth representation into members of the
  categories `Alg({I})` (Renard, VI.7.2).

Throughout, "`L_J` is associated to `L_I` through `n`" means
`IsAssociate I J n` together with `M J = n (M I) n⁻¹`, written
`∀ x, x ∈ M J ↔ n⁻¹ * x * n ∈ M I`, exactly the pair of conditions used by
`IsInSupportCategory`. Hypotheses and conclusions about association always
carry both conditions.

Every target is a `Prop`-valued definition of the data. None is asserted here.
For the rational points of a connected reductive group, with the standard
families and the Weyl association `IsAssociate` of the structural framework,
each target is a theorem of the cited sources.
-/

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

/-- Renard, Corollaire VI.2.1 (printed p. 139), read with Aubert's Notation 1.6:
every irreducible smooth representation of `G` lies in some cuspidal series
`𝔈(I)`, that is, it is a subquotient of `i^G_{L_I}(σ)` for an irreducible cuspidal
`σ` of a standard Levi `L_I`. -/
def CuspidalSeriesExistenceTarget : Prop :=
  ∀ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible →
    ∃ I : Finset ι, IsInCuspidalSeries P M U h hU I (hM I) (hL I) π

/-- Renard, Théorème VI.5.4, (iv) ⇒ (i) (printed pp. 173–174), for standard Levis:
if an irreducible `π` is a subquotient of `i^G_{L_I}(σ)` and of `i^G_{L_{I'}}(σ')`,
with `σ`, `σ'` irreducible cuspidal, then the cuspidal data are associated: some
`n` represents an association of `I` with `I'`, conjugates `L_I` onto `L_{I'}`, and
`σ' ≅ Ad(n)(σ)`. -/
def CuspidalSupportAssociationTarget : Prop :=
  ∀ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible →
    ∀ (I I' : Finset ι) (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I))
      (σ' : SmoothRep.{0, uG, max uG uV} ℂ (M I')),
      σ.IsIrreducible → IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
      σ'.IsIrreducible → IsLeviCuspidal P M U hU I' (hM I') (hL I') σ' →
      SmoothRep.IsSubquotient π ((normalizedInductionFunctor.{uG, max uG uV} (h I) (hU I)).obj σ) →
      SmoothRep.IsSubquotient π
        ((normalizedInductionFunctor.{uG, max uG uV} (h I') (hU I')).obj σ') →
      ∃ (n : G) (hn : ∀ x : G, x ∈ M I' ↔ n⁻¹ * x * n ∈ M I),
        IsAssociate I I' n ∧ Nonempty (σ' ≅ (conjugationFunctor n hn).obj σ)

/-- Erratum, p. 4687: `Alg({I})` depends only on the association class of `L_I`.
If `n` represents an association of `I` with `I'`, every member of `Alg({I})` is a
member of `Alg({I'})`. -/
def SupportCategoryAssociationInvarianceTarget : Prop :=
  ∀ (I I' : Finset ι) (n : G), IsAssociate I I' n →
    (∀ x : G, x ∈ M I' ↔ n⁻¹ * x * n ∈ M I) →
    ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
      IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E →
        IsInSupportCategory P M U h hU IsAssociate I' (hM I') (hL I') E

/-- Proof of Renard, Théorème VI.5.4 (printed p. 174, using Corollaire VI.2.1 and
Proposition VI.5.3 (ii)): an irreducible member of `Alg({I})` has a nonzero
normalized Jacquet module along some standard Levi `L_J` associated to `L_I`. Only
some associated `J` is asserted, not every one. -/
def SupportCategoryIrreducibleJacquetDetectionTarget : Prop :=
  ∀ (I : Finset ι) (π : SmoothRep.{0, uG, max uG uV} ℂ G), π.IsIrreducible →
    IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) π →
      ∃ (J : Finset ι) (n : G), IsAssociate I J n ∧
        (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) ∧
        Nontrivial ((jacquetFunctor.{uG, max uG uV} (h J) (hU J)).obj π)

/-- Erratum, p. 4687 ("par définition de la catégorie `Alg({I})`"), the case of a
single object: a member of `Alg({I})` whose normalized Jacquet modules along all
standard Levis associated to `L_I` vanish is zero. -/
def SupportCategoryZeroDetectionTarget : Prop :=
  ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uG uV} ℂ G),
    IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E →
      (∀ (J : Finset ι) (n : G), IsAssociate I J n →
        (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
        Subsingleton ((jacquetFunctor.{uG, max uG uV} (h J) (hU J)).obj E)) →
      Subsingleton E

/-- Erratum, p. 4687: for a sequence `A → B → C` of smooth representations with
`B ∈ Alg({I})`, exactness at `B` is equivalent to exactness at `r_{L_J}(B)` of the
normalized Jacquet sequences along all standard Levis `L_J` associated to `L_I`. -/
def SupportCategoryExactnessDetectionTarget : Prop :=
  ∀ (I : Finset ι) {A B C : SmoothRep.{0, uG, max uG uV} ℂ G} (f : A ⟶ B) (g : B ⟶ C),
    IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) B →
      (Function.Exact (SmoothRep.hom f) (SmoothRep.hom g) ↔
        ∀ (J : Finset ι) (n : G), IsAssociate I J n →
          (∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
          Function.Exact (SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} (h J) (hU J)).map f))
            (SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} (h J) (hU J)).map g)))

/-- Renard, Théorème VI.7.2 (printed p. 182) and Proposition VI.7.3 (printed
p. 185): `Alg({I})` is stable under `i^G_{L_K} ∘ r^G_{L_K}` for every standard
Levi `L_K`. -/
def SupportCategoryInductionJacquetTarget : Prop :=
  ∀ (I K : Finset ι) (E : SmoothRep.{0, uG, max uG uV} ℂ G),
    IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E →
      IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I)
        ((inductionJacquetFunctor.{uG, uV} (h K) (hU K)).obj E)

/-- Renard, Proposition VI.5.3 (i) (printed p. 173) and Proposition VI.7.3
(printed p. 185): if no standard Levi `L_J` with `J ⊆ K` is associated to `L_I`,
the normalized Jacquet module along `L_K` of every member of `Alg({I})` is zero. -/
def SupportCategoryJacquetVanishingTarget : Prop :=
  ∀ (I K : Finset ι),
    (∀ (J : Finset ι) (n : G), J ⊆ K → IsAssociate I J n →
      ¬ ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) →
    ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
      IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E →
        Subsingleton ((jacquetFunctor.{uG, max uG uV} (h K) (hU K)).obj E)

/-- Renard, Théorème VI.7.2 (Bernstein decomposition, printed p. 182), grouped by
association classes of cuspidal Levis: every smooth representation of `G` is the
internal direct sum of subrepresentations `S I`, indexed by the subsets `I`, with
`S I ∈ Alg({I})`. Uniqueness is not asserted, and summands may be zero. -/
def SupportCategoryDecompositionTarget : Prop :=
  ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
    ∃ S : Finset ι → Subrepresentation E.representation,
      (∀ I, IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I)
        (SmoothRep.subrepresentation E (S I))) ∧
      haveI := Classical.decEq (Finset ι)
      DirectSum.IsInternal fun I => (S I).toSubmodule

end Langlands.Aubert.General

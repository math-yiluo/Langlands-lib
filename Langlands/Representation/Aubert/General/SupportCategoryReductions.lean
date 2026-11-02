import Langlands.Representation.Aubert.General.SupportCategoryStatements
import Langlands.Representation.Category.IrreducibleSubquotientExistence

/-!
# Detection of zero on `Alg({I})` from detection on irreducible members

Normalized Jacquet restriction along a decomposition whose unipotent part is a
limit of compact subgroups is exact, so a subquotient of a representation with
zero Jacquet module has zero Jacquet module. Together with the existence of
irreducible subquotients of nonzero smooth representations, this reduces
`SupportCategoryZeroDetectionTarget` to
`SupportCategoryIrreducibleJacquetDetectionTarget`.
-/

open CategoryTheory

namespace Langlands.Aubert.General

open SmoothRep

universe uI uG uV

section Subquotient

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The inclusion of an invariant subspace and the quotient map onto the
corresponding quotient form an actual short exact sequence. -/
theorem subtype_mkQ_isShortExact (A : SmoothRep.{0, uG, uV} ℂ G)
    (S : Subrepresentation A.representation) :
    IsShortExact (hom (subtype A S)) (hom (mkQ A S)) := by
  refine ⟨subtype_injective A S, mkQ_surjective A S, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr y.2
  · intro hx
    exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).mp hx⟩, rfl⟩

end Subquotient

section Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Subgroup G}

/-- If the normalized Jacquet module of `E` is zero, so is that of every
subquotient of `E`, when `U` is a limit of compact subgroups. -/
theorem jacquet_subsingleton_of_isSubquotient (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    {E π : SmoothRep.{0, uG, uV} ℂ G} (hπ : IsSubquotient π E)
    (hE : Subsingleton ((jacquetFunctor.{uG, uV} h hU).obj E)) :
    Subsingleton ((jacquetFunctor.{uG, uV} h hU).obj π) := by
  obtain ⟨S, T, ⟨e⟩⟩ := hπ
  let r := jacquetFunctor.{uG, uV} h hU
  let B := subrepresentation E S
  have h1 := jacquetFunctor_map_isShortExact h hU hUc (subtype E S) (mkQ E S)
    (subtype_mkQ_isShortExact E S)
  have hB : Subsingleton (r.obj B) := ⟨fun a b => h1.1 (Subsingleton.elim _ _)⟩
  have h2 := jacquetFunctor_map_isShortExact h hU hUc (subtype B T) (mkQ B T)
    (subtype_mkQ_isShortExact B T)
  have hQ : Subsingleton (r.obj (quotient B T)) := ⟨fun a b => by
    obtain ⟨a', rfl⟩ := h2.2.1 a
    obtain ⟨b', rfl⟩ := h2.2.1 b
    rw [Subsingleton.elim a' b']⟩
  have hQ' : Subsingleton (r.obj (subquotient E S T)) := hQ
  let f := r.mapIso e
  have hinv : ∀ x, hom f.inv (hom f.hom x) = x := fun x => by
    have hx : hom (f.hom ≫ f.inv) x = hom (𝟙 (r.obj π)) x := by rw [f.hom_inv_id]
    exact hx
  exact ⟨fun a b => by
    rw [← hinv a, ← hinv b, @Subsingleton.elim _ hQ' (hom f.hom a) (hom f.hom b)]⟩

end Jacquet

section Reduction

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}

/-- Detection of zero on `Alg({I})` follows from detection of irreducible
members, when every `U J` is a limit of compact subgroups: a nonzero member has an
irreducible subquotient, which lies in `Alg({I})` and has a nonzero Jacquet
module along some associated `L_J`, and that module is a subquotient-image of the
Jacquet module of the member. -/
theorem supportCategoryZeroDetection_of_irreducibleJacquetDetection
    (hUc : ∀ J, Jacquet.Localization.IsLimitOfCompactSubgroups (U J))
    (hdet : SupportCategoryIrreducibleJacquetDetectionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate) :
    SupportCategoryZeroDetectionTarget.{uI, uG, uV} P M U h hU hM hL IsAssociate := by
  intro I E hE hvan
  by_contra hne
  rw [not_subsingleton_iff_nontrivial] at hne
  obtain ⟨π, hπ, hπE⟩ := exists_isIrreducible_isSubquotient_of_nontrivial E
  obtain ⟨J, n, hJ, hn, hnt⟩ := hdet I π hπ (hE.of_isSubquotient hπE)
  have hs := jacquet_subsingleton_of_isSubquotient (h J) (hU J) (hUc J) hπE (hvan J n hJ hn)
  exact not_subsingleton_iff_nontrivial.mpr hnt hs

end Reduction

end Langlands.Aubert.General

import Langlands.Representation.Aubert.General.SupportCategorySums
import Langlands.Representation.Aubert.General.DirectedUnions
import Langlands.Representation.Category.FiniteGenerationExhaustion

/-!
# Passage from finitely generated to arbitrary smooth support objects

The actual normalized induction-Jacquet image exhaustion is proved under the
displayed compact-quotient and compact-limit hypotheses. Preservation on all
finitely generated supported inputs remains a separate hypothesis.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

open SmoothRep

universe uI uG uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] {ι : Type uI}

/-- The actual invariant image of a finite invariant span under an endofunctor
of the smooth representation category. -/
def finiteSpanFunctorImage
    (F : SmoothRep.{0, uG, max uG uV} ℂ G ⥤ SmoothRep.{0, uG, max uG uV} ℂ G)
    (E : SmoothRep.{0, uG, max uG uV} ℂ G)
    (s : Finset E.representation.asModule) : Subrepresentation (F.obj E).representation :=
  (hom (F.map (subtype E (finiteSpanSubrepresentation E s)))).range

/-- The actual inclusion images of the finite invariant spans form a directed
family. -/
theorem finiteSpanSubtype_range_directed (E : SmoothRep.{0, uG, max uG uV} ℂ G) :
    Directed (· ≤ ·)
      (fun s => (hom (subtype E (finiteSpanSubrepresentation E s))).range) := by
  intro s t
  obtain ⟨r, hsr, htr⟩ := finiteSpanSubrepresentation_directed E s t
  refine ⟨r, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨⟨v.val, hsr v.property⟩, rfl⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨⟨v.val, htr v.property⟩, rfl⟩

/-- The actual inclusion images of finite invariant spans cover every vector. -/
theorem finiteSpanSubtype_range_cover (E : SmoothRep.{0, uG, max uG uV} ℂ G) :
    ∀ b : E, ∃ s, b ∈ (hom (subtype E (finiteSpanSubrepresentation E s))).range := by
  classical
  intro b
  refine ⟨{E.representation.asModuleEquiv.symm b}, ⟨b, ?_⟩, rfl⟩
  change E.representation.asModuleEquiv.symm b ∈
    Submodule.span (MonoidAlgebra ℂ G)
      (({E.representation.asModuleEquiv.symm b} :
        Finset E.representation.asModule) : Set E.representation.asModule)
  exact Submodule.subset_span (by simp)

variable [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- Every vector of the actual induction-Jacquet object lies in the image of
one finite invariant span, under the displayed topological hypotheses. -/
theorem inductionJacquet_iSup_finiteSpanFunctorImage
    {P₀ M₀ U₀ : Subgroup G} (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
    (hU₀ : IsClosed (U₀ : Set G)) [CompactSpace (Induction.LeftQuotient P₀)]
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U₀)
    (E : SmoothRep.{0, uG, max uG uV} ℂ G) :
    (⨆ s, finiteSpanFunctorImage (inductionJacquetFunctor.{uG, uV} h₀ hU₀) E s) = ⊤ := by
  apply top_unique
  intro f _
  obtain ⟨s, g, hg⟩ :=
    inductionJacquetFunctor_exists_preimage_of_directed_cover.{uG, uV, max uG uV}
      h₀ hU₀ hUc
      (fun s => subrepresentation E (finiteSpanSubrepresentation E s)) E
      (fun s => subtype E (finiteSpanSubrepresentation E s))
      (fun s => subtype_injective E (finiteSpanSubrepresentation E s))
      (finiteSpanSubtype_range_directed E) (finiteSpanSubtype_range_cover E) f
  exact (le_iSup (finiteSpanFunctorImage
    (inductionJacquetFunctor.{uG, uV} h₀ hU₀) E) s) ⟨g, hg⟩

variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {IsAssociate : Finset ι → Finset ι → G → Prop} {I : Finset ι}
  {hM : IsClosed (M I : Set G)}
  {hI : ∀ K : Finset I, IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
    ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}

/-- Exhaustion by invariant images of supported objects implies support of the
target. The indexing universe is unrestricted. -/
theorem isInSupportCategory_of_iSup_ranges
    {J : Type uJ} {B : SmoothRep.{0, uG, max uG uV} ℂ G}
    (A : J → SmoothRep.{0, uG, max uG uV} ℂ G) (f : ∀ j, A j ⟶ B)
    (hcover : (⨆ j, (hom (f j)).range) = ⊤)
    (hA : ∀ j, IsInSupportCategory P M U h hU IsAssociate I hM hI (A j)) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI B := by
  have him : ∀ j, IsInSupportCategory P M U h hU IsAssociate I hM hI
      (subrepresentation B (hom (f j)).range) := fun j =>
    (hA j).of_isSubquotient (IsQuotient.isSubquotient (image_isQuotient (f j)))
  have hsum := IsInSupportCategory.iSup (fun j => (hom (f j)).range) him
  rw [hcover] at hsum
  exact hsum.of_isSubquotient
    (IsQuotient.isSubquotient ⟨subtype B ⊤, fun b => ⟨⟨b, Submodule.mem_top⟩, rfl⟩⟩)

/-- If a functor exhausts every output by the images of finite invariant spans
and preserves support on all finitely generated inputs, it preserves support on
every smooth input. No finite-length reduction is used. -/
theorem supportCategory_preserved_of_finiteGeneration
    (F : SmoothRep.{0, uG, max uG uV} ℂ G ⥤ SmoothRep.{0, uG, max uG uV} ℂ G)
    (hcover : ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
      (⨆ s, finiteSpanFunctorImage F E s) = ⊤)
    (hfinite : ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
      Module.Finite (MonoidAlgebra ℂ G) E.representation.asModule →
      IsInSupportCategory P M U h hU IsAssociate I hM hI E →
      IsInSupportCategory P M U h hU IsAssociate I hM hI (F.obj E)) :
    ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
      IsInSupportCategory P M U h hU IsAssociate I hM hI E →
      IsInSupportCategory P M U h hU IsAssociate I hM hI (F.obj E) := by
  intro E hE
  apply isInSupportCategory_of_iSup_ranges
    (fun s => F.obj (subrepresentation E (finiteSpanSubrepresentation E s)))
    (fun s => F.map (subtype E (finiteSpanSubrepresentation E s))) (hcover E)
  intro s
  exact hfinite _ (finiteSpanSubrepresentation_finite E s)
    (hE.of_isSubquotient
      (IsSubrepresentation.isSubquotient (subrepresentation_isSubrepresentation _)))

/-- With compact quotient and compact-limit unipotent part, the only support
input still needed is preservation on every finitely generated supported
representation. -/
theorem supportCategory_inductionJacquet_of_finiteGeneration (K : Finset ι)
    [CompactSpace (Induction.LeftQuotient (P K))]
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (U K))
    (hfinite : ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
      Module.Finite (MonoidAlgebra ℂ G) E.representation.asModule →
      IsInSupportCategory P M U h hU IsAssociate I hM hI E →
      IsInSupportCategory P M U h hU IsAssociate I hM hI
        ((inductionJacquetFunctor.{uG, uV} (h K) (hU K)).obj E)) :
    ∀ E : SmoothRep.{0, uG, max uG uV} ℂ G,
      IsInSupportCategory P M U h hU IsAssociate I hM hI E →
      IsInSupportCategory P M U h hU IsAssociate I hM hI
        ((inductionJacquetFunctor.{uG, uV} (h K) (hU K)).obj E) :=
  supportCategory_preserved_of_finiteGeneration
    (inductionJacquetFunctor.{uG, uV} (h K) (hU K))
    (inductionJacquet_iSup_finiteSpanFunctorImage (h K) (hU K) hUc) hfinite

end Langlands.Aubert.General

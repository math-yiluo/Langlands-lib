import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.AlgebraicGeometry.Sites.EtaleFppfComparison
import Langlands.CategoryTheory.Sites.CommonKernelComparison

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A single surjective etale morphism generates a covering sieve in the
actual big etale topology on the full scheme slice. -/
theorem generate_singleton_mem_etaleTopology {W M : Over S} (q : W ⟶ M)
    [Etale q.left] [Surjective q.left] :
    Sieve.generate (Presieve.singleton q) ∈ Scheme.etaleTopology.over S M := by
  change Sieve.overEquiv M (Sieve.generate (Presieve.singleton q)) ∈
    Scheme.etaleTopology M.left
  rw [← Presieve.ofArrows_pUnit.{0} q, ← Sieve.ofArrows,
    Sieve.overEquiv_ofArrows, Sieve.ofArrows, Presieve.ofArrows_pUnit]
  apply Precoverage.generate_mem_toGrothendieck
  exact (Scheme.singleton_mem_precoverage_iff (@Etale.{u}) q.left).mpr
    ⟨(inferInstance : Surjective q.left).surj, inferInstance⟩

/-- A represented surjective etale scheme cover is locally surjective on
sections for the big etale topology. -/
theorem isLocallySurjective_etale_schemeYoneda_map {W M : Over S} (q : W ⟶ M)
    [Etale q.left] [Surjective q.left] :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      ((schemeYoneda S).map q) := by
  constructor
  intro T x
  apply (Scheme.etaleTopology.over S).superset_covering ?_
    ((Scheme.etaleTopology.over S).pullback_stable x.down
      (generate_singleton_mem_etaleTopology q))
  intro V g hg
  obtain ⟨Z, t, q', hq', hcomp⟩ := hg
  cases hq'
  refine ⟨⟨t⟩, ?_⟩
  apply ULift.ext
  exact hcomp

/-- The actual geometric etale and surjectivity conditions imply local
surjectivity on the full big etale site. -/
theorem isLocallySurjective_etale_of_isEtale_isSurjective
    {F G : Presheaf S} (a : F ⟶ G) (ha : IsEtale a) (hs : IsSurjective a) :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a := by
  constructor
  intro T x
  let g : (schemeYoneda S).obj T ⟶ G := uliftYonedaEquiv.symm x
  let p := ha.representable.snd g
  have : Etale p.left :=
    ha.projection g (ha.representable.fst g) p (ha.representable.isPullback g)
  have : Surjective p.left :=
    hs.projection g (ha.representable.fst g) p (ha.representable.isPullback g)
  apply (Scheme.etaleTopology.over S).superset_covering ?_
    (generate_singleton_mem_etaleTopology p)
  rw [Sieve.generate_le_iff, Presieve.singleton_le_iff]
  refine ⟨(ha.representable.fst g).app (op (ha.representable.pullback g)) ⟨𝟙 _⟩, ?_⟩
  simpa [g] using congrArg
    (fun z : (schemeYoneda S).obj (ha.representable.pullback g) ⟶ G =>
      z.app (op (ha.representable.pullback g)) ⟨𝟙 _⟩)
    (ha.representable.isPullback g).w

/-- Two etale sheaves with locally surjective scheme presentations and the
same kernel on all test schemes have a compatible presheaf isomorphism. -/
theorem exists_iso_of_common_etale_presentation
    {F G : Presheaf S} {W : Over S}
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hG : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) G)
    (a : (schemeYoneda S).obj W ⟶ F) (b : (schemeYoneda S).obj W ⟶ G)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hker : ∀ (T : Over S) (x y : T ⟶ W),
      a.app (op T) ⟨x⟩ = a.app (op T) ⟨y⟩ ↔
        b.app (op T) ⟨x⟩ = b.app (op T) ⟨y⟩) :
    ∃ e : F ≅ G, a ≫ e.hom = b := by
  let H := (Sites.fppfSheafToEtaleSheaf S (Type (u + 1))).obj
    ((schemeSheaf S).obj W)
  let F' : Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) := ⟨F, hF⟩
  let G' : Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) := ⟨G, hG⟩
  let a' : H ⟶ F' := ObjectProperty.homMk a
  let b' : H ⟶ G' := ObjectProperty.homMk b
  obtain ⟨e, he⟩ :=
    Langlands.CategoryTheory.Sites.exists_iso_of_isLocallySurjective_of_same_kernel
      a' b' ha hb (fun T x y => hker T.unop x.down y.down)
  exact ⟨(sheafToPresheaf (Scheme.etaleTopology.over S) (Type (u + 1))).mapIso e,
    (sheafToPresheaf (Scheme.etaleTopology.over S) (Type (u + 1))).congr_map he⟩

/-- The actual compatible isomorphism constructed from two etale-local
scheme presentations with the same kernel on every test scheme. -/
def commonEtalePresentationIso
    {F G : Presheaf S} {W : Over S}
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hG : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) G)
    (a : (schemeYoneda S).obj W ⟶ F) (b : (schemeYoneda S).obj W ⟶ G)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hker : ∀ (T : Over S) (x y : T ⟶ W),
      a.app (op T) ⟨x⟩ = a.app (op T) ⟨y⟩ ↔
        b.app (op T) ⟨x⟩ = b.app (op T) ⟨y⟩) :
    F ≅ G :=
  (exists_iso_of_common_etale_presentation hF hG a b ha hb hker).choose

/-- The common-presentation isomorphism identifies the actual presentation maps. -/
theorem commonEtalePresentationIso_hom_fac
    {F G : Presheaf S} {W : Over S}
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hG : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) G)
    (a : (schemeYoneda S).obj W ⟶ F) (b : (schemeYoneda S).obj W ⟶ G)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hker : ∀ (T : Over S) (x y : T ⟶ W),
      a.app (op T) ⟨x⟩ = a.app (op T) ⟨y⟩ ↔
        b.app (op T) ⟨x⟩ = b.app (op T) ⟨y⟩) :
    a ≫ (commonEtalePresentationIso hF hG a b ha hb hker).hom = b :=
  (exists_iso_of_common_etale_presentation hF hG a b ha hb hker).choose_spec

/-- An etale sheaf satisfies fppf descent if it has the same etale-local
scheme presentation as an actual fppf sheaf. -/
theorem isSheaf_fppf_of_common_etale_presentation
    {F : Presheaf S} {G : FppfSheaf S} {W : Over S}
    (hF : CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (a : (schemeYoneda S).obj W ⟶ F) (b : (schemeYoneda S).obj W ⟶ G.obj)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb : CategoryTheory.Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hker : ∀ (T : Over S) (x y : T ⟶ W),
      a.app (op T) ⟨x⟩ = a.app (op T) ⟨y⟩ ↔
        b.app (op T) ⟨x⟩ = b.app (op T) ⟨y⟩) :
    CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F := by
  let e := commonEtalePresentationIso hF
    (G.property.of_le (Sites.etaleTopologyOver_le_fppfTopologyOver S)) a b ha hb hker
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff e).mpr G.property

end Langlands.AlgebraicGeometry.AlgebraicSpace

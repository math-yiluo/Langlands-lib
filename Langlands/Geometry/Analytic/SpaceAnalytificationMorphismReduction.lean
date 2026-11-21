import Langlands.Geometry.Analytic.SpaceAnalytificationMorphismStatement
import Langlands.Geometry.Analytic.SpaceAnalytificationMorphismCompatibility
import Langlands.Geometry.Analytic.EtaleHomGluing
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Langlands.Geometry.Analytic.LocalizedPullbackPoints

/-! # Morphisms of analytifications from étale descent of morphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SpaceAnalytification

open SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- If morphisms out of `Y'` into `T` satisfy étale descent, two morphisms that
agree after composition with the analytic maps of all étale test points are
equal. -/
theorem IsAnalytification.hom_ext_of_etale
    {X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y' T : LocalizedCategory.{u, u, u} (K := K)} {p' : PointFamily K X' Y'}
    (hp' : IsAnalytification K X' Y' p')
    (hSheaf : Presieve.IsSheaf (etaleTopology Y')
      ((MorphismProperty.Over.forget _ _ Y' ⋙ Over.forget Y').op ⋙ yoneda.obj T))
    (F G : Y' ⟶ T)
    (h : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      AlgebraicSpace.IsEtale (pointHom K x) → p' A P x ≫ F = p' A P x ≫ G) :
    F = G :=
  hom_ext_of_etale_local_eq hSheaf F G fun y => by
    obtain ⟨A, _, _, P, x, hx, hy⟩ := hp'.jointly_surjective y
    exact ⟨_, p' A P x, hp'.etale_map P x hx, hy, h A P x hx⟩

/-- If morphisms out of `Y'` into `Y` satisfy étale descent, the analytic maps of
the images of the test points of a separated space glue to a morphism
`Y' ⟶ Y` compatible with every étale test point. -/
theorem IsAnalytification.exists_hom_etale_compatible
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX' : IsSeparated X')
    (f : X' ⟶ X) {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (hSheaf : Presieve.IsSheaf (etaleTopology Y')
      ((MorphismProperty.Over.forget _ _ Y' ⋙ Over.forget Y').op ⋙ yoneda.obj Y)) :
    ∃ F : Y' ⟶ Y, ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      AlgebraicSpace.IsEtale (pointHom K x) → p' A P x ≫ F = p A P (RingPoints.map f x) := by
  classical
  let B : EtaleSite Y' := MorphismProperty.Over.mk ⊤ (𝟙 Y') (etale_of_isIso _)
  -- `U` factors through the analytic map of some test point.
  let Fac : EtaleSite Y' → Prop := fun U =>
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A)
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A)
      (g : U.left ⟶ AffineAnalytification.localized K P), g ≫ p' A P x = U.hom
  -- The common value of all such factorizations.
  let Val : (U : EtaleSite Y') → (U.left ⟶ Y) → Prop := fun U l =>
    ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A)
      (g : U.left ⟶ AffineAnalytification.localized K P),
      g ≫ p' A P x = U.hom → g ≫ p A P (RingPoints.map f x) = l
  have hVal : ∀ U, Fac U → ∃ l, Val U l := by
    rintro U ⟨A, _, _, P, x, g, hg⟩
    refine ⟨g ≫ p A P (RingPoints.map f x), ?_⟩
    intro A' _ _ P' x' g' hg'
    exact hp'.comp_map_eq_of_comp_eq hX' f hp P' P x' x g' g (hg'.trans hg.symm)
  let R : Sieve B :=
    { arrows := fun U _ => Fac U
      downward_closed := by
        rintro U V e ⟨A, _, _, P, x, g, hg⟩ r
        refine ⟨A, inferInstance, inferInstance, P, x, r.left ≫ g, ?_⟩
        rw [Category.assoc, hg, MorphismProperty.Over.w] }
  have hR : R ∈ etaleTopology Y' B := by
    apply mem_etaleTopology_of_jointlySurjective
    intro y
    obtain ⟨A, _, _, P, x, hx, hy⟩ := hp'.jointly_surjective y
    let V : EtaleSite Y' := MorphismProperty.Over.mk ⊤ (p' A P x) (hp'.etale_map P x hx)
    let a : V ⟶ B := MorphismProperty.Over.homMk (p' A P x) (Category.comp_id _)
    exact ⟨V, a, ⟨A, inferInstance, inferInstance, P, x, 𝟙 _, Category.id_comp _⟩, hy⟩
  let fam : Presieve.FamilyOfElements
      ((MorphismProperty.Over.forget _ _ Y' ⋙ Over.forget Y').op ⋙ yoneda.obj Y) R.arrows :=
    fun U _ he => Classical.choose (hVal U he)
  have hfam {U : EtaleSite Y'} (e : U ⟶ B) (he : R e) : Val U (fam e he) :=
    Classical.choose_spec (hVal U he)
  have hcompat : fam.Compatible := by
    intro U₁ U₂ Z g₁ g₂ e₁ e₂ he₁ he₂ _
    change g₁.left ≫ fam e₁ he₁ = g₂.left ≫ fam e₂ he₂
    obtain ⟨A₁, _, _, P₁, x₁, k₁, hk₁⟩ := id he₁
    obtain ⟨A₂, _, _, P₂, x₂, k₂, hk₂⟩ := id he₂
    rw [← hfam e₁ he₁ A₁ P₁ x₁ k₁ hk₁, ← hfam e₂ he₂ A₂ P₂ x₂ k₂ hk₂, ← Category.assoc,
      ← Category.assoc]
    apply hp'.comp_map_eq_of_comp_eq hX' f hp
    rw [Category.assoc, Category.assoc, hk₁, hk₂, MorphismProperty.Over.w,
      MorphismProperty.Over.w]
  refine ⟨(hSheaf R hR).amalgamate fam hcompat, ?_⟩
  intro A _ _ P x hx
  let V : EtaleSite Y' := MorphismProperty.Over.mk ⊤ (p' A P x) (hp'.etale_map P x hx)
  let a : V ⟶ B := MorphismProperty.Over.homMk (p' A P x) (Category.comp_id _)
  have ha : R a := ⟨A, inferInstance, inferInstance, P, x, 𝟙 _, Category.id_comp _⟩
  have hglue := (hSheaf R hR).valid_glue hcompat a ha
  change p' A P x ≫ (hSheaf R hR).amalgamate fam hcompat = fam a ha at hglue
  rw [hglue]
  exact (hfam a ha A P x (𝟙 _) (Category.id_comp _)).symm.trans (Category.id_comp _)

/-- The published étale base change, together with the published lifting of
matching points through pullbacks, makes every map into an analytification factor
étale-locally through the analytic map of an étale test point. -/
theorem IsAnalytification.exists_etale_chart_factorization
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y S : LocalizedCategory.{u, u, u} (K := K)}
    {p : PointFamily K X Y} (hp : IsAnalytification K X Y p)
    (a : S ⟶ Y) (s : localizedSpaceFunctor.obj S) :
    ∃ (U : LocalizedCategory.{u, u, u} (K := K)) (e : U ⟶ S),
      etale e ∧ s ∈ Set.range (localizedSpaceFunctor.map e) ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A)
        (P : FinitePolynomialPresentation K A) (x : RingPoints K X A)
        (l : U ⟶ AffineAnalytification.localized K P),
        AlgebraicSpace.IsEtale (pointHom K x) ∧ l ≫ p A P x = e ≫ a := by
  obtain ⟨A, _, _, P, x, hx, α, hα⟩ := hp.jointly_surjective
    (localizedSpaceFunctor.map a s)
  obtain ⟨U, l, e, hU, he⟩ :=
    localizedEtalePullbackBaseChange.{u, u} (p A P x) a (hp.etale_map P x hx)
  obtain ⟨z, -, hz⟩ := exists_point_of_isPullback l e (p A P x) a hU α s hα
  exact ⟨U, e, he, ⟨z, hz⟩, A, inferInstance, inferInstance, P, x, l, hx, hU.w⟩

/-- Compatibility with étale test points implies compatibility with all test
points, given étale descent of morphisms into `Y`. -/
theorem IsAnalytification.comp_eq_of_etale_comp_eq
    (hSheaf : ∀ (S T : LocalizedCategory.{u, u, u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T))
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX' : IsSeparated X')
    (f : X' ⟶ X) {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p) (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      AlgebraicSpace.IsEtale (pointHom K x) → p' A P x ≫ F = p A P (RingPoints.map f x))
    (A : Type u) [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A) :
    p' A P x ≫ F = p A P (RingPoints.map f x) := by
  apply hom_ext_of_etale_local_eq (hSheaf _ Y)
  intro s
  obtain ⟨U, e, he, hs, B, _, _, Q, y, l, hy, hl⟩ :=
    hp'.exists_etale_chart_factorization (p' A P x) s
  refine ⟨U, e, he, hs, ?_⟩
  rw [← Category.assoc, ← hl, Category.assoc, hF B Q y hy]
  exact hp'.comp_map_eq_of_comp_eq hX' f hp Q P y x l e hl

/-- The analytic input of the morphism theorem for analytifications of algebraic
spaces, étale descent of morphisms: for every complete, ultrametric, nontrivially
normed field `K : Type u` and all objects `S` and `T` of the localized analytic
category `LocalizedCategory.{u, u, u}`, morphisms into `T` form a sheaf on the small
étale site of `S` for its étale topology. -/
def SpaceAnalytificationMorphismEtaleDescentInput : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (S T : LocalizedCategory.{u, u, u} (K := K)),
    Presieve.IsSheaf (etaleTopology S)
      ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T)

/-- The morphism statement for analytifications of algebraic spaces follows from
étale descent of analytic morphisms in the localized category. -/
theorem spaceAnalytificationMorphismStatement_of_etaleDescent
    (h : SpaceAnalytificationMorphismEtaleDescentInput.{u}) :
    SpaceAnalytificationMorphismStatement.{u} := by
  intro K _ _ _ X' X f hX' _ Y' Y p' p hp' hp
  have hS := h K
  obtain ⟨F, hF⟩ := hp'.exists_hom_etale_compatible hX' f hp (hS Y' Y)
  refine ⟨F, fun A _ _ P x =>
    hp'.comp_eq_of_etale_comp_eq hS hX' f hp F hF A P x, ?_⟩
  intro G hG
  apply hp'.hom_ext_of_etale (hS Y' Y)
  intro A _ _ P x _
  rw [hG A P x, hF A P x ‹_›]

end Langlands.Analytic.SpaceAnalytification

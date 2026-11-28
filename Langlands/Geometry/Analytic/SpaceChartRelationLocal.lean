import Langlands.Geometry.Analytic.SpaceChartRelation
import Langlands.Geometry.Analytic.EtaleCoverGluing
import Langlands.Geometry.Analytic.EtaleHomSheafStatement

/-! # Locality of the analytic relation of affine test points

Granting the sheaf property of Hom presheaves on small étale sites, the relation of two
analytic maps through a model of the fibre product of two affine test points is local on the
source for jointly surjective étale families. A pair of analytic maps into an analytic space
whose equalizing pairs are exactly the related pairs makes the analytified model square a
pullback. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ExistenceReduction.TestModel

open SaturatedAtlasPresentation AffineAnalytification
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  {u : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) ⟶ F}
  {v : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F}
  {P : FinitePolynomialPresentation K A} {Q : FinitePolynomialPresentation K B}

/-- The relation through a model is local on the source for jointly surjective étale
families. -/
theorem ARel.of_etale_cover (hSheaf : EtaleHomSheafStatement.{u, u}) (M : TestModel u v)
    {T : LocalizedCategory.{u, u, u} (K := K)} {L : Type u}
    (U : L → LocalizedCategory.{u, u, u} (K := K)) (e : ∀ l, U l ⟶ T) (he : ∀ l, etale (e l))
    (hcov : ∀ t : localizedSpaceFunctor.obj T,
      ∃ l, t ∈ Set.range (localizedSpaceFunctor.map (e l)))
    {α : T ⟶ localized K P} {β : T ⟶ localized K Q}
    (h : ∀ l, M.ARel P Q (e l ≫ α) (e l ≫ β)) : M.ARel P Q α β := by
  choose t ht₁ ht₂ using h
  obtain ⟨g, hg⟩ := exists_glue_of_etale_cover (hSheaf K T (localized K M.R)) U e he hcov t
    (fun V l l' a b hab => M.jointly_mono (P := P) (Q := Q) _ _
      (by rw [Category.assoc, Category.assoc, ht₁, ht₁, ← Category.assoc, hab, Category.assoc])
      (by rw [Category.assoc, Category.assoc, ht₂, ht₂, ← Category.assoc, hab, Category.assoc]))
  refine ⟨g, ?_, ?_⟩
  · exact hom_ext_of_etale_cover (hSheaf K T (localized K P)) U e he hcov _ _ fun l => by
      rw [← Category.assoc, hg, ht₁]
  · exact hom_ext_of_etale_cover (hSheaf K T (localized K Q)) U e he hcov _ _ fun l => by
      rw [← Category.assoc, hg, ht₂]

/-- If the pairs of analytic maps equalized by `πP` and `πQ` are exactly the pairs related
through the model `M`, then the analytified model square is a pullback. -/
theorem isPullback_of_aRel (M : TestModel u v) {Y : LocalizedCategory.{u, u, u} (K := K)}
    (πP : localized K P ⟶ Y) (πQ : localized K Q ⟶ Y)
    (hw : localizedHom K P M.R M.f ≫ πP = localizedHom K Q M.R M.g ≫ πQ)
    (h : ∀ {T : LocalizedCategory.{u, u, u} (K := K)} (α : T ⟶ localized K P)
      (β : T ⟶ localized K Q), α ≫ πP = β ≫ πQ → M.ARel P Q α β) :
    IsPullback (localizedHom K P M.R M.f) (localizedHom K Q M.R M.g) πP πQ := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => Classical.choose (h s.fst s.snd s.condition))
    (fun s => (Classical.choose_spec (h s.fst s.snd s.condition)).1)
    (fun s => (Classical.choose_spec (h s.fst s.snd s.condition)).2) ?_)
  intro s l hl₁ hl₂
  exact M.jointly_mono (P := P) (Q := Q) _ _
    (hl₁.trans (Classical.choose_spec (h s.fst s.snd s.condition)).1.symm)
    (hl₂.trans (Classical.choose_spec (h s.fst s.snd s.condition)).2.symm)

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction.TestModel

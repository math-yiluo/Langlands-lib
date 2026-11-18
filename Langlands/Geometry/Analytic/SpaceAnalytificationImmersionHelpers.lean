import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionRestrictions
import Langlands.Geometry.Analytic.SpaceAnalytificationImmersionStatement
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReduction
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Geometry.Analytic.LocalizedPullbackPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineFiniteTypePullbacks
import Langlands.AlgebraicGeometry.AlgebraicSpace.SliceOpenGluing

/-! # Injectivity and openness for analytified immersions -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory CategoryTheory.Limits _root_.Topology Opposite SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap)

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An analytified monomorphism has injective underlying map. -/
theorem map_injective_of_mono
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX : IsSeparated X) [Mono (hom f)]
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x)) :
    Function.Injective (localizedSpaceFunctor.map F) := by
  intro y₁ y₂ hy
  obtain ⟨A, _, _, P, x, _, a, ha⟩ := hp'.jointly_surjective y₁
  obtain ⟨B, _, _, Q, y, _, b, hb⟩ := hp'.jointly_surjective y₂
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  obtain ⟨C, _, _, hC, α, β, hpb⟩ := hasFiniteTypeAffinePullbacks_of_separated K X hX
    A B (pointHom K (RingPoints.map f x)) (pointHom K (RingPoints.map f y))
  let := hC
  let R := FinitePolynomialPresentation.ofFiniteType K C
  have hpoints : RingPoints.changeRing α (RingPoints.map f x) =
      RingPoints.changeRing β (RingPoints.map f y) := by
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    simpa only [pointHom_changeRing] using hpb.w
  have hsource : RingPoints.changeRing α x = RingPoints.changeRing β y := by
    apply (CategoryTheory.mono_iff_injective ((hom f).app (op (ringTest K C)))).mp
      inferInstance
    exact (RingPoints.changeRing_map f α x).symm.trans
      (hpoints.trans (RingPoints.changeRing_map f β y))
  have hxy : localizedSpaceFunctor.map (p A P (RingPoints.map f x)) a =
      localizedSpaceFunctor.map (p B Q (RingPoints.map f y)) b := by
    rw [← hF A P x, ← hF B Q y, Functor.map_comp, Functor.map_comp,
      TopCat.comp_app, TopCat.comp_app, ha, hb]
    exact hy
  obtain ⟨z, hz₁, hz₂⟩ := exists_point_of_isPullback _ _ _ _
    (hp.isPullback P Q R α β _ _ hpb) a b hxy
  have hnat : AffineAnalytification.localizedHom K P R α ≫ p' A P x =
      AffineAnalytification.localizedHom K Q R β ≫ p' B Q y := by
    rw [← hp'.naturality, ← hp'.naturality, hsource]
  have he := congrArg (fun k => localizedSpaceFunctor.map k z) hnat
  simpa only [Functor.map_comp, TopCat.comp_app, hz₁, hz₂, ha, hb] using he

/-- The analytification of an etale map is open on underlying points. -/
theorem isOpenMap_of_isEtale
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hf : AlgebraicSpace.IsEtale (hom f))
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x)) :
    IsOpenMap (localizedSpaceFunctor.map F) := by
  intro s hs
  apply isOpen_iff_forall_mem_open.mpr
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨A, _, _, P, x, hx, a, ha⟩ := hp'.jointly_surjective y
  have htarget : AlgebraicSpace.IsEtale (pointHom K (RingPoints.map f x)) := by
    rw [pointHom_map K]
    exact hx.comp hf
  have hopen := etaleOpenMap K (p A P (RingPoints.map f x)) (hp.etale_map P _ htarget)
  have heq : ∀ z, localizedSpaceFunctor.map (p A P (RingPoints.map f x)) z =
      localizedSpaceFunctor.map F (localizedSpaceFunctor.map (p' A P x) z) := by
    intro z
    rw [← hF A P x, Functor.map_comp, TopCat.comp_app]
  refine ⟨localizedSpaceFunctor.map (p A P (RingPoints.map f x)) ''
    (localizedSpaceFunctor.map (p' A P x) ⁻¹' s), ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, hz, (heq z).symm⟩
  · exact hopen _ (hs.preimage (localizedSpaceFunctor.map (p' A P x)).hom.continuous)
  · exact ⟨a, (by change localizedSpaceFunctor.map (p' A P x) a ∈ s; rw [ha]; exact hy), (heq a).trans (congrArg (localizedSpaceFunctor.map F) ha)⟩

/-- A representable open immersion is a monomorphism of presheaves. -/
theorem mono_of_isOpenImmersion {S : Scheme.{u}} {F G : Presheaf S} {i : F ⟶ G}
    (hi : AlgebraicSpace.IsOpenImmersion i) : Mono i := by
  apply SliceOpenGluing.relative_monomorphisms_le_monomorphisms i
  apply MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (Over.forget S)) ?_ i hi
  intro U V p hp
  let : _root_.AlgebraicGeometry.IsOpenImmersion p.left := hp
  exact Over.mono_of_mono_left p

/-- A representable closed immersion is a monomorphism of presheaves. -/
theorem mono_of_isClosedImmersion {S : Scheme.{u}} {F G : Presheaf S} {i : F ⟶ G}
    (hi : AlgebraicSpace.IsClosedImmersion i) : Mono i := by
  apply SliceOpenGluing.relative_monomorphisms_le_monomorphisms i
  apply MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)) ?_ i hi
  intro U V p hp
  let : _root_.AlgebraicGeometry.IsClosedImmersion p.left := hp
  exact Over.mono_of_mono_left p

/-- The analytification of an open immersion is an open embedding. -/
theorem isOpenEmbedding_of_isOpenImmersion
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX : IsSeparated X) (hf : AlgebraicSpace.IsOpenImmersion (hom f))
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x)) :
    IsOpenEmbedding (localizedSpaceFunctor.map F) := by
  let : Mono (hom f) := mono_of_isOpenImmersion hf
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (localizedSpaceFunctor.map F).hom.continuous (map_injective_of_mono f hX hp' hp F hF)
    (isOpenMap_of_isEtale f (PointOpenSubspace.isEtale_of_isOpenImmersion hf) hp' hp F hF)

/-- Open immersions have open embedding analytifications for arbitrary supplied
analytifications, with only the target separatedness hypothesis. -/
def OpenImmersionEmbeddingStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X' X : AlgebraicSpace (Spec (CommRingCat.of K))) (f : X' ⟶ X), IsSeparated X →
    ∀ (Y' Y : LocalizedCategory.{u, u, u} (K := K))
      (p' : PointFamily K X' Y') (p : PointFamily K X Y),
      IsAnalytification K X' Y' p' → IsAnalytification K X Y p →
      ∀ F : Y' ⟶ Y, (∀ (A : Type u) [CommRing A] [Algebra K A]
        (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
        p' A P x ≫ F = p A P (RingPoints.map f x)) →
        AlgebraicSpace.IsOpenImmersion (hom f) →
          IsOpenEmbedding (localizedSpaceFunctor.map F)

/-- The open immersion property follows from the proved point lifting and chart openness. -/
theorem openImmersionEmbedding : OpenImmersionEmbeddingStatement.{u} := by
  intro K _ _ _ X' X f hX Y' Y p' p hp' hp F hF hf
  exact isOpenEmbedding_of_isOpenImmersion f hX hf hp' hp F hF

end Langlands.Analytic.SpaceAnalytification

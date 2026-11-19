import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability

/-! # Comparison with a supplied analytification of an affine scheme -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)}

set_option backward.isDefEq.respectTransparency false in
/-- A surjective étale monomorphism is an isomorphism under analytic Hom
descent for the source and target. -/
def isoOfSurjectiveEtaleMono (f : X ⟶ Y) [Mono f]
    (hf : etale f) (hs : Function.Surjective (localizedSpaceFunctor.map f))
    (hX : Presieve.IsSheaf (etaleTopology Y)
      ((MorphismProperty.Over.forget etale ⊤ Y ⋙ Over.forget Y).op ⋙ yoneda.obj X))
    (hY : Presieve.IsSheaf (etaleTopology Y)
      ((MorphismProperty.Over.forget etale ⊤ Y ⋙ Over.forget Y).op ⋙ yoneda.obj Y)) :
    { e : X ≅ Y // e.hom = f } := by
  let A : EtaleSite Y := MorphismProperty.Over.mk ⊤ (𝟙 Y) (etale_of_isIso _)
  let B : EtaleSite Y := MorphismProperty.Over.mk ⊤ f hf
  let π : B ⟶ A := MorphismProperty.Over.homMk f (Category.comp_id _)
  have hπ : Presieve.singleton π ∈ etalePrecoverage Y A :=
    mem_etalePrecoverage_iff.mpr fun y => ⟨B, π, Presieve.singleton_self _, hs y⟩
  let P (Z : LocalizedCategory.{u, v, v} (K := K)) :=
    (MorphismProperty.Over.forget etale ⊤ Y ⋙ Over.forget Y).op ⋙ yoneda.obj Z
  have hmatch : ∀ {T : EtaleSite Y} (r s : T ⟶ B), r ≫ π = s ≫ π →
      (P X).map r.op (𝟙 X) = (P X).map s.op (𝟙 X) := by
    intro T r s h
    have h' : r.left ≫ f = s.left ≫ f := congrArg (·.left) h
    change r.left ≫ 𝟙 X = s.left ≫ 𝟙 X
    rw [(cancel_mono f).mp h']
  have hexists := (Presieve.isSheafFor_singleton (P := P X) (f := π)).mp
    (hX.isSheafFor_of_mem_precoverage hπ) (𝟙 X) hmatch
  let g : Y ⟶ X := hexists.exists.choose
  have hg : f ≫ g = 𝟙 X := hexists.exists.choose_spec
  have hi : g ≫ f = 𝟙 Y := by
    have huniq := (Presieve.isSeparatedFor_singleton (P := P Y) (f := π)).mp
      (hY.isSheafFor_of_mem_precoverage hπ).isSeparatedFor
    apply huniq
    change f ≫ g ≫ f = f ≫ 𝟙 Y
    rw [← Category.assoc, hg, Category.id_comp, Category.comp_id]
  exact ⟨⟨f, g, hg, hi⟩, rfl⟩

end Langlands.Analytic.SaturatedAtlasPresentation

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- The affine test point of the identity of the relative spectrum. -/
def affineIdentityPoint : RingPoints K ((schemeToSpace _).obj (ringTest K A)) A :=
  (schemeRingPointsEquiv K (ringTest K A) A).symm (𝟙 _)

/-- The point family on the polynomial-locus analytification of the
algebraic space represented by an affine scheme. -/
def affineSchemePointFamily :
    PointFamily K ((schemeToSpace _).obj (ringTest K A)) (AffineAnalytification.localized K P) :=
  fun B _ _ Q x => AffineAnalytification.localizedHom K P Q
    (affineRingPointEquiv K A B (schemeRingPointsEquiv K (ringTest K A) B x))

variable {K P} {Y : LocalizedCategory.{u, u, u} (K := K)}
  {p : PointFamily K ((schemeToSpace _).obj (ringTest K A)) Y}
  (hp : IsAnalytification K ((schemeToSpace _).obj (ringTest K A)) Y p)

include hp in
set_option backward.isDefEq.respectTransparency false in
/-- On an affine spectrum, the identity test determines every map
of a supplied analytification. -/
theorem affineSchemePointFamily_comp_identity
    {B : Type u} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
    (x : RingPoints K ((schemeToSpace _).obj (ringTest K A)) B) :
    affineSchemePointFamily K P B Q x ≫ p A P (affineIdentityPoint K) = p B Q x := by
  let r := schemeRingPointsEquiv K (ringTest K A) B x
  let g := affineRingPointEquiv K A B r
  have hg : RingPoints.changeRing g (affineIdentityPoint K) = x := by
    apply (schemeRingPointsEquiv K (ringTest K A) B).injective
    change ringTestMap K g ≫ 𝟙 _ = r
    exact (Category.comp_id _).trans (ringTestMap_affineRingPointEquiv K r)
  exact (hp.naturality P Q g (affineIdentityPoint K)).symm.trans
    (congrArg (p B Q) hg)

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem pointHom_affineIdentityPoint :
    pointHom K (affineIdentityPoint K (A := A)) =
      𝟙 ((schemeYoneda _).obj (ringTest K A)) := by
  apply uliftYonedaEquiv.{u + 1}.injective
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- Under analytic Hom descent, the identity affine test is an
isomorphism from the polynomial-locus model to a supplied analytification. -/
def affineIsoOfIsAnalytification
    (hp : IsAnalytification K ((schemeToSpace _).obj (ringTest K A)) Y p)
    (hHom : ∀ (S T : LocalizedCategory.{u, u, u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget etale ⊤ S ⋙ Over.forget S).op ⋙ yoneda.obj T)) :
    { e : AffineAnalytification.localized K P ≅ Y //
      e.hom = p A P (affineIdentityPoint K) } := by
  let x := affineIdentityPoint K (A := A)
  let f := p A P x
  have he : etale f := by
    apply hp.etale_map P x
    have h : pointHom K x = 𝟙 ((schemeYoneda _).obj (ringTest K A)) :=
      pointHom_affineIdentityPoint
    rw [h, ← (schemeYoneda (Spec (CommRingCat.of K))).map_id]
    exact isEtale_map (𝟙 (ringTest K A)) (by infer_instance)
  have hs : Function.Surjective (localizedSpaceFunctor.map f) := by
    intro y
    obtain ⟨B, _, _, Q, z, -, t, ht⟩ := hp.jointly_surjective y
    refine ⟨localizedSpaceFunctor.map (affineSchemePointFamily K P B Q z) t, ?_⟩
    have h := congrArg (fun g => localizedSpaceFunctor.map g t)
      (affineSchemePointFamily_comp_identity (P := P) hp Q z)
    rw [Functor.map_comp, TopCat.comp_app] at h
    exact h.trans ht
  have hAlg : IsPullback ((schemeYoneda _).map (ringTestMap K (AlgHom.id K A)))
      ((schemeYoneda _).map (ringTestMap K (AlgHom.id K A))) (pointHom K x) (pointHom K x) := by
    have h : (schemeYoneda _).map (ringTestMap K (AlgHom.id K A)) =
        𝟙 ((schemeYoneda _).obj (ringTest K A)) :=
      (congrArg ((schemeYoneda _).map) (ringTestMap_id K A)).trans
        ((schemeYoneda _).map_id _)
    have h' : pointHom K x = 𝟙 ((schemeYoneda _).obj (ringTest K A)) :=
      pointHom_affineIdentityPoint
    rw [h, h']
    exact IsPullback.of_id_snd
  have hAn := hp.isPullback P P P (AlgHom.id K A) (AlgHom.id K A) x x hAlg
  let : Mono f := ⟨fun r s h => (hAn.lift_fst r s h).symm.trans (hAn.lift_snd r s h)⟩
  exact isoOfSurjectiveEtaleMono f he hs (hHom _ _) (hHom _ _)

include hp in
/-- Existence of a supplied analytification and analytic Hom descent give
analytification on the canonical affine model with its natural point family. -/
theorem isAnalytification_affineSchemePointFamily
    (hHom : ∀ (S T : LocalizedCategory.{u, u, u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget etale ⊤ S ⋙ Over.forget S).op ⋙ yoneda.obj T)) :
    IsAnalytification K ((schemeToSpace _).obj (ringTest K A))
      (AffineAnalytification.localized K P) (affineSchemePointFamily K P) := by
  obtain ⟨e, he⟩ := affineIsoOfIsAnalytification (P := P) hp hHom
  let q : PointFamily K ((schemeToSpace _).obj (ringTest K A))
      (AffineAnalytification.localized K P) := fun B _ _ Q x => p B Q x ≫ e.inv
  have h : q = affineSchemePointFamily K P := by
    funext B _ _ Q x
    change p B Q x ≫ e.inv = affineSchemePointFamily K P B Q x
    rw [← affineSchemePointFamily_comp_identity (P := P) hp Q x, ← he,
      Category.assoc, e.hom_inv_id, Category.comp_id]
  exact h ▸ hp.comp_iso e.symm

end Langlands.Analytic.SpaceAnalytification

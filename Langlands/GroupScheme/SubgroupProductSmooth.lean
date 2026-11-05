import Langlands.GroupScheme.QuotientCell
import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Rational.SplitUnipotentProductGeometric
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.Rational.SubgroupIntersectionBaseChangeProperties
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Smooth subgroup products from their actual intersections -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace QuotientCell

/-- An fpqc map with the actual right-coset fibers of a smooth subgroup is smooth. -/
theorem smooth_of_smooth_subgroup
    {S : Scheme.{u}} {G E : GroupScheme S} {Q : Over S}
    (i : E ⟶ G) [Mono i.hom.hom] (q : G.X ⟶ Q)
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hf : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (hE : Smooth E.X.hom) : Smooth q.left := by
  let : Smooth E.X.hom := hE
  have hpb := (multiplication_isPullback i (𝟙 G.X) q hf).map (Over.forget S)
  change IsPullback (multiplication i (𝟙 G.X)).left
    (fst G.X E.X).left q.left ((𝟙 G.X) ≫ q).left at hpb
  simp only [Category.id_comp] at hpb
  have hsource : Smooth (fst G.X E.X).left := by
    change Smooth (pullback.fst G.X.hom E.X.hom)
    infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    hpb.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsource

end QuotientCell

/-- Over an algebraically closed field, a surjective product of two smooth affine
groups is smooth if its scheme-theoretic intersection is smooth. -/
theorem smooth_subgroupProductMap_of_surjective_of_smooth_intersection_algClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {V C U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth V.X.hom] [IsAffineHom V.X.hom]
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    [Smooth U.X.hom] [IsAffineHom U.X.hom]
    (j : V ⟶ U) (c : C ⟶ U) (hc : IsClosedSubgroup c)
    (hE : Smooth (subgroupIntersection j c).X.hom)
    (hsurj : Surjective (subgroupProductMap j c).left) :
    Smooth (subgroupProductMap j c).left := by
  let : Smooth (V ⊗ C).X.hom :=
    prop_tensor_hom (@Smooth) V.X C.X inferInstance inferInstance
  let a := SubgroupProductOrbit.action j c
  let q := a.orbitMap 1
  let e := RelativeRoot.ProductGeometry.secondFactorInversionIso V C
  have he : e.hom ≫ q = subgroupProductMap j c :=
    RelativeRoot.ProductGeometry.secondFactorInversionIso_hom_comp_orbitMap j c
  have : Surjective q.left := by
    have hcomp : Surjective (e.hom.left ≫ q.left) := by
      rw [← Over.comp_left, he]
      exact hsurj
    exact Surjective.of_comp e.hom.left q.left
  let : IsAffineHom (V ⊗ C).X.hom :=
    prop_tensor_hom (@IsAffineHom) V.X C.X inferInstance inferInstance
  let : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k U.X.left U.X.hom
  have htrans : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U.X,
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ (V ⊗ C).X,
        a.act g 1 = y := by
    intro y
    obtain ⟨g, hg⟩ := rationalPoint_lifts_of_surjective q y
    refine ⟨g, ?_⟩
    simpa only [q, SchemeAction.comp_orbitMap, toUnit_unit, Category.id_comp,
      MonObj.comp_one] using hg
  obtain ⟨hflat, _, hqc⟩ :=
    orbitMapFaithfullyFlat k (V ⊗ C) U.X a 1 htrans
  let : Flat q.left := hflat
  let : QuasiCompact q.left := hqc
  let i := SubgroupProductOrbit.intersectionDiagonal j c
  have hi : IsClosedSubgroup i :=
    SubgroupProductOrbit.closed_intersectionDiagonal j c hc
  let : Mono i.hom.hom.left := hi.mono
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Smooth q.left := QuotientCell.smooth_of_smooth_subgroup i q
    (SubgroupProductOrbit.orbit_fibers j c) hE
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  rw [← he, Over.comp_left]
  infer_instance

set_option linter.defProp false in
set_option warn.classDefReducibility false in
/-- Over any field, a surjective product of two smooth affine groups is smooth
if its actual scheme-theoretic intersection is smooth. -/
def smooth_subgroupProductMap_of_surjective_of_smooth_intersection
    {k : Type u} [Field k]
    {V C U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth V.X.hom] [IsAffineHom V.X.hom]
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    [Smooth U.X.hom] [IsAffineHom U.X.hom]
    (j : V ⟶ U) (c : C ⟶ U) (hc : IsClosedSubgroup c)
    (hE : Smooth (subgroupIntersection j c).X.hom)
    (hsurj : Surjective (subgroupProductMap j c).left) :
    Smooth (subgroupProductMap j c).left := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let V' := (GroupScheme.baseChange b).obj V
  let C' := (GroupScheme.baseChange b).obj C
  let U' := (GroupScheme.baseChange b).obj U
  let j' : V' ⟶ U' := (GroupScheme.baseChange b).map j
  let c' : C' ⟶ U' := (GroupScheme.baseChange b).map c
  let : Smooth V'.X.hom := by
    change Smooth (pullback.snd V.X.hom b)
    infer_instance
  let : Smooth C'.X.hom := by
    change Smooth (pullback.snd C.X.hom b)
    infer_instance
  let : Smooth U'.X.hom := by
    change Smooth (pullback.snd U.X.hom b)
    infer_instance
  let : IsAffineHom V'.X.hom := by
    change IsAffineHom (pullback.snd V.X.hom b)
    infer_instance
  let : IsAffineHom C'.X.hom := by
    change IsAffineHom (pullback.snd C.X.hom b)
    infer_instance
  let : IsAffineHom U'.X.hom := by
    change IsAffineHom (pullback.snd U.X.hom b)
    infer_instance
  let : Smooth (subgroupIntersection j c).X.hom := hE
  have hE' : Smooth (subgroupIntersection j' c').X.hom :=
    smooth_subgroupIntersection_baseChange b j c
  let e := subgroupMultiplicationBaseChangeIso b V C
  have he := subgroupMultiplication_baseChange b j c
  have hsurj' : Surjective (subgroupProductMap j' c').left := by
    have hb : Surjective ((Over.pullback b).map (subgroupMultiplication j c)).left :=
      MorphismProperty.of_isPullback (P := @Surjective)
        (overBaseChange_isPullback b (subgroupMultiplication j c)).flip hsurj
    rw [← he, Over.comp_left] at hb
    change Surjective (e.hom.left ≫ (subgroupProductMap j' c').left) at hb
    exact Surjective.of_comp e.hom.left _
  have hsm' := smooth_subgroupProductMap_of_surjective_of_smooth_intersection_algClosed
    (k := AlgebraicClosure k) (V := V') (C := C') (U := U')
    j' c' (hc.baseChange b) hE' hsurj'
  exact (smooth_surjective_subgroupMultiplication_of_fieldExtension
    (K := AlgebraicClosure k) j c hsm' hsurj').1

end Langlands.GroupScheme

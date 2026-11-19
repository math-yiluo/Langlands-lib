import Langlands.GroupScheme.CocycleRelativeTrivialization
import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.GroupScheme.AffinePointTopologicalGroup
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Matching the quotient images of cocycle trivializations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

private theorem coboundary_mul_section {S : Scheme.{u}} {G : GroupScheme S}
    {U Z : Over S} (v : U ⟶ G.X) (y : Over.mk (𝟙 S) ⟶ G.X) (a b : Z ⟶ U) :
    (coboundary (v * (toUnit U ≫ y))).toFun a b = (coboundary v).toFun a b := by
  simp only [coboundary, MonObj.comp_mul, ← Category.assoc, comp_toUnit]
  group

section CompatibleCover

variable {S S' : Scheme.{u}} {G Q : GroupScheme S} {U : Over S}
    (q : G ⟶ Q) (p : S' ⟶ S) {V : Over S'} (r : (Over.map p).obj V ⟶ U)

local notation "Gₚ" => Functor.obj (GroupScheme.baseChange p) G
local notation "Qₚ" => Functor.obj (GroupScheme.baseChange p) Q
local notation "qₚ" => CategoryTheory.Functor.map (GroupScheme.baseChange p) q
local notation "P'" => Over.mk (𝟙 S')

/-- The left translate by `c` of the image of the local group points, viewed
as quotient points on the test `S' ⟶ S`. -/
def quotientPointTranslate (c : P' ⟶ (Qₚ).X) : Set ((Over.map p).obj P' ⟶ Q.X) :=
  Set.range fun h : P' ⟶ (Gₚ).X =>
    baseChangePointsEquiv p Q P' (c * (h ≫ (qₚ).hom.hom))

/-- If each local translate of the image of the quotient map contains a base
quotient point, quotient and ambient trivializing cochains can be corrected
by sections so their images agree on the compatible cover. -/
theorem exists_compatible_quotient_trivializations [EffectiveEpi V.hom]
    (hcoset : ∀ c : P' ⟶ (Qₚ).X,
      ∃ y : Over.mk (𝟙 S) ⟶ Q.X,
        toUnit ((Over.map p).obj P') ≫ y ∈ quotientPointTranslate q p c)
    {ξ : Cocycle G U} (hv : (ξ.map q).IsTrivial) (hf : (ξ.baseChange p V r).IsTrivial) :
    ∃ (v : U ⟶ Q.X) (f : V ⟶ (Gₚ).X),
      (∀ {Z : Over S} (a b : Z ⟶ U),
        (ξ.map q).toFun a b = (coboundary v).toFun a b) ∧
      (∀ {Z : Over S'} (a b : Z ⟶ V),
        (ξ.baseChange p V r).toFun a b = (coboundary f).toFun a b) ∧
      baseChangePointsEquiv p Q V (f ≫ (qₚ).hom.hom) = r ≫ v := by
  obtain ⟨v, hv⟩ := hv
  obtain ⟨f, hf⟩ := hf
  let v' := (baseChangePointsEquiv p Q V).symm (r ≫ v)
  have heq {Z : Over S'} (a b : Z ⟶ V) :
      (coboundary v').toFun a b = (coboundary (f ≫ (qₚ).hom.hom)).toFun a b := by
    apply (baseChangePointsEquiv p Q Z).injective
    have hv' := hv ((Over.map p).map a ≫ r) ((Over.map p).map b ≫ r)
    simp only [Category.assoc] at hv'
    have h := congrArg (baseChangePointsEquiv p Q Z)
      (congrArg (fun x => x ≫ (qₚ).hom.hom) (hf a b))
    change baseChangePointsEquiv p Q Z ((ξ.baseChange p V r).toFun a b ≫ (qₚ).hom.hom) =
      baseChangePointsEquiv p Q Z (((a ≫ f) * (b ≫ f)⁻¹) ≫ (qₚ).hom.hom) at h
    rw [baseChangePointsEquiv_comp, baseChange_toFun] at h
    change (ξ.map q).toFun ((Over.map p).map a ≫ r) ((Over.map p).map b ≫ r) = _ at h
    rw [hv'] at h
    simpa only [coboundary, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, map_mul,
      map_inv, baseChangePointsEquiv_naturality, v', MulEquiv.apply_symm_apply] using h
  let w := v'⁻¹ * (f ≫ (qₚ).hom.hom)
  obtain ⟨s, hs, hs'⟩ := exists_section_of_forall_eq w (fun {Z} a b => by
    have hh := heq a b
    change (a ≫ v') * (b ≫ v')⁻¹ =
      (a ≫ f ≫ (qₚ).hom.hom) * (b ≫ f ≫ (qₚ).hom.hom)⁻¹ at hh
    simp only [w, MonObj.comp_mul, GrpObj.comp_inv]
    calc
      _ = (a ≫ v')⁻¹ * ((a ≫ f ≫ (qₚ).hom.hom) * (b ≫ f ≫ (qₚ).hom.hom)⁻¹) *
          (b ≫ f ≫ (qₚ).hom.hom) := by group
      _ = _ := by rw [← hh]; group)
  let c : P' ⟶ (Qₚ).X := Over.homMk s hs'
  have hc : toUnit V ≫ c = w := Over.OverMorphism.ext hs
  obtain ⟨y, h, hy⟩ := hcoset c
  refine ⟨v * (toUnit U ≫ y), f * (toUnit V ≫ h), ?_, ?_, ?_⟩
  · intro Z a b
    rw [coboundary_mul_section]
    exact hv a b
  · intro Z a b
    rw [coboundary_mul_section]
    exact hf a b
  · have hlocal : (f * (toUnit V ≫ h)) ≫ (qₚ).hom.hom =
        v' * (toUnit V ≫ (c * (h ≫ (qₚ).hom.hom))) := by
      simp only [MonObj.mul_comp, MonObj.comp_mul, hc, w, Category.assoc]
      group
    rw [hlocal, map_mul, baseChangePointsEquiv_naturality]
    change baseChangePointsEquiv p Q V v' *
      ((Over.map p).map (toUnit V) ≫ baseChangePointsEquiv p Q P' (c * (h ≫ (qₚ).hom.hom))) = _
    change baseChangePointsEquiv p Q P' (c * (h ≫ (qₚ).hom.hom)) =
      toUnit ((Over.map p).obj P') ≫ y at hy
    rw [hy]
    simp only [v', MulEquiv.apply_symm_apply, MonObj.comp_mul,
      ← Category.assoc, comp_toUnit]
    exact congrArg (fun t : (Over.map p).obj V ⟶ Over.mk (𝟙 S) =>
      (r ≫ v) * (t ≫ y)) (comp_toUnit ((Over.map p).map (toUnit V)))

end CompatibleCover

section CompleteField

variable {k F : Type u} [Field k] [NontriviallyNormedField F] [CompleteSpace F]
    [Algebra k F] {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] [IsAffine Q.X.left] (q : G ⟶ Q) [Smooth q.hom.hom.left]

local notation "p" => Spec.algebraMap k F
local notation "Gₚ" => Functor.obj (GroupScheme.baseChange p) G
local notation "Qₚ" => Functor.obj (GroupScheme.baseChange p) Q
local notation "qₚ" => CategoryTheory.Functor.map (GroupScheme.baseChange p) q
local notation "P'" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

/-- Density on quotient points and smoothness of the group map imply that
every left translate of its image over `F` meets the image of the base points. -/
theorem exists_quotient_point_in_translate
    (hdense : DenseRange (fun y : RingPoint k Q.X k => y.changeRing (Algebra.ofId k F)))
    (c : P' ⟶ (Qₚ).X) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X,
      toUnit ((Over.map p).obj P') ≫ y ∈ quotientPointTranslate q p c := by
  let : IsAffine (Gₚ).X.left := inferInstanceAs (IsAffine
    (CategoryTheory.Limits.pullback G.X.hom p))
  let : IsAffine (Qₚ).X.left := inferInstanceAs (IsAffine
    (CategoryTheory.Limits.pullback Q.X.hom p))
  let : Smooth (qₚ).hom.hom.left :=
    MorphismProperty.of_isPullback (overBaseChange_isPullback p q.hom.hom).flip inferInstance
  let A := CommAlgCat.of F F
  let : TopologicalSpace A := inferInstanceAs (TopologicalSpace F)
  let : IsTopologicalRing A := inferInstanceAs (IsTopologicalRing F)
  let : TopologicalSpace ((Gₚ).affinePoints A) := (Gₚ).affinePointsTopologicalSpace A
  let : TopologicalSpace ((Qₚ).affinePoints A) := (Qₚ).affinePointsTopologicalSpace A
  let : IsTopologicalGroup ((Qₚ).affinePoints A) := (Qₚ).affinePointsIsTopologicalGroup A
  let eG := (Gₚ).affinePointsRingPointHomeomorph A
  let eQ := (Qₚ).affinePointsRingPointHomeomorph A
  let c' : (Qₚ).affinePoints A := (ringTestSelfIso F).hom ≫ c
  let qpoints : (Gₚ).affinePoints A → (Qₚ).affinePoints A := fun h => h ≫ (qₚ).hom.hom
  let corr : (Gₚ).affinePoints A → (Qₚ).affinePoints A := fun h => c' * qpoints h
  have hq : IsOpenMap qpoints := by
    have heq : qpoints = eQ.symm ∘ (fun x : RingPoint F (Gₚ).X F => x ≫ (qₚ).hom.hom) ∘ eG := by
      funext h
      apply eQ.injective
      exact (affinePointsRingPointHomeomorph_postcomp (Gₚ) A (qₚ).hom.hom h).trans
        (eQ.apply_symm_apply (eG h ≫ (qₚ).hom.hom)).symm
    rw [heq]
    exact eQ.symm.isOpenMap.comp
      ((isOpenMap_affineSmoothPointMap F (qₚ).hom.hom).comp eG.isOpenMap)
  have hopen : IsOpenMap (eQ ∘ corr) :=
    eQ.isOpenMap.comp ((Homeomorph.mulLeft c').isOpenMap.comp hq)
  let E := ringPointBaseChangeEquiv k F F Q.X
  have hE : IsHomeomorph E := isHomeomorph_ringPointBaseChangeEquiv k F F Q.X
  have hdense' : DenseRange (fun y : RingPoint k Q.X k =>
      E (y.changeRing (Algebra.ofId k F))) := E.surjective.denseRange.comp hdense hE.continuous
  obtain ⟨y, hy⟩ := hdense'.exists_mem_open (s := Set.range (eQ ∘ corr))
    (by rw [← Set.image_univ]; exact hopen _ isOpen_univ)
    (Set.range_nonempty _)
  obtain ⟨h, hh⟩ := hy
  let y₀ := (rationalPointEquiv k Q.X).symm y
  let h₀ : P' ⟶ (Gₚ).X := (ringTestSelfIso F).inv ≫ h
  refine ⟨y₀, h₀, ?_⟩
  symm
  apply Over.OverMorphism.ext
  have hh' : E (y.changeRing (Algebra.ofId k F)) =
      (ringTestSelfIso F).hom ≫ (c * (h₀ ≫ (qₚ).hom.hom)) := by
    rw [← hh]
    change (Qₚ).affinePointsRingPointHomeomorph A (c' * (h ≫ (qₚ).hom.hom)) = _
    have hh₀ : (ringTestSelfIso F).hom ≫ h₀ = h := Iso.hom_inv_id_assoc _ _
    rw [affinePointsRingPointHomeomorph_apply, MonObj.comp_mul, ← Category.assoc, hh₀]
    rfl
  let yF : RingPoint k Q.X F := y.changeRing (Algebra.ofId k F)
  have hh'' := congrArg (fun (x : RingPoint F (Qₚ).X F) =>
    x.left ≫ CategoryTheory.Limits.pullback.fst Q.X.hom p) hh'
  have hleft := (ringPointBaseChangeEquiv_left_fst k F F Q.X yF).symm.trans hh''
  change p ≫ y₀.left = _
  rw [baseChangePointsEquiv_left]
  rw [show y₀.left = y.left from rationalPointEquiv_symm_left k Q.X y]
  change p ≫ y.left =
    (𝟙 _ ≫ (c * (h₀ ≫ (qₚ).hom.hom)).left) ≫ CategoryTheory.Limits.pullback.fst Q.X.hom p at hleft
  simpa only [Category.id_comp] using hleft

end CompleteField

end Langlands.GroupScheme.Cocycle

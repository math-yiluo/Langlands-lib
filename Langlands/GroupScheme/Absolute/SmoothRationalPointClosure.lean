import Langlands.GroupScheme.Absolute.RationalPointCommutativeSubgroup
import Langlands.GroupScheme.ImageGenerationJointInjective
import Langlands.GroupScheme.ImageGenerationFinitePower
import Langlands.GroupScheme.Rational.Characters

/-! # Geometric reducedness of rational-point closures over arbitrary fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.RationalPointClosure

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]

/-- Separation by rational evaluations gives separation of global sections of the spectrum. -/
theorem algSpec_appTop_eq_zero_of_separating
    {B : CommAlgCat.{u} (CommRingCat.of k)} {J : Type*}
    (χ : J → (B ⟶ baseAlgebra k))
    (hχ : ∀ b : B, (∀ j, (χ j).hom b = 0) → b = 0)
    (s : Γ(((algSpec (CommRingCat.of k)).obj (op B)).left, ⊤))
    (hs : ∀ j, ((algSpec (CommRingCat.of k)).map (χ j).op).left.appTop.hom s = 0) :
    s = 0 := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s = 0 := by
    apply hχ
    intro j
    have hn := congrArg (fun f : Γ(Spec (CommRingCat.of B), ⊤) ⟶ CommRingCat.of k =>
      f.hom s) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (χ j).hom.toRingHom))
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
      (((algSpec (CommRingCat.of k)).map (χ j).op).left.appTop.hom s) =
        (χ j).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s) at hn
    rw [hs j, map_zero] at hn
    exact hn.symm
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).1
    (h.trans (map_zero _).symm)

/-- An affine scheme whose coordinate algebra is separated by rational evaluations is
geometrically reduced, even over an imperfect field. -/
theorem geometricallyReduced_algSpec_of_separating
    {B : CommAlgCat.{u} (CommRingCat.of k)} {J : Type*}
    (χ : J → (B ⟶ baseAlgebra k))
    (hχ : ∀ b : B, (∀ j, (χ j).hom b = 0) → b = 0) :
    GeometricallyReduced ((algSpec (CommRingCat.of k)).obj (op B)).hom := by
  let X := (algSpec (CommRingCat.of k)).obj (op B)
  let P := (algSpec (CommRingCat.of k)).obj (op (baseAlgebra k))
  let a : J → (P ⟶ X) := fun j => (algSpec (CommRingCat.of k)).map (χ j).op
  have : IsIso P.hom := by
    change IsIso (Spec.map (𝟙 (CommRingCat.of k)))
    infer_instance
  have : GeometricallyReduced P.hom := ImageGeneration.geometricallyReduced_of_isIso P.hom
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  let Y : Over (Spec (CommRingCat.of k)) := Over.mk x
  have : IsAffine X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
  have : IsAffine P.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  have : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have : IsReduced (P ⊗ Y).left :=
    pullback_of_geometrically GeometricallyReduced.geometrically_isReduced K x
  change IsReduced (X ⊗ Y).left
  have : _root_.IsReduced Γ((X ⊗ Y).left, ⊤) := by
    refine ⟨fun s hs => ImageGeneration.appTop_tensorHom_eq_zero a
      (fun _ : Unit => 𝟙 Y) (algSpec_appTop_eq_zero_of_separating χ hχ)
      (fun s hs => by simpa using hs ()) s fun j _ => ?_⟩
    exact (hs.map (a j ⊗ₘ 𝟙 Y).left.appTop.hom).eq_zero
  have : IsAffine (X ⊗ Y).left :=
    inferInstanceAs (IsAffine (pullback X.hom Y.hom))
  exact isReduced_of_isAffine_isReduced _

variable {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (Delta : Subgroup (F.obj (baseAlgebra k)))

/-- The schematic closure of a group of rational points is geometrically reduced. -/
theorem geometricallyReduced_closure :
    GeometricallyReduced
      (Corepresented.cutGroupScheme (isCutOutBy_closureSubgroup e Delta)).X.hom := by
  exact geometricallyReduced_algSpec_of_separating
    (fun gamma : Delta => RationalPointClosure.lift gamma.1 (mem_cutSet_of_mem gamma.2))
    eq_zero_of_forall_lift

end Langlands.GroupScheme.RationalPointClosure

namespace Langlands.GroupScheme

/-- An actual smooth affine commutative closed subgroup containing the given rational point. -/
structure SmoothCommutativePointEnvelope {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (x : rationalPoints G) where
  group : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : group.toGrp ⟶ G
  point : rationalPoints group.toGrp
  closed : IsClosedSubgroup inclusion
  smooth : Smooth group.toGrp.X.hom
  affine : IsAffineHom group.toGrp.X.hom
  point_inclusion : rationalPoints.map inclusion point = x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
open RationalPointClosure in
/-- The schematic closure of the integer powers, with its actual rational point. -/
def smoothCommutativePointEnvelope {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (x : rationalPoints G) :
    SmoothCommutativePointEnvelope G x := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let hex := (essImage_algSpec (G := G.X)).mpr this
  let B : CommAlgCat.{u} (CommRingCat.of k) := hex.choose.unop
  let j : (algSpec (CommRingCat.of k)).obj (op B) ≅ G.X :=
    Classical.choice hex.choose_spec
  let e := AffineLinearEmbedding.corepresentableBy G j
  let baseIso : (algSpec (CommRingCat.of k)).obj (op (baseAlgebra k)) ≅
      Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change 𝟙 (Spec (CommRingCat.of k)) ≫ 𝟙 _ = Spec.map (𝟙 _)
      simp)
  let x' : Lie.AffinePoints G k := baseIso.hom ≫ x
  let Delta : Subgroup (G.affinePointFunctor.obj (baseAlgebra k)) := Subgroup.zpowers x'
  let : IsMulCommutative Delta := Subgroup.zpowers_isMulCommutative x'
  have hI := isCutOutBy_closureSubgroup e Delta
  let C : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { toGrp := Corepresented.cutGroupScheme hI
      comm := isCommMonObj_closure e Delta }
  let z : C.toGrp ⟶ G :=
    Corepresented.cutHom hI ≫ (AffineLinearEmbedding.modelIso G j).hom
  have hj : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget _).map j.hom))
  have hz : IsClosedSubgroup z := by
    have : IsClosedImmersion (Corepresented.cutHom hI).hom.hom.left :=
      Corepresented.isClosedImmersion_cutHom hI
    change IsClosedImmersion
      ((Corepresented.cutHom hI).hom.hom.left ≫
        (AffineLinearEmbedding.modelIso G j).hom.hom.hom.left)
    rw [modelIso_hom_hom_hom]
    infer_instance
  have : IsClosedImmersion z.hom.hom.left := hz
  have hfin : LocallyOfFiniteType C.toGrp.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  have haff : IsAffineHom C.toGrp.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  have hsm : Smooth C.toGrp.X.hom := by
    have : GeometricallyReduced C.toGrp.X.hom := geometricallyReduced_closure e Delta
    have : LocallyOfFiniteType C.toGrp.X.hom := hfin
    have : GrpObj (Over.mk C.toGrp.X.hom) := inferInstanceAs (GrpObj C.toGrp.X)
    exact smooth_of_grpObj C.toGrp.X.hom
  have hx : x' ∈ cutSet e Delta (baseAlgebra k) :=
    mem_cutSet_of_mem (Subgroup.mem_zpowers x')
  let y' : Lie.AffinePoints C.toGrp k := by
    change (algSpec (CommRingCat.of k)).obj (op (baseAlgebra k)) ⟶
      (algSpec (CommRingCat.of k)).obj (op (quotient e Delta))
    exact (algSpec (CommRingCat.of k)).map (lift (e := e) (Γ := Delta) x' hx).op
  have hy : y' ≫ z.hom.hom = x' := by
    have hc : (Corepresented.cutHom hI).hom.hom =
        (algSpec _).map (Corepresented.quotientMap (vanishingIdeal e Delta)).op := by
      apply Over.OverMorphism.ext
      exact Corepresented.cutHom_left hI
    change (algSpec _).map (lift (e := e) (Γ := Delta) x' hx).op ≫
      ((Corepresented.cutHom hI).hom.hom ≫
        (AffineLinearEmbedding.modelIso G j).hom.hom.hom) = x'
    rw [hc, modelIso_hom_hom_hom, ← Category.assoc, ← Functor.map_comp, ← op_comp,
      quotientMap_comp_lift]
    exact e.homEquiv.apply_symm_apply x'
  refine ⟨C, z, baseIso.inv ≫ y', hz, hsm, haff, ?_⟩
  change (baseIso.inv ≫ y') ≫ z.hom.hom = x
  rw [Category.assoc, hy]
  exact baseIso.inv_hom_id_assoc x

end Langlands.GroupScheme

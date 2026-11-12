import Langlands.AlgebraicGeometry.Picard.FieldSmoothAutomorphisms
import Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedClasses
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Group schemes of relative global units and the quotient along a finite subscheme -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativeUnitGroupSchemes

open Langlands.GroupScheme

section Generic

variable {S X : Scheme.{u}} (f : X ⟶ S) (U : Over S)
  (e : (AlgebraicSpace.schemeYoneda S).obj U ≅ RelativeGlobalUnits.presheaf f)

/-- The relative global units of `f` as a presheaf of groups. -/
abbrev groupPresheaf : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  RelativeGlobalUnits.groupPresheaf f ⋙ forget₂ CommGrpCat GrpCat

/-- A representing object of the relative global units represents the group presheaf. -/
def representableBy : (groupPresheaf f ⋙ forget GrpCat).RepresentableBy U where
  homEquiv {T} :=
    { toFun := fun x ↦ (e.hom.app (op T) ⟨x⟩).down
      invFun := fun a ↦ (e.inv.app (op T) ⟨a⟩).down
      left_inv := fun x ↦
        congrArg ULift.down (ConcreteCategory.congr_hom (e.hom_inv_id_app (op T)) ⟨x⟩)
      right_inv := fun a ↦
        congrArg ULift.down (ConcreteCategory.congr_hom (e.inv_hom_id_app (op T)) ⟨a⟩) }
  homEquiv_comp h x := congrArg ULift.down (NatTrans.naturality_apply e.hom h.op ⟨x⟩)

/-- The group scheme of relative global units of `f`, carried by `U`. -/
def group : GroupScheme S :=
  letI := GrpObj.ofRepresentableBy U (groupPresheaf f) (representableBy f U e)
  Grp.mk U

/-- Points of the unit group scheme are the relative global units. -/
def pointsEquiv (T : Over S) :
    (T ⟶ (group f U e).X) ≃* RelativeGlobalUnits.sections f T where
  toEquiv := (representableBy f U e).homEquiv
  map_mul' x y :=
    ((yonedaGrpObjIsoOfRepresentableBy U (groupPresheaf f) (representableBy f U e)).hom.app
      (op T)).hom.map_mul x y

lemma pointsEquiv_comp {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (group f U e).X) :
    pointsEquiv f U e T' (a ≫ x) =
      RelativeGlobalUnits.restriction f a (pointsEquiv f U e T x) :=
  (representableBy f U e).homEquiv_comp a x

variable {X' : Scheme.{u}} {f' : X' ⟶ S} (U' : Over S)
  (e' : (AlgebraicSpace.schemeYoneda S).obj U' ≅ RelativeGlobalUnits.presheaf f')
  (β : RelativeGlobalUnits.groupPresheaf f ⟶ RelativeGlobalUnits.groupPresheaf f')

lemma naturality_apply {T T' : Over S} (a : T' ⟶ T) (r : RelativeGlobalUnits.sections f T) :
    (β.app (op T')).hom (RelativeGlobalUnits.restriction f a r) =
      RelativeGlobalUnits.restriction f' a ((β.app (op T)).hom r) :=
  DFunLike.congr_fun (congrArg CommGrpCat.Hom.hom (β.naturality a.op)) r

/-- The natural transformation of point groups induced by `β`. -/
def pointsNatTrans : yonedaGrp.obj (group f U e) ⟶ yonedaGrp.obj (group f' U' e') where
  app T := GrpCat.ofHom ((pointsEquiv f' U' e' T.unop).symm.toMonoidHom.comp
    ((β.app T).hom.comp (pointsEquiv f U e T.unop).toMonoidHom))
  naturality {T T'} a := by
    ext x
    apply (pointsEquiv f' U' e' T'.unop).injective
    change pointsEquiv f' U' e' T'.unop ((pointsEquiv f' U' e' T'.unop).symm
        ((β.app T').hom (pointsEquiv f U e T'.unop (a.unop ≫ x)))) =
      pointsEquiv f' U' e' T'.unop (a.unop ≫ (pointsEquiv f' U' e' T.unop).symm
        ((β.app T).hom (pointsEquiv f U e T.unop x)))
    rw [MulEquiv.apply_symm_apply, pointsEquiv_comp, pointsEquiv_comp, MulEquiv.apply_symm_apply]
    exact naturality_apply f β a.unop _

/-- The homomorphism of unit group schemes induced by `β`. -/
def hom : group f U e ⟶ group f' U' e' :=
  yonedaGrpFullyFaithful.preimage (pointsNatTrans f U e U' e' β)

lemma pointsEquiv_comp_hom {T : Over S} (x : T ⟶ (group f U e).X) :
    pointsEquiv f' U' e' T (x ≫ (hom f U e U' e' β).hom.hom) =
      (β.app (op T)).hom (pointsEquiv f U e T x) := by
  have h := congrArg (fun α ↦ (α.app (op T)).hom x)
    (yonedaGrpFullyFaithful.map_preimage (pointsNatTrans f U e U' e' β))
  change x ≫ (hom f U e U' e' β).hom.hom = (pointsEquiv f' U' e' T).symm
    ((β.app (op T)).hom (pointsEquiv f U e T x)) at h
  rw [h, MulEquiv.apply_symm_apply]

end Generic

section Candidate

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
  (b : Module.Basis (Fin n) k A)

/-- A nonempty determinant-open unit candidate is connected: its coordinate ring is a
localization of a polynomial ring at a nonzero element. -/
lemma candidate_connectedSpace [Nonempty (FiniteAlgebraUnits.candidate b).left] :
    ConnectedSpace (FiniteAlgebraUnits.candidate b).left := by
  obtain ⟨x⟩ := ‹Nonempty (FiniteAlgebraUnits.candidate b).left›
  change PrimeSpectrum (FiniteAlgebraUnits.candidateRing b) at x
  have hdet : FiniteAlgebraUnits.determinant b ≠ 0 := by
    intro h0
    have hu : IsUnit (algebraMap (FiniteAlgebraUnits.coordinateRing k n)
        (FiniteAlgebraUnits.candidateRing b) (FiniteAlgebraUnits.determinant b)) :=
      IsLocalization.Away.algebraMap_isUnit _
    rw [congrArg (algebraMap (FiniteAlgebraUnits.coordinateRing k n)
      (FiniteAlgebraUnits.candidateRing b)) h0, map_zero] at hu
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Submodule.zero_mem _) hu)
  have : IsDomain (FiniteAlgebraUnits.candidateRing b) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hdet)
  change ConnectedSpace (Spec (CommRingCat.of (FiniteAlgebraUnits.candidateRing b)))
  infer_instance

end Candidate

section Field

open Langlands.AlgebraicGeometry.Modules

variable {k : Type u} [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The unit group scheme of a proper scheme over a field, carried by the published
determinant-open unit scheme. -/
abbrev fieldGroup [IsProper f] : GroupScheme (Spec (CommRingCat.of k)) :=
  group f (PicardGroupoid.fieldUnitScheme f) (PicardGroupoid.fieldUnitSchemeIso f)

variable [IsProper f]

/-- Points of the unit group scheme of a proper scheme over a field. -/
abbrev fieldPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (fieldGroup f).X) ≃* RelativeGlobalUnits.sections f T :=
  pointsEquiv f _ (PicardGroupoid.fieldUnitSchemeIso f) T

instance fieldGroup_smooth : Smooth (fieldGroup f).X.hom :=
  PicardGroupoid.fieldUnitScheme_smooth f

instance fieldGroup_isAffine : IsAffine (fieldGroup f).X.left := by
  let := GlobalFunctionsAlgebra.algebra f
  let := FieldGlobalFunctions.finite_algebra f
  change IsAffine (Spec (CommRingCat.of
    (FiniteAlgebraUnits.candidateRing (Module.finBasis k Γ(X, ⊤)))))
  infer_instance

instance fieldGroup_nonempty : Nonempty (fieldGroup f).X.left := by
  have : Nonempty (Spec (CommRingCat.of k)) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact ⟨(1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (fieldGroup f).X).left
    (Nonempty.some this)⟩

instance fieldGroup_connectedSpace : ConnectedSpace (fieldGroup f).X.left := by
  let := GlobalFunctionsAlgebra.algebra f
  let := FieldGlobalFunctions.finite_algebra f
  have : Nonempty (FiniteAlgebraUnits.candidate (Module.finBasis k Γ(X, ⊤))).left :=
    fieldGroup_nonempty f
  exact candidate_connectedSpace (Module.finBasis k Γ(X, ⊤))

variable (g : Z ⟶ Spec (CommRingCat.of k)) (z : Z ⟶ X) (hz : z ≫ f = g)

open SubschemeRigidification

/-- Pulling back global units along `T ×_k Z ⟶ T ×_k X`. -/
def unitsNatTrans : RelativeGlobalUnits.groupPresheaf f ⟶ RelativeGlobalUnits.groupPresheaf g where
  app T := CommGrpCat.ofHom
    (Units.map ((zRel f g z hz).app T.unop).appTop.hom.toMonoidHom)
  naturality {T T'} a := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro r
    apply Units.ext
    let r₀ : RelativeGlobalUnits.sections f T.unop := r
    let r' : Γ((relativeSpace f).obj T.unop, ⊤) := r₀.val
    change ((zRel f g z hz).app T'.unop).appTop (((relativeSpace f).map a.unop).appTop r') =
      ((relativeSpace g).map a.unop).appTop (((zRel f g z hz).app T.unop).appTop r')
    have h := congrArg (fun m ↦ m.appTop r') ((zRel f g z hz).naturality a.unop)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
    exact h.symm

variable [IsProper g]

/-- The homomorphism of unit group schemes induced by `z`. -/
def unitsHom : fieldGroup f ⟶ fieldGroup g :=
  hom f _ _ _ _ (unitsNatTrans f g z hz)

lemma pointsEquiv_unitsHom {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ (fieldGroup f).X) :
    fieldPointsEquiv g T (x ≫ (unitsHom f g z hz).hom.hom) =
      Units.map ((zRel f g z hz).app T).appTop.hom.toMonoidHom (fieldPointsEquiv f T x) :=
  pointsEquiv_comp_hom f _ _ _ _ (unitsNatTrans f g z hz) x

lemma mono_unitsHom (hinj : ∀ T, Function.Injective ((zRel f g z hz).app T).appTop) :
    Mono (unitsHom f g z hz).hom.hom := by
  constructor
  intro T a b hab
  apply (fieldPointsEquiv f T).injective
  have h := congrArg (fieldPointsEquiv g T) hab
  rw [pointsEquiv_unitsHom, pointsEquiv_unitsHom] at h
  exact Units.ext (hinj T (congrArg Units.val h))

lemma range_unitsHom_isNormal : (SubgroupFunctor.range (unitsHom f g z hz)).IsNormal := by
  intro T x y _ hy
  have : x * y * x⁻¹ = y := by
    apply (fieldPointsEquiv g T).injective
    rw [map_mul, map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  rw [this]
  exact hy

/-- **The quotient of the units of `Z` by the units of `X`.** If pulling back global functions
along `T ×_k Z ⟶ T ×_k X` is injective for every test `T`, there is a smooth affine group
scheme `Q` with a smooth fppf quotient map from the units of `Z` whose kernel consists exactly
of the units coming from `T ×_k X`. -/
theorem exists_quotient (hinj : ∀ T, Function.Injective ((zRel f g z hz).app T).appTop) :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : fieldGroup g ⟶ Q),
      Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧ Flat q.hom.hom.left ∧
        Surjective q.hom.hom.left ∧ LocallyOfFinitePresentation q.hom.hom.left ∧
        IsAffineHom q.hom.hom.left ∧ Smooth q.hom.hom.left ∧
        ∀ {T : Over (Spec (CommRingCat.of k))} (h : T ⟶ (fieldGroup g).X),
          h ≫ q.hom.hom = 1 ↔ fieldPointsEquiv g T h ∈
            (Units.map ((zRel f g z hz).app T).appTop.hom.toMonoidHom).range := by
  have := mono_unitsHom f g z hz hinj
  have hclosed := HomImage.isClosedSubgroup_of_mono (unitsHom f g z hz)
  obtain ⟨Q, q, hQs, hQa, hq⟩ := normalSubgroupQuotient k (fieldGroup g) (fieldGroup f)
    (unitsHom f g z hz) hclosed (range_unitsHom_isNormal f g z hz)
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have hsm := hq.smooth_of_smooth_kernel (z := unitsHom f g z hz) ⟨inferInstance, rfl⟩
    (fieldGroup_smooth f)
  refine ⟨Q, q, hQs, hQa, hq.1, hq.2.1, hq.2.2.1, inferInstance, hsm, ?_⟩
  intro T h
  rw [← mem_range_kernelι_iff, hq.2.2.2, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨fieldPointsEquiv f T y, (pointsEquiv_unitsHom f g z hz y).symm⟩
  · rintro ⟨r, hr⟩
    refine ⟨(fieldPointsEquiv f T).symm r, ?_⟩
    apply (fieldPointsEquiv g T).injective
    rw [pointsEquiv_unitsHom, MulEquiv.apply_symm_apply]
    exact hr

end Field

end Langlands.AlgebraicGeometry.Picard.RelativeUnitGroupSchemes

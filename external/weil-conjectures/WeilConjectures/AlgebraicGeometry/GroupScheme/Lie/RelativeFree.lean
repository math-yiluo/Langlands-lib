/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.RelativePoints
public import WeilConjectures.AlgebraicGeometry.SmoothUniformizer

/-!
# Infinitesimal points with values in a scheme form a free module

Let `G` be a group scheme locally of finite type over a field `k`, `X` a scheme over `k`, and
`(b_i)` a basis of `Lie(G)`. Every infinitesimal point `v : X[ε] ⟶ G` with values in `X` is
uniquely a product `∏ᵢ (b_i)_X(rᵢ ε)` of rescaled base changes of the `b_i`, with `rᵢ` global
functions on `X` (`AlgebraicGeometry.GrpObj.existsUnique_prod_eq`): the infinitesimal points with
values in `X` are `Lie(G) ⊗_k Γ(X, 𝒪_X)`.

The proof goes through an affine chart `j : Spec A ⟶ G` at the identity with a `k`-point `e` of
`A` over the identity. A point `v` has the same underlying map as the identity of `G(X)`, so it
factors through `j`; it is then given by a ring homomorphism `ψ_v : A → Γ(X, 𝒪_X)[ε]` of the form
`a ↦ e(a) + ε D_v(a)`, with `D_v` a derivation at `e`. The group law is the addition of the `D_v`
(the point `v_ε w_δ` over `X[ε][δ]` restricted along `δ = ε`), rescaling multiplies `D_v` by the
function, and a derivation at `e` is determined by its values on lifts `a_i ∈ ker e` of a basis
of `(ker e)/(ker e)²` dual to `(b_i)`, since `Lie(G)` is the dual of this cotangent space
(`AlgebraicGeometry.GrpObj.lieToDualCotangent`).

## Main statements

- `AlgebraicGeometry.GrpObj.isMulCommutative_infPointsAt`: the infinitesimal points with values in
  `X` commute.
- `AlgebraicGeometry.GrpObj.existsUnique_prod_eq`: they form a free `Γ(X, 𝒪_X)`-module with basis
  the base changes `(b_i)_X` of a basis of `Lie(G)`.

## Blueprint

- `lemma-stable-subspaces-center`: `Lie(G) ⊗ A` as the infinitesimal points of `G` with values in
`A`, on which
  `G(A)` acts by the adjoint action.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj IsMulCommutative

namespace AlgebraicGeometry

/-! ### Morphisms into an affine open subscheme -/

section LiftRingHom

variable {Y Y' Z : Scheme.{u}} {A : CommRingCat.{u}}

theorem Scheme.ΓSpecIso_inv_comp_specMap_appTop {B : CommRingCat.{u}} (ψ : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (Spec.map ψ).appTop = ψ ≫ (Scheme.ΓSpecIso B).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, Scheme.ΓSpecIso_naturality]

theorem Scheme.ΓSpecIso_inv_comp_toSpecΓ_specMap_appTop (ψ : A ⟶ Γ(Y, ⊤)) :
    (Scheme.ΓSpecIso A).inv ≫ (Y.toSpecΓ ≫ Spec.map ψ).appTop = ψ := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, Scheme.ΓSpecIso_inv_comp_specMap_appTop,
    Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

variable (j : Spec A ⟶ Z) [IsOpenImmersion j]

/-- The ring homomorphism `A → Γ(Y, 𝒪_Y)` of a morphism `y : Y ⟶ Z` landing in the image of an
open immersion `j : Spec A ⟶ Z`: `y` is `Y ⟶ Spec Γ(Y, 𝒪_Y) ⟶ Spec A ⟶ Z`. -/
noncomputable def IsOpenImmersion.liftRingHom (y : Y ⟶ Z) (h : Set.range y ⊆ Set.range j) :
    A ⟶ Γ(Y, ⊤) :=
  (Scheme.ΓSpecIso A).inv ≫ (IsOpenImmersion.lift j y h).appTop

theorem IsOpenImmersion.toSpecΓ_comp_liftRingHom (y : Y ⟶ Z) (h : Set.range y ⊆ Set.range j) :
    Y.toSpecΓ ≫ Spec.map (IsOpenImmersion.liftRingHom j y h) ≫ j = y := by
  rw [IsOpenImmersion.liftRingHom, ← Category.assoc,
    Scheme.toSpecΓ_SpecMap_ΓSpecIso_inv_appTop, IsOpenImmersion.lift_fac]

theorem IsOpenImmersion.liftRingHom_congr {y y' : Y ⟶ Z} (e : y = y')
    (h : Set.range y ⊆ Set.range j) (h' : Set.range y' ⊆ Set.range j) :
    IsOpenImmersion.liftRingHom j y h = IsOpenImmersion.liftRingHom j y' h' := by
  subst e
  rfl

theorem IsOpenImmersion.liftRingHom_comp (φ : Y' ⟶ Y) (y : Y ⟶ Z)
    (h : Set.range y ⊆ Set.range j) (h' : Set.range (φ ≫ y) ⊆ Set.range j) :
    IsOpenImmersion.liftRingHom j (φ ≫ y) h' = IsOpenImmersion.liftRingHom j y h ≫ φ.appTop := by
  rw [IsOpenImmersion.liftRingHom, IsOpenImmersion.liftRingHom, Category.assoc,
    ← Scheme.Hom.comp_appTop, ← IsOpenImmersion.lift_uniq j (φ ≫ y) h'
      (φ ≫ IsOpenImmersion.lift j y h) (by rw [Category.assoc, IsOpenImmersion.lift_fac])]

theorem IsOpenImmersion.liftRingHom_injective {y y' : Y ⟶ Z} (h : Set.range y ⊆ Set.range j)
    (h' : Set.range y' ⊆ Set.range j)
    (e : IsOpenImmersion.liftRingHom j y h = IsOpenImmersion.liftRingHom j y' h') : y = y' := by
  rw [← IsOpenImmersion.toSpecΓ_comp_liftRingHom j y h, e,
    IsOpenImmersion.toSpecΓ_comp_liftRingHom]

theorem IsOpenImmersion.liftRingHom_specMap_comp {B : CommRingCat.{u}} (ψ : A ⟶ B)
    (h : Set.range (Spec.map ψ ≫ j) ⊆ Set.range j) :
    IsOpenImmersion.liftRingHom j (Spec.map ψ ≫ j) h = ψ ≫ (Scheme.ΓSpecIso B).inv := by
  rw [IsOpenImmersion.liftRingHom, ← IsOpenImmersion.lift_uniq j _ h (Spec.map ψ) rfl,
    Scheme.ΓSpecIso_inv_comp_specMap_appTop]

end LiftRingHom

/-! ### Global sections of the thickening maps -/

section AppTop

variable {X Y : Scheme.{u}}

theorem Scheme.dualNumbersι_appTop_apply (x : Γ(X.dualNumbers, ⊤)) :
    X.dualNumbersι.appTop x = TrivSqZeroExt.fst x :=
  rfl

theorem Scheme.dualNumbersProj_appTop_apply (x : Γ(X, ⊤)) :
    X.dualNumbersProj.appTop x = (TrivSqZeroExt.inl x : DualNumber Γ(X, ⊤)) :=
  rfl

theorem Scheme.Hom.dualNumbers_appTop_apply (f : X ⟶ Y) (x : Γ(Y.dualNumbers, ⊤)) :
    f.dualNumbers.appTop x = DualNumber.mapRingHom f.appTop.hom x :=
  rfl

theorem Scheme.dualNumbersFold_appTop_apply (x : Γ(X.dualNumbers.dualNumbers, ⊤)) :
    X.dualNumbersFold.appTop x = DualNumber.foldRingHom x :=
  rfl

theorem Scheme.dualNumbersScale_appTop_apply (c : Γ(X, ⊤)) (x : Γ(X.dualNumbers, ⊤)) :
    (X.dualNumbersScale c).appTop x = DualNumber.scale c x := by
  refine (Scheme.dualNumbersScale_app (X := X) c ⊤ x).trans ?_
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

end AppTop

namespace GrpObj

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]

theorem one_points_left : (1 : points G k).left = unitSection G := by
  rw [Hom.one_def, Over.comp_left]
  simp [specOverSpec_over]
  rfl

theorem one_left_eq (X : Over (Spec (.of k))) : (1 : X ⟶ G).left = X.hom ≫ unitSection G := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem unitSection_apply (p : Spec (.of k)) : unitSection G p = onePoint G := by
  rw [Subsingleton.elim p ⟨⊥, Ideal.isPrime_bot⟩]
  rfl

/-! ### Infinitesimal points in an affine chart -/

section Chart

variable {A : Type u} [CommRing A] [Algebra k A] {j : Spec (.of A) ⟶ G.left} [IsOpenImmersion j]

/-- The ring homomorphism `A → Γ(Y, 𝒪_Y)` of a point `y : Y ⟶ G` landing in the chart `j`. -/
noncomputable def chartHomOf {Y : Over (Spec (.of k))} (y : Y ⟶ G)
    (h : Set.range y.left ⊆ Set.range j) : CommRingCat.of A ⟶ Γ(Y.left, ⊤) :=
  IsOpenImmersion.liftRingHom j y.left h

omit [GrpObj G] [Algebra k A] [IsOpenImmersion j] in
theorem range_comp_left_subset {Y Y' : Over (Spec (.of k))} (φ : Y' ⟶ Y) (y : Y ⟶ G)
    (h : Set.range y.left ⊆ Set.range j) : Set.range (φ ≫ y).left ⊆ Set.range j :=
  fun _ ⟨x, hx⟩ ↦ h ⟨φ.left x, hx⟩

omit [GrpObj G] [Algebra k A] in
theorem chartHomOf_comp {Y Y' : Over (Spec (.of k))} (φ : Y' ⟶ Y) (y : Y ⟶ G)
    (h : Set.range y.left ⊆ Set.range j) (h' : Set.range (φ ≫ y).left ⊆ Set.range j) :
    chartHomOf (φ ≫ y) h' = chartHomOf y h ≫ φ.left.appTop :=
  IsOpenImmersion.liftRingHom_comp j φ.left y.left h h'

omit [GrpObj G] [Algebra k A] in
theorem chartHomOf_congr {Y : Over (Spec (.of k))} {y y' : Y ⟶ G} (e : y = y')
    (h : Set.range y.left ⊆ Set.range j) (h' : Set.range y'.left ⊆ Set.range j) :
    chartHomOf y h = chartHomOf y' h' := by
  subst e
  rfl

omit [GrpObj G] [Algebra k A] in
theorem toSpecΓ_comp_chartHomOf {Y : Over (Spec (.of k))} (y : Y ⟶ G)
    (h : Set.range y.left ⊆ Set.range j) :
    Y.left.toSpecΓ ≫ Spec.map (chartHomOf y h) ≫ j = y.left :=
  IsOpenImmersion.toSpecΓ_comp_liftRingHom j y.left h

omit [GrpObj G] [Algebra k A] in
theorem chartHomOf_injective {Y : Over (Spec (.of k))} {y y' : Y ⟶ G}
    (h : Set.range y.left ⊆ Set.range j) (h' : Set.range y'.left ⊆ Set.range j)
    (e : chartHomOf y h = chartHomOf y' h') : y = y' :=
  Over.OverMorphism.ext (IsOpenImmersion.liftRingHom_injective j h h' e)

variable {e : A →ₐ[k] k}
  (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j = (1 : points G k).left)

omit [IsOpenImmersion j] in
include he in
theorem onePoint_mem_range : onePoint G ∈ Set.range j :=
  ⟨Spec.map (CommRingCat.ofHom e.toRingHom) (IsLocalRing.closedPoint k), by
    rw [← Scheme.Hom.comp_apply, he, one_points_left, unitSection_apply]⟩

omit [IsOpenImmersion j] in
include he in
theorem range_one_left_subset (X : Over (Spec (.of k))) :
    Set.range (1 : X ⟶ G).left ⊆ Set.range j := by
  rintro _ ⟨x, rfl⟩
  rw [one_left_eq, Scheme.Hom.comp_apply, unitSection_apply]
  exact onePoint_mem_range he

include he in
/-- The ring homomorphism of the identity point `X ⟶ Spec k ⟶ G` is `e` followed by
`k → Γ(X, 𝒪_X)`. -/
theorem chartHomOf_one (X : Over (Spec (.of k))) :
    chartHomOf (1 : X ⟶ G) (range_one_left_subset he X) =
      CommRingCat.ofHom e.toRingHom ≫ (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop := by
  have e₁ : (1 : X ⟶ G).left = X.hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j := by
    rw [one_left_eq, he, one_points_left]
  have hr : Set.range (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j) ⊆ Set.range j :=
    fun _ ⟨x, hx⟩ ↦ ⟨_, hx⟩
  refine (IsOpenImmersion.liftRingHom_congr j e₁ _ fun _ ⟨x, hx⟩ ↦ ⟨_, hx⟩).trans ?_
  rw [IsOpenImmersion.liftRingHom_comp j X.hom _ hr, IsOpenImmersion.liftRingHom_specMap_comp,
    Category.assoc]

omit [IsOpenImmersion j] in
include he in
theorem range_left_subset {X : Over (Spec (.of k))} (v : infPointsAt G X) :
    Set.range v.1.left ⊆ Set.range j := by
  rintro _ ⟨x, rfl⟩
  have h : v.1.left x = (overDualNumbersι X ≫ v.1).left x := rfl
  rw [h, ι_comp_infPointsAt]
  exact range_one_left_subset he X ⟨x, rfl⟩

/-- The ring homomorphism `ψ_v : A → Γ(X, 𝒪_X)[ε]` of an infinitesimal point `v` with values in
`X`, through the chart `j`. -/
noncomputable def chartHom {X : Over (Spec (.of k))} (v : infPointsAt G X) :
    CommRingCat.of A ⟶ Γ(X.left.dualNumbers, ⊤) :=
  chartHomOf v.1 (range_left_subset he v)

/-- The derivation `D_v : A → Γ(X, 𝒪_X)` of an infinitesimal point `v`, the `ε`-part of `ψ_v`. -/
noncomputable def chartCoeff {X : Over (Spec (.of k))} (v : infPointsAt G X) :
    A →+ Γ(X.left, ⊤) where
  toFun a := TrivSqZeroExt.snd (R := Γ(X.left, ⊤)) (M := Γ(X.left, ⊤)) (chartHom he v a)
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add]; rfl

theorem chartCoeff_apply {X : Over (Spec (.of k))} (v : infPointsAt G X) (a : A) :
    chartCoeff he v a =
      TrivSqZeroExt.snd (R := Γ(X.left, ⊤)) (M := Γ(X.left, ⊤)) (chartHom he v a) :=
  rfl

/-- The constant part of `ψ_v` is `e`. -/
theorem fst_chartHom {X : Over (Spec (.of k))} (v : infPointsAt G X) (a : A) :
    TrivSqZeroExt.fst (R := Γ(X.left, ⊤)) (M := Γ(X.left, ⊤)) (chartHom he v a) =
      overΓAlgebraMap X (e a) := by
  have h := (chartHomOf_comp (overDualNumbersι X) v.1 (range_left_subset he v)
    (range_comp_left_subset _ _ (range_left_subset he v))).symm.trans
      ((chartHomOf_congr (ι_comp_infPointsAt v) _ (range_one_left_subset he X)).trans
        (chartHomOf_one he X))
  exact congrArg (fun f ↦ f a) h

/-- `ψ_v` is a homomorphism over `k`. -/
theorem chartHom_algebraMap {X : Over (Spec (.of k))} (v : infPointsAt G X)
    (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A))) (c : k) :
    chartHom he v (algebraMap k A c) =
      (TrivSqZeroExt.inl (overΓAlgebraMap X c) : DualNumber Γ(X.left, ⊤)) := by
  have hw : (overDualNumbers X).left.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A) ≫ chartHomOf v.1 (range_left_subset he v)) =
        (overDualNumbers X).hom := by
    rw [Spec.map_comp, ← hj]
    refine Eq.trans ?_ ((congrArg (· ≫ G.hom)
      (toSpecΓ_comp_chartHomOf v.1 (range_left_subset he v))).trans (Over.w v.1))
    simp only [Category.assoc]
  have h := congrArg (fun f ↦ (Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Hom.appTop f) hw
  rw [Scheme.ΓSpecIso_inv_comp_toSpecΓ_specMap_appTop, overDualNumbers_hom,
    Scheme.Hom.comp_appTop] at h
  exact congrArg (fun f ↦ f c) h

theorem chartCoeff_algebraMap {X : Over (Spec (.of k))} (v : infPointsAt G X)
    (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A))) (c : k) :
    chartCoeff he v (algebraMap k A c) = 0 := by
  rw [chartCoeff_apply, chartHom_algebraMap he v hj]
  rfl

/-- `D_v` is a derivation at `e`. -/
theorem chartCoeff_mul {X : Over (Spec (.of k))} (v : infPointsAt G X) (a b : A) :
    chartCoeff he v (a * b) = overΓAlgebraMap X (e a) * chartCoeff he v b +
      overΓAlgebraMap X (e b) * chartCoeff he v a := by
  rw [chartCoeff_apply, chartCoeff_apply, chartCoeff_apply, map_mul, TrivSqZeroExt.snd_mul,
    fst_chartHom, fst_chartHom, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

theorem chartHom_eq {X : Over (Spec (.of k))} (v : infPointsAt G X) (a : A) :
    chartHom he v a = (TrivSqZeroExt.inl (overΓAlgebraMap X (e a)) +
      TrivSqZeroExt.inr (chartCoeff he v a) : DualNumber Γ(X.left, ⊤)) :=
  TrivSqZeroExt.ext ((fst_chartHom he v a).trans (by simp)) (by simp [chartCoeff_apply])

/-- An infinitesimal point is determined by its derivation. -/
theorem chartCoeff_injective {X : Over (Spec (.of k))} {v w : infPointsAt G X}
    (h : chartCoeff he v = chartCoeff he w) : v = w := by
  have e' : chartHom he v = chartHom he w := by
    ext a
    rw [chartHom_eq, chartHom_eq, h]
  exact Subtype.ext (chartHomOf_injective _ _ e')

theorem chartCoeff_infPointsAtMap {X Y : Over (Spec (.of k))} (φ : Y ⟶ X)
    (v : infPointsAt G X) (a : A) :
    chartCoeff he (infPointsAtMap φ v) a = φ.left.appTop (chartCoeff he v a) := by
  have h := chartHomOf_comp (overDualNumbersMap φ) v.1 (range_left_subset he v)
    (range_left_subset he (infPointsAtMap φ v))
  rw [chartCoeff_apply, chartCoeff_apply]
  refine (congrArg (fun f ↦ TrivSqZeroExt.snd (R := Γ(Y.left, ⊤)) (M := Γ(Y.left, ⊤)) (f a))
    h).trans ?_
  change TrivSqZeroExt.snd (φ.left.dualNumbers.appTop (chartHom he v a)) = _
  rw [Scheme.Hom.dualNumbers_appTop_apply, DualNumber.snd_mapRingHom]

theorem chartCoeff_infPointsAtScale {X : Over (Spec (.of k))} (c : Γ(X.left, ⊤))
    (v : infPointsAt G X) (a : A) :
    chartCoeff he (infPointsAtScale X c v) a = c * chartCoeff he v a := by
  have h := chartHomOf_comp (overDualNumbersScale X c) v.1 (range_left_subset he v)
    (range_left_subset he (infPointsAtScale X c v))
  rw [chartCoeff_apply, chartCoeff_apply]
  refine (congrArg (fun f ↦ TrivSqZeroExt.snd (R := Γ(X.left, ⊤)) (M := Γ(X.left, ⊤)) (f a))
    h).trans ?_
  change TrivSqZeroExt.snd ((X.left.dualNumbersScale c).appTop (chartHom he v a)) = _
  rw [Scheme.dualNumbersScale_appTop_apply, DualNumber.snd_scale]

/-- **The group law is the addition of derivations.** The product `v w` is the restriction of
`v_ε w_δ : X[ε][δ] ⟶ G` along `δ = ε`, so `D_{vw} = D_v + D_w`. -/
theorem chartCoeff_mul_left {X : Over (Spec (.of k))} (v w : infPointsAt G X) :
    chartCoeff he (v * w) = chartCoeff he v + chartCoeff he w := by
  set z : overDualNumbers (overDualNumbers X) ⟶ G :=
    (overDualNumbersProj (overDualNumbers X) ≫ v.1) *
      (overDualNumbersMap (overDualNumbersProj X) ≫ w.1)
  have hvw : overDualNumbersFold X ≫ z = (v * w).1 := by
    rw [MonObj.comp_mul, overDualNumbersFold_comp_proj_assoc,
      overDualNumbersFold_comp_map_proj_assoc]
    rfl
  have hv : overDualNumbersι (overDualNumbers X) ≫ z = v.1 := by
    rw [MonObj.comp_mul, overDualNumbersι_comp_proj_assoc, overDualNumbersι_comp_map_proj_assoc,
      ι_comp_infPointsAt, MonObj.comp_one, mul_one]
  have hw : overDualNumbersMap (overDualNumbersι X) ≫ z = w.1 := by
    rw [MonObj.comp_mul, overDualNumbersMap_ι_comp_proj_assoc,
      overDualNumbersMap_ι_comp_map_proj_assoc, ι_comp_infPointsAt, MonObj.comp_one, one_mul]
  have hz : Set.range z.left ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have h : z.left x = (overDualNumbersι (overDualNumbers X) ≫ z).left x := rfl
    rw [h, hv]
    exact range_left_subset he v ⟨x, rfl⟩
  have e₁ : chartHom he (v * w) = chartHomOf z hz ≫ X.left.dualNumbersFold.appTop :=
    (chartHomOf_congr hvw.symm _ (range_comp_left_subset _ _ hz)).trans
      (chartHomOf_comp _ _ hz _)
  have e₂ : chartHom he v = chartHomOf z hz ≫ X.left.dualNumbers.dualNumbersι.appTop :=
    (chartHomOf_congr hv.symm _ (range_comp_left_subset _ _ hz)).trans
      (chartHomOf_comp _ _ hz _)
  have e₃ : chartHom he w = chartHomOf z hz ≫ X.left.dualNumbersι.dualNumbers.appTop :=
    (chartHomOf_congr hw.symm _ (range_comp_left_subset _ _ hz)).trans
      (chartHomOf_comp _ _ hz _)
  ext a
  rw [AddMonoidHom.add_apply, chartCoeff_apply, chartCoeff_apply, chartCoeff_apply, e₁, e₂, e₃]
  change TrivSqZeroExt.snd (X.left.dualNumbersFold.appTop (chartHomOf z hz a)) =
    TrivSqZeroExt.snd (X.left.dualNumbers.dualNumbersι.appTop (chartHomOf z hz a)) +
      TrivSqZeroExt.snd (X.left.dualNumbersι.dualNumbers.appTop (chartHomOf z hz a))
  rw [Scheme.dualNumbersFold_appTop_apply, Scheme.dualNumbersι_appTop_apply,
    Scheme.Hom.dualNumbers_appTop_apply, DualNumber.snd_foldRingHom, DualNumber.snd_mapRingHom]
  rfl

theorem chartCoeff_one {X : Over (Spec (.of k))} : chartCoeff he (1 : infPointsAt G X) = 0 := by
  have h := chartCoeff_mul_left he (1 : infPointsAt G X) 1
  rw [mul_one] at h
  exact (add_eq_left.mp h.symm)

variable (hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A)))
  {x : Spec (.of A)} (hx : j x = onePoint G)

/-- The derivation of the infinitesimal point `y_X` of a tangent vector `y` is the derivation
`A → k` of `y` through the chart, followed by `k → Γ(X, 𝒪_X)`. -/
theorem chartCoeff_lieAt (X : Over (Spec (.of k))) (y : Lie G) (a : A) :
    chartCoeff he (lieAt X y) a =
      overΓAlgebraMap X (tangentChartHom hj hx (lieEquivTangent G y) a).snd := by
  set χ := tangentChartHom hj hx (lieEquivTangent G y)
  have hy : (tangentPoint y).left = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ j :=
    left_eq_specMap_comp hx (lieEquivTangent G y)
  have hl : (lieAt X y).1.left = (X.hom.dualNumbers ≫ Scheme.dualNumbersToSpec (.of k)) ≫
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ j := by
    rw [← hy]
    rfl
  have hr : Set.range (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ j) ⊆ Set.range j :=
    fun _ ⟨x, hx⟩ ↦ ⟨_, hx⟩
  have h := IsOpenImmersion.liftRingHom_congr j hl (range_left_subset he (lieAt X y))
    (fun _ ⟨x, hx⟩ ↦ ⟨_, hx⟩)
  rw [IsOpenImmersion.liftRingHom_comp j _ _ hr,
    IsOpenImmersion.liftRingHom_specMap_comp, Scheme.Hom.comp_appTop, Scheme.dualNumbersToSpec,
    Category.assoc, ← Category.assoc ((Scheme.ΓSpecIso _).inv),
    Scheme.ΓSpecIso_inv_comp_toSpecΓ_specMap_appTop] at h
  rw [chartCoeff_apply]
  refine (congrArg (fun f ↦ TrivSqZeroExt.snd (R := Γ(X.left, ⊤)) (M := Γ(X.left, ⊤)) (f a))
    h).trans ?_
  change TrivSqZeroExt.snd (DualNumber.mapRingHom X.hom.appTop.hom
    (DualNumber.mapRingHom (Scheme.ΓSpecIso (.of k)).inv.hom (χ a))) = _
  rw [DualNumber.snd_mapRingHom, DualNumber.snd_mapRingHom]
  rfl

/-- The derivation `A → k` at `e` of a tangent vector `y ∈ Lie(G)`, through the chart. -/
noncomputable def tangentChartCoeff (y : Lie G) : A →ₗ[k] k :=
  TrivSqZeroExt.sndHom k k ∘ₗ (tangentChartHom hj hx (lieEquivTangent G y)).toLinearMap

theorem tangentChartCoeff_apply (y : Lie G) (a : A) :
    tangentChartCoeff hj hx y a = (tangentChartHom hj hx (lieEquivTangent G y) a).snd :=
  rfl

theorem tangentChartCoeff_algebraMap (y : Lie G) (c : k) :
    tangentChartCoeff hj hx y (algebraMap k A c) = 0 := by
  rw [tangentChartCoeff_apply, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl,
    TrivSqZeroExt.snd_inl]

include he in
/-- On `ker e`, the derivation of `y` is its linear form on the cotangent space. -/
theorem tangentChartCoeff_eq_lieToDualCotangent (y : Lie G) {a : A} (ha : a ∈ RingHom.ker e) :
    tangentChartCoeff hj hx y a =
      lieToDualCotangent hj hx he y ((RingHom.ker e).toCotangent ⟨a, ha⟩) :=
  (lieToDualCotangent_toCotangent hj hx he y ⟨a, ha⟩).symm

variable {I : Type u} [Fintype I] [DecidableEq I] (b : Module.Basis I k (Lie G))

omit [Fintype I] in
include he in
/-- There are elements `a_i ∈ ker e` on which the derivations of a basis `(b_j)` of `Lie(G)` are
`δ_ij`: the `b_j` are linearly independent forms on the cotangent space at `e`. -/
theorem exists_dual_family [Finite I] : ∃ a : I → A, (∀ i, a i ∈ RingHom.ker e) ∧
    ∀ i j, tangentChartCoeff hj hx (b j) (a i) = if i = j then 1 else 0 := by
  cases nonempty_fintype I
  set L := lieToDualCotangent hj hx he
  let ev : (RingHom.ker e).Cotangent →ₗ[k] (I → k) := LinearMap.pi fun j ↦ L (b j)
  have hev : Function.Surjective ev := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    set c : I → k := fun j ↦ φ fun l ↦ if j = l then 1 else 0
    have h1 : L (∑ j, c j • b j) = 0 := by
      refine LinearMap.ext fun w ↦ ?_
      have h := LinearMap.congr_fun hφ w
      rw [LinearMap.dualMap_apply, LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ] at h
      rw [map_sum, LinearMap.sum_apply, LinearMap.zero_apply, ← h]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
    have h2 : ∑ j, c j • b j = 0 :=
      (injective_iff_map_eq_zero L).1 (lieToDualCotangent_injective hj hx he) _ h1
    have h3 : ∀ j, c j = 0 := Fintype.linearIndependent_iff.1 b.linearIndependent c h2
    refine LinearMap.ext fun w ↦ ?_
    rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [show φ _ = c j from rfl, h3 j, smul_zero]
  choose w hw using fun i ↦ hev (Pi.single i 1)
  choose a' ha' using fun i ↦ (RingHom.ker e).toCotangent_surjective (w i)
  refine ⟨fun i ↦ (a' i : A), fun i ↦ (a' i).2, fun i j ↦ ?_⟩
  rw [tangentChartCoeff_eq_lieToDualCotangent he hj hx _ (a' i).2, Subtype.coe_eta, ha' i]
  have := congrFun (hw i) j
  rw [LinearMap.pi_apply] at this
  rw [this, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

include he in
/-- **A derivation at `e` is determined by its values on a dual family.** If `a_i ∈ ker e` and
the derivations of a basis `(b_j)` of `Lie(G)` are `δ_ij` on them, every derivation `D` at `e`
with values in a `k`-algebra satisfies `D(a) = ∑_j D_{b_j}(a) D(a_j)`. -/
theorem derivation_eq_sum {R : Type u} [CommRing R] (σ : k →+* R) (D : A →+ R)
    (hD : ∀ a a', D (a * a') = σ (e a) * D a' + σ (e a') * D a)
    (hc : ∀ c, D (algebraMap k A c) = 0) (a : I → A) (ha : ∀ i, a i ∈ RingHom.ker e)
    (hab : ∀ i j, tangentChartCoeff hj hx (b j) (a i) = if i = j then 1 else 0) (a' : A) :
    D a' = ∑ j, σ (tangentChartCoeff hj hx (b j) a') * D (a j) := by
  have hsmul (c : k) (a'' : A) : D (c • a'') = σ c * D a'' := by
    rw [Algebra.smul_def, hD, hc, AlgHom.commutes, mul_zero, add_zero]
    rfl
  set m := a' - algebraMap k A (e a') - ∑ j, tangentChartCoeff hj hx (b j) a' • a j
  have hm : m ∈ RingHom.ker e := by
    rw [RingHom.mem_ker]
    simp only [m, map_sub, map_sum, map_smul, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [RingHom.mem_ker.1 (ha j), smul_zero]
  have hcot : (RingHom.ker e).toCotangent ⟨m, hm⟩ = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro φ
    obtain ⟨y, rfl⟩ := lieToDualCotangent_surjective hj hx he φ
    let f : Lie G →ₗ[k] k :=
      LinearMap.applyₗ ((RingHom.ker e).toCotangent ⟨m, hm⟩) ∘ₗ lieToDualCotangent hj hx he
    have hf : f = 0 := b.ext fun i ↦ by
      change lieToDualCotangent hj hx he (b i) ((RingHom.ker e).toCotangent ⟨m, hm⟩) = 0
      rw [← tangentChartCoeff_eq_lieToDualCotangent he hj hx _ hm]
      simp only [m, map_sub, map_sum, map_smul, tangentChartCoeff_algebraMap, sub_zero,
        smul_eq_mul, hab, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, sub_self]
    exact LinearMap.congr_fun hf y
  have hsq : D m = 0 := by
    have hz := (Ideal.toCotangent_eq_zero _ _).1 hcot
    rw [pow_two] at hz
    refine Submodule.mul_induction_on (C := fun z ↦ D z = 0) hz (fun p hp q hq ↦ ?_)
      (fun p q hp hq ↦ ?_)
    · rw [hD, RingHom.mem_ker.1 hp, RingHom.mem_ker.1 hq, map_zero, zero_mul, zero_mul, add_zero]
    · rw [map_add, hp, hq, add_zero]
  simp only [m, map_sub, map_sum, hsmul, hc, sub_zero] at hsq
  exact sub_eq_zero.1 hsq

include he in
theorem infPointsAt_mul_comm {X : Over (Spec (.of k))} (v w : infPointsAt G X) :
    v * w = w * v :=
  chartCoeff_injective he (by rw [chartCoeff_mul_left, chartCoeff_mul_left, add_comm])

end Chart

/-! ### The Lie algebra is finite-dimensional -/

/-- The cotangent space `I/I²` of a noetherian `k`-algebra at a `k`-point is finite-dimensional:
it is finite over `A`, and `A` acts on it through the point. -/
theorem _root_.AlgHom.finite_cotangent_ker {A : Type u} [CommRing A] [Algebra k A]
    [IsNoetherianRing A] (e : A →ₐ[k] k) : Module.Finite k (RingHom.ker e).Cotangent := by
  set I := RingHom.ker e
  have hsmul (c : A) (w : I.Cotangent) : c • w = e c • w := by
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective w
    have hc : c - algebraMap k A (e c) ∈ I := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self]
    rw [← algebraMap_smul A (e c), ← sub_eq_zero, ← sub_smul, ← map_smul,
      Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul hc y.2
  have : Module.Finite A I := Module.Finite.iff_fg.2 (IsNoetherian.noetherian I)
  have : Module.Finite A I.Cotangent :=
    Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A I.Cotangent).FG)
  refine ⟨⟨s, ?_⟩⟩
  let N : Submodule A I.Cotangent :=
    { Submodule.span k (s : Set I.Cotangent) with
      smul_mem' c w hw := by
        change c • w ∈ Submodule.span k (s : Set I.Cotangent)
        rw [hsmul]
        exact (Submodule.span k _).smul_mem _ hw }
  have h : Submodule.span A (s : Set I.Cotangent) ≤ N := Submodule.span_le.2 Submodule.subset_span
  rw [hs] at h
  exact eq_top_iff.2 fun w _ ↦ h trivial

/-- The Lie algebra of a group scheme locally of finite type over a field is finite-dimensional:
it is dual to the cotangent space of an affine chart at the identity. -/
instance finiteDimensional_lie [LocallyOfFiniteType G.hom] : FiniteDimensional k (Lie G) := by
  obtain ⟨A, _, _, j, _, e, hA, hj, he⟩ := exists_affine_chart G
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have := AlgHom.finite_cotangent_ker e
  have hx : j (Spec.map (CommRingCat.ofHom e.toRingHom) (IsLocalRing.closedPoint k)) =
      onePoint G := by
    rw [← Scheme.Hom.comp_apply, he]
    exact one_left_apply G _
  exact Module.Finite.of_injective (lieToDualCotangent hj hx he)
    (lieToDualCotangent_injective hj hx he)

/-! ### The infinitesimal points with values in a scheme form a free module -/

section Free

variable [LocallyOfFiniteType G.hom]

/-- The infinitesimal points with values in `X` of a group scheme locally of finite type over a
field commute: their group law is the addition of `Lie(G) ⊗ Γ(X, 𝒪_X)`. -/
instance isMulCommutative_infPointsAt (X : Over (Spec (.of k))) :
    IsMulCommutative (infPointsAt G X) :=
  ⟨⟨fun v w ↦ by
    obtain ⟨A, _, _, j, _, e, -, -, he⟩ := exists_affine_chart G
    exact infPointsAt_mul_comm he v w⟩⟩

/-- Rescaling is additive in the scalar: `v((c + d)ε) = v(cε) v(dε)`. -/
theorem infPointsAtScale_add (X : Over (Spec (.of k))) (c d : Γ(X.left, ⊤))
    (v : infPointsAt G X) :
    infPointsAtScale X (c + d) v = infPointsAtScale X c v * infPointsAtScale X d v := by
  obtain ⟨A, _, _, j, _, e, -, -, he⟩ := exists_affine_chart G
  refine chartCoeff_injective he (AddMonoidHom.ext fun a ↦ ?_)
  rw [chartCoeff_mul_left, AddMonoidHom.add_apply, chartCoeff_infPointsAtScale,
    chartCoeff_infPointsAtScale, chartCoeff_infPointsAtScale, add_mul]

theorem infPointsAtScale_zero (X : Over (Spec (.of k))) (v : infPointsAt G X) :
    infPointsAtScale X 0 v = 1 := by
  have h := infPointsAtScale_add X 0 0 v
  rw [add_zero] at h
  exact left_eq_mul.mp h

variable {I : Type u} [Fintype I] (b : Module.Basis I k (Lie G))

/-- **The infinitesimal points with values in a scheme form a free module.** For a basis `(b_i)`
of `Lie(G)` and a scheme `X` over `k`, every infinitesimal point with values in `X` is uniquely a
product `∏ᵢ (b_i)_X(rᵢ ε)` with `rᵢ ∈ Γ(X, 𝒪_X)`. (blueprint: `lemma-stable-subspaces-center`) -/
theorem existsUnique_prod_eq (X : Over (Spec (.of k))) (v : infPointsAt G X) :
    ∃! r : I → Γ(X.left, ⊤), ∏ i, infPointsAtScale X (r i) (lieAt X (b i)) = v := by
  classical
  obtain ⟨A, _, _, j, _, e, -, hj, he⟩ := exists_affine_chart G
  have hx : j (Spec.map (CommRingCat.ofHom e.toRingHom) (IsLocalRing.closedPoint k)) =
      onePoint G := by
    rw [← Scheme.Hom.comp_apply, he]
    exact one_left_apply G _
  obtain ⟨a, ha, hab⟩ := exists_dual_family he hj hx b
  have hsum (f : I → infPointsAt G X) (t : Finset I) :
      chartCoeff he (∏ i ∈ t, f i) = ∑ i ∈ t, chartCoeff he (f i) := by
    induction t using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, chartCoeff_one]
    | insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, chartCoeff_mul_left, ih]
  have hprod (r : I → Γ(X.left, ⊤)) (a' : A) :
      chartCoeff he (∏ i, infPointsAtScale X (r i) (lieAt X (b i))) a' =
        ∑ i, r i * overΓAlgebraMap X (tangentChartCoeff hj hx (b i) a') := by
    rw [hsum, AddMonoidHom.finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [chartCoeff_infPointsAtScale, chartCoeff_lieAt he hj hx]
    rfl
  refine ⟨fun i ↦ chartCoeff he v (a i), ?_, fun r hr ↦ funext fun i ↦ ?_⟩
  · refine chartCoeff_injective he (AddMonoidHom.ext fun a' ↦ ?_)
    rw [hprod, derivation_eq_sum he hj hx b (overΓAlgebraMap X) (chartCoeff he v)
      (chartCoeff_mul he v) (chartCoeff_algebraMap he v hj) a ha hab a']
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  · rw [← hr, hprod]
    simp only [hab, apply_ite, map_one, map_zero, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [Fintype I] in
variable {b} in
theorem lieAt_sum (X : Over (Spec (.of k))) (c : I → k) (t : Finset I) :
    lieAt X (∑ i ∈ t, c i • b i) = ∏ i ∈ t, infPointsAtScale X (overΓAlgebraMap X (c i))
      (lieAt X (b i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, lieAt_zero]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, lieAt_add, ih, lieAt_smul]

/-- The coordinates `rᵢ ∈ Γ(X, 𝒪_X)` of an infinitesimal point `v = ∏ᵢ (b_i)_X(rᵢ ε)` with values
in `X`, in the basis `(b_i)_X`. -/
noncomputable def infPointsAtCoord (X : Over (Spec (.of k))) (v : infPointsAt G X) :
    I → Γ(X.left, ⊤) :=
  (existsUnique_prod_eq b X v).exists.choose

theorem prod_infPointsAtCoord (X : Over (Spec (.of k))) (v : infPointsAt G X) :
    ∏ i, infPointsAtScale X (infPointsAtCoord b X v i) (lieAt X (b i)) = v :=
  (existsUnique_prod_eq b X v).exists.choose_spec

theorem infPointsAtCoord_eq {X : Over (Spec (.of k))} {v : infPointsAt G X} (r : I → Γ(X.left, ⊤))
    (h : ∏ i, infPointsAtScale X (r i) (lieAt X (b i)) = v) : infPointsAtCoord b X v = r :=
  (existsUnique_prod_eq b X v).unique (prod_infPointsAtCoord b X v) h

theorem infPointsAtCoord_injective (X : Over (Spec (.of k))) :
    Function.Injective (infPointsAtCoord b X) := fun v w h ↦ by
  rw [← prod_infPointsAtCoord b X v, ← prod_infPointsAtCoord b X w, h]

theorem infPointsAtCoord_mul {X : Over (Spec (.of k))} (v w : infPointsAt G X) :
    infPointsAtCoord b X (v * w) = infPointsAtCoord b X v + infPointsAtCoord b X w := by
  refine infPointsAtCoord_eq b _ ?_
  simp only [Pi.add_apply, infPointsAtScale_add, Finset.prod_mul_distrib, prod_infPointsAtCoord]

theorem infPointsAtCoord_one (X : Over (Spec (.of k))) :
    infPointsAtCoord b X (1 : infPointsAt G X) = 0 :=
  infPointsAtCoord_eq b _ (by simp only [Pi.zero_apply, infPointsAtScale_zero,
    Finset.prod_const_one])

theorem infPointsAtCoord_prod {X : Over (Spec (.of k))} {J : Type*} (f : J → infPointsAt G X)
    (t : Finset J) :
    infPointsAtCoord b X (∏ j ∈ t, f j) = ∑ j ∈ t, infPointsAtCoord b X (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, infPointsAtCoord_one]
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, infPointsAtCoord_mul, ih]

theorem infPointsAtCoord_infPointsAtScale {X : Over (Spec (.of k))} (c : Γ(X.left, ⊤))
    (v : infPointsAt G X) :
    infPointsAtCoord b X (infPointsAtScale X c v) = c • infPointsAtCoord b X v := by
  refine infPointsAtCoord_eq b _ ?_
  conv_rhs => rw [← prod_infPointsAtCoord b X v]
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Pi.smul_apply, smul_eq_mul, infPointsAtScale_mul]

theorem infPointsAtCoord_lieAt (X : Over (Spec (.of k))) (y : Lie G) :
    infPointsAtCoord b X (lieAt X y) = fun i ↦ overΓAlgebraMap X (b.repr y i) := by
  refine infPointsAtCoord_eq b _ ?_
  conv_rhs => rw [← b.sum_repr y]
  rw [lieAt_sum]

theorem infPointsAtCoord_infPointsAtMap {X Y : Over (Spec (.of k))} (φ : Y ⟶ X)
    (v : infPointsAt G X) :
    infPointsAtCoord b Y (infPointsAtMap φ v) =
      fun i ↦ φ.left.appTop (infPointsAtCoord b X v i) := by
  refine infPointsAtCoord_eq b _ ?_
  conv_rhs => rw [← prod_infPointsAtCoord b X v]
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [infPointsAtMap_infPointsAtScale, infPointsAtMap_lieAt]

end Free

end GrpObj

end AlgebraicGeometry

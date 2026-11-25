/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential

/-!
# Infinitesimal points with values in a scheme

Let `G` be a group scheme over `S` and `X` a scheme over `S`. The thickening `X[ε]` is a scheme
over `S` through `X[ε] ⟶ X ⟶ S` (`AlgebraicGeometry.overDualNumbers`). The *infinitesimal points
of `G` with values in `X`* are the points `v : X[ε] ⟶ G` over `S` with `v|_X = 1`
(`AlgebraicGeometry.GrpObj.infPointsAt`); for `X = S` these are the infinitesimal points of `G`.
They are functorial in `X`, carry the rescalings `ε ↦ cε` by global functions `c` of `X`, and the
`X`-points `x` of `G` act on them by conjugation `v ↦ x v x⁻¹`: this is the adjoint action of `G`
on `Lie(G) ⊗ Γ(X, 𝒪_X)`.

Over a field `k`, a tangent vector `y ∈ Lie(G)` gives the infinitesimal point
`y_X : X[ε] ⟶ (Spec k)[ε] ⟶ G` with values in any `k`-scheme `X`
(`AlgebraicGeometry.GrpObj.lieAt`); `y ↦ y_X` turns addition into the group law and scalars
`c ∈ k` into rescalings.

## Main definitions

- `AlgebraicGeometry.overDualNumbers`: the thickening `X[ε]` of a scheme `X` over `S`, as a
  scheme over `S`, with `overDualNumbersι`, `overDualNumbersProj`, `overDualNumbersMap`,
  `overDualNumbersScale` and `overDualNumbersFold`.
- `AlgebraicGeometry.GrpObj.infPointsAt`: the infinitesimal points of `G` with values in `X`.
- `AlgebraicGeometry.GrpObj.infPointsAtMap`, `AlgebraicGeometry.GrpObj.infPointsAtScale`,
  `AlgebraicGeometry.GrpObj.infPointsAtConj`: base change, rescaling and conjugation.
- `AlgebraicGeometry.GrpObj.lieAt`: the infinitesimal point `y_X` of a tangent vector `y`.

## Blueprint

- `lemma-stable-subspaces-center`: the adjoint representation, through its action on infinitesimal
points.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-- Rescaling the infinitesimal commutes with the thickening of a morphism. -/
@[reassoc]
theorem Scheme.Hom.dualNumbers_comp_dualNumbersScale {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : Γ(Y, ⊤)) :
    f.dualNumbers ≫ Y.dualNumbersScale c = X.dualNumbersScale (f.appTop c) ≫ f.dualNumbers := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.mapRingHom (f.app U).hom
      (DualNumber.scale (Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op c) a) =
    DualNumber.scale (X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U ⟶ ⊤).op (f.appTop c))
      (DualNumber.mapRingHom (f.app U).hom a)
  rw [← DualNumber.scale_mapRingHom]
  congr 2
  rw [Scheme.Hom.appTop, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, f.naturality]
  rfl

/-! ### The thickening of a scheme over a base -/

section OverDualNumbers

variable {S : Scheme.{u}} (X : Over S)

/-- The thickening `X[ε]` of a scheme `X` over `S`, as a scheme over `S` through
`X[ε] ⟶ X ⟶ S`. -/
noncomputable def overDualNumbers : Over S :=
  Over.mk (X.left.dualNumbersProj ≫ X.hom)

@[simp]
theorem overDualNumbers_left : (overDualNumbers X).left = X.left.dualNumbers :=
  rfl

@[simp]
theorem overDualNumbers_hom : (overDualNumbers X).hom = X.left.dualNumbersProj ≫ X.hom :=
  rfl

/-- The closed immersion `X ⟶ X[ε]`, `ε ↦ 0`, over `S`. -/
noncomputable def overDualNumbersι : X ⟶ overDualNumbers X :=
  Over.homMk X.left.dualNumbersι (by simp)

/-- The projection `X[ε] ⟶ X` over `S`. -/
noncomputable def overDualNumbersProj : overDualNumbers X ⟶ X :=
  Over.homMk X.left.dualNumbersProj rfl

/-- Rescaling the infinitesimal `ε ↦ cε` by a global function `c` of `X`, over `S`. -/
noncomputable def overDualNumbersScale (c : Γ(X.left, ⊤)) :
    overDualNumbers X ⟶ overDualNumbers X :=
  Over.homMk (X.left.dualNumbersScale c) (by simp)

/-- The map `X[ε] ⟶ X[ε][δ]`, `ε, δ ↦ ε`, over `S`. -/
noncomputable def overDualNumbersFold : overDualNumbers X ⟶ overDualNumbers (overDualNumbers X) :=
  Over.homMk X.left.dualNumbersFold (by simp)

variable {X} in
/-- The thickening `X[ε] ⟶ Y[ε]` of a morphism `φ : X ⟶ Y` over `S`. -/
noncomputable def overDualNumbersMap {Y : Over S} (φ : X ⟶ Y) :
    overDualNumbers X ⟶ overDualNumbers Y :=
  Over.homMk φ.left.dualNumbers (by simp [Over.w φ])

@[simp]
theorem overDualNumbersι_left : (overDualNumbersι X).left = X.left.dualNumbersι :=
  rfl

@[simp]
theorem overDualNumbersProj_left : (overDualNumbersProj X).left = X.left.dualNumbersProj :=
  rfl

@[simp]
theorem overDualNumbersScale_left (c : Γ(X.left, ⊤)) :
    (overDualNumbersScale X c).left = X.left.dualNumbersScale c :=
  rfl

@[simp]
theorem overDualNumbersFold_left : (overDualNumbersFold X).left = X.left.dualNumbersFold :=
  rfl

@[simp]
theorem overDualNumbersMap_left {Y : Over S} (φ : X ⟶ Y) :
    (overDualNumbersMap φ).left = φ.left.dualNumbers :=
  rfl

@[reassoc (attr := simp)]
theorem overDualNumbersι_comp_proj : overDualNumbersι X ≫ overDualNumbersProj X = 𝟙 X := by
  ext1
  simp

@[reassoc (attr := simp)]
theorem overDualNumbersMap_comp_proj {Y : Over S} (φ : X ⟶ Y) :
    overDualNumbersMap φ ≫ overDualNumbersProj Y = overDualNumbersProj X ≫ φ := by
  ext1
  simp

@[reassoc (attr := simp)]
theorem overDualNumbersι_comp_map {Y : Over S} (φ : X ⟶ Y) :
    overDualNumbersι X ≫ overDualNumbersMap φ = φ ≫ overDualNumbersι Y := by
  ext1
  simp

@[simp]
theorem overDualNumbersMap_id : overDualNumbersMap (𝟙 X) = 𝟙 _ := by
  ext1
  simp [Scheme.Hom.dualNumbers_id]

theorem overDualNumbersMap_comp {Y Z : Over S} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    overDualNumbersMap (φ ≫ ψ) = overDualNumbersMap φ ≫ overDualNumbersMap ψ := by
  ext1
  simp [Scheme.Hom.dualNumbers_comp]

@[reassoc (attr := simp)]
theorem overDualNumbersScale_comp_proj (c : Γ(X.left, ⊤)) :
    overDualNumbersScale X c ≫ overDualNumbersProj X = overDualNumbersProj X := by
  ext1
  simp

@[reassoc (attr := simp)]
theorem overDualNumbersι_comp_scale (c : Γ(X.left, ⊤)) :
    overDualNumbersι X ≫ overDualNumbersScale X c = overDualNumbersι X := by
  ext1
  simp

@[simp]
theorem overDualNumbersScale_one : overDualNumbersScale X 1 = 𝟙 _ := by
  ext1
  simp

theorem overDualNumbersScale_mul (c d : Γ(X.left, ⊤)) :
    overDualNumbersScale X (c * d) = overDualNumbersScale X c ≫ overDualNumbersScale X d := by
  ext1
  simp [Scheme.dualNumbersScale_mul]

@[reassoc]
theorem overDualNumbersMap_comp_scale {Y : Over S} (φ : X ⟶ Y) (c : Γ(Y.left, ⊤)) :
    overDualNumbersMap φ ≫ overDualNumbersScale Y c =
      overDualNumbersScale X (φ.left.appTop c) ≫ overDualNumbersMap φ := by
  ext1
  simp [Scheme.Hom.dualNumbers_comp_dualNumbersScale]

@[reassoc (attr := simp)]
theorem overDualNumbersFold_comp_proj :
    overDualNumbersFold X ≫ overDualNumbersProj (overDualNumbers X) = 𝟙 _ := by
  ext1
  simp

@[reassoc (attr := simp)]
theorem overDualNumbersFold_comp_map_proj :
    overDualNumbersFold X ≫ overDualNumbersMap (overDualNumbersProj X) = 𝟙 _ := by
  ext1
  simp

/-- Setting `δ = 0` and then forgetting `ε`: `X[ε] ⟶ X[ε][δ] ⟶ X[δ]` factors through `X`. -/
@[reassoc]
theorem overDualNumbersι_comp_map_proj :
    overDualNumbersι (overDualNumbers X) ≫ overDualNumbersMap (overDualNumbersProj X) =
      overDualNumbersProj X ≫ overDualNumbersι X := by
  ext1
  simp

/-- Setting `ε = 0` and then forgetting `δ`: `X[δ] ⟶ X[ε][δ] ⟶ X[ε]` factors through `X`. -/
@[reassoc]
theorem overDualNumbersMap_ι_comp_proj :
    overDualNumbersMap (overDualNumbersι X) ≫ overDualNumbersProj (overDualNumbers X) =
      overDualNumbersProj X ≫ overDualNumbersι X := by
  ext1
  simp

@[reassoc (attr := simp)]
theorem overDualNumbersMap_ι_comp_map_proj :
    overDualNumbersMap (overDualNumbersι X) ≫ overDualNumbersMap (overDualNumbersProj X) =
      𝟙 _ := by
  rw [← overDualNumbersMap_comp, overDualNumbersι_comp_proj, overDualNumbersMap_id]

end OverDualNumbers

/-! ### Infinitesimal points with values in a scheme -/

namespace GrpObj

section InfPointsAt

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] (X : Over S)

/-- The infinitesimal points of a group scheme `G` over `S` with values in a scheme `X` over `S`:
the points `v : X[ε] ⟶ G` over `S` with `v|_X = 1`, the kernel of `G(X[ε]) → G(X)`.
(blueprint: `lemma-stable-subspaces-center`) -/
noncomputable def infPointsAt : Subgroup (overDualNumbers X ⟶ G) :=
  (pointsPrecomp G (overDualNumbersι X)).ker

variable {G X}

theorem mem_infPointsAt {v : overDualNumbers X ⟶ G} :
    v ∈ infPointsAt G X ↔ overDualNumbersι X ≫ v = 1 :=
  MonoidHom.mem_ker

theorem ι_comp_infPointsAt (v : infPointsAt G X) : overDualNumbersι X ≫ v.1 = 1 :=
  mem_infPointsAt.1 v.2

/-- Base change of infinitesimal points along a morphism `φ : Y ⟶ X` over `S`: `v ↦ φ[ε] ≫ v`. -/
noncomputable def infPointsAtMap {Y : Over S} (φ : Y ⟶ X) : infPointsAt G X →* infPointsAt G Y :=
  ((pointsPrecomp G (overDualNumbersMap φ)).comp (infPointsAt G X).subtype).codRestrict _
    fun v ↦ by
      rw [mem_infPointsAt, MonoidHom.comp_apply, pointsPrecomp_apply,
        overDualNumbersι_comp_map_assoc, Subgroup.coe_subtype, ι_comp_infPointsAt,
        MonObj.comp_one]

@[simp]
theorem coe_infPointsAtMap {Y : Over S} (φ : Y ⟶ X) (v : infPointsAt G X) :
    (infPointsAtMap φ v : overDualNumbers Y ⟶ G) = overDualNumbersMap φ ≫ v.1 :=
  rfl

theorem infPointsAtMap_id (v : infPointsAt G X) : infPointsAtMap (𝟙 X) v = v :=
  Subtype.ext (by simp)

theorem infPointsAtMap_comp {Y Z : Over S} (φ : Z ⟶ Y) (ψ : Y ⟶ X) (v : infPointsAt G X) :
    infPointsAtMap (φ ≫ ψ) v = infPointsAtMap φ (infPointsAtMap ψ v) :=
  Subtype.ext (by simp [overDualNumbersMap_comp])

variable (X) in
/-- The rescaling `v ↦ v(cε)` of infinitesimal points by a global function `c` of `X`. -/
noncomputable def infPointsAtScale (c : Γ(X.left, ⊤)) : infPointsAt G X →* infPointsAt G X :=
  ((pointsPrecomp G (overDualNumbersScale X c)).comp (infPointsAt G X).subtype).codRestrict _
    fun v ↦ by
      rw [mem_infPointsAt, MonoidHom.comp_apply, pointsPrecomp_apply,
        overDualNumbersι_comp_scale_assoc, Subgroup.coe_subtype, ι_comp_infPointsAt]

@[simp]
theorem coe_infPointsAtScale (c : Γ(X.left, ⊤)) (v : infPointsAt G X) :
    (infPointsAtScale X c v : overDualNumbers X ⟶ G) = overDualNumbersScale X c ≫ v.1 :=
  rfl

theorem infPointsAtScale_one (v : infPointsAt G X) : infPointsAtScale X 1 v = v :=
  Subtype.ext (by simp)

theorem infPointsAtScale_mul (c d : Γ(X.left, ⊤)) (v : infPointsAt G X) :
    infPointsAtScale X (c * d) v = infPointsAtScale X c (infPointsAtScale X d v) :=
  Subtype.ext (by simp [overDualNumbersScale_mul])

theorem infPointsAtMap_infPointsAtScale {Y : Over S} (φ : Y ⟶ X) (c : Γ(X.left, ⊤))
    (v : infPointsAt G X) :
    infPointsAtMap φ (infPointsAtScale X c v) =
      infPointsAtScale Y (φ.left.appTop c) (infPointsAtMap φ v) :=
  Subtype.ext (by simp [overDualNumbersMap_comp_scale_assoc])

/-- The conjugation `v ↦ x v x⁻¹` of infinitesimal points with values in `X` by an `X`-point `x`
of `G`, pulled back to `X[ε]`. This is the adjoint action of `x` on `Lie(G) ⊗ Γ(X, 𝒪_X)`.
(blueprint: `lemma-stable-subspaces-center`) -/
noncomputable def infPointsAtConj (x : X ⟶ G) : infPointsAt G X →* infPointsAt G X where
  toFun v := ⟨(overDualNumbersProj X ≫ x) * v.1 * (overDualNumbersProj X ≫ x)⁻¹, by
    rw [mem_infPointsAt, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
      overDualNumbersι_comp_proj_assoc, ι_comp_infPointsAt, mul_one, mul_inv_cancel]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' v w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp]
theorem coe_infPointsAtConj (x : X ⟶ G) (v : infPointsAt G X) :
    (infPointsAtConj x v : overDualNumbers X ⟶ G) =
      (overDualNumbersProj X ≫ x) * v.1 * (overDualNumbersProj X ≫ x)⁻¹ :=
  rfl

theorem infPointsAtConj_one (v : infPointsAt G X) : infPointsAtConj (1 : X ⟶ G) v = v :=
  Subtype.ext (by simp)

theorem infPointsAtConj_mul (x y : X ⟶ G) (v : infPointsAt G X) :
    infPointsAtConj (x * y) v = infPointsAtConj x (infPointsAtConj y v) :=
  Subtype.ext (by simp only [coe_infPointsAtConj, MonObj.comp_mul]; group)

theorem infPointsAtConj_infPointsAtScale (x : X ⟶ G) (c : Γ(X.left, ⊤)) (v : infPointsAt G X) :
    infPointsAtConj x (infPointsAtScale X c v) = infPointsAtScale X c (infPointsAtConj x v) :=
  Subtype.ext (by
    simp only [coe_infPointsAtConj, coe_infPointsAtScale, MonObj.comp_mul, GrpObj.comp_inv,
      overDualNumbersScale_comp_proj_assoc])

theorem infPointsAtMap_infPointsAtConj {Y : Over S} (φ : Y ⟶ X) (x : X ⟶ G)
    (v : infPointsAt G X) :
    infPointsAtMap φ (infPointsAtConj x v) = infPointsAtConj (φ ≫ x) (infPointsAtMap φ v) :=
  Subtype.ext (by
    simp only [coe_infPointsAtConj, coe_infPointsAtMap, MonObj.comp_mul, GrpObj.comp_inv,
      overDualNumbersMap_comp_proj_assoc])

end InfPointsAt

/-! ### Tangent vectors as infinitesimal points with values in a scheme -/

section LieAt

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]

/-- The `k`-algebra structure `k → Γ(X, 𝒪_X)` of a scheme `X` over `k`. -/
noncomputable def overΓAlgebraMap (X : Over (Spec (.of k))) : k →+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom

theorem appTop_overΓAlgebraMap {X Y : Over (Spec (.of k))} (φ : Y ⟶ X) (c : k) :
    φ.left.appTop (overΓAlgebraMap X c) = overΓAlgebraMap Y c := by
  simp only [overΓAlgebraMap, ← Over.w φ, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

/-- The map `X[ε] ⟶ (Spec k)[ε] ≅ Spec k[ε]` over `k` of a scheme `X` over `k`. -/
noncomputable def overDualNumbersToSpec (X : Over (Spec (.of k))) :
    overDualNumbers X ⟶ (Spec (.of (DualNumber k))).asOver (Spec (.of k)) :=
  Over.homMk (X.hom.dualNumbers ≫ Scheme.dualNumbersToSpec (.of k))
    ((Category.assoc _ _ _).trans ((congrArg (X.hom.dualNumbers ≫ ·)
      (Scheme.dualNumbersToSpec_comp_specMap (.of k))).trans
        (Scheme.Hom.dualNumbers_comp_proj X.hom)))

@[reassoc]
theorem overDualNumbersMap_comp_toSpec {X Y : Over (Spec (.of k))} (φ : Y ⟶ X) :
    overDualNumbersMap φ ≫ overDualNumbersToSpec X = overDualNumbersToSpec Y := by
  ext1
  simp only [overDualNumbersToSpec, Over.comp_left, overDualNumbersMap_left, Over.homMk_left]
  rw [← Category.assoc, ← Scheme.Hom.dualNumbers_comp, Over.w φ]

theorem overDualNumbersι_comp_toSpec (X : Over (Spec (.of k))) :
    overDualNumbersι X ≫ overDualNumbersToSpec X =
      CartesianMonoidalCategory.toUnit X ≫ Scheme.dualNumbersιOver (Spec (.of k)) ≫
        dualNumbersToSpecOver := by
  ext1
  simp [overDualNumbersToSpec, dualNumbersToSpecOver, Over.toUnit_left]

@[reassoc]
theorem overDualNumbersScale_comp_toSpec (X : Over (Spec (.of k))) (c : k) :
    overDualNumbersScale X (overΓAlgebraMap X c) ≫ overDualNumbersToSpec X =
      overDualNumbersToSpec X ≫
        (Spec.map (CommRingCat.ofHom (DualNumber.scale c).toRingHom)).asOver (Spec (.of k)) := by
  ext1
  have h := Scheme.Hom.dualNumbers_comp_dualNumbersScale_assoc X.hom
    ((Scheme.ΓSpecIso (.of k)).inv c) (Scheme.dualNumbersToSpec (.of k))
  rw [Scheme.dualNumbersScale_comp_dualNumbersToSpec] at h
  exact h.symm

variable (X : Over (Spec (.of k)))

theorem overDualNumbersToSpec_comp_tangentPoint_mem (y : Lie G) :
    overDualNumbersToSpec X ≫ tangentPoint y ∈ infPointsAt G X := by
  rw [mem_infPointsAt, ← Category.assoc, overDualNumbersι_comp_toSpec, Category.assoc,
    Category.assoc, (mem_infPoints G).1
      (dualNumbersToSpecOver_comp_mem_infPoints G (tangentPoint_mem_tangentGroup y)),
    MonObj.comp_one]

/-- The infinitesimal point `y_X : X[ε] ⟶ (Spec k)[ε] ⟶ G` with values in a scheme `X` over `k`
of a tangent vector `y ∈ Lie(G)`. (blueprint: `lemma-stable-subspaces-center`) -/
noncomputable def lieAt (y : Lie G) : infPointsAt G X :=
  ⟨overDualNumbersToSpec X ≫ tangentPoint y, overDualNumbersToSpec_comp_tangentPoint_mem X y⟩

@[simp]
theorem coe_lieAt (y : Lie G) :
    (lieAt X y : overDualNumbers X ⟶ G) = overDualNumbersToSpec X ≫ tangentPoint y :=
  rfl

theorem tangentPoint_add (y z : Lie G) : tangentPoint (y + z) = tangentPoint y * tangentPoint z :=
  congrArg Subtype.val (lieEquivTangent_add y z)

theorem tangentPoint_smul (c : k) (y : Lie G) :
    tangentPoint (c • y) =
      (Spec.map (CommRingCat.ofHom (DualNumber.scale c).toRingHom)).asOver (Spec (.of k)) ≫
        tangentPoint y := by
  have e : DualNumber.liftElem (R := k) (inr c) (inr_mul_self c) = DualNumber.scale c := by
    ext <;> simp [DualNumber.liftElem_apply, algebraMap_eq_inl]
  have h := congrArg Subtype.val (lieEquivTangent_smul c y)
  change tangentPoint (c • y) = points.map G (DualNumber.liftElem (R := k) (inr c)
    (inr_mul_self c)) (tangentPoint y) at h
  rw [h, e]
  rfl

theorem lieAt_add (y z : Lie G) : lieAt X (y + z) = lieAt X y * lieAt X z :=
  Subtype.ext (by rw [coe_lieAt, tangentPoint_add, MonObj.comp_mul]; rfl)

theorem lieAt_smul (c : k) (y : Lie G) :
    lieAt X (c • y) = infPointsAtScale X (overΓAlgebraMap X c) (lieAt X y) :=
  Subtype.ext (by
    rw [coe_lieAt, tangentPoint_smul, coe_infPointsAtScale, coe_lieAt,
      overDualNumbersScale_comp_toSpec_assoc])

theorem lieAt_zero : lieAt X (0 : Lie G) = 1 := by
  have h := lieAt_add X (0 : Lie G) 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem infPointsAtMap_lieAt {Y : Over (Spec (.of k))} (φ : Y ⟶ X) (y : Lie G) :
    infPointsAtMap φ (lieAt X y) = lieAt Y y :=
  Subtype.ext (by
    rw [coe_infPointsAtMap, coe_lieAt, coe_lieAt, overDualNumbersMap_comp_toSpec_assoc])

end LieAt

end GrpObj

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The underived algebra-valued sheaf Hom adjunction

Source: Stacks Project, Modules, Tag 0A6F; Duality for Schemes, Tags 0BV0 and 0BV1
(blueprint: lem-sc-sheaf-algebra-hom-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- O-module sheaves used in the private adjunction construction. -/
private abbrev OMod (Y : Scheme.{u}) : Type (u + 1) := SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat RingCat)).obj Y.sheaf)

/-- B-module sheaves used in the private adjunction construction. -/
private abbrev BMod (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) : Type (u + 1) :=
  SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat RingCat)).obj B.right)

private noncomputable local instance sheafAlgebraHomRestrictedTargetModule
    {Y : Scheme.{u}} {B : Y.CommAlgebraSheaf} (M : BMod Y B)
    {U V : (Opens Y)ᵒᵖ} (f : U ⟶ V) :
    Module (B.right.obj.obj V)
      ((ModuleCat.restrictScalars (((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right).obj.map f).hom).obj (M.val.obj V)) :=
  (M.val.obj V).isModule

/-- Scalar restriction along the structure map of B. -/
private noncomputable abbrev res (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) :
    BMod Y B ⥤ OMod Y :=
  SheafOfModules.restrictScalars.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).map B.hom)

set_option backward.isDefEq.respectTransparency false in
/-- Send m to the O-linear map b ↦ φ(b • m), on every open over U.
Source: Stacks Project, Modules, Tag 0A6F
(blueprint: lem-sc-sheaf-algebra-hom-adjunction). -/
private noncomputable def currySection
    {Y : Scheme.{u}} {B : Y.CommAlgebraSheaf} {M : BMod Y B} {F : OMod Y} (φ : (res Y B).obj M ⟶ F)
    (U : (Opens Y)ᵒᵖ) (m : M.val.obj U) : sheafAlgebraHomSections Y B F U where
  app W := ModuleCat.ofHom
    (X := ((PresheafOfModules.restrictOver Y.sheaf.obj U.unop).obj B.toModule.val).obj W)
    (Y := ((PresheafOfModules.restrictOver Y.sheaf.obj U.unop).obj F.val).obj W)
    { toFun := fun b ↦ φ.val.app (Opposite.op W.unop.left)
        ((@id (B.right.obj.obj (Opposite.op W.unop.left)) b) • M.val.map W.unop.hom.op m)
      map_add' := by
        intro b c
        change φ.val.app _
          (((@id (B.right.obj.obj (Opposite.op W.unop.left)) b) +
            (@id (B.right.obj.obj (Opposite.op W.unop.left)) c)) • M.val.map _ m) = _
        rw [add_smul, map_add]
      map_smul' := by
        intro r b
        let b' : B.right.obj.obj (Opposite.op W.unop.left) := b
        change φ.val.app (Opposite.op W.unop.left)
          (((B.hom.hom.app (Opposite.op W.unop.left)).hom r * b') •
            M.val.map W.unop.hom.op m) =
          r • φ.val.app (Opposite.op W.unop.left) (b' • M.val.map W.unop.hom.op m)
        rw [mul_smul]
        exact (φ.val.app (Opposite.op W.unop.left)).hom.map_smul r _ }
  naturality {W V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change B.right.obj.obj (Opposite.op W.unop.left) at b
    change φ.val.app (Opposite.op V.unop.left)
      (B.right.obj.map f.unop.left.op b • M.val.map V.unop.hom.op m) =
      F.val.map f.unop.left.op
        (φ.val.app (Opposite.op W.unop.left) (b • M.val.map W.unop.hom.op m))
    rw [← PresheafOfModules.naturality_apply φ.val]
    change _ = φ.val.app (Opposite.op V.unop.left)
      (M.val.map f.unop.left.op (b • M.val.map W.unop.hom.op m))
    rw [M.val.map_smul]
    congr 2
    rw [← M.val.map_comp_apply, ← op_comp, Over.w]

set_option backward.isDefEq.respectTransparency false in
/-- Assemble the sectionwise maps into a B-linear sheaf morphism.
Source: Stacks Project, Modules, Tag 0A6F
(blueprint: lem-sc-sheaf-algebra-hom-adjunction). -/
private noncomputable def curry
    {Y : Scheme.{u}} {B : Y.CommAlgebraSheaf} {M : BMod Y B} {F : OMod Y}
    (φ : (res Y B).obj M ⟶ F) :
    M ⟶ sheafAlgebraHomObj Y B F where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (Y := (sheafAlgebraHomObj Y B F).val.obj U)
        { toFun := currySection φ U
          map_add' := by
            intro m n
            apply PresheafOfModules.hom_ext
            intro W
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro b
            let b' : B.right.obj.obj (Opposite.op W.unop.left) := b
            change φ.val.app _ (b' • M.val.map _ (m + n)) =
              φ.val.app _ (b' • M.val.map _ m) + φ.val.app _ (b' • M.val.map _ n)
            simp only [map_add, smul_add]
          map_smul' := by
            intro b m
            apply PresheafOfModules.hom_ext
            intro W
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro c
            rw [RingHom.id_apply, sheafAlgebraHom_smul]
            let c' : B.right.obj.obj (Opposite.op W.unop.left) := c
            change φ.val.app _ (c' • M.val.map _ (b • m)) =
              φ.val.app _ ((B.right.obj.map W.unop.hom.op b * c') •
                M.val.map W.unop.hom.op m)
            rw [M.val.map_smul, mul_smul]
            congr 1
            exact smul_comm c' (B.right.obj.map W.unop.hom.op b)
              (show M.val.obj (Opposite.op W.unop.left) from M.val.map W.unop.hom.op m) }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        change B.right.obj.obj (Opposite.op W.unop.left) at b
        change φ.val.app _ (b • M.val.map W.unop.hom.op (M.val.map f m)) =
          φ.val.app _ (b • (show M.val.obj (Opposite.op W.unop.left) from
            M.val.map ((Over.map f.unop).obj W.unop).hom.op m))
        congr 2
        rw [← M.val.map_comp_apply]
        exact M.val.congr_map_apply (Subsingleton.elim _ _) m }

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate at 1 to recover an O-linear sheaf morphism.
Source: Stacks Project, Modules, Tag 0A6F
(blueprint: lem-sc-sheaf-algebra-hom-adjunction). -/
private noncomputable def uncurry
    {Y : Scheme.{u}} {B : Y.CommAlgebraSheaf} {M : BMod Y B} {F : OMod Y}
    (ψ : M ⟶ sheafAlgebraHomObj Y B F) :
    (res Y B).obj M ⟶ F where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((res Y B).obj M).val.obj U)
        { toFun := fun m ↦ (ψ.val.app U m).app (Opposite.op (Over.mk (𝟙 U.unop)))
            (1 : B.right.obj.obj U)
          map_add' := by
            intro m n
            change (ψ.val.app U (m + n)).app _ _ = _
            rw [map_add]
            rfl
          map_smul' := by
            intro r m
            let m' : M.val.obj U := m
            change (ψ.val.app U ((B.hom.hom.app U).hom r • m')).app _ _ = _
            rw [(ψ.val.app U).hom.map_smul, sheafAlgebraHom_underlying_linear]
            let r' : Y.sheaf.obj.obj U := r
            change Y.sheaf.obj.map (𝟙 U.unop).op r' •
              (show F.val.obj U from (ψ.val.app U m').app
                (Opposite.op (Over.mk (𝟙 U.unop))) (1 : B.right.obj.obj U)) = _
            rw [op_id, Y.sheaf.obj.map_id]
            rfl }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        change (ψ.val.app V (M.val.map f m)).app (Opposite.op (Over.mk (𝟙 V.unop)))
          (1 : B.right.obj.obj V) =
          F.val.map f ((ψ.val.app U m).app (Opposite.op (Over.mk (𝟙 U.unop)))
            (1 : B.right.obj.obj U))
        rw [PresheafOfModules.naturality_apply ψ.val]
        change (ψ.val.app U m).app (Opposite.op (Over.mk (𝟙 V.unop ≫ f.unop)))
          (1 : B.right.obj.obj V) = _
        rw [PresheafOfModules.restrictOver_hom_app_congr _ (Category.id_comp f.unop)]
        have h := PresheafOfModules.naturality_apply (ψ.val.app U m)
          (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop)).op
          (1 : B.right.obj.obj U)
        change (ψ.val.app U m).app (Opposite.op (Over.mk f.unop))
          (B.right.obj.map f 1) = _ at h
        rw [map_one] at h
        exact h }

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise formula for the forward map. -/
private theorem curry_apply
    {Y : Scheme.{u}} {B : Y.CommAlgebraSheaf} {M : BMod Y B} {F : OMod Y} (φ : (res Y B).obj M ⟶ F)
    (U : (Opens Y)ᵒᵖ) (m : M.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (b : B.toModule.val.obj (Opposite.op W.unop.left)) :
    ((curry φ).val.app U m).app W b = φ.val.app (Opposite.op W.unop.left)
      ((@id (B.right.obj.obj (Opposite.op W.unop.left)) b) • M.val.map W.unop.hom.op m) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise formula for the inverse map. -/
private theorem uncurry_apply
    {Y : Scheme.{u}} {B : Y.CommAlgebraSheaf} {M : BMod Y B} {F : OMod Y}
    (ψ : M ⟶ sheafAlgebraHomObj Y B F)
    (U : (Opens Y)ᵒᵖ) (m : M.val.obj U) :
    (uncurry ψ).val.app U m = (ψ.val.app U m).app (Opposite.op (Over.mk (𝟙 U.unop)))
      (1 : B.right.obj.obj U) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of scalars is left adjoint to the explicitly constructed algebra-valued Hom.

Proof: For a B-module sheaf M and an O-module sheaf F, send a morphism φ from the
scalar restriction of M to F to ψ with ψ_U(m)_V(b) = φ_V(b • res_{U,V}(m)).
Here V ranges over opens contained in U, as in `sheafAlgebraHomSections`.
Conversely send ψ to φ_U(m) = (ψ_U(m)).app (op (Over.mk (𝟙 U))) 1.
Additivity in m and b follows from distributivity and additivity of φ. O-linearity
in b follows from O-linearity of φ and the scalar-tower identity. B-linearity in m
follows from associativity and commutativity of multiplication and
`sheafAlgebraHom_smul`: multiplying ψ by c precomposes its argument by c.
For V contained in U, restrictions preserve products and scalar multiplication;
φ's naturality therefore makes the family in V a presheaf morphism and the family
in U a sheaf morphism into `sheafAlgebraHomObj`. Evaluation at 1 is O-linear by
`sheafAlgebraHom_underlying_linear`, and commutes with restrictions since ring
restriction preserves 1. The composites are φ(1 • m) = φ(m) and
ψ(b • m)(1) = (b • ψ(m))(1) = ψ(m)(b). Thus the two maps are inverse.
Precomposition in M and postcomposition in F commute with these formulas;
`sheafAlgebraHomMap` is precisely postcomposition, so the equivalences are natural
in both variables. Apply `Adjunction.mkOfHomEquiv` to these natural equivalences.
The same formulas work when B is the zero ring or the scheme is empty: units and
module identities still hold, and no choice of a nonzero section was used.

Source: Stacks Project, Modules, Tag 0A6F; Duality for Schemes, Tags 0BV0 and 0BV1
(blueprint: lem-sc-sheaf-algebra-hom-adjunction). -/
theorem sheafAlgebraHom_adjunction (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) :
    Nonempty ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)) ⊣ sheafAlgebraHom Y B) := by
  refine ⟨Adjunction.mkOfHomEquiv
    { homEquiv := fun M F ↦
        { toFun := curry
          invFun := uncurry
          left_inv := fun φ ↦ ?_
          right_inv := fun ψ ↦ ?_ }
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }⟩
  · ext U m
    change (uncurry (curry φ)).val.app U m = φ.val.app U m
    rw [uncurry_apply, curry_apply]
    simp only [Over.mk_hom, Over.mk_left, op_id, id_eq, one_smul]
    rw [M.val.map_id]
    rfl
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    let b' : B.right.obj.obj (Opposite.op W.unop.left) := b
    change (ψ.val.app (Opposite.op W.unop.left) (b' • M.val.map W.unop.hom.op m)).app
      (Opposite.op (Over.mk (𝟙 W.unop.left))) (1 : B.right.obj.obj (Opposite.op W.unop.left)) = _
    rw [(ψ.val.app (Opposite.op W.unop.left)).hom.map_smul, sheafAlgebraHom_smul]
    simp only [Over.mk_hom, Over.mk_left, op_id, B.right.obj.map_id,
      CommRingCat.id_apply, id_eq, mul_one]
    rw [PresheafOfModules.naturality_apply ψ.val]
    change (ψ.val.app U m).app (Opposite.op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom))) b' = _
    exact PresheafOfModules.restrictOver_hom_app_congr (ψ.val.app U m)
      (Category.id_comp W.unop.hom) b
  · intro M' M F f ψ
    ext U m
    rfl
  · intro M F F' φ g
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    rfl

end AlgebraicGeometry

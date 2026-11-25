/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenTensorRestrictionSquareStalkUnit
/-! # Homology transport for normalized open tensor coordinates

Source: Stacks Project, Tag 0098, stalks of pullback and restriction.
-/


@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange


variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]


-- Reuse the proved unit-germ argument from OpenOrdinaryTensorPureGermCoordinatesCanonical.
open TopologicalSpace Opposite in
set_option linter.unusedSectionVars false in
private theorem tensor_unit_stalk {X Y : Scheme.{u}} (k : X ⟶ Y) (x : X)
    (M : Y.Modules) (m : M.presheaf.stalk (k x)) :
    (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso k x)).inv.app M
        ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (k x), (k.stalkMap x).hom] m) =
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k x)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M))) ≫
        ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
          AddCommGrpCat.{u} k.base x) m := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  obtain ⟨W, hx, s, rfl⟩ := M.presheaf.exists_germ_eq m
  have he := Classical.choose_spec (Scheme.Modules.exists_tensorPullback_stalk_iso k x)
    M W hx s
  have hi := congrArg (fun t ↦
    (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso k x)).inv.app M t) he
  have hunit :
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso k x)).inv.app M
          ((1 : X.presheaf.stalk x) ⊗ₜ[_, (k.stalkMap x).hom]
            (M.presheaf.germ W (k x) hx s)) =
        ((Scheme.Modules.tensorPullback k).obj M).presheaf.germ (k ⁻¹ᵁ W) x hx
          ((Classical.choose
            (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M |>.app W s) := by
    simp only [← ModuleCat.comp_apply, Iso.hom_inv_id_app, ModuleCat.id_apply] at hi
    exact hi.symm
  rw [hunit]
  change _ = ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
    AddCommGrpCat.{u} k.base x
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k x)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)))
        (M.presheaf.germ W (k x) hx s))
  have hm := TopCat.Presheaf.stalkFunctor_map_germ_apply W (k x) hx
    (Scheme.Modules.Hom.mapPresheaf
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)) s
  have hp := TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u} k.base
    ((Scheme.Modules.tensorPullback k).obj M).presheaf W x hx
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M).app W s)
  exact hp.symm.trans (congrArg
    (((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
      AddCommGrpCat.{u} k.base x) hm.symm)

open TopologicalSpace Opposite in
set_option linter.unusedSectionVars false in
private theorem tensor_unit_stalk_cast {X Y : Scheme.{u}} (k : X ⟶ Y) (x : X)
    (M : Y.Modules) (a : Y.presheaf.stalk (k x) →+* X.presheaf.stalk x)
    (ha : a = (k.stalkMap x).hom) (m : M.presheaf.stalk (k x)) :
    (eqToHom (congrArg (fun b ↦ (ModuleCat.extendScalars b).obj
        ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (k x)).obj M)) ha) ≫
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso k x)).inv.app M)
        ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (k x), a] m) =
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k x)).map
        (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M))) ≫
        ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
          AddCommGrpCat.{u} k.base x) m := by
  subst a
  simpa using tensor_unit_stalk k x M m


/-- Coefficient-one case of open tensor restriction on pure stalk tensors.

Proof: represent x as a section germ s on an open neighborhood W of g' z.
By the defining component equation of tensorStalkIso and the unit-germ formula
of exists_tensorPullback_stalk_iso, the coefficient-one tensor is the germ of
the chosen tensor-pullback adjunction unit applied to s. The eqToHom in the
component equation changes only the scalar-extension map, using tensorMap's
restriction equation; it leaves this tensor unchanged.
Restrict that output germ along pullback.fst g' U.ι. The inverse restriction
stalk formula identifies it with the germ of the restricted unit section.
Evaluate the two tensorPullbackCompositionIso unit identities and the two
openTensorRestrictionIso leftAdjointUniq unit identities on that section.
Their composite, which defines openTensorRestrictionSquareIso, sends it to
the tensor-pullback unit of the same section restricted along U.ι. The equality
pullback.condition identifies the inverse-image neighborhoods in the two routes.
Apply the restricted tensorStalkIso unit-germ formula. Its input is precisely
stalkCongr along hp followed by inverse restriction along U.ι: stalkCongr only
renames the point of the original germ, and inverse restriction sends it to
the germ of the restricted section. Thus the two routes agree. Every x admits
a section representative, so the result follows for all k and x. Empty opens
have no z0; zero modules, zero rings, and negative degrees cause no exception.
Source: Stacks Project, Tags 0098 and 0D5U; the specified unit identities for
composition mates and uniqueness of left adjoints.
(blueprint: lem-pc-open-restricted-tensor-chain-transport-pure-one). -/
theorem openRestricted_tensor_chain_transport_pure_one
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (U : X.Opens)
    (sq0 : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z0 : (pullback g' U.ι : Scheme.{u}))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := pullback.fst g' U.ι z0
    let P0 := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
      (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z0)) AddCommGrpCat.{u}
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (U.ι ≫ f) (pullback.snd g' U.ι) z0
    letI := rightAlgebra (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sq0 z0
    letI := (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (U.ι ≫ f) (pullback.snd g' U.ι) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (pullback.fst g' U.ι ≫ f') z0))
    let R0 := R (U.ι ≫ f) (pullback.snd g' U.ι) z0
    let A0 := A (pullback.snd g' U.ι) z0
    let B0 := B (pullback.fst g' U.ι ≫ f') z0
    let Q := stalkComplex g' z P
    let hp : g' z = U.ι (pullback.snd g' U.ι z0) :=
      congrArg (fun h : pullback g' U.ι ⟶ X => h z0) pullback.condition
    ∀ (k : ℤ) (x : Q.X k),
      (F.map ((tensorStalkIso f f' g g' sq z P).hom.f k) ≫
        (Scheme.Modules.restrictStalkNatIso (pullback.fst g' U.ι) z0).inv.app (Pg.X k) ≫
        F0.map ((RingedSpace.moduleStalkFunctor
          (pullback g' U.ι).toRingedSpace z0).map
            ((openTensorRestrictionComplexIso g' U P).hom.f k)))
          ((1 : C z) ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
            (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
      F0.map ((tensorStalkIso (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sq0 z0 P0).hom.f k)
          (((pullback.fst g' U.ι).stalkMap z0).hom (1 : C z) ⊗ₜ[A0,
            (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
              g (pullback.snd g' U.ι) sq0 z0).comp
              (algebraMap A0 (A0 ⊗[R0] B0))]
            ((Scheme.Modules.restrictStalkNatIso U.ι (pullback.snd g' U.ι z0)).inv.app
              (P.X k) (((show X.Modules from P.X k).presheaf.stalkCongr (.of_eq hp)).hom x)))
      := by
  dsimp only
  intro k x
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let z := pullback.fst g' U.ι z0
  let P0 := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := leftAlgebra (U.ι ≫ f) (pullback.snd g' U.ι) z0
  let := rightAlgebra (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sq0 z0
  simp only [map_one]
  erw [Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z P) k,
    Classical.choose_spec (exists_tensorStalkIso (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sq0 z0 P0) k]
  change ((RingedSpace.moduleStalkFunctor (pullback g' U.ι).toRingedSpace z0).map
      ((openTensorRestrictionSquareIso g' U).hom.app (P.X k)))
    ((Scheme.Modules.restrictStalkNatIso (pullback.fst g' U.ι) z0).inv.app
      ((Scheme.Modules.tensorPullback g').obj (P.X k)) ((eqToHom _ ≫
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.app
        (P.X k)) _)) =
    (eqToHom _ ≫
      (Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso
        (pullback.snd g' U.ι) z0)).inv.app (P0.X k)) _
  rw [tensor_unit_stalk_cast, tensor_unit_stalk_cast]
  · exact ConcreteCategory.congr_hom
      (openTensorRestrictionSquare_stalk_unit g' U (P.X k) z0) x
  · exact (Classical.choose_spec
      (exists_tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sq0 z0)).1
  · exact (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1

end AlgebraicGeometry.SingleComplexBaseChange

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorChainTransportPureOne
import WeilConjectures.AlgebraicGeometry.RestrictStalkInvSmul
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


set_option linter.unusedVariables false in
/-- The open tensor restriction square carries a pure tensor to the same restricted germ.

Proof: use the specified components of tensorStalkIso to reduce to the ordinary
pullback-stalk isomorphism. Represent x by a section on a neighborhood of g′ z.
The tensor-pullback adjunction unit sends that section to its tensor with 1.
The unit identities for the two composition mates defining
openTensorRestrictionSquareIso identify both routes on this unit with restriction
of that same section. The inverse restrictStalkNatIso sends its germ to the germ
of the restricted section; stalkCongr changes only the equality naming its point.
Thus both routes agree for coefficient 1. The output restriction is semilinear
for the actual projection stalk map, so multiplying by d gives the displayed
formula. Every input stalk element is represented by a section germ. This proves
all x and d without making any auxiliary coordinate choices. Empty opens have
no z0; zero rings, zero complexes, and negative degrees need no extra assumption.
Source: Stacks Project, Tag 0098, restriction of stalk germs; Tag 0D5U,
restriction of modules; the unit identities of the specified composition mates.
(blueprint: lem-pc-open-restricted-tensor-chain-transport-pure). -/
theorem openRestricted_tensor_chain_transport_pure
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
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (pullback.snd g' U.ι) z0 P0
    let V0 := tensorComplex (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sq0 z0 P0
    let hp : g' z = U.ι (pullback.snd g' U.ι z0) :=
      congrArg (fun h : pullback g' U.ι ⟶ X => h z0) pullback.condition
    ∀ (k : ℤ) (d : C z) (x : Q.X k),
      (F.map ((tensorStalkIso f f' g g' sq z P).hom.f k) ≫
        (Scheme.Modules.restrictStalkNatIso (pullback.fst g' U.ι) z0).inv.app (Pg.X k) ≫
        F0.map ((RingedSpace.moduleStalkFunctor
          (pullback g' U.ι).toRingedSpace z0).map
            ((openTensorRestrictionComplexIso g' U P).hom.f k)))
          (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
            (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
      F0.map ((tensorStalkIso (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sq0 z0 P0).hom.f k)
          (((pullback.fst g' U.ι).stalkMap z0).hom d ⊗ₜ[A0,
            (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
              g (pullback.snd g' U.ι) sq0 z0).comp
              (algebraMap A0 (A0 ⊗[R0] B0))]
            ((Scheme.Modules.restrictStalkNatIso U.ι (pullback.snd g' U.ι z0)).inv.app
              (P.X k) (((show X.Modules from P.X k).presheaf.stalkCongr (.of_eq hp)).hom x)))
      := by
  dsimp only
  intro k d x
  let z := pullback.fst g' U.ι z0
  let P0 := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
  let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let a := (tensorMap f f' g g' sq z).comp
    (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))
  let := leftAlgebra (U.ι ≫ f) (pullback.snd g' U.ι) z0
  let := rightAlgebra (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sq0 z0
  let a0 := (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sq0 z0).comp
      (algebraMap (A (pullback.snd g' U.ι) z0)
        (A (pullback.snd g' U.ι) z0 ⊗[R (U.ι ≫ f) (pullback.snd g' U.ι) z0]
          B (pullback.fst g' U.ι ≫ f') z0))
  let e := (tensorStalkIso f f' g g' sq z P).hom.f k
  let e0 := (tensorStalkIso (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sq0 z0 P0).hom.f k
  let c := (RingedSpace.moduleStalkFunctor (pullback g' U.ι).toRingedSpace z0).map
    ((openTensorRestrictionComplexIso g' U P).hom.f k)
  let r := (Scheme.Modules.restrictStalkNatIso (pullback.fst g' U.ι) z0).inv.app (Pg.X k)
  let hp : g' z = U.ι (pullback.snd g' U.ι z0) :=
    congrArg (fun h : pullback g' U.ι ⟶ X => h z0) pullback.condition
  let x0 := (Scheme.Modules.restrictStalkNatIso U.ι (pullback.snd g' U.ι z0)).inv.app
    (P.X k) (((show X.Modules from P.X k).presheaf.stalkCongr (.of_eq hp)).hom x)
  let d0 := ((pullback.fst g' U.ι).stalkMap z0).hom d
  change c.hom (r (e.hom (d ⊗ₜ[A g' z, a] x))) =
    e0.hom (d0 ⊗ₜ[A (pullback.snd g' U.ι) z0, a0] x0)
  have h := openRestricted_tensor_chain_transport_pure_one f f' g g' sq U sq0 z0 P k x
  simp only [map_one] at h
  change c.hom (r (e.hom ((1 : C z) ⊗ₜ[A g' z, a] x))) =
    e0.hom ((1 : C z0) ⊗ₜ[A (pullback.snd g' U.ι) z0, a0] x0) at h
  rw [← mul_one d]
  erw [← ModuleCat.ExtendScalars.smul_tmul a d 1 x, e.hom.map_smul]
  erw [Scheme.Modules.restrictStalkNatIso_inv_smul, c.hom.map_smul]
  rw [h]
  dsimp only [d0]
  erw [← e0.hom.map_smul]
  congr 1
  exact (ModuleCat.ExtendScalars.smul_tmul a0
    (((pullback.fst g' U.ι).stalkMap z0).hom d) 1 _).trans (by rw [mul_one])

end AlgebraicGeometry.SingleComplexBaseChange

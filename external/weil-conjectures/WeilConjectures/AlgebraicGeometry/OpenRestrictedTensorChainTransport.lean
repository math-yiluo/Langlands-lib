/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorChainTransportPure
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


/-- The normalized tensor coordinates commute with the ordinary open restriction square.

Proof: evaluate the specified tensorStalkIso components on a pure tensor d tensor x.
Represent x by a section germ. The units of tensor pullback take this section to
1 tensor its germ. The unit identities for the composition adjunction mates in
openTensorRestrictionSquareIso identify the two composites with restriction of
that section and multiplication by the image of d under the output stalk map.
The hypotheses identify that image with eD d and the input germ with q x; the
pure-tensor formula for t therefore gives the same result. Stalk elements are
section germs. Tensor induction and additivity extend the equality from pure
tensors to every element, and extensionality gives equality of additive maps.
This is only a degreewise statement: it uses neither homology nor localization.
Empty opens have no z0; zero complexes and zero rings require no extra condition.
Source: Stacks Project, Tag 0098 (stalks of pullback modules), and Tag 0D5U
(exact restriction); the units of the specified pullback adjunctions.
(blueprint: lem-pc-open-restricted-tensor-chain-transport). -/
theorem openRestricted_tensor_chain_transport
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
    ∀ (eA : A g' z ≃+* A0)
      (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0)
      (t : tensorComplex f f' g g' sq z P ≅
        ((ModuleCat.restrictScalars.{u} eD.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj V0),
      eD.toRingHom = ((pullback.fst g' U.ι).stalkMap z0).hom →
      (∀ (k : ℤ) (x : Q.X k),
        (show Q0.X k from q.hom.f k x) =
          (Scheme.Modules.restrictStalkNatIso U.ι (pullback.snd g' U.ι z0)).inv.app
            (P.X k) (((show X.Modules from P.X k).presheaf.stalkCongr (.of_eq hp)).hom x)) →
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
          g (pullback.snd g' U.ι) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) →
      ∀ k : ℤ,
        F.map ((tensorStalkIso f f' g g' sq z P).hom.f k) ≫
          (Scheme.Modules.restrictStalkNatIso (pullback.fst g' U.ι) z0).inv.app (Pg.X k) ≫
          F0.map ((RingedSpace.moduleStalkFunctor
            (pullback g' U.ι).toRingedSpace z0).map
              ((openTensorRestrictionComplexIso g' U P).hom.f k)) =
        F.map (t.hom.f k) ≫
          F0.map ((tensorStalkIso (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
            g (pullback.snd g' U.ι) sq0 z0 P0).hom.f k) := by
  dsimp only
  intro eA eD q t heD hq ht k
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul d x =>
    have h := openRestricted_tensor_chain_transport_pure f f' g g' sq U sq0 z0 P k d x
    dsimp only at h
    have hd : eD d = ((pullback.fst g' U.ι).stalkMap z0).hom d :=
      congrArg (fun a => a d) heD
    change _ = (tensorStalkIso (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sq0 z0 _).hom.f k (t.hom.f k _)
    rw [ht k d x, hd, hq k x]
    exact h
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgebraicGeometry.SingleComplexBaseChange

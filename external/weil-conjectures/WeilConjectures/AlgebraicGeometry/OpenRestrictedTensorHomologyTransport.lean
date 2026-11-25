/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorChainTransport
import WeilConjectures.AlgebraicGeometry.OpenStalkChainHomologyTransport
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


/-- The homology transport equation for normalized open tensor coordinates.

Proof: The input-chain normalization is the inverse same-germ restriction map,
and eD is the actual open projection stalk map. Evaluate tensorStalkIso and the
adjunction mates defining openTensorRestrictionSquareIso on a pure tensor of a
coefficient and a section germ. The assumed formula for t makes both resulting
chain maps equal to the same restricted germ with coefficient eD(d). Every stalk
element is a section germ and tensor induction gives equality of chain maps.
Apply homology. The exact restrictScalars homology isomorphism accounts for the
change of coefficient ring. Use comparisonStalkHomologyIso_naturality to move the
localized chain restriction square across the stalk-homology comparisons. Expand
openDerivedStalkIso into exact stalk homology, the same-germ restriction map,
exact restriction homology, and the derived restriction comparison. Exact-functor
homology naturality identifies these factors with openRestrictionRepresentativeIso.
Its inverse is the first factor of openRestrictedTensorDerivedIso, so it cancels;
the remaining factor is the localized chain square already identified. This is
the displayed equation. No flatness, boundedness, nonzero stalk ring or resolution
is used. Empty opens have no point, and zero complexes give zero morphisms.
This lemma supplies only the homology equation; it constructs none of the ring,
input-chain or tensor-chain isomorphisms.
Source: Stacks Project, Tags 0098 and 0D5U, Section 20.32 opening paragraph;
Mathlib exact-functor homology naturality.
(blueprint: lem-pc-open-restricted-tensor-homology-transport). -/
theorem openRestricted_tensor_homology_transport
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (U : X.Opens)
    (sq0 : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z0 : (pullback g' U.ι : Scheme.{u})) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := pullback.fst g' U.ι z0
    let P0 := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
      (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let Pg0 := ((Scheme.Modules.tensorPullback (pullback.snd g' U.ι)).mapHomologicalComplex
      (.up ℤ)).obj P0
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z0)) AddCommGrpCat.{u}
    let HU := comparisonStalkCohomology (pullback g' U.ι) z0 i ⋙ F0
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
      F.map (HomologicalComplex.homologyMap t.hom i) ≫
          F.map ((V0.sc i).mapHomologyIso
            (ModuleCat.restrictScalars.{u} eD.toRingHom)).hom ≫
          F0.map (HomologicalComplex.homologyMap
            (tensorStalkIso (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
              g (pullback.snd g' U.ι) sq0 z0 P0).hom i ≫
            (comparisonStalkHomologyIso (pullback g' U.ι) z0 Pg0 i).inv) =
        F.map (HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
          (comparisonStalkHomologyIso X' z Pg i).inv) ≫
          (openDerivedStalkIso (pullback.fst g' U.ι) z0 i).hom.app
            (DerivedCategory.Q.obj Pg) ≫ HU.map (openRestrictedTensorDerivedIso g' U P).hom
    := by
  dsimp only
  intro eA eD q t heD hq ht
  have hc := openRestricted_tensor_chain_transport f f' g g' sq U sq0 z0 P
    eA eD q t heD hq ht
  exact openStalk_chain_homology_transport (pullback.fst g' U.ι) z0 i _ _ _ _ eD t.hom
    (tensorStalkIso f f' g g' sq (pullback.fst g' U.ι z0) P).hom
    (tensorStalkIso (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g
      (pullback.snd g' U.ι) sq0 z0 _).hom
    (openTensorRestrictionComplexIso g' U P).hom hc

end AlgebraicGeometry.SingleComplexBaseChange

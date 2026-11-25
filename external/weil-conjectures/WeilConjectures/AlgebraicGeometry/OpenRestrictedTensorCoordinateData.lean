/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenRestrictedStalkCoordinates
import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorHomologyTransport
/-! # Open stalk ring and tensor coordinates

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
private def tensorDegreeIso
    {A A₀ D D₀ : Type u}
    [CommRing A] [CommRing A₀] [CommRing D] [CommRing D₀]
    (φ : A →+* D) (φ₀ : A₀ →+* D₀) (eA : A ≃+* A₀) (eD : D ≃+* D₀)
    (h : ∀ a, eD (φ a) = φ₀ (eA a))
    (M : ModuleCat.{u} A) (M₀ : ModuleCat.{u} A₀)
    (q : M ≅ (ModuleCat.restrictScalars eA.toRingHom).obj M₀) :
    (ModuleCat.extendScalars φ).obj M ≅
      (ModuleCat.restrictScalars eD.toRingHom).obj
        ((ModuleCat.extendScalars φ₀).obj M₀) := by
  let := RingHomInvPair.of_ringEquiv eA
  let := RingHomInvPair.of_ringEquiv_symm eA
  let : Module A D := Module.compHom D φ
  let : Module A₀ D₀ := Module.compHom D₀ φ₀
  let d : LinearEquiv (eA : A →+* A₀) (σ' := (eA.symm : A₀ →+* A)) D D₀ :=
    { __ := eD.toAddEquiv
      map_smul' := by
        intro a x
        change eD (φ a * x) = φ₀ (eA a) * eD x
        rw [map_mul, h] }
  let c : LinearEquiv (eA : A →+* A₀) (σ' := (eA.symm : A₀ →+* A)) M M₀ :=
    { __ := q.toLinearEquiv.toAddEquiv
      map_smul' := q.hom.hom.map_smul }
  let T := TensorProduct.congr (σ₂₁ := (eA.symm : A₀ →+* A)) d c
  let T' : (ModuleCat.extendScalars φ).obj M ≃ₗ[D]
      (ModuleCat.restrictScalars eD.toRingHom).obj
        ((ModuleCat.extendScalars φ₀).obj M₀) :=
    { __ := T.toAddEquiv
      map_smul' := by
        intro b z
        induction z using TensorProduct.inductionOn with
        | tmul b' m =>
          change D at b'
          change T ((b * b') ⊗ₜ[A] m) = eD b • T (b' ⊗ₜ[A] m)
          change eD (b * b') ⊗ₜ[A₀] c m = (eD b * eD b') ⊗ₜ[A₀] c m
          rw [map_mul]
        | add z w hz hw =>
          change T (b • (z + w)) = eD b • T (z + w)
          change T (b • z) = eD b • T z at hz
          change T (b • w) = eD b • T w at hw
          rw [smul_add, map_add, hz, hw, map_add, smul_add] }
  exact T'.toModuleIso

private theorem tensorDegreeIso_tmul
    {A A₀ D D₀ : Type u}
    [CommRing A] [CommRing A₀] [CommRing D] [CommRing D₀]
    (φ : A →+* D) (φ₀ : A₀ →+* D₀) (eA : A ≃+* A₀) (eD : D ≃+* D₀)
    (h : ∀ a, eD (φ a) = φ₀ (eA a))
    (M : ModuleCat.{u} A) (M₀ : ModuleCat.{u} A₀)
    (q : M ≅ (ModuleCat.restrictScalars eA.toRingHom).obj M₀)
    (d : D) (m : M) :
    (tensorDegreeIso φ φ₀ eA eD h M M₀ q).hom (d ⊗ₜ[A, φ] m) =
      eD d ⊗ₜ[A₀, φ₀] (show M₀ from q.hom m) := by
  rfl

private theorem exists_tensorComplexIso
    {A A₀ D D₀ : Type u}
    [CommRing A] [CommRing A₀] [CommRing D] [CommRing D₀]
    (φ : A →+* D) (φ₀ : A₀ →+* D₀) (eA : A ≃+* A₀) (eD : D ≃+* D₀)
    (h : ∀ a, eD (φ a) = φ₀ (eA a))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (Q₀ : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (q : Q ≅ ((ModuleCat.restrictScalars eA.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj Q₀) :
    ∃ t : ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj Q ≅
        ((ModuleCat.restrictScalars eD.toRingHom).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars φ₀).mapHomologicalComplex (.up ℤ)).obj Q₀),
      ∀ (k : ℤ) (d : D) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A, φ] x) =
          eD d ⊗ₜ[A₀, φ₀] (show Q₀.X k from q.hom.f k x) := by
  let e (k : ℤ) := tensorDegreeIso φ φ₀ eA eD h (Q.X k) (Q₀.X k)
    (HomologicalComplex.eval _ _ k |>.mapIso q)
  have he (k : ℤ) (d : D) (x : Q.X k) :
      (e k).hom (d ⊗ₜ[A, φ] x) =
        eD d ⊗ₜ[A₀, φ₀] (show Q₀.X k from q.hom.f k x) :=
    tensorDegreeIso_tmul φ φ₀ eA eD h _ _ _ d x
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_, ?_⟩
  · intro k l _
    ext x
    symm
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul d x =>
      change (e l).hom ((ModuleCat.extendScalars φ).map (Q.d k l) (d ⊗ₜ[A, φ] x)) =
        (ModuleCat.restrictScalars eD.toRingHom).map
          ((ModuleCat.extendScalars φ₀).map (Q₀.d k l)) ((e k).hom (d ⊗ₜ[A, φ] x))
      rw [ModuleCat.ExtendScalars.map_tmul, he, he]
      change eD d ⊗ₜ[A₀, φ₀] (show Q₀.X l from q.hom.f l (Q.d k l x)) =
        eD d ⊗ₜ[A₀, φ₀] (Q₀.d k l (show Q₀.X k from q.hom.f k x))
      congr 1
      exact (ConcreteCategory.congr_hom (q.hom.comm k l) x).symm
  · exact he

namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]


/-- Compatible ring and chain coordinates for restriction to an arbitrary source open.

Proof: take the open stalk maps of U.ι and pullback.fst for eA and eD.
The pullback condition identifies U.ι(qz) with g'(pz). Use stalkMap_comp and
stalkMap_congr_hom to identify the base rings, and the same point of S' for eB.
These identities give hA and hB. On each tensor inclusion the two tensorMap maps
agree after transport, which gives hD by tensor induction. The same-germ restriction
stalk isomorphism is semilinear for eA: represent a scalar and a module germ on a
common open, use germ_smul and germ_restrictStalkNatIso_hom_app, and identify the
ring germs using the inverse open stalk map. Invert this natural linear isomorphism
in every degree to get q; naturality makes it commute with differentials. Define
t by d tensor x ↦ eD(d) tensor q(x). The compatibility hD makes this balanced;
use the inverse ring and chain maps to construct its inverse. Its pure tensor
formula is the penultimate assertion. For the final equation apply the stalk
pullback germ formula to the adjunction mates defining openTensorRestrictionSquareIso.
Both resulting chain maps send d tensor a section germ to the same restricted germ
with coefficient eD(d); tensor induction proves equality. Apply homology and use
comparisonStalkHomologyIso_naturality. Exact restriction homology and exact stalk
homology identify the additive restriction map with openDerivedStalkIso followed
by the image of openRestrictionRepresentativeIso. Its inverse cancels the first
factor of openRestrictedTensorDerivedIso, leaving precisely the chain map just
identified. This proves the final equation. No localizedComparison or source
base-derived tensor cohomology is involved in this statement.
For the empty open there is no z; top opens, zero rings and zero complexes use
exactly the same germ and tensor identities.
Source: Stacks Project, Tag 0098; Mathlib restrictStalkNatIso and its germ formulas.
(blueprint: lem-pc-open-restricted-tensor-coordinate-data). -/
theorem exists_openRestricted_tensor_coordinate_data
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
    ∃ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0)
      (t : tensorComplex f f' g g' sq z P ≅
        ((ModuleCat.restrictScalars.{u} eD.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj V0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) ∧
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
          g (pullback.snd g' U.ι) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) ∧
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
  classical
  intro z P0 Pg Pg0 F F0 HU R0 A0 B0 D0 Q Q0 V0
  obtain ⟨eR, eA, eB, eD, q, hRA, hRB, hD, heD, hq⟩ :=
    exists_openRestricted_stalk_coordinates f f' g g' sq U sq0 z0 P
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := leftAlgebra (U.ι ≫ f) (pullback.snd g' U.ι) z0
  let := rightAlgebra (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sq0 z0
  let := (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sq0 z0).toAlgebra
  let φ := (tensorMap f f' g g' sq z).comp
    (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))
  let φ0 := (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sq0 z0).comp (algebraMap A0 (A0 ⊗[R0] B0))
  have hφ (a : A g' z) : eD (φ a) = φ0 (eA a) := by
    change eD ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z))
      (a ⊗ₜ[R f g' z] 1)) =
        (algebraMap (A0 ⊗[R0] B0) D0) (eA a ⊗ₜ[R0] 1)
    simpa only [map_one] using hD a 1
  obtain ⟨t, ht⟩ := exists_tensorComplexIso φ φ0 eA eD hφ Q Q0 q
  refine ⟨eR, eA, eB, eD, q, t, hRA, hRB, hD, ht, ?_⟩
  exact openRestricted_tensor_homology_transport f f' g g' sq U sq0 z0 i P
    eA eD q t heD hq ht


end AlgebraicGeometry.SingleComplexBaseChange

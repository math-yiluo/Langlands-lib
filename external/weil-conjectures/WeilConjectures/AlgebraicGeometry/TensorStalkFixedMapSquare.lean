/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
import WeilConjectures.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison
import WeilConjectures.AlgebraicGeometry.TensorStalkChainCoordinates

/-! # Tensor compatibility of a fixed stalk chain map

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-tensor-stalk-fixed-map-square).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry



-- Elaborate nested localized stalk comparison maps.
private theorem coordinates_comparison_normalize
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c : SingleComplexBaseChange.Coordinates g' K K' φ) (z : X') (i : ℤ) :
    SingleComplexBaseChange.stalkComparison f f' g g' sq c z i =
      SingleComplexBaseChange.comparisonIntoPullback f f' g g' sq z c.P c.counit_isIso i ≫
        (SingleComplexBaseChange.comparisonStalkCohomology X' z i).map
          ((derivedPullback g').map c.e.hom ≫ φ ≫ c.e'.inv) ≫
        (SingleComplexBaseChange.comparisonStalkHomologyIso X' z c.N i).hom := by
  let := SingleComplexBaseChange.leftAlgebra f g' z
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
  let := c.counit_isIso
  let H := SingleComplexBaseChange.comparisonStalkCohomology X' z i
  have ht : (DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace))).map c.t =
      inv ((SingleComplexBaseChange.counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        c.P)) ≫
        ((derivedPullback g').map c.e.hom ≫ φ ≫ c.e'.inv) := by
    apply (cancel_epi ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P))).mp
    simpa only [cast_eq, Category.assoc, IsIso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun k ↦ k ≫ c.e'.inv) c.represents
  have hn := SingleComplexBaseChange.comparisonStalkHomologyIso_naturality X' z c.t i
  rw [ht, H.map_comp] at hn
  have hn' := congrArg (fun k ↦
    (SingleComplexBaseChange.comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).inv
        ≫ k) hn
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hn'
  simpa only [SingleComplexBaseChange.stalkComparison,
    SingleComplexBaseChange.comparisonIntoPullback, cast_eq, Category.assoc] using
    congrArg (fun k ↦
      (SingleComplexBaseChange.cohomologyModel f f' g g' sq z c.P).localizedComparison i ≫
        HomologicalComplex.homologyMap (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z
          c.P).hom i ≫ k)
      hn'.symm


-- Elaborate nested localized stalk comparison maps.
private theorem coordinates_comparison_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c d : SingleComplexBaseChange.Coordinates g' K K' φ) (z : X') (i : ℤ) :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
    let G := ModuleCat.extendScalars.{u, u, u}
      (algebraMap (TensorProduct (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g'
        z) (SingleComplexBaseChange.B f' z)) (SingleComplexBaseChange.C z))
    let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)
    ∃ (a : G.obj ((SingleComplexBaseChange.cohomologyModel f f' g g' sq z c.P).cohomology i) ≅
        G.obj ((SingleComplexBaseChange.cohomologyModel f f' g g' sq z d.P).cohomology i))
      (b : (S.obj c.N).homology i ≅ (S.obj d.N).homology i),
      a.hom ≫ SingleComplexBaseChange.stalkComparison f f' g g' sq d z i =
        SingleComplexBaseChange.stalkComparison f f' g g' sq c z i ≫ b.hom := by
  let := SingleComplexBaseChange.leftAlgebra f g' z
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
  let G := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (TensorProduct (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g'
      z) (SingleComplexBaseChange.B f' z)) (SingleComplexBaseChange.C z))
  let H := SingleComplexBaseChange.comparisonStalkCohomology X' z i
  let a := c.e ≪≫ d.e.symm
  obtain ⟨e, he, _⟩ := SingleComplexBaseChange.exists_comparisonSourceIso f f' g g' sq z c.P d.P a i
  have hn := SingleComplexBaseChange.comparisonIntoPullback_naturality f f' g g' sq z c.P d.P
    c.isKFlat d.isKFlat c.counit_isIso d.counit_isIso a i e he
  let b := (SingleComplexBaseChange.comparisonStalkHomologyIso X' z c.N i).symm ≪≫
    H.mapIso (c.e' ≪≫ d.e'.symm) ≪≫ SingleComplexBaseChange.comparisonStalkHomologyIso X' z d.N i
  refine ⟨G.mapIso e, b, ?_⟩
  rw [coordinates_comparison_normalize f f' g g' sq c z i,
    coordinates_comparison_normalize f f' g g' sq d z i]
  change G.map e.hom ≫ _ = _ ≫ b.hom
  have ha : (derivedPullback g').map a.hom ≫
      ((derivedPullback g').map d.e.hom ≫ φ ≫ d.e'.inv) =
    ((derivedPullback g').map c.e.hom ≫ φ ≫ c.e'.inv) ≫
      (c.e'.hom ≫ d.e'.inv) := by
    have hd := ((derivedPullback g').mapIso d.e).inv_hom_id
    have hc := c.e'.inv_hom_id
    simp only [Functor.mapIso_inv, Functor.mapIso_hom] at hd
    simp only [a, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hd, reassoc_of% hc]
  calc
    _ = (SingleComplexBaseChange.comparisonIntoPullback f f' g g' sq z c.P c.counit_isIso i ≫
        H.map ((derivedPullback g').map a.hom)) ≫
        H.map ((derivedPullback g').map d.e.hom ≫ φ ≫ d.e'.inv) ≫
        (SingleComplexBaseChange.comparisonStalkHomologyIso X' z d.N i).hom := by
      rw [hn]
      simp only [G, H, Category.assoc]
    _ = _ := by
      rw [Category.assoc, ← H.map_comp_assoc, ha, H.map_comp]
      simp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rfl


/-- Tensor comparison for the fixed chain map induced by the coordinates c.

Proof: take the total tensor of the K-flat sheaf complexes P and c.P.
The localization tensor map identifies its derived object with E tensor K via
eP and c.e. The stalk tensor isomorphism identifies its stalk with U tensor Q.
The canonical pullback tensor equation in hτ identifies the pullback of this
representative with the tensor of the two termwise pullbacks, using the shared
counit. Compose with tensoring c.t. The represents equation of c and naturality
of τ show that this chain map represents τ followed by tensoring φ.
The pullback-stalk isomorphisms and tensor associativity identify its stalk map
with the inverse scalar-extension tensorator followed by tensoring t. This
identification is fixed on each tensor summand by the canonical module maps.
Exact stalks and derived cohomology supply the target isomorphism to d.N through
this representation and d.represents. The source isomorphism is induced by the
derived isomorphism from P tensor c.P to d.P; its A-tensor-R-B linearity follows
from the model's cohomologyIso_smul equation. The universal derived scalar-extension
counits make the source isomorphism compatible with comparison_eq; localized_eq
transposes the equality to C-linear maps. Naturality of comparison into pullback
for derived isomorphisms yields the displayed square for arbitrary d.
No horizontal comparison is assumed invertible. The construction uses unbounded
K-flat representatives; zero complexes and zero rings cause no exception.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), the tensor-transitivity computation
of Tag 0BYJ, with equation-bc before Tag 0DJ8 and the canonical tensor equation.
(blueprint: lem-pc-tensor-stalk-fixed-map-square). -/
theorem tensorStalkComparison_fixedMap_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (E K : schemeDerivedQCohCategory X) (K' : schemeDerivedQCohCategory X')
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback g').obj (A ⊗ B) ⟶
        (derivedPullback g').obj A ⊗ (derivedPullback g').obj B)
    (hτ : IsCanonicalPullbackTensorComparison g' τ)
    (c : SingleComplexBaseChange.Coordinates g' K.obj K'.obj φ)
    (d : SingleComplexBaseChange.Coordinates g' (E.obj ⊗ K.obj)
      (((derivedPullback g').obj E.obj) ⊗ K'.obj)
      (τ E.obj K.obj ≫ ((derivedPullback g').obj E.obj ◁ φ)))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ E.obj) (hP : P.IsKFlatTensor) (z : X') :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
    let R := SingleComplexBaseChange.R f g' z
    let A := SingleComplexBaseChange.A g' z
    let B := SingleComplexBaseChange.B f' z
    let C := SingleComplexBaseChange.C z
    let F := (ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))).mapHomologicalComplex (.up ℤ)
    let G := ModuleCat.extendScalars.{u, u, u} (algebraMap (TensorProduct R A B) C)
    let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)
    let U := SingleComplexBaseChange.stalkComplex g' z P
    let Q := SingleComplexBaseChange.stalkComplex g' z c.P
    let t := (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z c.P).hom ≫ S.map c.t
    let mU := ModuleCat.baseDerivedTensorCohomologyModel R A B (U ⊗ Q) C
    ∀ i : ℤ,
      ∃ (aU : G.obj (mU.cohomology i) ≅
          G.obj ((SingleComplexBaseChange.cohomologyModel f f' g g' sq z d.P).cohomology i))
        (bU : (F.obj U ⊗ S.obj c.N).homology i ≅ (S.obj d.N).homology i),
        aU.hom ≫ SingleComplexBaseChange.stalkComparison f f' g g' sq d z i =
          mU.localizedComparison i ≫ HomologicalComplex.homologyMap
            ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i ≫ bU.hom := by
  let := SingleComplexBaseChange.leftAlgebra f g' z
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
  let F := (ModuleCat.extendScalars.{u, u, u}
    ((algebraMap (TensorProduct (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g'
      z) (SingleComplexBaseChange.B f' z)) (SingleComplexBaseChange.C z)).comp
      (algebraMap (SingleComplexBaseChange.A g' z)
        (TensorProduct (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g' z)
          (SingleComplexBaseChange.B f' z))))).mapHomologicalComplex (.up ℤ)
  let G := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (TensorProduct (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g'
      z) (SingleComplexBaseChange.B f' z)) (SingleComplexBaseChange.C z))
  let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
    (.up ℤ)
  let U := SingleComplexBaseChange.stalkComplex g' z P
  let Q := SingleComplexBaseChange.stalkComplex g' z c.P
  let t := (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z c.P).hom ≫ S.map c.t
  let mU := ModuleCat.baseDerivedTensorCohomologyModel
    (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g' z)
      (SingleComplexBaseChange.B f' z) (U ⊗ Q) (SingleComplexBaseChange.C z)
  obtain ⟨e, σ, ρ, _, _, hchain⟩ :=
    exists_tensorStalk_chain_coordinates f f' g g' sq E K K' φ τ hτ c P eP hP z
  dsimp only
  intro i
  obtain ⟨a, b, hab⟩ := coordinates_comparison_transport f f' g g' sq e d z i
  obtain ⟨s, hs⟩ := ModuleCat.exists_baseDerivedTensorModel_quasiIso_comparison
    (SingleComplexBaseChange.R f g' z) (SingleComplexBaseChange.A g' z)
      (SingleComplexBaseChange.B f' z) (SingleComplexBaseChange.C z) σ.hom (by infer_instance)
    mU (SingleComplexBaseChange.cohomologyModel f f' g g' sq z e.P) i
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} (SingleComplexBaseChange.C z)) (.up
    ℤ) i
  refine ⟨G.mapIso s ≪≫ a, H.mapIso ρ ≪≫ b, ?_⟩
  have hhom := congrArg (fun k ↦ HomologicalComplex.homologyMap k i) hchain
  simp only [HomologicalComplex.homologyMap_comp] at hhom
  have hcoords : (G.mapIso s).hom ≫ SingleComplexBaseChange.stalkComparison f f' g g' sq e z i =
      mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i ≫
          HomologicalComplex.homologyMap ρ.hom i := by
    rw [SingleComplexBaseChange.stalkComparison]
    have h := congrArg (fun k ↦ k ≫
      HomologicalComplex.homologyMap (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z
        e.P).hom i ≫
      HomologicalComplex.homologyMap (S.map e.t) i) hs.symm
    have h' := congrArg (fun k ↦ mU.localizedComparison i ≫ k) hhom
    simp only [Category.assoc] at h h'
    simpa only [Functor.mapIso_hom, Category.assoc, F, G, S, U, Q, t,
      HomologicalComplex.homologyMap_comp] using h.trans h'
  simp only [Iso.trans_hom, Category.assoc]
  rw [hab, ← Category.assoc, hcoords]
  rfl


end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension

/-! # Transport of the source of the stalk comparison

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-source-transport).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem restriction_scalar_naturality
    {R₀ A₀ : Type u} [CommRing R₀] [CommRing A₀] [Algebra R₀ A₀]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A₀)]
    (U V : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (t : DerivedCategory.Q.obj U ⟶ DerivedCategory.Q.obj V) (r : A₀) :
    let F := ModuleCat.restrictScalars.{u} (algebraMap R₀ A₀)
    let j := fun W : CochainComplex (ModuleCat.{u} A₀) ℤ ↦
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R₀)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj W) ≪≫
      F.mapDerivedCategoryFactors.symm.app W
    let m := (j U).hom ≫ F.mapDerivedCategory.map t ≫ (j V).inv
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((F.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 U))) ≫ m =
      m ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((F.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 V))) := by
  dsimp only
  let F := ModuleCat.restrictScalars.{u} (algebraMap R₀ A₀)
  let j := fun W : CochainComplex (ModuleCat.{u} A₀) ℤ ↦
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R₀)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj W) ≪≫
    F.mapDerivedCategoryFactors.symm.app W
  have hj (W : CochainComplex (ModuleCat.{u} A₀) ℤ) :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((F.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 W))) ≫ (j W).hom =
        (j W).hom ≫ F.mapDerivedCategory.map (r • 𝟙 (DerivedCategory.Q.obj W)) := by
    dsimp [j]
    rw [← Category.assoc, DerivedCategory.quotientCompQhIso_hom_naturality,
      Category.assoc]
    have h := F.mapDerivedCategoryFactors.inv.naturality (r • 𝟙 W)
    simp only [Functor.comp_map] at h
    rw [(DerivedCategory.Q (C := ModuleCat.{u} A₀)).map_smul,
      (DerivedCategory.Q (C := ModuleCat.{u} A₀)).map_id] at h
    simpa only [Category.assoc] using congrArg
      (fun k ↦ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R₀)).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj W) ≫ k) h
  have hj' :
      F.mapDerivedCategory.map (r • 𝟙 (DerivedCategory.Q.obj V)) ≫ (j V).inv =
        (j V).inv ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((F.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 V))) := by
    apply (cancel_epi (j V).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.id_comp,
      Category.comp_id] using congrArg (fun h ↦ h ≫ (j V).inv) (hj V).symm
  change _ ≫ ((j U).hom ≫ F.mapDerivedCategory.map t ≫ (j V).inv) =
    ((j U).hom ≫ F.mapDerivedCategory.map t ≫ (j V).inv) ≫ _
  have ht : (r • 𝟙 (DerivedCategory.Q.obj U)) ≫ t =
      t ≫ (r • 𝟙 (DerivedCategory.Q.obj V)) := by simp
  simp only [Category.assoc]
  rw [reassoc_of% hj U, ← Functor.map_comp_assoc, ht,
    Functor.map_comp_assoc, hj']


private theorem lift_tensor_iso
    {R₀ A₀ B₀ : Type u} [CommRing R₀] [CommRing A₀] [CommRing B₀]
    [Algebra R₀ A₀] [Algebra R₀ B₀]
    (U V : ModuleCat.{u} (A₀ ⊗[R₀] B₀))
    (e : (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeRight (R := R₀) (A := A₀) (B := B₀)).toRingHom).obj U ≅
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeRight (R := R₀) (A := A₀) (B := B₀)).toRingHom).obj V)
    (h : ∀ (r : A₀) (x : U),
      e.hom ((Algebra.TensorProduct.includeLeft (S := R₀) r : A₀ ⊗[R₀] B₀) • x) =
        (Algebra.TensorProduct.includeLeft (S := R₀) r : A₀ ⊗[R₀] B₀) • e.hom x) :
    ∃! d : U ≅ V,
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeRight (R := R₀) (A := A₀) (B := B₀)).toRingHom).map
          d.hom = e.hom := by
  let F := ModuleCat.restrictScalars.{u}
    (Algebra.TensorProduct.includeRight (R := R₀) (A := A₀) (B := B₀)).toRingHom
  have hs (r : A₀ ⊗[R₀] B₀) (x : U) : e.hom (r • x) = r • e.hom x := by
    induction r using TensorProduct.inductionOn with
    | tmul a b =>
      have hr : a ⊗ₜ[R₀] b =
          Algebra.TensorProduct.includeRight b * Algebra.TensorProduct.includeLeft (S := R₀) a := by
        simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]
      rw [hr, mul_smul, mul_smul]
      change e.hom (b • (Algebra.TensorProduct.includeLeft (S := R₀) a • x)) =
        b • (Algebra.TensorProduct.includeLeft (S := R₀) a • e.hom x)
      rw [map_smul, h]
    | add r s hr hs =>
      rw [add_smul, add_smul]
      change e.hom.hom (r • x + s • x) = _
      rw [e.hom.hom.map_add, hr, hs]
  let l : U ≃ₗ[A₀ ⊗[R₀] B₀] V :=
    { e.toLinearEquiv.toAddEquiv with map_smul' := hs }
  let d : U ≅ V :=
    { hom := ModuleCat.ofHom l.toLinearMap
      inv := ModuleCat.ofHom l.symm.toLinearMap
      hom_inv_id := by ext x; exact l.symm_apply_apply x
      inv_hom_id := by ext x; exact l.apply_symm_apply x }
  have hd : F.map d.hom = e.hom := by ext x; rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  exact F.map_injective (hd'.trans hd.symm)

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Additivity of the module stalk functor, by additivity of abelian-group stalks.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
instance comparisonStalkAdditive (Y : Scheme.{u}) (y : Y) :
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive where
  map_add := by
    intro M N a b
    ext m
    change (TopCat.Presheaf.stalkFunctor Ab y).map
      ((PresheafOfModules.toPresheaf _).map (a + b).val) m = _
    change (TopCat.Presheaf.stalkFunctor Ab y).map
      ((PresheafOfModules.toPresheaf _).map (a.val + b.val)) m = _
    rw [Functor.map_add, Functor.map_add]
    rfl

/-- Exactness of the module stalk functor, from the shared stalk exactness theorem.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
instance comparisonStalkHomology (Y : Scheme.{u}) (y : Y) :
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro T hT
  exact ((RingedSpace.module_stalk_exact Y.toRingedSpace T.f).2.2.2.2
    T.X₃ T.f T.g T.zero).mp hT y

/-- (blueprint: lem-pc-stalk-comparison-source-transport) -/
instance comparisonStalkLimits (Y : Scheme.{u}) (y : Y) :
    PreservesFiniteLimits (RingedSpace.moduleStalkFunctor Y.toRingedSpace y) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- (blueprint: lem-pc-stalk-comparison-source-transport) -/
instance comparisonStalkColimits (Y : Scheme.{u}) (y : Y) :
    PreservesFiniteColimits (RingedSpace.moduleStalkFunctor Y.toRingedSpace y) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The exact stalk functor on derived categories, with the standard module localization.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
def comparisonDerivedStalk (Y : Scheme.{u}) (y : Y) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapDerivedCategory

/-- Derived stalk cohomology, as a functor on the sheaf derived category.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
def comparisonStalkCohomology (Y : Scheme.{u}) (y : Y) (i : ℤ) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  comparisonDerivedStalk Y y ⋙ DerivedCategory.homologyFunctor _ i

/-- Identification of the derived stalk cohomology with the homology of the stalk complex.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
def comparisonStalkHomologyIso (Y : Scheme.{u}) (y : Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (i : ℤ) :
    (comparisonStalkCohomology Y y i).obj (DerivedCategory.Q.obj P) ≅
      (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
        (.up ℤ)).obj P).homology i :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  (DerivedCategory.homologyFunctor _ i).mapIso
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapDerivedCategoryFactors.app P) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _

/-- Naturality of the identification of derived stalk cohomology.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
@[reassoc]
theorem comparisonStalkHomologyIso_naturality (Y : Scheme.{u}) (y : Y)
    {P Q : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (a : P ⟶ Q) (i : ℤ) :
    (comparisonStalkCohomology Y y i).map (DerivedCategory.Q.map a) ≫
        (comparisonStalkHomologyIso Y y Q i).hom =
      (comparisonStalkHomologyIso Y y P i).hom ≫
        HomologicalComplex.homologyMap
          (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
            (.up ℤ)).map a) i := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  simp only [comparisonStalkCohomology, comparisonDerivedStalk,
    comparisonStalkHomologyIso, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp,
    Functor.mapDerivedCategoryFactors_hom_naturality, Functor.map_comp, Category.assoc,
    DerivedCategory.homologyFunctorFactors_hom_naturality, Category.assoc]

variable {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Exact derived restriction of stalk modules to the base stalk ring.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
def comparisonBaseRestriction (z : X') :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := leftAlgebra f g' z
  (ModuleCat.restrictScalars.{u} (algebraMap (R f g' z) (A g' z))).mapDerivedCategory

/-- The model's input identifies with the derived restriction of the derived stalk.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
def comparisonModelInputIso (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := leftAlgebra f g' z
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((ModuleCat.restrictScalars.{u} (algebraMap (R f g' z) (A g' z))).mapHomologicalComplex
        (.up ℤ)).obj (stalkComplex g' z P))) ≅
      (comparisonBaseRestriction f g' z).obj
        ((comparisonDerivedStalk X (g' z)).obj (DerivedCategory.Q.obj P)) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := leftAlgebra f g' z
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (R f g' z))).app
      (((ModuleCat.restrictScalars.{u} (algebraMap (R f g' z) (A g' z))).mapHomologicalComplex
        (.up ℤ)).obj (stalkComplex g' z P)) ≪≫
    ((ModuleCat.restrictScalars.{u} (algebraMap (R f g' z) (A g' z))).mapDerivedCategoryFactors
      |>.symm.app (stalkComplex g' z P)) ≪≫
    (comparisonBaseRestriction f g' z).mapIso
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).mapDerivedCategoryFactors
        |>.symm.app P)

/-- The counit-compatible isomorphism between the two derived tensor functors.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
def comparisonModelDerivedIso (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    (cohomologyModel f f' g g' sq z P).derived ≅
      (cohomologyModel f f' g g' sq z Q).derived := by
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  let M := cohomologyModel f f' g g' sq z P
  let N := cohomologyModel f f' g g' sq z Q
  have := M.universal
  have := N.universal
  exact Functor.leftDerivedNatIso M.derived N.derived M.counit N.counit
    (HomotopyCategory.quasiIso _ (.up ℤ)) (Iso.refl _)

/-- The canonical B-linear cohomology transport before lifting to the tensor algebra.
(blueprint: lem-pc-stalk-comparison-source-transport)
-/
def comparisonSourceUnderlyingIso (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj
      ((cohomologyModel f f' g g' sq z P).cohomology i) ≅
    (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj
      ((cohomologyModel f f' g g' sq z Q).cohomology i) := by
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  let M := cohomologyModel f f' g g' sq z P
  let N := cohomologyModel f f' g g' sq z Q
  let b := comparisonModelInputIso f g' z P ≪≫
    (comparisonBaseRestriction f g' z).mapIso
      ((comparisonDerivedStalk X (g' z)).mapIso a) ≪≫
    (comparisonModelInputIso f g' z Q).symm
  exact M.cohomologyIso i ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      (M.derived.mapIso b ≪≫ (comparisonModelDerivedIso f f' g g' sq z P Q).app _) ≪≫
    (N.cohomologyIso i).symm

/-- The canonical underlying cohomology transport lifts uniquely to a tensor-algebra
linear isomorphism. No K-flatness or morphism to a target complex is needed.

Proof: apply exact stalks and exact restriction to the derived isomorphism a. The
unique counit-compatible identification of total left derived scalar extensions
then gives comparisonSourceUnderlyingIso. For every element of A, naturality of a
commutes with multiplication; this holds for derived morphisms because multiplication
is a natural transformation on complexes, hence descends through localization.
The equations cohomologyIso_smul identify these multiplication actions with the
A-actions on the model cohomologies. Thus the underlying B-linear isomorphism and
its inverse commute with A. Tensor-product induction gives A-tensor-R-B linearity.
Bundle the two linear maps as inverse module morphisms. Restriction of scalars is
faithful, so the specified underlying homomorphism determines the isomorphism uniquely.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8; More on Algebra,
derived change of rings (Tag 06Y6).
(blueprint: lem-pc-stalk-comparison-source-transport). -/
theorem exists_comparisonSourceIso (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    ∃! e : (cohomologyModel f f' g g' sq z P).cohomology i ≅
        (cohomologyModel f f' g g' sq z Q).cohomology i,
      (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map e.hom =
        (comparisonSourceUnderlyingIso f f' g g' sq z P Q a i).hom := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  let M := cohomologyModel f f' g g' sq z P
  let N := cohomologyModel f f' g g' sq z Q
  let F := ModuleCat.restrictScalars.{u} (algebraMap (R f g' z) (A g' z))
  let L := RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)
  let b := comparisonModelInputIso f g' z P ≪≫
    (comparisonBaseRestriction f g' z).mapIso
      ((comparisonDerivedStalk X (g' z)).mapIso a) ≪≫
    (comparisonModelInputIso f g' z Q).symm
  let d := comparisonModelDerivedIso f f' g g' sq z P Q
  let c := M.derived.mapIso b ≪≫ d.app _
  let e := comparisonSourceUnderlyingIso f f' g g' sq z P Q a i
  apply lift_tensor_iso (M.cohomology i) (N.cohomology i) e
  intro r x
  let μ := fun W : CochainComplex (ModuleCat.{u} (A g' z)) ℤ ↦
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      ((F.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 W)))
  have hb : μ (stalkComplex g' z P) ≫ b.hom =
      b.hom ≫ μ (stalkComplex g' z Q) := by
    have h := restriction_scalar_naturality (R₀ := R f g' z)
      (A₀ := A g' z) (stalkComplex g' z P)
      (stalkComplex g' z Q)
      (L.mapDerivedCategoryFactors.inv.app P ≫ L.mapDerivedCategory.map a.hom ≫
        L.mapDerivedCategoryFactors.hom.app Q) r
    simpa only [b, μ, comparisonModelInputIso, comparisonBaseRestriction,
      comparisonDerivedStalk, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc] using h
  have hc : M.derived.map (μ (stalkComplex g' z P)) ≫ c.hom =
      c.hom ≫ N.derived.map (μ (stalkComplex g' z Q)) := by
    dsimp only [c, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [← M.derived.map_comp_assoc, hb, M.derived.map_comp_assoc,
      d.hom.naturality]
    simp only [Category.assoc]
    rfl
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (B f' z)) i
  let G := ModuleCat.restrictScalars.{u}
    (Algebra.TensorProduct.includeRight (R := R f g' z)
      (A := A g' z) (B := B f' z)).toRingHom
  have hN : H.map (N.derived.map (μ (stalkComplex g' z Q))) ≫
      (N.cohomologyIso i).inv =
    (N.cohomologyIso i).inv ≫ G.map
      ((Algebra.TensorProduct.includeLeft (S := R f g' z) r :
        A g' z ⊗[R f g' z] B f' z) • 𝟙 (N.cohomology i)) := by
    apply (cancel_epi (N.cohomologyIso i).hom).mp
    have h := congrArg (fun k ↦ k ≫ (N.cohomologyIso i).inv)
      (N.cohomologyIso_smul i r).symm
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  have he : G.map
      ((Algebra.TensorProduct.includeLeft (S := R f g' z) r :
        A g' z ⊗[R f g' z] B f' z) • 𝟙 (M.cohomology i)) ≫
        e.hom =
      e.hom ≫ G.map
        ((Algebra.TensorProduct.includeLeft (S := R f g' z) r :
        A g' z ⊗[R f g' z] B f' z) • 𝟙 (N.cohomology i)) := by
    change _ ≫ ((M.cohomologyIso i).hom ≫ H.map c.hom ≫ (N.cohomologyIso i).inv) =
      ((M.cohomologyIso i).hom ≫ H.map c.hom ≫ (N.cohomologyIso i).inv) ≫ _
    simp only [Category.assoc]
    rw [reassoc_of% M.cohomologyIso_smul i r, ← H.map_comp_assoc, hc,
      H.map_comp_assoc, hN]
  exact congrArg (fun k ↦ k x) he

end AlgebraicGeometry.SingleComplexBaseChange

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization

/-! # Symmetry of the canonical degree-zero tensor comparison -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X : AlgebraicGeometry.Scheme.{u}}

section Cochain

variable {C : Type uB} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C]

private lemma singleCochainTensorIso_inv_f (L M : C) :
    (singleCochainTensorIso L M).inv.f 0 =
      HomologicalComplex.ιTensorObj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M) 0 0 0 rfl := by
  simp [singleCochainTensorIso, CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.single, whiskerLeft_id]

private lemma singleCochainTensorIso_symmetry
    (L M : C) :
    (β_ ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M)).hom ≫
      (singleCochainTensorIso M L).hom =
    (singleCochainTensorIso L M).hom ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map (β_ L M).hom := by
  apply (cancel_epi (singleCochainTensorIso L M).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (cancel_mono (singleCochainTensorIso M L).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, singleCochainTensorIso_inv_f]
  change HomologicalComplex.ιTensorObj _ _ 0 0 0 rfl ≫
      (CochainComplex.Monoidal.braiding
        ((HomologicalComplex.single C (.up ℤ) 0).obj L)
        ((HomologicalComplex.single C (.up ℤ) 0).obj M)).hom.f 0 = _
  simpa [HomologicalComplex.single] using
    (CochainComplex.Monoidal.ι_braiding_hom
      (K := (HomologicalComplex.single C (.up ℤ) 0).obj L)
      (L := (HomologicalComplex.single C (.up ℤ) 0).obj M) 0 0 0 rfl)

private lemma canonicalTensorSymmetry_hom_app
    [Abelian.HasFunctorialFlatResolution C] (K M : DerivedCategory C) :
    ((DerivedCategory.canonicalTensorSymmetry C).hom.app K).app M =
      (letI := DerivedCategory.braidedCategory' C; (β_ K M).hom) := by
  rfl

end Cochain

private lemma localization_braided
    {C : Type uB} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (K M : CochainComplex C ℤ) :
    let := DerivedCategory.braidedCategory' C
    let F := HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh
    (β_ (F.obj K) (F.obj M)).hom ≫ Functor.LaxMonoidal.μ F M K =
      Functor.LaxMonoidal.μ F K M ≫ F.map (β_ K M).hom := by
  let := DerivedCategory.braidedCategory' C
  let H := HomotopyCategory.quotient C (.up ℤ)
  let : H.LaxBraided :=
    { braided K M := by
        change (𝟙 _) ≫ H.map (β_ K M).hom = H.map (β_ K M).hom ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id] }
  let : (DerivedCategory.Qh (C := C)).LaxBraided :=
    { braided := fun K M ↦ (DerivedMonoidal.braiding_hom_μ _ _ K M).symm }
  exact (Functor.LaxBraided.braided (F := H ⋙ DerivedCategory.Qh) K M).symm

@[irreducible]
private noncomputable def singleIsoQh :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology B) 0 ≅
      HomologicalComplex.single _ (.up ℤ) 0 ⋙ HomotopyCategory.quotient _ (.up ℤ) ⋙
        DerivedCategory.Qh :=
  DerivedCategory.singleFunctorIsoCompQ _ 0 ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm

omit [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B] in
private lemma singleIsoQh_hom_app (A : Sheaf X.smallEtaleTopology B) :
    (singleIsoQh (B := B) (X := X)).hom.app A = (singleFunctorObjIsoQh A).hom := by
  unfold singleIsoQh singleFunctorObjIsoQh
  rfl

omit [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B] in
private lemma singleIsoQh_inv_app (A : Sheaf X.smallEtaleTopology B) :
    (singleIsoQh (B := B) (X := X)).inv.app A = (singleFunctorObjIsoQh A).inv := by
  unfold singleIsoQh singleFunctorObjIsoQh
  rfl

private lemma singleTensorator_factorization
    (A C : Sheaf X.smallEtaleTopology B) (hA : ObjectProperty.flat A) :
    let H := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology B) (.up ℤ)
    let sg := HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0
    let F := H ⋙ DerivedCategory.Qh
    let e := singleIsoQh (B := B) (X := X)
    (singleFunctorObjTensorIso A C hA).hom =
      (e.hom.app A ⊗ₘ e.hom.app C) ≫
        Functor.LaxMonoidal.μ F (sg.obj A) (sg.obj C) ≫
        F.map (singleCochainTensorIso A C).hom ≫ e.inv.app (A ⊗ C) := by
  dsimp only
  rw [singleIsoQh_hom_app, singleIsoQh_hom_app, singleIsoQh_inv_app]
  exact singleFunctorObjTensorIso_factorization A C hA

/-- The canonical flat single tensorators preserve the signed braiding in degree zero.
Source: Stacks, Cohomology on Sites, Tags 06YQ and 06YU, signed tensor symmetry.
(auxiliary; not a blueprint node).
Proof: the tensor product of two single complexes has only its (0,0) summand.
Precomposition with that summand reduces the signed cochain braiding to the ordinary
braiding, since (-1)^(0*0)=1. All other summands have a zero factor. Apply the braided
homotopy quotient. The defining identity braiding_hom_μ for the canonical derived
braiding then moves the Qh tensorator through that braiding. Naturality of braiding
moves the two single/quotient isomorphisms through it, and their inverses cancel at
the target. The remaining composite is exactly the displayed equality. Both factors
are flat only to identify the comparison maps with the stated isomorphisms; the
computation also applies to zero objects and empty schemes. -/
theorem singleFunctorObjTensorIso_symmetry
    (L M : Sheaf X.smallEtaleTopology B)
    (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M) :
    (((derivedTensorSymmetry B X).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj L)).app
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
      (singleFunctorObjTensorIso M L hM).hom =
    (singleFunctorObjTensorIso L M hL).hom ≫
      (DerivedCategory.singleFunctor _ 0).map (β_ L M).hom := by
  let := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology B)
  let H := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology B) (.up ℤ)
  let sg := HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0
  let F := H ⋙ DerivedCategory.Qh
  let e := singleIsoQh (B := B) (X := X)
  have fac (A C : Sheaf X.smallEtaleTopology B) (hA : ObjectProperty.flat A) :
      (singleFunctorObjTensorIso A C hA).hom =
        (e.hom.app A ⊗ₘ e.hom.app C) ≫
          Functor.LaxMonoidal.μ F (sg.obj A) (sg.obj C) ≫
          F.map (singleCochainTensorIso A C).hom ≫ e.inv.app (A ⊗ C) :=
    singleTensorator_factorization A C hA
  rw [derivedTensorSymmetry, canonicalTensorSymmetry_hom_app]
  rw [fac L M hL, fac M L hM]
  simp only [Category.assoc]
  have hb : (β_ (F.obj (sg.obj L)) (F.obj (sg.obj M))).hom ≫
      Functor.LaxMonoidal.μ F (sg.obj M) (sg.obj L) =
      Functor.LaxMonoidal.μ F (sg.obj L) (sg.obj M) ≫
        F.map (β_ (sg.obj L) (sg.obj M)).hom :=
    localization_braided (sg.obj L) (sg.obj M)
  rw [← BraidedCategory.braiding_naturality_assoc]
  erw [reassoc_of% hb]
  rw [← F.map_comp_assoc, singleCochainTensorIso_symmetry, F.map_comp, Category.assoc]
  exact congrArg ((e.hom.app L ⊗ₘ e.hom.app M) ≫
    Functor.LaxMonoidal.μ F (sg.obj L) (sg.obj M) ≫
      F.map (singleCochainTensorIso L M).hom ≫ ·) (e.inv.naturality (β_ L M).hom)

end AlgebraicGeometry.Etale

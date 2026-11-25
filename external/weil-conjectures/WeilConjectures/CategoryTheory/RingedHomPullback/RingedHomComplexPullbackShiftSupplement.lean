/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.Algebra.Homology.RingedHomComplexPullbackShift

set_option linter.privateModule false

/-! # Pullback of Hom complexes and signed source shifts

Source: Stacks Project, sites-modules.tex, Tag 0GMX (remark-pullback-internal-hom),
with sites-cohomology.tex, Tags 0A8X and 08JC; the signed calculation is the
agent formulation in the DAG (blueprint: lem-sf-ringed-hom-complex-pullback-shift).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v d t r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CochainPullback

namespace CategoryTheory.RingedHomPullback

section AbstractTransport

variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  [MonoidalCategory A] [MonoidalCategory B]
  (F : A ⥤ B) [F.Additive]
  (μ : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
  (μnat : ∀ {X X' Y Y'} (a : X ⟶ X') (b : Y ⟶ Y'),
    (F.map a ⊗ₘ F.map b) ≫ (μ X' Y').inv = (μ X Y).inv ≫ F.map (a ⊗ₘ b))
  {HA : A → A → A} {HB : B → B → B}
  (UA : ∀ {X Y T}, (T ⟶ HA X Y) → (T ⊗ X ⟶ Y))
  (UB : ∀ {X Y T}, (T ⟶ HB X Y) → (T ⊗ X ⟶ Y))
  (CB : ∀ {X Y T}, (T ⊗ X ⟶ Y) → (T ⟶ HB X Y))
  (hUC : ∀ {X Y T} (g : T ⊗ X ⟶ Y), UB (CB g) = g)
  (hUI : ∀ X Y T, Function.Injective (@UB X Y T))

omit [Preadditive A] [Preadditive B] [F.Additive] in
include hUC hUI μnat in
private lemma transport_pre_abstract
    (hUA : ∀ {X Y T T'} (t : T' ⟶ T) (g : T ⟶ HA X Y),
      UA (t ≫ g) = (t ⊗ₘ 𝟙 X) ≫ UA g)
    (hUB : ∀ {X Y T T'} (t : T' ⟶ T) (g : T ⟶ HB X Y),
      UB (t ≫ g) = (t ⊗ₘ 𝟙 X) ≫ UB g)
    {X Y T T'} (a : T' ⟶ T) (g : T ⟶ HA X Y) :
    CB ((μ T' X).inv ≫ F.map (UA (a ≫ g))) =
      F.map a ≫ CB ((μ T X).inv ≫ F.map (UA g)) := by
  apply hUI
  rw [hUC, hUB, hUC, hUA, F.map_comp]
  rw [← Category.assoc, ← μnat a (𝟙 X), F.map_id, Category.assoc]

omit [Preadditive A] [Preadditive B] [F.Additive] in
include hUC hUI μnat in
private lemma transport_map_abstract
    (MA : ∀ {X X' Y Y'}, (X' ⟶ X) → (Y ⟶ Y') → (HA X Y ⟶ HA X' Y'))
    (MB : ∀ {X X' Y Y'}, (X' ⟶ X) → (Y ⟶ Y') → (HB X Y ⟶ HB X' Y'))
    (hUA : ∀ {X X' Y Y' T} (a : X' ⟶ X) (b : Y ⟶ Y') (g : T ⟶ HA X Y),
      UA (g ≫ MA a b) = (𝟙 T ⊗ₘ a) ≫ UA g ≫ b)
    (hUB : ∀ {X X' Y Y' T} (a : X' ⟶ X) (b : Y ⟶ Y') (g : T ⟶ HB X Y),
      UB (g ≫ MB a b) = (𝟙 T ⊗ₘ a) ≫ UB g ≫ b)
    {X X' Y Y' T} (a : X' ⟶ X) (b : Y ⟶ Y') (g : T ⟶ HA X Y) :
    CB ((μ T X').inv ≫ F.map (UA (g ≫ MA a b))) =
      CB ((μ T X).inv ≫ F.map (UA g)) ≫ MB (F.map a) (F.map b) := by
  apply hUI
  rw [hUC, hUB, hUC, hUA, F.map_comp, F.map_comp]
  rw [← Category.assoc, ← μnat (𝟙 T) a, F.map_id]
  simp only [Category.assoc]

include hUC hUI in
private lemma transport_sub_abstract
    (hUA : ∀ {X Y T} (g h : T ⟶ HA X Y), UA (g - h) = UA g - UA h)
    (hUB : ∀ {X Y T} (g h : T ⟶ HB X Y), UB (g - h) = UB g - UB h)
    {X Y T} (g h : T ⟶ HA X Y) :
    CB ((μ T X).inv ≫ F.map (UA (g - h))) =
      CB ((μ T X).inv ≫ F.map (UA g)) - CB ((μ T X).inv ≫ F.map (UA h)) := by
  apply hUI
  rw [hUC, hUB, hUC, hUC, hUA, F.map_sub, Preadditive.comp_sub]

include hUC hUI in
private lemma transport_smul_abstract
    (hUA : ∀ {X Y T} (a : ℤˣ) (g : T ⟶ HA X Y), UA (a • g) = a • UA g)
    (hUB : ∀ {X Y T} (a : ℤˣ) (g : T ⟶ HB X Y), UB (a • g) = a • UB g)
    {X Y T} (a : ℤˣ) (g : T ⟶ HA X Y) :
    CB ((μ T X).inv ≫ F.map (UA (a • g))) = a • CB ((μ T X).inv ≫ F.map (UA g)) := by
  apply hUI
  rw [hUC, hUB, hUC, hUA, F.map_units_smul, Linear.comp_units_smul]

end AbstractTransport

section AbstractHomComplex

set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [Category A] [Preadditive A]

-- The product-Hom identities used by the comparison construction.
private structure HomData (A : Type*) [Category A] [Preadditive A] where
  obj : A → A → A
  map : ∀ {X X' Y Y'}, (X' ⟶ X) → (Y ⟶ Y') → (obj X Y ⟶ obj X' Y')
  map_id : ∀ X Y, map (𝟙 X) (𝟙 Y) = 𝟙 (obj X Y)
  H : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ
  π : ∀ (E I : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
    (((H.obj (op E)).obj I).X n ⟶ obj (E.X p) (I.X q))
  limit : ∀ E I n, IsLimit (Fan.mk (((H.obj (op E)).obj I).X n)
    (fun p : ℤ ↦ π E I n p (p + n) rfl))
  differential : ∀ E I n m p q q' p' (_hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q),
    ((H.obj (op E)).obj I).d n m ≫ π E I m p q hpq =
      π E I n p q' hq' ≫ map (𝟙 (E.X p)) (I.d q' q) -
        n.negOnePow • (π E I n p' q hp' ≫ map (E.d p p') (𝟙 (I.X q)))
  naturality : ∀ {E E' I I'} (u : E' ⟶ E) (z : I ⟶ I') n p q (h : p + n = q),
    (((H.map u.op).app I) ≫ (H.obj (op E')).map z).f n ≫ π E' I' n p q h =
      π E I n p q h ≫ map (u.f p) (z.f q)
  shift : ∀ (E I : CochainComplex A ℤ) (m : ℤ),
    (H.obj (op (E⟦m⟧))).obj I ≅ ((H.obj (op E)).obj I)⟦-m⟧
  shift_spec : ∀ E I m n p q (h : p + (n + -m) = q),
    (shift E I m).hom.f n ≫ π E I (n + -m) p q h =
      (m * n).negOnePow • (π (E⟦m⟧) I n (p - m) q (by omega) ≫
        map (E.shiftFunctorObjXIso m (p - m) p (by omega)).inv (𝟙 (I.X q)))

private abbrev homObject (h : HomData A) (E I : CochainComplex A ℤ) :
    CochainComplex A ℤ :=
  (h.H.obj (op E)).obj I

private lemma homData_ext (h : HomData A) {E I : CochainComplex A ℤ} {n : ℤ}
    {T : A} {f g : T ⟶ (homObject h E I).X n}
    (he : ∀ p q (hpq : p + n = q), f ≫ h.π E I n p q hpq = g ≫ h.π E I n p q hpq) :
    f = g :=
  (h.limit E I n).hom_ext (fun ⟨p⟩ ↦ he p (p + n) rfl)

private lemma homData_pre_π (h : HomData A) {E E' I : CochainComplex A ℤ}
    (u : E' ⟶ E) (n p q : ℤ) (hpq : p + n = q) :
    ((h.H.map u.op).app I).f n ≫ h.π E' I n p q hpq =
      h.π E I n p q hpq ≫ h.map (u.f p) (𝟙 (I.X q)) := by
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.comp_f,
    HomologicalComplex.id_f] using h.naturality u (𝟙 I) n p q hpq

variable {B : Type*} [Category B] [Preadditive B]

private structure TransportData (a : HomData A) (b : HomData B) (F : A ⥤ B)
    [F.Additive] where
  map : ∀ {X Y T}, (T ⟶ a.obj X Y) → (F.obj T ⟶ b.obj (F.obj X) (F.obj Y))
  pre : ∀ {X Y T T'} (t : T' ⟶ T) (g : T ⟶ a.obj X Y),
    map (t ≫ g) = F.map t ≫ map g
  naturality : ∀ {X X' Y Y' T} (u : X' ⟶ X) (z : Y ⟶ Y') (g : T ⟶ a.obj X Y),
    map (g ≫ a.map u z) = map g ≫ b.map (F.map u) (F.map z)
  sub : ∀ {X Y T} (g h : T ⟶ a.obj X Y), map (g - h) = map g - map h
  smul : ∀ {X Y T} (k : ℤˣ) (g : T ⟶ a.obj X Y), map (k • g) = k • map g

private abbrev mapped (F : A ⥤ B) [F.Additive] :
    CochainComplex A ℤ ⥤ CochainComplex B ℤ :=
  F.mapHomologicalComplex (ComplexShape.up ℤ)

@[no_expose] private def abstractComponent
    (a : HomData A) (b : HomData B) (F : A ⥤ B) [F.Additive]
    (tr : TransportData a b F) (E I : CochainComplex A ℤ) (n : ℤ) :
    F.obj ((homObject a E I).X n) ⟶
      (homObject b ((mapped F).obj E) ((mapped F).obj I)).X n :=
  Fan.IsLimit.lift (b.limit ((mapped F).obj E) ((mapped F).obj I) n)
    (fun p ↦ tr.map (a.π E I n p (p + n) rfl))

attribute [local irreducible] abstractComponent

private lemma abstractComponent_π
    (a : HomData A) (b : HomData B) (F : A ⥤ B) [F.Additive]
    (tr : TransportData a b F) (E I : CochainComplex A ℤ) (n p q : ℤ)
    (hpq : p + n = q) :
    abstractComponent a b F tr E I n ≫
        b.π ((mapped F).obj E) ((mapped F).obj I) n p q hpq =
      tr.map (a.π E I n p q hpq) := by
  subst q
  unfold abstractComponent
  exact Fan.IsLimit.fac (b.limit ((mapped F).obj E) ((mapped F).obj I) n) _ p

private lemma abstractComponent_comm
    (a : HomData A) (b : HomData B) (F : A ⥤ B) [F.Additive]
    (tr : TransportData a b F) (E I : CochainComplex A ℤ) (n m : ℤ)
    (hnm : n + 1 = m) :
    abstractComponent a b F tr E I n ≫
        (homObject b ((mapped F).obj E) ((mapped F).obj I)).d n m =
      F.map ((homObject a E I).d n m) ≫ abstractComponent a b F tr E I m := by
  apply homData_ext b
  intro p q h
  rw [Category.assoc,
    b.differential ((mapped F).obj E) ((mapped F).obj I) n m p q (p + n) (p + 1)
      hnm h rfl (by omega), Preadditive.comp_sub, Linear.comp_units_smul,
    ← Category.assoc, abstractComponent_π, ← Category.assoc, abstractComponent_π]
  conv_rhs =>
    rw [Category.assoc, abstractComponent_π]
    erw [← tr.pre]
  rw [a.differential E I n m p q (p + n) (p + 1) hnm h rfl (by omega),
    tr.sub, tr.smul, tr.naturality, tr.naturality]
  simp only [Functor.map_id]
  rfl

@[no_expose] private def abstractMap
    (a : HomData A) (b : HomData B) (F : A ⥤ B) [F.Additive]
    (tr : TransportData a b F) (E I : CochainComplex A ℤ) :
    (mapped F).obj (homObject a E I) ⟶
      homObject b ((mapped F).obj E) ((mapped F).obj I) where
  f := abstractComponent a b F tr E I
  comm' n m h := abstractComponent_comm a b F tr E I n m h

private lemma abstractMap_f
    (a : HomData A) (b : HomData B) (F : A ⥤ B) [F.Additive]
    (tr : TransportData a b F) (E I : CochainComplex A ℤ) (n : ℤ) :
    (abstractMap a b F tr E I).f n = abstractComponent a b F tr E I n := rfl

attribute [local irreducible] abstractMap

private lemma abstractMap_naturality
    (a : HomData A) (b : HomData B) (F : A ⥤ B) [F.Additive]
    (tr : TransportData a b F) (E E' I I' : CochainComplex A ℤ)
    (u : E' ⟶ E) (z : I ⟶ I') :
    (mapped F).map (((a.H.map u.op).app I) ≫ (a.H.obj (op E')).map z) ≫
        abstractMap a b F tr E' I' =
      abstractMap a b F tr E I ≫
        (((b.H.map ((mapped F).map u).op).app ((mapped F).obj I)) ≫
          (b.H.obj (op ((mapped F).obj E'))).map ((mapped F).map z)) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, abstractMap_f, abstractMap_f]
  change F.map _ ≫ abstractComponent a b F tr E' I' n =
    abstractComponent a b F tr E I n ≫ _
  apply homData_ext b
  intro p q h
  rw [Category.assoc, abstractComponent_π, ← tr.pre, a.naturality u z, tr.naturality,
    Category.assoc, b.naturality ((mapped F).map u) ((mapped F).map z),
    ← Category.assoc, abstractComponent_π]
  rfl

private lemma mapped_XIsoOfEq_inv (F : A ⥤ B) [F.Additive]
    (E : CochainComplex A ℤ) (p p' : ℤ) (h : p = p') :
    F.map (E.XIsoOfEq h).inv = (((mapped F).obj E).XIsoOfEq h).inv := by
  subst p'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Functor.map_id]
  rfl

private lemma abstractMap_shift
    (a : HomData A) (b : HomData B) (F : A ⥤ B) [F.Additive]
    (tr : TransportData a b F) (E I : CochainComplex A ℤ) (m : ℤ) :
    abstractMap a b F tr (E⟦m⟧) I ≫
        (((b.H.map (((mapped F).commShiftIso m).inv.app E).op).app ((mapped F).obj I))) ≫
        (b.shift ((mapped F).obj E) ((mapped F).obj I) m).hom =
      (mapped F).map (a.shift E I m).hom ≫
        ((mapped F).commShiftIso (-m)).hom.app (homObject a E I) ≫
          (abstractMap a b F tr E I)⟦-m⟧' := by
  apply HomologicalComplex.hom_ext
  intro n
  dsimp only [CochainComplex.shiftFunctor_obj_X']
  apply homData_ext b
  intro p q h
  simp only [HomologicalComplex.comp_f, Category.assoc, abstractMap_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctor_map_f']
  erw [Category.id_comp]
  erw [b.shift_spec]
  erw [Linear.comp_units_smul, ← Category.assoc]
  erw [homData_pre_π b (((mapped F).commShiftIso m).inv.app E)]
  erw [← Category.assoc]
  simp only [Functor.mapHomologicalComplex_commShiftIso_inv_app_f]
  erw [b.map_id, Category.comp_id, Linear.comp_units_smul,
    ← Category.assoc, abstractComponent_π]
  conv_rhs =>
    change (F.map ((a.shift E I m).hom.f n) ≫
        abstractComponent a b F tr E I (n + -m)) ≫
      b.π ((mapped F).obj E) ((mapped F).obj I) (n + -m) p q h
    rw [Category.assoc, abstractComponent_π, ← tr.pre]
    erw [a.shift_spec]
    rw [tr.smul, tr.naturality]
  simp only [Functor.map_id, CochainComplex.shiftFunctorObjXIso]
  erw [mapped_XIsoOfEq_inv F E]
  rfl

end AbstractHomComplex

section AbstractClosed

variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  [MonoidalCategory A] [MonoidalCategory B]

-- Evaluation and transposition, with the tensor factors in evaluation order.
private structure ClosedData (obj : A → A → A)
    (map : ∀ {X X' Y Y'}, (X' ⟶ X) → (Y ⟶ Y') → (obj X Y ⟶ obj X' Y')) where
  unc : ∀ {X Y T}, (T ⟶ obj X Y) → (T ⊗ X ⟶ Y)
  cur : ∀ {X Y T}, (T ⊗ X ⟶ Y) → (T ⟶ obj X Y)
  unc_cur : ∀ {X Y T} (g : T ⊗ X ⟶ Y), unc (cur g) = g
  injective : ∀ X Y T, Function.Injective (@unc X Y T)
  pre : ∀ {X Y T T'} (t : T' ⟶ T) (g : T ⟶ obj X Y),
    unc (t ≫ g) = (t ⊗ₘ 𝟙 X) ≫ unc g
  naturality : ∀ {X X' Y Y' T} (u : X' ⟶ X) (z : Y ⟶ Y') (g : T ⟶ obj X Y),
    unc (g ≫ map u z) = (𝟙 T ⊗ₘ u) ≫ unc g ≫ z
  sub : ∀ {X Y T} (g h : T ⟶ obj X Y), unc (g - h) = unc g - unc h
  smul : ∀ {X Y T} (k : ℤˣ) (g : T ⟶ obj X Y), unc (k • g) = k • unc g

@[no_expose] private def closedTransport {a : HomData A} {b : HomData B}
    (ca : ClosedData a.obj (@a.map))
    (cb : ClosedData b.obj (@b.map)) (F : A ⥤ B) [F.Additive]
    (μ : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (μnat : ∀ {X X' Y Y'} (u : X ⟶ X') (z : Y ⟶ Y'),
      (F.map u ⊗ₘ F.map z) ≫ (μ X' Y').inv = (μ X Y).inv ≫ F.map (u ⊗ₘ z)) :
    TransportData a b F where
  map g := cb.cur ((μ _ _).inv ≫ F.map (ca.unc g))
  pre := transport_pre_abstract F μ (μnat := μnat) ca.unc cb.unc cb.cur
    (hUC := cb.unc_cur) (hUI := cb.injective)
    ca.pre cb.pre
  naturality := transport_map_abstract F μ (μnat := μnat) ca.unc cb.unc cb.cur
    (hUC := cb.unc_cur) (hUI := cb.injective)
    a.map b.map ca.naturality cb.naturality
  sub := transport_sub_abstract F μ ca.unc cb.unc cb.cur
    (hUC := cb.unc_cur) (hUI := cb.injective) ca.sub cb.sub
  smul := transport_smul_abstract F μ ca.unc cb.unc cb.cur
    (hUC := cb.unc_cur) (hUI := cb.injective)
    ca.smul cb.smul

private lemma closedTransport_map {a : HomData A} {b : HomData B}
    (ca : ClosedData a.obj (@a.map)) (cb : ClosedData b.obj (@b.map))
    (F : A ⥤ B) [F.Additive]
    (μ : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (μnat : ∀ {X X' Y Y'} (u : X ⟶ X') (z : Y ⟶ Y'),
      (F.map u ⊗ₘ F.map z) ≫ (μ X' Y').inv = (μ X Y).inv ≫ F.map (u ⊗ₘ z))
    {X Y T : A} (g : T ⟶ a.obj X Y) :
    (closedTransport ca cb F μ μnat).map g =
      cb.cur ((μ T X).inv ≫ F.map (ca.unc g)) := rfl

attribute [local irreducible] closedTransport

end AbstractClosed

set_option backward.isDefEq.respectTransparency false in
private theorem closedComparison
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    (a : HomData A) (b : HomData B) (ca : ClosedData a.obj (@a.map))
    (cb : ClosedData b.obj (@b.map))
    (F : A ⥤ B) [F.Additive]
    (μ : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (μnat : ∀ {X X' Y Y'} (u : X ⟶ X') (z : Y ⟶ Y'),
      (F.map u ⊗ₘ F.map z) ≫ (μ X' Y').inv = (μ X Y).inv ≫ F.map (u ⊗ₘ z)) :
    ∃ comparison : ∀ E I : CochainComplex A ℤ,
        (mapped F).obj (homObject a E I) ⟶
          homObject b ((mapped F).obj E) ((mapped F).obj I),
      (∀ E I n p q (h : p + n = q),
        ((comparison E I).f n ⊗ₘ 𝟙 (F.obj (E.X p))) ≫
            cb.unc (b.π ((mapped F).obj E) ((mapped F).obj I) n p q h) =
          (μ ((homObject a E I).X n) (E.X p)).inv ≫ F.map (ca.unc (a.π E I n p q h))) ∧
      (∀ (E E' I I' : CochainComplex A ℤ) (u : E' ⟶ E) (z : I ⟶ I'),
        (mapped F).map (((a.H.map u.op).app I) ≫ (a.H.obj (op E')).map z) ≫
            comparison E' I' =
          comparison E I ≫
            (((b.H.map ((mapped F).map u).op).app ((mapped F).obj I)) ≫
              (b.H.obj (op ((mapped F).obj E'))).map ((mapped F).map z))) ∧
      (∀ (E I : CochainComplex A ℤ) (m : ℤ),
        comparison (E⟦m⟧) I ≫
            ((b.H.map (((mapped F).commShiftIso m).inv.app E).op).app ((mapped F).obj I)) ≫
            (b.shift ((mapped F).obj E) ((mapped F).obj I) m).hom =
          (mapped F).map (a.shift E I m).hom ≫
            ((mapped F).commShiftIso (-m)).hom.app (homObject a E I) ≫
              (comparison E I)⟦-m⟧') := by
  let tr := closedTransport ca cb F μ μnat
  refine ⟨abstractMap a b F tr, ?_, abstractMap_naturality a b F tr,
    abstractMap_shift a b F tr⟩
  intro E I n p q h
  erw [abstractMap_f, ← cb.pre, abstractComponent_π]
  dsimp only [tr]
  rw [closedTransport_map, cb.unc_cur]

section OneSite

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  (R : Sheaf J CommRingCat.{max c v r})

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

open WeilConjectures.ZeroClassAux

attribute [local instance 2000] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor
  tensorHomEquiv WeilConjectures.ZeroClassAux.ModuleCategory
  sheafCompose HasForget₂.forget₂

@[no_expose] private def unc {A B T : Modules R}
    (g : T ⟶ SheafOfModules.homObj.{max c v r, v, c, max c v r}
    (R := R) A B) :
    T ⊗ A ⟶ B :=
  (β_ T A).hom ≫ (tensorHomEquiv.{r, c, v} R A T B).symm g

@[no_expose] private def cur {A B T : Modules R} (g : T ⊗ A ⟶ B) :
    T ⟶ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B :=
  tensorHomEquiv.{r, c, v} R A T B ((β_ A T).hom ≫ g)

attribute [local irreducible] unc cur

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

attribute [local semireducible] sheafCompose HasForget₂.forget₂

omit [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
@[no_expose] private def ev : EvaluationFamily.{c, v, r} R :=
  fun E I n p q h ↦ unc.{c, v, r} R (homComplexπ E I n p q h)

attribute [local irreducible] ev

attribute [local irreducible] sheafCompose HasForget₂.forget₂

@[no_expose] private def forwardShiftIso (E I : Complex R) (m : ℤ) :
    (homComplex (R := R) E I)⟦-m⟧ ≅ homComplex (R := R) (E⟦m⟧) I :=
  ((RingedHomUniverses.ordinaryLeftShift.{c, v, r} J R m).choose).app (op E, I)

attribute [local irreducible] forwardShiftIso

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
@[no_expose] private def sourceShift : SourceShiftFamily.{c, v, r} R :=
  fun E I m ↦ (forwardShiftIso.{c, v, r} R E I m).symm

attribute [local irreducible] sourceShift

end OneSite

section TwoSites

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor
  WeilConjectures.ZeroClassAux.tensorHomEquiv
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  sheafCompose HasForget₂.forget₂

variable {C : Type c} [Category.{v} C] {D : Type d} [Category.{t} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v d t r} RingCat.{max c v d t r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max c v d t r} RingCat.{max c v d t r})]
  {R : Sheaf J CommRingCat.{max c v d t r}}
  {S : Sheaf K CommRingCat.{max c v d t r}}

variable [HasSheafify J AddCommGrpCat.{max c v d t r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v d t r}]
  [HasSheafify K AddCommGrpCat.{max c v d t r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max c v d t r}]

end TwoSites
end CategoryTheory.RingedHomPullback

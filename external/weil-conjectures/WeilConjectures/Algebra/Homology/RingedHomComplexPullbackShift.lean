/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses

/-! # Pullback of Hom complexes and signed source shifts

Source: Stacks Project, sites-modules.tex, Tag 0GMX (remark-pullback-internal-hom),
with sites-cohomology.tex, Tags 0A8X and 08JC; the signed calculation is the
agent formulation in the blueprint (auxiliary; not a blueprint node).
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

section OneSite

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The type of evaluation maps after each Hom-product projection.
Source: Stacks 0A8X and 0GMX
(auxiliary; not a blueprint node). -/
abbrev EvaluationFamily :=
  ∀ (E I : Complex R) (n p q : ℤ), p + n = q →
    ((homComplex (R := R) E I).X n ⊗ E.X p ⟶ I.X q)

/-- Source-shift isomorphisms of the actual unbounded Hom complexes.
Source: Stacks 0A8X and the signed calculation underlying 08JC
(auxiliary; not a blueprint node). -/
abbrev SourceShiftFamily :=
  ∀ (E I : Complex R) (m : ℤ),
    homComplex (R := R) (E⟦m⟧) I ≅ (homComplex (R := R) E I)⟦-m⟧

/-- The forward source-shift map has component `(-1)^(m*n) f^(p-m)`.
The equality of source terms uses the canonical `shiftFunctorObjXIso`.
Source: Stacks 0A8X and the signed chain calculation underlying 08JC
(auxiliary; not a blueprint node). -/
def IsSignedSourceShift (s : SourceShiftFamily.{c, v, r} R) : Prop :=
  ∀ (E I : Complex R) (m n p q : ℤ) (h : p + (n + -m) = q),
    (s E I m).hom.f n ≫ homComplexπ E I (n + -m) p q h =
      (m * n).negOnePow •
        (homComplexπ (E⟦m⟧) I n (p - m) q (by omega) ≫
          SheafOfModules.homObjMap (E.shiftFunctorObjXIso m (p - m) p (by omega)).inv (𝟙 (I.X q)))

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
private lemma forwardShift_formula (E I : Complex R) (m n p q : ℤ) (h : p + n = q) :
    (forwardShiftIso.{c, v, r} R E I m).hom.f n ≫ homComplexπ (E⟦m⟧) I n p q h =
      (m * n).negOnePow • homComplexπ E I (n + -m) (p + m) q (by omega) := by
  unfold forwardShiftIso
  exact (RingedHomUniverses.ordinaryLeftShift.{c, v, r} J R m).choose_spec E I n p q h

@[no_expose] private def sourceShift : SourceShiftFamily.{c, v, r} R :=
  fun E I m ↦ (forwardShiftIso.{c, v, r} R E I m).symm

attribute [local irreducible] sourceShift

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private lemma sourceShift_spec : IsSignedSourceShift R (sourceShift.{c, v, r} R) := by
  intro E I m n p q h
  unfold sourceShift
  dsimp only [Iso.symm_hom]
  let e := forwardShiftIso.{c, v, r} R E I m
  change (forwardShiftIso.{c, v, r} R E I m).inv.f n ≫ _ = _
  have hi : e.inv.f n ≫ e.hom.f n = 𝟙 _ :=
    congrArg (fun z ↦ z.f n) e.inv_hom_id
  have hc := congrArg (fun z ↦ e.inv.f n ≫ z)
    (forwardShift_formula.{c, v, r} R E I m n (p - m) q (by omega))
  rw [← Category.assoc, hi, Category.id_comp] at hc
  erw [Linear.comp_units_smul] at hc
  erw [hc, Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul,
    Category.assoc]
  change _ = e.inv.f n ≫ homComplexπ E I (n + -m) (p - m + m) q _ ≫
    SheafOfModules.homObjMap (E.XIsoOfEq (show p - m + m = p by omega)).inv (𝟙 _)
  have hpi (p' : ℤ) (hp : p' = p) :
      homComplexπ E I (n + -m) p' q (by omega) ≫
          SheafOfModules.homObjMap (E.XIsoOfEq hp).inv (𝟙 _) =
        homComplexπ E I (n + -m) p q h := by
    subst p'
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
      SheafOfModules.homObjMap_id, Category.comp_id]
  exact congrArg (fun z ↦ e.inv.f n ≫ z) (hpi _ (by omega)).symm

@[no_expose] private def siteHomData : HomData (Modules R) where
  obj := fun A B ↦ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B
  map := fun a b ↦ SheafOfModules.homObjMap.{max c v r, v, c, max c v r}
    (R := R) a b
  map_id := fun A B ↦ SheafOfModules.homObjMap_id (M := A) (N := B)
  H := homComplexFunctor.{c, v, max c v r, max c v r} (R := R)
  π := homComplexπ.{c, v, max c v r, max c v r} (R := R)
  limit := homComplexIsLimit.{c, v, max c v r, max c v r} (R := R)
  differential := homComplex_d_π.{c, v, max c v r, max c v r} (R := R)
  naturality := homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} (R := R)
  shift := sourceShift.{c, v, r} R
  shift_spec := sourceShift_spec.{c, v, r} R

@[no_expose] private def siteClosedData : ClosedData
    (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R))
    (fun {_ _ _ _} u z ↦ SheafOfModules.homObjMap.{max c v r, v, c, max c v r}
      (R := R) u z) := by
  have unc_cur {A B T : Modules R} (g : T ⊗ A ⟶ B) :
      unc.{c, v, r} R (cur.{c, v, r} R g) = g := by
    simp only [unc, cur, Equiv.symm_apply_apply, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp]
  have cur_unc {A B T : Modules R}
      (g : T ⟶ SheafOfModules.homObj.{max c v r, v, c, max c v r}
      (R := R) A B) :
      cur.{c, v, r} R (unc.{c, v, r} R g) = g := by
    simp only [unc, cur, ← Category.assoc, SymmetricCategory.symmetry,
      Category.id_comp, Equiv.apply_symm_apply]
  have unc_injective {A B T : Modules R} :
      Function.Injective (unc.{c, v, r} R (A := A) (B := B) (T := T)) := by
    intro g h he
    simpa only [cur_unc] using congrArg (cur.{c, v, r} R) he
  have unc_naturality {A A' B B' T T' : Modules R}
      (a : A' ⟶ A) (b : B ⟶ B') (t : T' ⟶ T)
      (g : T ⟶ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B) :
      unc.{c, v, r} R (t ≫ g ≫ SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) a b) =
        (t ⊗ₘ a) ≫ unc.{c, v, r} R g ≫ b := by
    have hn : (tensorHomEquiv.{r, c, v} R A' T' B').symm
        (t ≫ g ≫ SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) a b) =
        (a ⊗ₘ t) ≫ (tensorHomEquiv.{r, c, v} R A T B).symm g ≫ b := by
      apply (tensorHomEquiv.{r, c, v} R A' T' B').injective
      rw [Equiv.apply_symm_apply]
      let ψ := (tensorHomEquiv.{r, c, v} R A T B).symm g
      change _ = tensorHomEquiv.{r, c, v} R A' T' B' ((a ⊗ₘ t) ≫ ψ ≫ b)
      conv_rhs => rw [← Category.assoc]
      rw [tensorHomEquiv_right.{r, c, v} R A' ((a ⊗ₘ t) ≫ ψ) b]
      rw [tensorHom_def, Category.assoc,
        tensorHomEquiv_pre.{r, c, v} R a (A ◁ t ≫ ψ),
        tensorHomEquiv_left.{r, c, v} R A t ψ]
      dsimp only [ψ]
      rw [Equiv.apply_symm_apply]
      simp only [Category.assoc,
        SheafOfModules.homObjMap_comp_homObjMap.{max c v r, v, c, max c v r},
        Category.id_comp]
    simp only [unc]
    rw [hn]
    simp only [← Category.assoc]
    rw [BraidedCategory.braiding_naturality]
  have unc_pre {A B T T' : Modules R} (t : T' ⟶ T)
      (g : T ⟶ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B) :
      unc.{c, v, r} R (t ≫ g) = (t ⊗ₘ 𝟙 A) ≫ unc.{c, v, r} R g := by
    simpa using unc_naturality (𝟙 A) (𝟙 B) t g
  have unc_map {A A' B B' T : Modules R}
      (a : A' ⟶ A) (b : B ⟶ B')
      (g : T ⟶ SheafOfModules.homObj.{max c v r, v, c, max c v r}
      (R := R) A B) :
      unc.{c, v, r} R (g ≫ SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) a b) =
        (𝟙 T ⊗ₘ a) ≫ unc.{c, v, r} R g ≫ b := by
    simpa using unc_naturality a b (𝟙 T) g
  have unc_eq {A B T : Modules R}
      (g : T ⟶ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B) :
      unc.{c, v, r} R g = (g ⊗ₘ 𝟙 A) ≫ unc.{c, v, r} R (𝟙 (SheafOfModules.homObj A B)) := by
    simpa only [Category.comp_id] using
      unc_pre g (𝟙 (SheafOfModules.homObj A B))
  have unc_sub {A B T : Modules R}
      (g h : T ⟶ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B) :
      unc.{c, v, r} R (g - h) = unc.{c, v, r} R g - unc.{c, v, r} R h := by
    let := SheafOfModules.cochainModulesPreadditive.{c, v, max c v r} R
    rw [unc_eq, unc_eq g, unc_eq h]
    simp only [tensorHom_id]
    have he := (tensorRight A).map_sub (f := g) (g := h)
    change (g - h) ▷ A = g ▷ A - h ▷ A at he
    rw [he, Preadditive.sub_comp]
  have unc_smul {A B T : Modules R} (a : ℤˣ)
      (g : T ⟶ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B) :
      unc.{c, v, r} R (a • g) = a • unc.{c, v, r} R g := by
    let := SheafOfModules.cochainModulesPreadditive.{c, v, max c v r} R
    rw [unc_eq, unc_eq g]
    simp only [tensorHom_id]
    have he := (tensorRight A).map_units_smul a g
    change (a • g) ▷ A = a • (g ▷ A) at he
    rw [he, Linear.units_smul_comp]
  exact
    { unc := unc.{c, v, r} R
      cur := cur.{c, v, r} R
      unc_cur := unc_cur
      injective := fun _ _ _ ↦ unc_injective
      pre := unc_pre
      naturality := unc_map
      sub := unc_sub
      smul := unc_smul }

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

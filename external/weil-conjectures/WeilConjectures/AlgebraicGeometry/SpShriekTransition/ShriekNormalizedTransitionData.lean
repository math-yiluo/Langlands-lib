/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison

/-! # Normalized scalar coordinates of actual tower transitions

Source: blueprint latest, sk-prop-sp-integral-adjunction-direct-image.proof.md,
paragraph (1), the reduction maps are b followed by Rf_! of the input reduction
(blueprint: def-sp-normalized-transition-coordinates).

All systems and evaluations are the published ordinary derived sequence-site model.
Index n denotes the positive exponent n+1. Scalar coordinates below are fixed by
adjunction uniqueness, rather than a choice of maps between evaluated objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SemilinearSections.hasDerived
  SemilinearSections.moduleAbelian

namespace AlgebraicGeometry.ProEtale.SpShriekTransition

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A scalar reduction transported through a specified natural isomorphism.
Source: change of adjunction coordinates
(blueprint: def-sp-normalized-transition-coordinates). -/
def coordinateReduction
    {A B : Type*} [categoryA : Category A] [categoryB : Category B]
    {S S' : A ⥤ B} (s : S ≅ S') {K : A} {L : B} (f : S.obj K ⟶ L) :
    S'.obj K ⟶ L := s.inv.app K ≫ f

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Scalar reassociation transported through three specified natural isomorphisms.
Source: change of adjunction coordinates
(blueprint: def-sp-normalized-transition-coordinates). -/
def coordinateAssociator
    {A B C : Type*} [Category A] [Category B] [Category C]
    {S S' : A ⥤ B} {T T' : B ⥤ C} {R R' : A ⥤ C}
    (s : S ≅ S') (t : T ≅ T') (r : R ≅ R') (a : S ⋙ T ≅ R) :
    S' ⋙ T' ≅ R' :=
  Functor.isoWhiskerRight s.symm T' ≪≫
    Functor.isoWhiskerLeft S t.symm ≪≫ a ≪≫ r

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A transition conjugated through specified evaluation isomorphisms.
Source: change of evaluation coordinates
(blueprint: def-sp-normalized-transition-coordinates). -/
def conjugateReduction
    {A B : Type*} [Category A] [Category B] (S : A ⥤ B)
    {K K' : A} {L L' : B} (i : K ≅ K') (j : L ≅ L') (f : S.obj K ⟶ L) :
    S.obj K' ⟶ L' := S.map i.inv ≫ f ≫ j.hom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The actual composite quotient homomorphism, including equal indices.
Source: blueprint coefficient convention
(blueprint: def-sp-normalized-transition-coordinates). -/
def quotientMap {m n : ℕ} (h : m ≤ n) : SpTowerShriek.R l E n →+* SpTowerShriek.R l E m :=
  ((Functor.ofOpSequence
    (X := fun a : ℕ ↦ CommRingCat.of (SpTowerShriek.R l E a))
    (fun a ↦ CommRingCat.ofHom
      (Ideal.Quotient.factorPowSucc (spEllIdeal l E) (a + 1)))).map (homOfLE h).op).hom

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The sequence-site coefficient map is the constant sheaf of the actual quotient map.
Source: blueprint paragraph (1), coefficient transitions
(blueprint: def-sp-normalized-transition-coordinates).
Proof: induction on the length of the index interval reduces to the adjacent quotient
map. Constant sheafification preserves its identity and composite, and ULift preserves
composition of ring homomorphisms. Thus both sides are the same quotient map. -/
theorem coefficientMap_eq (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SemilinearSections.coefficientMap (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h =
      proEtaleConstantRingMap (T := T) (quotientMap l E h) := by
  let : HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
    WeilConjectures.integralCoefficientRingSheafify.{u, u} T
  let L : CommRingCat.{u} ⥤ CommRingCat.{u + 1} :=
    { obj := fun A ↦ CommRingCat.of (ULift.{u + 1} A)
      map := fun f ↦ CommRingCat.ofHom (RingHom.ulift f.hom) }
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u} := Functor.ofOpSequence
    (X := fun a : ℕ ↦ CommRingCat.of (SpTowerShriek.R l E a))
    (fun a ↦ CommRingCat.ofHom
      (Ideal.Quotient.factorPowSucc (spEllIdeal l E) (a + 1)))
  let G : CommRingCat.{u} ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
    L ⋙ constantSheaf.{u, u + 1, u + 1, u + 2} (ProEt.topology T) CommRingCat.{u + 1}
  let t : SemilinearSections.rings.{u + 1, u, u + 1} (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) ⟶ Q ⋙ G := by
    refine NatTrans.ofOpSequence (fun n ↦ 𝟙 _) ?_
    intro n
    simp only [SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ,
      CategoryTheory.Functor.comp_map]
    erw [Category.comp_id, Category.id_comp]
    dsimp only [G, L, CategoryTheory.Functor.comp_map]
    unfold SpTowerShriek.tau spCoefficientCommRings Q
    simp only [Functor.ofOpSequence_map_homOfLE_succ]
    rfl
  exact (Category.comp_id _).symm.trans
    ((t.naturality (homOfLE h).op).trans (Category.id_comp _))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The unique left-adjoint comparison from the generic normalized scalar model to
constant-ring scalar extension. Its right-adjoint comparison is equality transport
of the actual quotient map. Source: blueprint paragraph (1), scalar-adjoint convention
(blueprint: def-sp-normalized-transition-coordinates). -/
def scalarCoordinates (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) :
    ((b.calculus T).scalar h).T ≅ scalarExtensionFunctor (quotientMap l E h) T :=
  ((b.calculus T).scalar h).adjunction.leftAdjointUniq
    ((proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotientMap l E h))).ofNatIsoRight
        (eqToIso (congrArg
          (fun a ↦ SemilinearSections.resD a) (coefficientMap_eq l E T h))).symm)

attribute [local irreducible] scalarCoordinates quotientMap
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The scalar-adjoint of the actual strict transition in constant-ring coordinates.
Source: blueprint paragraph (1); the derived system model's reduction construction
(blueprint: def-sp-normalized-transition-coordinates). -/
def rho (b : SpTowerShriek.Base l E) (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (C : SpTowerShriek.D l E T) :
    (scalarExtensionFunctor (quotientMap l E h) T).obj ((SpTowerShriek.Ev l E T n).obj C) ⟶
      (SpTowerShriek.Ev l E T m).obj C :=
  coordinateReduction
    (A := proEtaleDerivedCategory T (SpTowerShriek.R l E n))
    (B := proEtaleDerivedCategory T (SpTowerShriek.R l E m))
    (categoryA := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (categoryB := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (scalarCoordinates l E b T h)
    (SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) h ((b.calculus T).scalar h) C)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Canonical scalar reassociation transported from the normalized system calculus.
Source: blueprint paragraph (1), the canonical scalar associators
(blueprint: def-sp-normalized-transition-coordinates). -/
def alpha (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {r m n : ℕ} (h : r ≤ m) (k : m ≤ n) :
    scalarExtensionFunctor (quotientMap l E k) T ⋙
        scalarExtensionFunctor (quotientMap l E h) T ≅
      scalarExtensionFunctor (quotientMap l E (h.trans k)) T :=
  coordinateAssociator (scalarCoordinates l E b T k) (scalarCoordinates l E b T h)
    (scalarCoordinates l E b T (h.trans k)) ((b.calculus T).scalarComposition h k)

end AlgebraicGeometry.ProEtale.SpShriekTransition

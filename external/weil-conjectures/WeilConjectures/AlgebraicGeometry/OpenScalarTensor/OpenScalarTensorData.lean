/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarExchange
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Open scalar, tensor and coefficient normalization

## References

* Stacks 06YY
* Stacks 03CY, 08FJ
* Stacks 07A6, 07A4, 05V4
* Stacks 03DA, 07A4
* Stacks 0GL1, 0E8I, 07A6, 0D6D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- Presentations of the existing unbounded tensors and normalized scalar adjunctions. -/
abbrev Models := ∀ T : Scheme.{u},
  ScalarHomModels.{u + 1, u, u + 1, u + 2} (Scheme.ProEt.topology T)

variable (m : Models.{u})

/-- The existing scalar derived pair at the constant ring map. -/
abbrev scalarPair {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :=
  (m T).scalar (proEtaleConstantRingMap (T := T) φ)

/-- The scalar functor of this normalized universal presentation. -/
abbrev scalar {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) := (scalarPair m φ T).derived

/-- Identification with the scalar functor by its normalized adjunction. -/
def scalarIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) : scalar m φ T ≅ scalarExtension φ T :=
  (scalarPair m φ T).adjunction.leftAdjointUniq
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ))

/-- The existing derived tensor in the selected representative presentation. -/
abbrev tensor (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  ((m T).closed (proEtaleConstantRing T A)).tensor

/-- Its derived tensor unit, canonically the constant coefficient module. -/
abbrev unit (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  ((m T).closed (proEtaleConstantRing T A)).monoidal.tensorUnit

/-- Restriction of the B tensor unit is the constant A-module B. -/
abbrev coefficient {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :=
  (scalarRestriction φ T).obj (unit m B T)

/-- The exact open adjunction already used by the operations. -/
abbrev openAdj (A : Type u) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :=
  proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X A)
    (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A)

/-- The identity-on-actions inverse-image/restriction comparison. -/
def rightSquare {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) :
    constantPullback (A := B) j ⋙ scalarRestriction φ U ≅
      scalarRestriction φ X ⋙ constantPullback (A := A) j :=
  proEtaleRingRestrictionDerivedPullback j
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRing U A) (proEtaleConstantRing U B)
    (proEtaleConstantRingMap (T := X) φ) (proEtaleConstantRingMap (T := U) φ)
    (proEtaleConstantRingComparison j A) (proEtaleConstantRingComparison j B)
    (by simpa [proEtaleConstantRingComparison, proEtaleConstantRingMap] using
      (proEtaleConstantInverseImageMap_naturality j
        (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)

/-- The specified balanced inverse-image/scalar comparison, transported by scalar units. -/
def lambda {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) :
    scalar m φ X ⋙ constantPullback (A := B) j ≅
      constantPullback (A := A) j ⋙ scalar m φ U :=
  Functor.isoWhiskerRight (scalarIso m φ X) _ ≪≫ tensorPullbackIso φ j ≪≫
    Functor.isoWhiskerLeft _ (scalarIso m φ U).symm

/-- The common-right-adjoint open scalar comparison, transported by `scalarIso`.
Its components retain the B-linear action. -/
def beta {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openExtension (A := A) j ⋙ scalar m φ X ≅
      scalar m φ U ⋙ openExtension (A := B) j :=
  Functor.isoWhiskerLeft (openExtension (A := A) j) (scalarIso m φ X) ≪≫
    openScalarIso φ j ≪≫
      Functor.isoWhiskerRight (scalarIso m φ U).symm (openExtension (A := B) j)

/-- The open mate of identity on restricted actions, before asserting invertibility. -/
def restrictionOpen {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    scalarRestriction φ U ⋙ openExtension (A := A) j ⟶
      openExtension (A := B) j ⋙ scalarRestriction φ X :=
  ((mateEquiv (openAdj B j) (openAdj A j)).symm
    (TwoSquare.mk _ _ _ _ (rightSquare φ j).hom))

set_option backward.isDefEq.respectTransparency.types true in
/-- Restricting the existing K-flat tensor model to flat-term representatives. -/
def tensorModel (A : Type u) [CommRing A] (T : Scheme.{u}) :
    ProEtaleTensorModel T (proEtaleConstantRing T A) :=
  let i : (proEtaleFlatRepresentatives T (proEtaleConstantRing T A)).FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology T) (R := proEtaleConstantRing T A)) := {
    obj := fun P ↦ ⟨P.obj,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).mpr P.property.1⟩
    map := fun f ↦ ObjectProperty.homMk f.hom }
  let e := Functor.isoWhiskerLeft (i.prod i)
    ((m T).model (proEtaleConstantRing T A)).comparison
  { tensor := tensor m A T
    representative := e }

/-- The canonical restriction tensorator, fixed on signed K-flat total tensors. -/
def restrictionTensor (A : Type u) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) :
    tensor m A X ⋙ constantPullback (A := A) j ≅
      ((constantPullback (A := A) j).prod (constantPullback (A := A) j)) ⋙ tensor m A U :=
  proEtaleCanonicalTensorComparison j (proEtaleConstantRing X A)
    (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A)
    (tensorModel m A X) (tensorModel m A U)

/-- Type of strong monoidal structures on the exact open inverse image. -/
def OpenMonoidal (A : Type u) [CommRing A] {U X : Scheme.{u}} (j : U ⟶ X) :=
  letI := ((m X).closed (proEtaleConstantRing X A)).monoidal
  letI := ((m U).closed (proEtaleConstantRing U A)).monoidal
  (constantPullback (A := A) j).Monoidal

/-- The tensorator of a chosen strong monoidal structure, with explicit model instances. -/
def openDelta (A : Type u) [CommRing A] {U X : Scheme.{u}} (j : U ⟶ X)
    (h : OpenMonoidal m A j)
    (F G : proEtaleDerivedCategory X A) :
    (constantPullback (A := A) j).obj ((tensor m A X).obj (F, G)) ⟶
      (tensor m A U).obj
        ((constantPullback (A := A) j).obj F, (constantPullback (A := A) j).obj G) :=
  letI := ((m X).closed (proEtaleConstantRing X A)).monoidal
  letI := ((m U).closed (proEtaleConstantRing U A)).monoidal
  letI : (constantPullback (A := A) j).Monoidal := h
  Functor.OplaxMonoidal.δ (constantPullback (A := A) j) F G

/-- The canonical tensor-unit comparison of open inverse image. -/
def openUnit (A : Type u) [CommRing A] {U X : Scheme.{u}} (j : U ⟶ X)
    (h : OpenMonoidal m A j) :
    (constantPullback (A := A) j).obj (unit m A X) ≅ unit m A U :=
  letI := ((m X).closed (proEtaleConstantRing X A)).monoidal
  letI := ((m U).closed (proEtaleConstantRing U A)).monoidal
  letI : (constantPullback (A := A) j).Monoidal := h
  (Functor.Monoidal.εIso (constantPullback (A := A) j)).symm

/-- Canonical tensor comparison presentations, including unit coherence for restriction.
All tensorators are fixed by their existing K-flat representative characterizations. -/
structure Choices where
  scalarTensor : ∀ {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}),
    ScalarHomTensorComparison.{u + 1, u, u + 1, u + 2} (m T) (proEtaleConstantRingMap (T := T) φ)
  openMonoidal : ∀ (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], OpenMonoidal m A j
  open_normalization : ∀ (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F G : proEtaleDerivedCategory X A),
    openDelta m A j (openMonoidal A j) F G = (restrictionTensor m A j).hom.app (F, G)

variable (c : Choices m)

/-- The canonical scalar tensor identification, written in the direction
`K tensor Res(B) ⟶ Res(S(K))`. Its scalar adjunct applies the normalized scalar
monoidal comparison, then the scalar counit at the tensor unit and the right unitor.
Thus this is a specified map, with no choice of an isomorphism of endpoints. -/
def scalarProjection {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A) :
    (tensor m A T).obj (K, coefficient m φ T) ⟶
      (scalarRestriction φ T).obj ((scalar m φ T).obj K) :=
  (scalarPair m φ T).adjunction.homEquiv _ _
    ((c.scalarTensor φ T).iso.hom.app (K, coefficient m φ T) ≫
      (tensor m B T).map (Prod.mkHom (𝟙 _)
        ((scalarPair m φ T).adjunction.counit.app (unit m B T))) ≫
      (((m T).closed (proEtaleConstantRing T B)).monoidal.rightUnitor
        ((scalar m φ T).obj K)).hom)

/-- The constant coefficient identification under restriction to the open, obtained
from the identity-on-actions square and the normalized inverse-image tensor unit. -/
def coefficientPullback {A B : Type u} [CommRing A] [CommRing B] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (constantPullback (A := A) j).obj (coefficient m φ X) ≅ coefficient m φ U :=
  (rightSquare φ j).symm.app (unit m B X) ≪≫
    (scalarRestriction φ U).mapIso (openUnit m B j (c.openMonoidal B j))

/-- The forward open projection isomorphism with its inverse adjunct prescribed.
This is the normalization of `derivedOpenImmersionLowerShriekProjectionIso`, transported
to these presentations of derived tensor, with its direction reversed. Its
`derivedOpenImmersionLowerShriekProjectionMap` is precisely the adjunct prescribed below. -/
structure Projection (A : Type u) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] where
  iso : ((openExtension (A := A) j).prod (𝟭 _)) ⋙ tensor m A X ≅
    ((𝟭 _).prod (constantPullback (A := A) j)) ⋙ tensor m A U ⋙ openExtension (A := A) j
  inverse_adjunct : ∀ (K : proEtaleDerivedCategory U A) (Q : proEtaleDerivedCategory X A),
    (openAdj A j).homEquiv _ _ (iso.inv.app (K, Q)) =
      (tensor m A U).map (Prod.mkHom ((openAdj A j).unit.app K) (𝟙 _)) ≫
        (restrictionTensor m A j).inv.app ((openExtension (A := A) j).obj K, Q)

/-- Balanced coefficient associativity, including the constant-sheaf composition transport. -/
def scalarComp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u}) :
    scalar m φ T ⋙ scalar m ψ T ≅ scalar m (ψ.comp φ) T :=
  scalarHomExtensionComp (m T) (proEtaleConstantRingMap (T := T) φ)
    (proEtaleConstantRingMap (T := T) ψ) ≪≫
      eqToIso (congrArg (fun a ↦ ((m T).scalar a).derived)
        ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_comp
          (CommRingCat.ofHom (RingHom.ulift φ))
          (CommRingCat.ofHom (RingHom.ulift ψ))).symm)

/-- The canonical scalar identity is uniquely fixed to its original restriction-adjunction
construction. This equality specification shields the derived localization from reduction. -/
theorem scalarId_existsUnique (A : Type u) [CommRing A] (T : Scheme.{u}) :
    ∃! e : scalar m (RingHom.id A) T ≅ 𝟭 (proEtaleDerivedCategory T A),
      e = eqToIso (congrArg (fun a ↦ ((m T).scalar a).derived)
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A)))) ≪≫
    scalarHomExtensionId (m T) (proEtaleConstantRing T A) := by
  exact ⟨_, rfl, fun _ h ↦ h⟩

/-- The unit-normalized identity scalar isomorphism, with its original canonical value. -/
def scalarId (A : Type u) [CommRing A] (T : Scheme.{u}) :
    scalar m (RingHom.id A) T ≅ 𝟭 (proEtaleDerivedCategory T A) :=
  (scalarId_existsUnique m A T).exists.choose

/-- All clauses of the open scalar normalization, on ordinary unbounded module
categories. The projection maps and scalar tensor identifications are prescribed
adjunction transposes, rather than freely chosen isomorphisms. -/
structure Normalization where
  projection : ∀ (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], Projection m A j
  scalar_projection_isIso : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u})
    (K : proEtaleDerivedCategory T A), IsIso (scalarProjection m c φ T K)
  restriction_open_isIso : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j], IsIso (restrictionOpen φ j)
  beta_inverse : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : proEtaleDerivedCategory U A),
    (openAdj B j).homEquiv _ _ ((beta m φ j).inv.app K) =
      (scalar m φ U).map ((openAdj A j).unit.app K) ≫
        (lambda m φ j).inv.app ((openExtension (A := A) j).obj K)
  restricted_beta : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : proEtaleDerivedCategory U A),
    scalarProjection m c φ X ((openExtension (A := A) j).obj K) ≫
        (scalarRestriction φ X).map ((beta m φ j).hom.app K) =
      (projection A j).iso.hom.app (K, coefficient m φ X) ≫
        (openExtension (A := A) j).map
          ((tensor m A U).map (Prod.mkHom (𝟙 K) (coefficientPullback m c φ j).hom) ≫
            scalarProjection m c φ U K) ≫
        (restrictionOpen φ j).app ((scalar m φ U).obj K)
  coefficient_comp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : proEtaleDerivedCategory U A),
    (scalar m ψ X).map ((beta m φ j).hom.app K) ≫
        (beta m ψ j).hom.app ((scalar m φ U).obj K) ≫
        (openExtension (A := C) j).map ((scalarComp m φ ψ U).hom.app K) =
      (scalarComp m φ ψ X).hom.app ((openExtension (A := A) j).obj K) ≫
        (beta m (ψ.comp φ) j).hom.app K
  coefficient_id : ∀ (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : proEtaleDerivedCategory U A),
    (beta m (RingHom.id A) j).hom.app K ≫
        (openExtension (A := A) j).map ((scalarId m A U).hom.app K) =
      (scalarId m A X).hom.app ((openExtension (A := A) j).obj K)
  tensor_square : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (K : proEtaleDerivedCategory U A) (Q : proEtaleDerivedCategory X A),
    (scalar m φ X).map ((projection A j).iso.hom.app (K, Q)) ≫
        (beta m φ j).hom.app
          ((tensor m A U).obj (K, (constantPullback (A := A) j).obj Q)) ≫
        (openExtension (A := B) j).map
          ((c.scalarTensor φ U).iso.hom.app
              (K, (constantPullback (A := A) j).obj Q) ≫
            (tensor m B U).map
              (Prod.mkHom (𝟙 _) ((lambda m φ j).inv.app Q))) =
      (c.scalarTensor φ X).iso.hom.app ((openExtension (A := A) j).obj K, Q) ≫
        (tensor m B X).map (Prod.mkHom ((beta m φ j).hom.app K) (𝟙 _)) ≫
        (projection B j).iso.hom.app ((scalar m φ U).obj K, (scalar m φ X).obj Q)

end AlgebraicGeometry.ProEtale.OpenScalarTensor

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Integral quotient scalar comparison for unbounded direct image

(1), (3);
Stacks Project, Tags 093M, 0D6D, 0D6E, 07A6 and 0944
(auxiliary; not a blueprint node).

Positive quotient levels are indexed by n + 1. All categories are ordinary unbounded
derived categories of the recorded internal module objects. No completion is applied.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

/-- The existing internal module category, with its canonical derived localization.
Source: Stacks 00YV, 06YY (auxiliary; not a blueprint node). -/
abbrev Modules (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ₀]
    (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ₀ T)

/-- The ordinary extension whose total left derived functor is scalar extension.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
abbrev extension (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    Modules Λ T ⥤ Modules Λ' T :=
  Mod.extendScalars (coefficientMap a T)

/-- The existing total left derived scalar extension, without a flatness restriction.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
@[irreducible] def D (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    DerivedCategory (Modules Λ T) ⥤ DerivedCategory (Modules Λ' T) :=
  by
    exact (extension a T).leftDerivedFunctor

/-- The existing total derived module pullback.
Source: blueprint derived push-pull (auxiliary; not a blueprint node).
-/
@[irreducible] def L (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules Λ₀ Y) ⥤ DerivedCategory (Modules Λ₀ X) :=
  CondensedRing.moduleObjectDerivedPullback Λ₀ f

/-- The existing total derived module direct image.
Source: blueprint derived push-pull (auxiliary; not a blueprint node).
-/
@[irreducible] def F (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules Λ₀ X) ⥤ DerivedCategory (Modules Λ₀ Y) :=
  CondensedRing.moduleObjectDerivedPushforward Λ₀ f

/-- The given geometric derived adjunction, including its specified counit.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[irreducible] def adj (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L Λ₀ f ⊣ F Λ₀ f :=
  by
    unfold L F
    exact CondensedRing.derivedUpperStarLowerStarAdjunction Λ₀ f

/-- The computation counit with its scalar interface exposed.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def scalarCounit (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ D a T ⟶
      (extension a T).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
  unfold D
  exact (extension a T).leftDerivedFunctorCounit

/-- The computation counit with its geometric interface exposed.
Source: Stacks 0G7E (auxiliary; not a blueprint node). -/
def pullCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ L Λ f ⟶
      (CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact (CondensedRing.upperStar Λ f).leftDerivedFunctorCounit

/-- The existing scalar adjunction with typed interfaces.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def scalarAdj (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    D a T ⊣ (Mod.comap (C := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (coefficientMap a T)).mapDerivedCategory := by
  unfold D
  exact Mod.derivedExtendMapDerivedCategoryAdjunction _

/-- The representative normalization of the balancing isomorphism. Both sides are
composed with the universal computation counits, so this also specifies the comparison
on flat-term K-flat representatives, where those counits are invertible. The ordinary
comparison is the fixed pure-tensor balancing map, not a choice of an isomorphism.
Source: Stacks 0D6D, 0G7E (auxiliary; not a blueprint node). -/
def PullNormalized (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) : Prop :=
  ∀ P : HomotopyCategory (Modules Λ Y) (.up ℤ),
    b.hom.app (DerivedCategory.Qh.obj P) ≫
        (D a X).map ((pullCounit (Λ := Λ) f).app P) ≫
        (scalarCounit a X).app
          (((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (CondensedRing.upperStar Λ f ⋙ extension a X)) (.up ℤ)).hom.app P) =
      (L Λ' f).map ((scalarCounit a Y).app P) ≫
        (pullCounit (Λ := Λ') f).app
          (((extension a Y).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (CondensedRing.pullIso a f).symm (.up ℤ)).hom.app P)

/-- The actual direct-image mate. Its adjunct is balancing followed by the image
of the integral counit, exactly as specified in the node.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def rho (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) :
    F Λ f ⋙ D a Y ⟶ D a X ⋙ F Λ' f :=
  (mateEquiv (adj Λ f) (adj Λ' f) (TwoSquare.mk _ _ _ _ b.hom))

end AlgebraicGeometry.ProEtale.QuotientChange
namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']

/-- Ordinary scalar restriction.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
abbrev V₀ (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    Modules Λ' T ⥤ Modules Λ T := Mod.comap (coefficientMap a T)

/-- Exact scalar restriction on the ordinary unbounded derived category.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
abbrev V (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    DerivedCategory (Modules Λ' T) ⥤ DerivedCategory (Modules Λ T) :=
  (V₀ a T).mapDerivedCategory

/-- The quotient coefficient as a module over the source ring.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
abbrev B₀ (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) : Modules Λ T :=
  (V₀ a T).obj (Mod.regular (condensedRingObj Λ' T))

/-- The quotient coefficient in degree zero.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
abbrev B (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Modules Λ T) 0).obj (B₀ a T))

/-- The actual universal scalar computation map at a cochain complex.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def compute (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    (D a T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((extension a T).mapHomologicalComplex (.up ℤ)).obj P) :=
  (D a T).map ((DerivedCategory.quotientCompQhIso (Modules Λ T)).inv.app P) ≫
    (scalarCounit a T).app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((extension a T).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (Modules Λ' T)).hom.app
      (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)

-- Total tensor colimit search needs the same bound as the upstream module-object API.
/-- Total tensor with the actual degree-zero coefficient is termwise tensor.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def singleTensor (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    CochainComplex.mapBifunctor P ((CochainComplex.singleFunctor _ 0).obj (B₀ a T))
      (curriedTensor (Modules Λ T)) ≅
      ((tensorRight (B₀ a T)).mapHomologicalComplex (.up ℤ)).obj P :=
  CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Modules Λ T)) (B₀ a T) P

/-- Normalization of restricted scalar extension as the relative tensor functor.
The ordinary isomorphism is fixed on underlying sheaves by the existing balanced
coequalizer comparison and symmetry. The derived isomorphism is fixed by its universal
computation map and the single-factor total tensor comparison, so no arbitrary tensor
identification is admitted.
Source: Stacks 06YY, 0G7E (auxiliary; not a blueprint node). -/
structure TensorNormalization (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) where
  ordinary : extension a T ⋙ V₀ a T ≅ tensorRight (B₀ a T)
  ordinary_hom : ∀ M : Modules Λ T,
    (ordinary.hom.app M).hom =
      (Mod.extendForgetTensorObjIso (coefficientMap a T) M).hom ≫
        (β_ (B₀ a T) M).hom.hom
  derived : D a T ⋙ V a T ≅ tensorRight (B a T)
/-- The derived tensor identification has the same universal computation map as ordinary
balanced extension. This equation uniquely normalizes the identification on K-flat inputs.
Source: Stacks 06YY, 0G7E (auxiliary; not a blueprint node). -/
def TensorNormalized (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (t : TensorNormalization a T) : Prop :=
  ∀ P : CochainComplex (Modules Λ T) ℤ,
    t.derived.hom.app (DerivedCategory.Q.obj P) ≫
        Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Modules Λ T)) P
          ((CochainComplex.singleFunctor (Modules Λ T) 0).obj (B₀ a T)) ≫
        DerivedCategory.Q.map (singleTensor a T P).hom =
      (V a T).map (compute a T P) ≫
        (V₀ a T).mapDerivedCategoryFactors.hom.app
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso t.ordinary (.up ℤ)).hom.app P)

/-- The canonical restriction/direct-image comparison, conjugate to balancing between
composite left adjoints. Its definition uses the specified adjunctions and counits.
Source: Stacks 0D6E, 07A6 (auxiliary; not a blueprint node). -/
def restrictPush (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) :
    F Λ' f ⋙ V a Y ≅ V a X ⋙ F Λ f :=
  ((scalarAdj a Y).comp
      (adj Λ' f)).rightAdjointUniq
    (((adj Λ f).comp
      (scalarAdj a X)).ofNatIsoLeft
        b.symm)

end AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']

end AlgebraicGeometry.ProEtale.QuotientChange

/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# The derived category of a monoidal closed Grothendieck abelian category is monoidal closed

Let `C` be a Grothendieck abelian category which is monoidal closed, and whose monoidal
structure is compatible with the additive structure in the way that is needed in order to
tensor cochain complexes (`MonoidalPreadditive C` and the `GradedObject` hypotheses below,
which are exactly the ones under which `DerivedCategory C` is monoidal, see
`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`). This file shows that,
when moreover K-flat complexes form a left derivability structure for the quasi-isomorphisms
(which holds as soon as `C` has functorial flat resolutions, see
`CategoryTheory.Abelian.LeftResolution.homotopyCategory_kFlat_isLeftDerivabilityStructure`
in `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`), the derived category `D(C)`
is again monoidal closed, the monoidal structure being the derived tensor product `- ⊗^L -`.
This K-flat derivability structure is the only hypothesis beyond those needed to tensor
complexes: the monoidal structure on `D(C)` is itself deduced from it.

Since `MonoidalClosed` only asks for a right adjoint of `X ⊗^L -` for every object `X` of
`D(C)`, no binary `RHom` bifunctor has to be constructed by hand: the bifunctoriality of the
internal hom is produced by the closed structure itself. The proof of the instance below is
therefore organized in the following four steps.

1. **Closedness at the homotopy level** (done in
   `WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom`). For cochain complexes
   `P`, `Y` in `C`, the internal hom complex `CochainComplex.internalHomObj P Y` has
   `(iHom P Y)ⁿ = ∏_{p + n = q} iHom (P.X p) (Y.X q)`, with differential
   `(-1)ᵖ • (f ≫ d_Y - d_P ≫ f)` on the factor indexed by `(p, q)` (the products exist since
   `C` is Grothendieck abelian). The tensor-hom bijection `(P ⊗ X ⟶ Y) ≃ (X ⟶ iHom P Y)` is
   plain currying on morphisms of complexes, and currying with the sign `(-1) ^ (p * n)` on
   cochains of degree `n` commutes with `δ`, so it is compatible with homotopies. This gives
   `HomotopyCategory.tensorHomAdjunction P : tensorLeft P ⊣ H_P` on
   `K(C) := HomotopyCategory C (ComplexShape.up ℤ)`, with `H_P = HomotopyCategory.internalHom P`.
2. **Fixing one variable of the binary derived tensor.** Deduce from the fact that the derived
   tensor product is the binary left derived functor of the tensor product on `K(C)` (the
   `IsLeftDerivedFunctor₂` instance in
   `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`) that `Qh.obj P ⊗^L -`
   is the (unary) left derived functor of `P ⊗ -`: the comparison map
   `Qh.obj P ⊗^L Qh.obj Z ⟶ Qh.obj (P ⊗ Z)` is an isomorphism for K-flat `Z`
   (`DerivedCategory.tensorLeftQhObjCounit`, a specialisation of
   `CategoryTheory.DerivedMonoidal.isIso_counit_app_app_of_kFlat_right`).
3. **Deriving the adjunction.** Right derive `H_P` using K-injective resolutions, which exist
   since `C` is Grothendieck abelian
   (`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`), and apply
   `CategoryTheory.Adjunction.derived` to `P ⊗ - ⊣ H_P` to obtain `Qh.obj P ⊗^L - ⊣ R H_P`
   (`DerivedCategory.tensorHomAdjunctionQhObj`). The absoluteness hypotheses of
   `Adjunction.derived` are checked on K-flat, respectively K-injective, complexes, by
   `CategoryTheory.LocalizerMorphism.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure`
   and its dual. Only the individual right derived functors are needed here, not their
   functoriality in `P`.
4. **Transport to an arbitrary object.** Every `X : DerivedCategory C` is isomorphic to
   `Qh.obj P` for some `P` (essential surjectivity of the localization functor), and
   closedness transfers along an isomorphism of objects, since an isomorphism `Qh.obj P ≅ X`
   induces a natural isomorphism `Qh.obj P ⊗^L - ≅ X ⊗^L -`, along which the adjunction of
   step 3 can be transported (`CategoryTheory.Adjunction.ofNatIsoLeft`). The object `P` is
   chosen with `Qh.objPreimage X`, so `ihom X` is `R H_P` for this *noncanonical* choice of
   `P`.

Once the instance is available, its internal hom is *the* derived internal hom. By uniqueness of
right adjoints, `ihom (Qh.obj P) ≅ R H_P` for every `P`, independently of the choice made in
step 4; this identification, and the one with the concrete hom-complex-of-a-K-injective-replacement
model, is further work, which is what an `RHom` API would be about.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [(HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]
  (P : HomotopyCategory C (ComplexShape.up ℤ))

/-- The comparison `Qh.obj P ⊗^L Qh.obj Z ⟶ Qh.obj (P ⊗ Z)`, natural in `Z`, exhibiting
`Qh.obj P ⊗^L -` as the left derived functor of `P ⊗ -`:
```
K(C) ──P ⊗ -──▶ K(C)
 │               │
 Qh      ⇙       Qh
 ▼               ▼
D(C) ─Qh P ⊗ᴸ -─▶ D(C)
```
It is `Functor.bifunctorCounit₁` of `Functor.LaxMonoidal.μNatTrans Qh` at `P`. -/
noncomputable def tensorLeftQhObjCounit :
    Qh ⋙ tensorLeft (Qh.obj P) ⟶ tensorLeft P ⋙ Qh :=
  Functor.bifunctorCounit₁ (Functor.LaxMonoidal.μNatTrans Qh) P

omit [IsGrothendieckAbelian.{w} C] in
/-- The comparison map `Qh.obj P ⊗^L Qh.obj Z ⟶ Qh.obj (P ⊗ Z)` is an isomorphism at
K-flat complexes `Z`. -/
lemma isIso_tensorLeftQhObjCounit_app (Z : HomotopyCategory C (ComplexShape.up ℤ))
    (hZ : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat Z) :
    IsIso ((tensorLeftQhObjCounit P).app Z) :=
  DerivedMonoidal.isIso_counit_app_app_of_kFlat_right Qh _ P Z hZ

omit [IsGrothendieckAbelian.{w} C] in
/-- The derived tensor product `Qh.obj P ⊗^L -` is the left derived functor of `P ⊗ -`. -/
instance isLeftDerivedFunctor_tensorLeft :
    (tensorLeft (Qh.obj P)).IsLeftDerivedFunctor (tensorLeftQhObjCounit P)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  DerivedMonoidal.isLeftDerivedFunctor_bifunctorCounit₁_kFlat Qh _ P

/-- The right derived functor of the internal hom `iHom P -` of the homotopy category,
computed on K-injective complexes. It is the internal hom out of `Qh.obj P` in `D(C)`. -/
noncomputable def internalHomQhObj : DerivedCategory C ⥤ DerivedCategory C :=
  (HomotopyCategory.internalHom P ⋙ Qh).totalRightDerived Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The natural transformation exhibiting `internalHomQhObj P` as the right derived functor
of `iHom P -`. -/
noncomputable def internalHomQhObjUnit :
    HomotopyCategory.internalHom P ⋙ Qh ⟶ Qh ⋙ internalHomQhObj P :=
  (HomotopyCategory.internalHom P ⋙ Qh).totalRightDerivedUnit Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- `internalHomQhObj P` is the right derived functor of `iHom P -`. -/
instance isRightDerivedFunctor_internalHomQhObj :
    (internalHomQhObj P).IsRightDerivedFunctor (internalHomQhObjUnit P)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [internalHomQhObj, internalHomQhObjUnit]
  infer_instance

/-- The first absoluteness hypothesis of `Adjunction.derived` for `P ⊗ - ⊣ iHom P -`:
`R H_P` applied after `Qh.obj P ⊗^L -` is the left derived functor of
`K(C) ─P ⊗ -─▶ K(C) ─Qh─▶ D(C) ─R H_P─▶ D(C)`, for the 2-cell
```
K(C) ──P ⊗ -──▶ K(C) ──Qh──▶ D(C)
 │                            │
 Qh             ⇙             R H_P
 ▼                            ▼
D(C) ─Qh P ⊗ᴸ -─▶ D(C) ─R H_P─▶ D(C)
```
obtained by whiskering `tensorLeftQhObjCounit P` with `R H_P`. It holds because
`tensorLeftQhObjCounit P` is an isomorphism at K-flat complexes. -/
lemma isLeftDerivedFunctor_tensorLeft_comp_internalHomQhObj :
    (tensorLeft (Qh.obj P) ⋙ internalHomQhObj P).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (tensorLeftQhObjCounit P) (internalHomQhObj P))
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).localizerMorphismKFlat
    |>.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure _
      (fun Z ↦ isIso_tensorLeftQhObjCounit_app P Z.1 Z.2) _

/-- The second absoluteness hypothesis of `Adjunction.derived` for `P ⊗ - ⊣ iHom P -`:
`Qh.obj P ⊗^L -` applied after `R H_P` is the right derived functor of
`K(C) ─iHom P -─▶ K(C) ─Qh─▶ D(C) ─Qh P ⊗ᴸ -─▶ D(C)`, for the 2-cell
```
K(C) ─iHom P -─▶ K(C) ──Qh──▶ D(C)
 │                             │
 Qh              ⇗             Qh P ⊗ᴸ -
 ▼                             ▼
D(C) ──R H_P──▶ D(C) ─Qh P ⊗ᴸ -─▶ D(C)
```
obtained by whiskering `internalHomQhObjUnit P` with `Qh.obj P ⊗^L -`. It holds because
`internalHomQhObjUnit P` is an isomorphism at K-injective complexes. -/
lemma isRightDerivedFunctor_internalHomQhObj_comp_tensorLeft :
    (internalHomQhObj P ⋙ tensorLeft (Qh.obj P)).IsRightDerivedFunctor
      (Functor.whiskerRight (internalHomQhObjUnit P) (tensorLeft (Qh.obj P)) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.KInjectives.localizerMorphism C)
    |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
      (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
        _).isIso_of_isRightDerivedFunctor _ I) _

/-- The derived tensor-hom adjunction `Qh.obj P ⊗^L - ⊣ R H_P`, obtained by deriving the
tensor-hom adjunction `P ⊗ - ⊣ H_P` of the homotopy category, where `H_P = iHom P -`.
The two absoluteness hypotheses of `Adjunction.derived` are
`isLeftDerivedFunctor_tensorLeft_comp_internalHomQhObj` and
`isRightDerivedFunctor_internalHomQhObj_comp_tensorLeft`. -/
noncomputable def tensorHomAdjunctionQhObj :
    tensorLeft (Qh.obj P) ⊣ internalHomQhObj P :=
  have := isLeftDerivedFunctor_tensorLeft_comp_internalHomQhObj P
  have := isRightDerivedFunctor_internalHomQhObj_comp_tensorLeft P
  (HomotopyCategory.tensorHomAdjunction P).derived
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (tensorLeftQhObjCounit P) (internalHomQhObjUnit P)

variable (C) in
/-- The derived category of a monoidal closed Grothendieck abelian category is monoidal
closed for the derived tensor product, provided K-flat complexes form a left derivability
structure (which holds whenever `Abelian.HasFunctorialFlatResolution C` does): for every
`X : DerivedCategory C`, the functor `X ⊗^L -` admits a right adjoint.

The right adjoint `ihom X` is `R H_P` for the noncanonical choice `P := Qh.objPreimage X`.
Its adjunction is `tensorHomAdjunctionQhObj P`, transported along the natural isomorphism
`Qh.obj P ⊗^L - ≅ X ⊗^L -` that `tensoringLeft` induces from `Qh.objObjPreimageIso X`. -/
noncomputable instance monoidalClosed : MonoidalClosed (DerivedCategory C) where
  closed X :=
    { rightAdj := internalHomQhObj (Qh.objPreimage X)
      adj := (tensorHomAdjunctionQhObj (Qh.objPreimage X)).ofNatIsoLeft
        ((tensoringLeft _).mapIso (Qh.objObjPreimageIso X)) }

end DerivedCategory

/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!

# Derived complete objects of the derived category of sheaves of modules

Let `(C, J)` be an (essentially small) site, let `R` be a commutative ring and let `I` be
an ideal of `R`, the intended case being that `R` is `I`-adically complete — for instance
the ring of integers `𝒪_E` of a finite extension of `ℚ_ℓ`, with `I` its maximal ideal.
This file defines what it means for an object `K` of the derived category

```
  D(J, R) := DerivedCategory (Sheaf J (ModuleCat R))
```

of sheaves of `R`-modules on `(C, J)` to be *derived complete*: that `K` is the homotopy
limit `R lim` of its reductions `K ⊗ᴸ R/Iⁿ` (Stacks, Tags 091N and 091Z).

The tower of reductions and the maps into it are built as a chain of cones, each the image
of the previous one under a functor:

* `Ideal.quotPowCone I`, the quotient maps `R ⟶ R ⧸ Iⁿ`, a cone over the tower
  `Ideal.quotPowFunctor I` in `ModuleCat R` whose point is the monoidal unit
  `𝟙_ (ModuleCat R) = R`. If `R` is `I`-adically complete this cone is a limit cone
  (`Ideal.isLimitQuotPowCone`), which is the classical completeness of `R` in the language
  of limits;
* `CategoryTheory.Sheaf.quotPowCone J I`, its image under `constantSheaf J (ModuleCat R)`,
  whose point is the monoidal unit of `Sheaf J (ModuleCat R)`, the constant sheaf on
  `R = 𝟙_ (ModuleCat R)` being that unit;
* `DerivedCategory.quotPowCone J I`, the image of the previous cone under
  `DerivedCategory.singleFunctor _ 0` — a cone over the tower
  `DerivedCategory.quotPowFunctor J I` — whose point is moved to the monoidal unit
  `𝟙_ D(J, R)` along `DerivedCategory.εSingleFunctorZero : 𝟙_ D(J, R) ⟶ (R in degree 0)`
  (the unit comparison of `DerivedCategory.sheafTensorStructure`);
* `DerivedCategory.derivedCompletionCone J I K`, the image of the previous cone under
  `K ⊗ᴸ -` — a cone over the tower `DerivedCategory.derivedCompletionDiagram J I K` —
  whose point is moved to `K` itself along the inverse right unitor
  `K ≅ K ⊗ᴸ 𝟙_ D(J, R)`. Its legs are therefore the reduction maps `K ⟶ K ⊗ᴸ R/Iⁿ`, and
  its point is `K`.

The object `K` is *derived complete* when this last cone is a homotopy limit
(`CategoryTheory.Pretriangulated.IsHomotopyLimit`), i.e. when its legs induce an isomorphism

```
  K ≅ R lim_n (K ⊗ᴸ R/Iⁿ)
```

onto the homotopy limit of the tower: the triangle
`K ⟶ ∏ₙ K ⊗ᴸ R/Iⁿ ──1 - t──▶ ∏ₙ K ⊗ᴸ R/Iⁿ ⟶ K⟦1⟧` is distinguished (the Milnor triangle,
Stacks, Tag 08TB). The homotopy limit is not the categorical limit of the tower, which need
not exist in a triangulated category and, when it exists, is not the derived limit.
Derived completeness of `K` does not presuppose completeness of `R`, and the definition does
not assume `IsAdicComplete I R`.

## Main definitions

- `Ideal.quotPowFunctor` and `Ideal.quotPowCone` : the tower `n ↦ R ⧸ Iⁿ` in `ModuleCat R`
  and the cone over it given by the quotient maps out of the monoidal unit.
- `CategoryTheory.Sheaf.quotPowFunctor` and `CategoryTheory.Sheaf.quotPowCone` : the same
  tower and cone in the category of sheaves of `R`-modules, through the constant sheaf
  functor.
- `DerivedCategory.TensorStructure` and `DerivedCategory.sheafTensorStructure` : the derived
  tensor product of `D(J, R)` with its additivity, linearity, compatibility with shifts and
  triangulatedness in each variable, bundled once (see the implementation notes).
- `DerivedCategory.quotPowFunctor` and `DerivedCategory.quotPowCone` : the tower
  `n ↦ R/Iⁿ` in the derived category and the cone over it out of the monoidal unit.
- `DerivedCategory.derivedCompletionDiagram` : the tower `n ↦ K ⊗ᴸ R/Iⁿ` of reductions
  of `K`.
- `DerivedCategory.derivedCompletionCone` : the cone `K ⟶ K ⊗ᴸ R/Iⁿ`, with point `K`.
- `DerivedCategory.derivedComplete` : the object property of being derived complete.

## Main results

- `Ideal.isLimitQuotPowCone` : if `R` is `I`-adically complete then `R` is the limit of the
  tower `n ↦ R ⧸ Iⁿ`.
- `DerivedCategory.derivedComplete_iff_exists_iso` : given any homotopy limit
  `R lim_n (K ⊗ᴸ R/Iⁿ)` of the tower, `K` is derived complete exactly when it is isomorphic
  to it compatibly with the reduction maps.

## Implementation notes

Mathlib's `IsAdicComplete` API is phrased in terms of the quotients `M ⧸ (Iⁿ • ⊤)` of a
module `M`, whereas the tower here is phrased in terms of the ideal quotients `R ⧸ Iⁿ`,
which is the form in which it is tensored downstream. The two are compared by
`Ideal.quotSmulTopEquiv`, which is where `Iⁿ • (⊤ : Submodule R R) = Iⁿ` is used; every
compatibility with it holds by `rfl`, both sides being quotients of `R` by propositionally
equal submodules.

Every piece of structure the constructions below need is found by instance search, for any
essentially small site and with no local activation or hypothesis: `Sheaf J (ModuleCat R)`
is Grothendieck abelian and has a derived category; it is monoidal by
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall` (the
sheafification of the objectwise tensor product) and monoidal closed by
`…monoidalClosed_sheaf_of_essentiallySmall` (Day's reflection theorem); and it has
functorial flat resolutions because `ModuleCat R` does
(`ModuleCat.hasFunctorialFlatResolution`), which through
`DerivedCategory.hasDerivedMonoidalCategory` supplies the K-flat derived monoidal structure
`DerivedCategory.Qh.HasDerivedMonoidalCategory` and hence the monoidal structure of
`DerivedCategory (Sheaf J (ModuleCat R))`.

That convenience has a cost which the declarations below are written to avoid, and which is
the reason `DerivedCategory.derivedCompletionDiagram` exists as a definition of its own.
The elaborated `MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat R)))` instance is an
expression carrying `HasSheafify`, `IsGrothendieckAbelian`, `MonoidalPreadditive` and
`Qh.HasDerivedMonoidalCategory` proofs inside it. When such an expression occurs in the
*declared type* of a definition, `Lean.Meta.abstractNestedProofs` — which lifts the proofs
occurring in a definition's **value** into auxiliary theorems, but does not touch its
declared type — makes the inferred and the declared type differ in every one of those proof
positions; the kernel then has to reconcile them through proof irrelevance, which means
comparing propositions whose own instance arguments differ in the same way, and the descent
fans out. In practice it does not terminate: stating `derivedCompletionCone` directly over
`DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K` does not compile even with `sorry` for
its value, whereas the version below, whose type mentions only the constant
`DerivedCategory.derivedCompletionDiagram` applied to `J`, `I` and `K`, compiles in a few
seconds. Keeping the monoidal structure of the derived category inside definition *bodies*
and out of the types stated here is what makes this file check; the `Aux` section above
does the same for `DerivedCategory.εSingleFunctorZero`.

The same mechanism also makes the *bodies* expensive to compare with freshly elaborated
terms: elaborating a definition abstracts the proofs nested in the monoidal instance, so the
instance in the body of `derivedCompletionDiagram` is no longer syntactically the one
elaborated in a later file, and unfolding it there makes the kernel run the same descent.
For this reason the monoidal structure used here is not the one found by instance search at
each use, but the field `monoidalCategory` of the constant
`DerivedCategory.sheafTensorStructure J R`, which bundles once the derived monoidal structure
together with the instances the proofs about derived completeness need (additivity and
`R`-linearity in each variable, compatibility with shifts, triangulatedness). Files proving
results about derived completeness use the fields of this constant as their instances, so
that every comparison is between applications of the same constant.
The constant is the specialization of `DerivedCategory.tensorStructure`, which is built for an
arbitrary category `A`: building the structure directly for sheaves would check its fields
against types containing the concrete monoidal instance, with the same cost.

-/

@[expose] public section

universe w v' u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The tower `n ↦ R ⧸ Iⁿ` of quotients by the powers of an ideal `I`, as a functor
`ℕᵒᵖ ⥤ ModuleCat R`. The transition map attached to `m ≤ n` is the projection
`R ⧸ Iⁿ ⟶ R ⧸ Iᵐ`. -/
noncomputable def quotPowFunctor : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (R ⧸ I ^ n.unop)
  map f := ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right (leOfHom f.unop)))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The tower `n ↦ R ⧸ Iⁿ` together with the quotient maps out of `R`, as a cone whose
point is the monoidal unit `𝟙_ (ModuleCat R) = R`. -/
noncomputable def quotPowCone : Cone (quotPowFunctor I) where
  pt := 𝟙_ (ModuleCat.{u} R)
  π :=
    { app n := ModuleCat.ofHom (Submodule.mkQ (I ^ n.unop))
      naturality _ _ _ := by ext; rfl }

/-- The quotient `R ⧸ (Iⁿ • ⊤)` used by mathlib's `IsAdicComplete` API is the quotient
`R ⧸ Iⁿ` used by `Ideal.quotPowFunctor`: the submodule `Iⁿ • (⊤ : Submodule R R)` is the
ideal `Iⁿ`. -/
noncomputable def quotSmulTopEquiv (n : ℕ) :
    (R ⧸ (I ^ n • ⊤ : Submodule R R)) ≃ₗ[R] (R ⧸ I ^ n) :=
  Submodule.quotEquivOfEq _ _ (by simp)

variable {I}

/-- The family of maps into the mathlib model `R ⧸ (Iⁿ • ⊤)` of the tower attached to a
cone over `Ideal.quotPowFunctor`; this is the input of `IsAdicComplete.lift`. -/
noncomputable def quotPowConeFamily (s : Cone (quotPowFunctor I)) (n : ℕ) :
    s.pt →ₗ[R] R ⧸ (I ^ n • ⊤ : Submodule R R) :=
  (quotSmulTopEquiv I n).symm.toLinearMap ∘ₗ (s.π.app (op n)).hom

lemma quotPowConeFamily_compat (s : Cone (quotPowFunctor I)) {m n : ℕ} (hle : m ≤ n) :
    Submodule.factorPow I R hle ∘ₗ quotPowConeFamily s n = quotPowConeFamily s m := by
  have hs : Submodule.factor (Ideal.pow_le_pow_right hle) ∘ₗ (s.π.app (op n)).hom
      = (s.π.app (op m)).hom :=
    congrArg ModuleCat.Hom.hom (s.w (op (homOfLE hle) : (op n : ℕᵒᵖ) ⟶ op m))
  have h : Submodule.factorPow I R hle ∘ₗ (quotSmulTopEquiv I n).symm.toLinearMap =
      (quotSmulTopEquiv I m).symm.toLinearMap ∘ₗ
        Submodule.factor (Ideal.pow_le_pow_right hle) := by
    ext; rfl
  rw [quotPowConeFamily, quotPowConeFamily, ← LinearMap.comp_assoc, h, LinearMap.comp_assoc,
    hs]

variable (I) [IsAdicComplete I R]

/-- If `R` is `I`-adically complete, then `R` is the limit of the tower `n ↦ R ⧸ Iⁿ` along
the quotient maps. This is `IsAdicComplete` in the language of limits of `R`-modules: the
lift is `IsAdicComplete.lift` and its uniqueness is `IsAdicComplete.eq_lift`. -/
noncomputable def isLimitQuotPowCone : IsLimit (quotPowCone I) where
  lift s := ModuleCat.ofHom
    (IsAdicComplete.lift I (quotPowConeFamily s) (quotPowConeFamily_compat s))
  fac s n := by
    ext x
    exact (quotSmulTopEquiv I n.unop).symm.injective
      (IsAdicComplete.mk_lift I (quotPowConeFamily_compat s) n.unop x)
  uniq s m hm := by
    ext x
    refine congrFun (congrArg _ (IsAdicComplete.eq_lift I (quotPowConeFamily_compat s)
      (F := m.hom) fun n ↦ ?_)) x
    have h : (quotSmulTopEquiv I n).symm.toLinearMap ∘ₗ Submodule.mkQ (I ^ n) =
        Submodule.mkQ (I ^ n • ⊤ : Submodule R R) := by ext; rfl
    rw [quotPowConeFamily, ← congrArg ModuleCat.Hom.hom (hm (op n)), ← h]
    rfl

end Ideal

section Aux

variable (A : Type u') [Category.{v'} A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{w} A]
  [DerivedCategory.Qh.HasDerivedMonoidalCategory
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- The comparison from the monoidal unit of the derived category of `A` to the monoidal
unit of `A` placed in degree `0`. It is the unit of the lax monoidal structure of the
localization functor `Q`: the monoidal unit of `CochainComplex A ℤ` is by definition the
unit of `A` in degree `0`, and `Q` of a complex concentrated in degree `0` is by definition
`DerivedCategory.singleFunctor A 0` of its value.

This is the only place where the monoidal structure on cochain complexes appears. Stating
it here, for a variable `A`, keeps the definitional unfolding of `𝟙_ (CochainComplex A ℤ)`
out of the concrete sheaf-theoretic terms below, where checking it is prohibitively
expensive. -/
noncomputable def DerivedCategory.εSingleFunctorZero :
    𝟙_ (DerivedCategory A) ⟶ (DerivedCategory.singleFunctor A 0).obj (𝟙_ A) :=
  Functor.LaxMonoidal.ε DerivedCategory.Q

end Aux

/-- The structure of the derived category `D(A)` of a monoidal abelian category `A` used to
state derived completeness: a monoidal structure on `D(A)` which is additive and `R`-linear
in each variable, which commutes with the shifts in both variables
(`Functor.CommShift₂Int`, with the usual sign) and is triangulated in each variable, together
with an isomorphism `ε` from its unit to the unit of `A` placed in degree `0`.

Bundling these instances is an implementation device; see the implementation notes. The
structure for sheaves of modules is `DerivedCategory.sheafTensorStructure`, made of the
derived tensor product and of `DerivedCategory.εSingleFunctorZero`. -/
structure DerivedCategory.TensorStructure (A : Type u') [Category.{v'} A] [Abelian A]
    [HasDerivedCategory.{w} A] [MonoidalCategory A] (R : Type*) [Ring R] [Linear R A] where
  /-- The monoidal structure of `D(A)`. -/
  [monoidalCategory : MonoidalCategory (DerivedCategory A)]
  /-- The tensor product of `D(A)` is additive in each variable. -/
  [monoidalPreadditive : MonoidalPreadditive (DerivedCategory A)]
  /-- The tensor product of `D(A)` is `R`-linear in each variable. -/
  [monoidalLinear : MonoidalLinear R (DerivedCategory A)]
  /-- The tensor product of `D(A)` commutes with the shifts in both variables. -/
  [commShift₂ : (curriedTensor (DerivedCategory A)).CommShift₂Int]
  /-- The functors `K ⊗ -` are triangulated. -/
  [isTriangulated_tensorLeft (K : DerivedCategory A) :
    ((curriedTensor (DerivedCategory A)).obj K).IsTriangulated]
  /-- The functors `- ⊗ K` are triangulated. -/
  [isTriangulated_tensorRight (K : DerivedCategory A) :
    ((curriedTensor (DerivedCategory A)).flip.obj K).IsTriangulated]
  /-- The comparison from the unit of `D(A)` to the unit of `A` placed in degree `0`. -/
  ε : 𝟙_ (DerivedCategory A) ⟶ (DerivedCategory.singleFunctor A 0).obj (𝟙_ A)
  [isIso_ε : IsIso ε]

section TensorStructure

variable (A : Type u') [Category.{v'} A] [Abelian A] [IsGrothendieckAbelian.{v'} A]
  [HasDerivedCategory.{v'} A] [MonoidalCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
  [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  (R : Type*) [Ring R] [Linear R A] [MonoidalLinear R A]

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

/-- The derived tensor product of a monoidal closed braided Grothendieck abelian category `A`
with functorial flat resolutions, as a `DerivedCategory.TensorStructure`: the monoidal
structure of `DerivedCategory A`, its additivity and linearity
(`DerivedCategory.monoidalPreadditive`, `DerivedCategory.monoidalLinear`), its commutation
with shifts (`DerivedCategory.commShift₂CurriedTensor`) and triangulatedness
(`DerivedCategory.isTriangulated_tensorLeft` and `…Right`), and the unit comparison
`DerivedCategory.εSingleFunctorZero`. -/
noncomputable def DerivedCategory.tensorStructure : DerivedCategory.TensorStructure.{v'} A R where
  ε := DerivedCategory.εSingleFunctorZero.{v'} A
  isIso_ε := by
    have : IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := A))) :=
      inferInstanceAs (IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))))
    change IsIso ((Functor.LaxMonoidal.ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map
      (Functor.LaxMonoidal.ε (HomotopyCategory.quotient A (ComplexShape.up ℤ)))) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app _)
    infer_instance

end TensorStructure

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

variable (R) in
/-- The derived tensor product of `D(J, R) = DerivedCategory (Sheaf J (ModuleCat R))`, as a
`DerivedCategory.TensorStructure`: the instance of `DerivedCategory.tensorStructure` for the
category of sheaves of `R`-modules. -/
noncomputable def DerivedCategory.sheafTensorStructure :
    DerivedCategory.TensorStructure (Sheaf J (ModuleCat.{u + 1} R)) R :=
  DerivedCategory.tensorStructure _ R

/-- The tower `n ↦ R/Iⁿ` of constant sheaves of `R`-modules on a site, the image of the
tower `Ideal.quotPowFunctor` under the constant sheaf functor. -/
noncomputable def CategoryTheory.Sheaf.quotPowFunctor : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{u + 1} R) :=
  Ideal.quotPowFunctor I ⋙ constantSheaf J (ModuleCat.{u + 1} R)

/-- The tower `n ↦ R/Iⁿ` of constant sheaves together with the quotient maps out of the
monoidal unit, the image of `Ideal.quotPowCone` under the constant sheaf functor. Its point
is `𝟙_ (Sheaf J (ModuleCat R))`, since the constant sheaf on `R = 𝟙_ (ModuleCat R)` is the
monoidal unit of the sheaf category. -/
noncomputable def CategoryTheory.Sheaf.quotPowCone : Cone (Sheaf.quotPowFunctor J I) :=
  (constantSheaf J (ModuleCat.{u + 1} R)).mapCone (Ideal.quotPowCone I)

@[simp]
lemma CategoryTheory.Sheaf.quotPowCone_pt :
    (Sheaf.quotPowCone J I).pt = 𝟙_ (Sheaf J (ModuleCat.{u + 1} R)) := rfl

section Derived

/-- The tower `n ↦ R/Iⁿ` of constant sheaves, viewed in the derived category of sheaves of
`R`-modules through `DerivedCategory.singleFunctor _ 0`. -/
noncomputable def DerivedCategory.quotPowFunctor :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  Sheaf.quotPowFunctor J I ⋙ DerivedCategory.singleFunctor _ 0

/-- The tower `n ↦ R/Iⁿ` in the derived category together with the maps out of the monoidal
unit `𝟙_ D(J, R)`: the cone `Sheaf.quotPowCone` pushed into the derived category by
`DerivedCategory.singleFunctor _ 0`, its point moved from `R` in degree `0` to `𝟙_ D(J, R)`
along the unit comparison `ε` of `DerivedCategory.sheafTensorStructure`, which is
`DerivedCategory.εSingleFunctorZero`. -/
noncomputable def DerivedCategory.quotPowCone : Cone (DerivedCategory.quotPowFunctor J I) :=
  ((DerivedCategory.singleFunctor _ 0).mapCone (Sheaf.quotPowCone J I)).extend
    (DerivedCategory.sheafTensorStructure J R).ε

@[simp]
lemma DerivedCategory.quotPowCone_pt :
    letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
    (DerivedCategory.quotPowCone J I).pt = 𝟙_ (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  rfl

/-- The tower `n ↦ K ⊗ᴸ R/Iⁿ` of reductions of an object `K` of the derived category, the
image of `DerivedCategory.quotPowFunctor` under `K ⊗ᴸ -`.

This is a definition of its own, rather than `DerivedCategory.quotPowFunctor J I ⋙
tensorLeft K` spelled out at each use site, so that the monoidal structure of the derived
category stays out of the *types* of the declarations below; see the implementation notes.
Downstream statements should be phrased in terms of the diagram. -/
noncomputable def DerivedCategory.derivedCompletionDiagram
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
  DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K

/-- The reduction maps `K ⟶ K ⊗ᴸ R/Iⁿ`, as a cone over the tower
`DerivedCategory.derivedCompletionDiagram` **whose point is `K` itself**: the cone
`DerivedCategory.quotPowCone` tensored on the left with `K`, its point moved from
`K ⊗ᴸ 𝟙_ D(J, R)` to `K` along the inverse right unitor. -/
noncomputable def DerivedCategory.derivedCompletionCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (DerivedCategory.derivedCompletionDiagram J I K) :=
  letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
  ((tensorLeft K).mapCone (DerivedCategory.quotPowCone J I)).extend (ρ_ K).inv

@[simp]
lemma DerivedCategory.derivedCompletionCone_pt
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    (DerivedCategory.derivedCompletionCone J I K).pt = K := rfl

/-- Derived complete objects (Stacks 091S), for sheaves of modules over the constant ring `R` on a
site; the repository realises the integral stage `D(Y, 𝒪_E)` on the small étale site with `R = 𝒪_E`,
`I = 𝔪_E` (`DerivedCategory.derivedCompleteIntegral`). The blueprint's tower `(K ⊗ᴸ A_{E,n})_n` and
its derived limit (Roos/Milnor triangle) are `DerivedCategory.derivedCompletionCone` and
`CategoryTheory.Pretriangulated.IsHomotopyLimit`.

An object `K` of the derived category of sheaves of `R`-modules on `(C, J)` is *derived
complete* with respect to the ideal `I` if the reduction maps `K ⟶ K ⊗ᴸ R/Iⁿ` of
`DerivedCategory.derivedCompletionCone` exhibit `K` as the homotopy limit of the tower of
reductions:

```
  K ≅ R lim_n (K ⊗ᴸ R/Iⁿ)
```

(Stacks, Tags 091N and 091Z). Here `R lim` is the homotopy limit of
`CategoryTheory.Pretriangulated.IsHomotopyLimit`: the condition is that, for a product
`∏ₙ K ⊗ᴸ R/Iⁿ` with transition endomorphism `t`, the triangle

```
  K ⟶ ∏ₙ K ⊗ᴸ R/Iⁿ ──1 - t──▶ ∏ₙ K ⊗ᴸ R/Iⁿ ⟶ K⟦1⟧
```

whose first map is induced by the reduction maps is distinguished (the Milnor triangle,
Stacks, Tag 08TB). This is not the categorical limit of the tower in the derived category,
which in general does not exist. The intended setting is that `R` is `I`-adically complete,
which by `Ideal.isLimitQuotPowCone` says that `R` is itself the limit of the tower
`n ↦ R/Iⁿ`; the definition does not need that hypothesis. For a principal ideal generated by
a nonzerodivisor, derived completeness is characterised by the vanishing of maps from objects
on which the generator acts invertibly, see
`DerivedCategory.derivedComplete_iff_rightOrthogonal`. -/
def DerivedCategory.derivedComplete :
    ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  fun K ↦ Pretriangulated.IsHomotopyLimit (DerivedCategory.derivedCompletionCone J I K)

namespace DerivedCategory

variable {J I}

lemma derivedComplete_iff (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    derivedComplete J I K ↔ Pretriangulated.IsHomotopyLimit (derivedCompletionCone J I K) :=
  Iff.rfl

/-- Given a homotopy limit `c` of the tower of reductions `K ⊗ᴸ R/Iⁿ`, the object `K` is
derived complete if and only if it is isomorphic to `c.pt = R lim_n (K ⊗ᴸ R/Iⁿ)` compatibly
with the maps to the reductions. -/
lemma derivedComplete_iff_exists_iso (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    {c : Cone (derivedCompletionDiagram J I K)} (hc : Pretriangulated.IsHomotopyLimit c) :
    derivedComplete J I K ↔ ∃ e : K ≅ c.pt,
      ∀ n : ℕ, e.hom ≫ c.π.app (op n) = (derivedCompletionCone J I K).π.app (op n) :=
  ⟨fun h ↦ h.exists_iso hc, fun ⟨e, he⟩ ↦ hc.of_iso (Iso.refl _) _ e.symm fun n ↦ by
    simp [← he]⟩

end DerivedCategory

end Derived

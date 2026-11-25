/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The eight curve-cohomology assertions

Let `k` be an algebraically closed field, `X` a separated `k`-scheme of finite type of
dimension at most one (`AlgebraicGeometry.IsCurve`), and `F` a torsion étale sheaf on `X`.
The proof of proper base change for the projective line rests on eight assertions
`C₁(X, F), …, C₈(X, F)` about the étale cohomology `Hᵠ(X, F)`:

1. `Hᵠ(X, F) = 0` for `q > 2`;
2. `Hᵠ(X, F) = 0` for `q > 1` when `X` is affine;
3. `Hᵠ(X, F) = 0` for `q > 1` when `char k = p > 0` and `F` is `p`-primary;
4. `Hᵠ(X, F)` is finite when `F` is constructible with torsion prime to `char k`;
5. `Hᵠ(X, F)` is finite when `X` is proper and `F` is constructible;
6. `Hᵠ(X, F) ⟶ Hᵠ(X_{k'}, F|)` is bijective for every algebraically closed extension `k'/k`
   when the torsion of `F` is prime to `char k`;
7. the same map is bijective when `X` is proper, with no restriction on the torsion;
8. `H²(X, F) ⟶ H²(W, F|_W)` is surjective for every open `W ⊆ X`.

They are bundled in `AlgebraicGeometry.IsCurve.Assertions`. The coefficient sheaf is a
sheaf of `Λ`-modules and `Hᵠ(X, F)` is the cohomology of its underlying abelian sheaf; the
torsion conditions are conditions on the geometric stalks
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf`,
`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder`). The field extension in `C₆` and
`C₇` is given by an arbitrary cartesian square

```
X' --ι'--> X
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

## Main definitions

- `AlgebraicGeometry.Scheme.IsPrimaryTorsionSheaf`: a sheaf whose geometric stalks are
  `p`-primary torsion groups.
- `AlgebraicGeometry.IsCurve.VanishingAboveTwo`, …,
  `AlgebraicGeometry.IsCurve.SurjectiveRestrictionTwo`: the eight assertions `C₁, …, C₈`, each
  as a separate predicate.
- `AlgebraicGeometry.IsCurve.Assertions`: the conjunction `C(X, F)` of the eight assertions.

The constructibility hypothesis of `C₄` and `C₅` (blueprint: `def-weil-pbc-constructible-torsion`)
is `AlgebraicGeometry.Scheme.IsConstructibleSheaf`: a finite stratification of `X` by locally
closed constructible subschemes on each of which `F` is locally constant with finite stalks.
The pullback map of `C₆` and `C₇` (blueprint: `theorem-cohomology-curves--7`) is
`AlgebraicGeometry.Etale.cohomologyMap`.

## Main statements

- `AlgebraicGeometry.IsCurve.assertions_iff`: `C(X, F)` holds if and only if each of the eight
  assertions `C₁(X, F), …, C₈(X, F)` holds.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A sheaf `F` of `Λ`-modules on the small étale site of `X` is *`p`-primary torsion* if
every element of every geometric stalk of `F` is killed by a power of `p`
(blueprint: `def-weil-pbc-primary-torsion`; the companion condition *prime to `p`* is
`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder (Spec k)`). -/
def Scheme.IsPrimaryTorsionSheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (p : ℕ) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (x : ↥((pointSmallEtale s).sheafFiber.obj F)), ∃ n : ℕ, p ^ n • x = 0

namespace IsCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- **Assertion `C₁`**: `Hᵠ(X, F) = 0` for every `q > 2`, where `Hᵠ(X, F)` is the cohomology of
the underlying abelian sheaf of `F`. (blueprint: `theorem-cohomology-curves--1`) -/
def VanishingAboveTwo : Prop :=
  ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)

/-- **Assertion `C₂`**: if `X` is affine, then `Hᵠ(X, F) = 0` for every `q > 1`.
(blueprint: `theorem-cohomology-curves--2`) -/
def VanishingAboveOneOfIsAffine : Prop :=
  ∀ [IsAffine X] (q : ℕ), 1 < q → Subsingleton (Sheaf.H
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)

/-- **Assertion `C₃`**: for a field `k`, if `char k = p > 0` and `F` is
`p`-primary torsion, then `Hᵠ(X, F) = 0` for every `q > 1`. (blueprint:
`theorem-cohomology-curves--3`) -/
def VanishingAboveOneOfIsPrimaryTorsionSheaf (k : Type u) [Field k] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP k p], Scheme.IsPrimaryTorsionSheaf Λ F p →
    ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)

/-- **Assertion `C₄`**: for a field `k`, if `F` is constructible with
torsion prime to `char k`, then every `Hᵠ(X, F)` is finite. (blueprint:
`theorem-cohomology-curves--4`) -/
def FiniteOfInvertibleOrder (k : Type u) [Field k] : Prop :=
  ∀ [Scheme.IsConstructibleSheaf F] [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F]
    (q : ℕ), Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)

/-- **Assertion `C₅`**: if `f : X ⟶ Spec k` is proper and `F` is constructible, then every
`Hᵠ(X, F)` is finite. (blueprint: `theorem-cohomology-curves--5`) -/
def FiniteOfIsProper : Prop :=
  ∀ [IsProper f] [Scheme.IsConstructibleSheaf F] (q : ℕ), Finite (Sheaf.H
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)

/-- **Assertion `C₆`**: if the torsion of `F` is prime to `char k`, then for every
algebraically closed extension `k'/k`, given by a cartesian square
`X' ⟶ X, X' ⟶ Spec k', Spec k' ⟶ Spec k` over `f`, the pullback map
`Hᵠ(X, F) ⟶ Hᵠ(X', F|_{X'})` (blueprint: `theorem-cohomology-curves--7`) is bijective for
every `q`. (blueprint: `theorem-cohomology-curves--6`) -/
def BaseChangeOfInvertibleOrder : Prop :=
  ∀ [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F]
    (k' : Type u) [Field k'] [IsAlgClosed k'] {X' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : X' ⟶ Spec (.of k')} {ι' : X' ⟶ X}, IsPullback ι' f' f ι → ∀ q : ℕ,
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)

/-- **Assertion `C₇`**: if `f : X ⟶ Spec k` is proper, then for every algebraically closed
extension `k'/k`, given by a cartesian square over `f`, the pullback map
`Hᵠ(X, F) ⟶ Hᵠ(X', F|_{X'})` (blueprint: `theorem-cohomology-curves--7`) is bijective for
every `q`, without a restriction on the torsion of `F`. (blueprint:
`theorem-cohomology-curves--7`) -/
def BaseChangeOfIsProper : Prop :=
  ∀ [IsProper f]
    (k' : Type u) [Field k'] [IsAlgClosed k'] {X' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : X' ⟶ Spec (.of k')} {ι' : X' ⟶ X}, IsPullback ι' f' f ι → ∀ q : ℕ,
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)

/-- **Assertion `C₈`**: for every open immersion `a : W ⟶ X`, the restriction map
`H²(X, F) ⟶ H²(W, a⁻¹F)` is surjective. (blueprint: `theorem-cohomology-curves--8`) -/
def SurjectiveRestrictionTwo : Prop :=
  ∀ {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a],
    Function.Surjective (Etale.cohomologyMap a
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) 2)

end IsCurve

/-- **The eight curve-cohomology assertions** `C(X, F) = C₁(X, F) ∧ ⋯ ∧ C₈(X, F)` for a
`k`-scheme `f : X ⟶ Spec k` and a sheaf `F` of `Λ`-modules on `X_ét`, where `Hᵠ(X, F)` is the
cohomology of the underlying abelian sheaf of `F`. They are meant for `k` algebraically
closed, `X` a curve over `k` (`AlgebraicGeometry.IsCurve`) and `F` torsion; each field
carries the hypotheses of the corresponding assertion.
(blueprint: `theorem-cohomology-curves`) -/
structure IsCurve.Assertions {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop where
  /-- `C₁`: `Hᵠ(X, F) = 0` for `q > 2`. -/
  subsingleton_of_two_lt (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₂`: `Hᵠ(X, F) = 0` for `q > 1` when `X` is affine. -/
  subsingleton_of_one_lt_of_isAffine [IsAffine X] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₃`: `Hᵠ(X, F) = 0` for `q > 1` when `char k = p > 0` and `F` is `p`-primary. -/
  subsingleton_of_one_lt_of_isPrimaryTorsionSheaf (p : ℕ) [Fact p.Prime] [CharP k p]
    (hF : Scheme.IsPrimaryTorsionSheaf Λ F p) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₄`: `Hᵠ(X, F)` is finite when `F` is constructible with torsion prime to `char k`. -/
  finite_of_isTorsionSheafOfInvertibleOrder [Scheme.IsConstructibleSheaf F]
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F] (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₅`: `Hᵠ(X, F)` is finite when `X` is proper and `F` is constructible. -/
  finite_of_isProper [IsProper f] [Scheme.IsConstructibleSheaf F] (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₆`: the pullback `Hᵠ(X, F) ⟶ Hᵠ(X_{k'}, F|)` is bijective for every algebraically
  closed extension `k'/k` when the torsion of `F` is prime to `char k`. -/
  bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F]
    (k' : Type u) [Field k'] [IsAlgClosed k'] {X' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : X' ⟶ Spec (.of k')} {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₇`: the pullback `Hᵠ(X, F) ⟶ Hᵠ(X_{k'}, F|)` is bijective for every algebraically
  closed extension `k'/k` when `X` is proper. -/
  bijective_cohomologyMap_of_isProper [IsProper f]
    (k' : Type u) [Field k'] [IsAlgClosed k'] {X' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : X' ⟶ Spec (.of k')} {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
  /-- `C₈`: the restriction `H²(X, F) ⟶ H²(W, F|_W)` is surjective for every open
  immersion `a : W ⟶ X`. -/
  surjective_cohomologyMap_of_isOpenImmersion {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a] :
    Function.Surjective (Etale.cohomologyMap a
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) 2)

/-- **Detailed form of the eight curve-cohomology assertions**: `C(X, F)` is the conjunction
of the eight assertions `C₁(X, F), …, C₈(X, F)`.
(blueprint: `theorem-cohomology-curves`,
`sk-curve-calculations-pbc-for-the-projective-line--remark-1`) -/
theorem IsCurve.assertions_iff {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsCurve.Assertions Λ f F ↔
      IsCurve.VanishingAboveTwo Λ F ∧ IsCurve.VanishingAboveOneOfIsAffine Λ F ∧
        IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf Λ F k ∧
        IsCurve.FiniteOfInvertibleOrder Λ F k ∧ IsCurve.FiniteOfIsProper Λ f F ∧
        IsCurve.BaseChangeOfInvertibleOrder Λ f F ∧ IsCurve.BaseChangeOfIsProper Λ f F ∧
        IsCurve.SurjectiveRestrictionTwo Λ F :=
  ⟨fun h ↦ ⟨h.1, @h.2, h.3, @h.4, @h.5, @h.6, @h.7, @h.8⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ ↦ ⟨h₁, @h₂, h₃, @h₄, @h₅, @h₆, @h₇, @h₈⟩⟩

end AlgebraicGeometry

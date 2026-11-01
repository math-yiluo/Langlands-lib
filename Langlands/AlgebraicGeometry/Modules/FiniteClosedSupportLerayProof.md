# A finite-support Leray comparison for actual scheme modules: proof

Author: Worker 894.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportLerayStatement.{u}`
from `Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportLerayStatement`,
which it imports unchanged.

## Main result

`Langlands.AlgebraicGeometry.Modules.finiteClosedSupportLeray` is the theorem

```lean
theorem finiteClosedSupportLeray : FiniteClosedSupportLerayStatement.{u}
```

for an arbitrary universe `u`. Unfolded, it says: for all schemes
`X Y : Scheme.{u}`, every commutative ring `R : CommRingCat.{u}`, all
morphisms `f : X ⟶ Y` and `g : Y ⟶ Spec R` and every `M : X.Modules`,

```lean
(∀ q : ℕ, HasFiniteClosedSupport ((DerivedSections.higherDirectImage f q).obj M)) →
∀ n : ℕ,
  Nonempty
    (((DerivedSections.relativeCohomology (f ≫ g) n).obj M) ≅
      (DerivedSections.relativeGlobalSections g).obj
        ((DerivedSections.higherDirectImage f n).obj M))
```

In classical notation: if every `Rᵠ f_* M` has finite support made of closed
points of `Y`, then `Hⁿ(X, M) ≅ Γ(Y, Rⁿ f_* M)` as `R`-modules for every `n`,
including `n = 0`. The theorem adds no hypothesis to the statement. Empty
schemes, the zero ring and the zero module are covered. Only the existence
of an isomorphism is proved, for each fixed `n` and `M`. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Supporting declarations

Both are in the namespace
`Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportLeray`.

- `mapDirectImageComplexIso f g M` is the isomorphism of cochain complexes
  of `R`-modules

  ```lean
  ((DerivedSections.relativeGlobalSections g).mapHomologicalComplex _).obj
      (DerivedSections.directImageComplex f M) ≅
    DerivedSections.relativeComplex (f ≫ g) M
  ```

  It is Mathlib's `Functor.mapHomologicalComplexCompIso` applied to the
  published `DerivedSections.relativeGlobalSectionsCompIso f g`, evaluated at
  the cocomplex of Mathlib's chosen injective resolution of `M`.
- `nonempty_iso_of_isZero f g M hM n` proves the conclusion of the
  statement in degree `n` under the hypothesis

  ```lean
  hM : ∀ q r : ℕ, IsZero ((DerivedSections.relativeCohomology g (r + 1)).obj
    ((DerivedSections.higherDirectImage f q).obj M))
  ```

  Thus every higher direct image `Rᵠ f_* M` only has to be acyclic for
  `R`-module global sections along `g`. Finite closed support is not used in
  this lemma.

## Route of the proof

The proof follows the route recorded in the statement's Markdown, with one
simplification in step 3. Let `I` be Mathlib's chosen injective resolution of
`M`. Write `K := DerivedSections.directImageComplex f M`, the termwise
pushforward of `I` along `f`, and `F := DerivedSections.relativeGlobalSections g`.
By definition, `DerivedSections.relativeCohomology g k` is
`F.rightDerived k`.

1. **Acyclic terms.** The term `K.X i` is the pushforward along `f` of the
   injective module `I.cocomplex.X i`. The published theorem
   `pushforwardInjectiveAcyclic`, applied to `f` and this injective module,
   gives `IsZero ((F.rightDerived (r + 1)).obj (K.X i))` for all `i` and `r`.
2. **Homology of the direct-image complex.** The published isomorphism
   `DerivedSections.higherDirectImageIso f M i` identifies
   `(DerivedSections.higherDirectImage f i).obj M` with `K.homology i`.
3. **Acyclic homology.** Applying the functor `F.rightDerived (r + 1)` to the
   isomorphism of step 2 transports the hypothesis `hM i r` of
   `nonempty_iso_of_isZero` to
   `IsZero ((F.rightDerived (r + 1)).obj (K.homology i))`. The suggested
   route instead transports finite closed support along this isomorphism
   with `hasFiniteClosedSupport_iff_of_iso` and then applies module
   acyclicity to `K.homology i`. The implemented proof applies module
   acyclicity to the higher direct images themselves (see the last section)
   and transports the resulting vanishing. The two orders are equivalent.
4. **Comparison on the base.** The published generic theorem
   `Langlands.Cohomology.acyclicTermsHomologyComparisonStatement`, applied to
   `C := Y.Modules`, `D := ModuleCat R`, the functor `F` and the complex `K`,
   uses steps 1 and 3. It gives an isomorphism
   `((F.mapHomologicalComplex _).obj K).homology n ≅ F.obj (K.homology n)`.
   Its instance arguments are found by instance search: `HasInjectiveResolutions`
   for `Y.Modules`, and the `Additive` and `PreservesFiniteLimits` instances
   for `F` from `DerivedSections`.
5. **Total cohomology.** The published isomorphism
   `DerivedSections.relativeCohomologyIso (f ≫ g) M n` identifies
   `(DerivedSections.relativeCohomology (f ≫ g) n).obj M` with the `n`-th
   homology of `DerivedSections.relativeComplex (f ≫ g) M`, which is
   `DerivedSections.relativeGlobalSections (f ≫ g)` applied termwise to the
   same resolution `I`. The homology functor
   `HomologicalComplex.homologyFunctor _ _ n`, applied to the inverse of
   `mapDirectImageComplexIso f g M`, identifies this homology with
   `((F.mapHomologicalComplex _).obj K).homology n`. This step does not use
   that `f_* I` resolves `f_* M`, which is false in general.

The isomorphism of `nonempty_iso_of_isZero` is the composite of step 5, the
isomorphism of step 4, and `F.mapIso` of the inverse of the step 2
isomorphism in degree `n`. The last of these rewrites `F.obj (K.homology n)`
as `F.obj ((DerivedSections.higherDirectImage f n).obj M)`.

## The final theorem

For the statement, introduce `X Y R f g M`, the premise `hM` and `n`, and
apply `nonempty_iso_of_isZero f g M`. For each `q` and `r`, the published
theorem `Langlands.AlgebraicGeometry.Modules.finiteClosedSupportCohomology`,
from `Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyProof`,
is applied to the scheme `Y`, the module
`(DerivedSections.higherDirectImage f q).obj M` and its finite closed
support `hM q`. The relative part of its conclusion, for the ring `R` and the
morphism `g`, gives the required vanishing of
`(DerivedSections.relativeCohomology g (r + 1)).obj
((DerivedSections.higherDirectImage f q).obj M)`.

## Inputs

All inputs are imported by Lean name from published modules. The proof does
not re-prove any of them.

- `Langlands.Cohomology.acyclicTermsHomologyComparisonStatement`, from
  `Langlands.Cohomology.AcyclicResolution.AcyclicTermsHomologyComparisonProof`.
- `Langlands.AlgebraicGeometry.Modules.pushforwardInjectiveAcyclic`, from
  `Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof`.
- `Langlands.AlgebraicGeometry.Modules.finiteClosedSupportCohomology`, from
  `Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyProof`.
- `DerivedSections.relativeGlobalSectionsCompIso`, from
  `Langlands.AlgebraicGeometry.Modules.PushforwardComparison`. It is an
  unconditional isomorphism of functors.
- `DerivedSections.directImageComplex`, `DerivedSections.higherDirectImageIso`
  and `DerivedSections.relativeCohomologyIso`, from
  `Langlands.AlgebraicGeometry.Modules.DerivedSections`.
- Mathlib's `Functor.mapHomologicalComplexCompIso` and
  `HomologicalComplex.homologyFunctor`.

## Scope

The theorem constructs no spectral sequence and no edge map. The isomorphism
it produces is a composite of choices, and the theorem asserts nothing about
canonicity, naturality in `M` or compatibility between degrees.

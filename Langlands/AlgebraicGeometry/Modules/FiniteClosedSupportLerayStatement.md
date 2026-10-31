# A finite-support Leray comparison for actual scheme modules

Authors: Worker 360 (statement specification, draft pair and proof-route
rationale); Worker 894 (Markdown revision, checks and submission).

`Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportLerayStatement.{u}`
is a proposition definition. This file defines a proposition and does not
prove it. Proving this exact proposition is a separate obligation, and so are
the exact proofs of the module-acyclicity and generic-comparison inputs
described below.

## Statement

The proposition quantifies over arbitrary schemes `X Y : Scheme.{u}`, an
arbitrary commutative ring `R : CommRingCat.{u}`, arbitrary morphisms
`f : X ⟶ Y` and `g : Y ⟶ Spec R`, and an arbitrary actual module
`M : X.Modules`, all in one universe `u`. Empty schemes, the zero ring and
the zero module are allowed. Its single premise is

```lean
∀ q : ℕ, HasFiniteClosedSupport ((DerivedSections.higherDirectImage f q).obj M)
```

and, for every `n : ℕ`, its conclusion is

```lean
Nonempty
  (((DerivedSections.relativeCohomology (f ≫ g) n).obj M) ≅
    (DerivedSections.relativeGlobalSections g).obj
      ((DerivedSections.higherDirectImage f n).obj M))
```

In classical notation: if every `Rᵠ f_* M` has finite support made of closed
points of `Y`, then `Hⁿ(X, M) ≅ Γ(Y, Rⁿ f_* M)` as `R`-modules for all `n`.

## Conventions

Every name is imported unchanged from the published modules
`Langlands.AlgebraicGeometry.Modules.ModuleSupport` and
`Langlands.AlgebraicGeometry.Modules.DerivedSections`.

- `DerivedSections.higherDirectImage f q` is
  `(Scheme.Modules.pushforward f).rightDerived q`, the actual right derived
  functor of the actual pushforward `X.Modules ⥤ Y.Modules`. The premise
  covers `q = 0` too, so it applies to `f_* M` up to the degree-zero
  isomorphism.
- `HasFiniteClosedSupport N`, for `N : Y.Modules`, says that
  `stalkSupport N` is finite and that each of its points is closed in `Y`.
  Here `stalkSupport N` is the set of points where the stalk of the
  underlying abelian presheaf `N.presheaf` is not a zero object. Different
  degrees `q` may have different supports, so the premise does not ask for
  one finite set containing all of them.
- `DerivedSections.relativeGlobalSections g` is
  `Scheme.Modules.pushforward g ⋙ moduleSpecΓFunctor`, the global sections of
  a `Y`-module as an `R`-module.
- `DerivedSections.relativeCohomology (f ≫ g) n` is
  `(DerivedSections.relativeGlobalSections (f ≫ g)).rightDerived n`, the
  actual `n`-th right derived functor of `R`-module global sections on
  `X.Modules`, where `X` lies over `Spec R` through `f ≫ g`.

The conclusion covers every `n`, including `n = 0`. It only asserts that some
isomorphism of `R`-modules exists for each fixed `n` and `M`. It says nothing
about canonical maps, edge maps, naturality in `M`, compatibility between
degrees, or a spectral-sequence construction.

## Excluded hypotheses

There is no coherence, quasi-coherence, finite-generation, noetherian,
properness, separation, smoothness or flatness hypothesis on any scheme,
module or morphism. The statement does not assume that positive higher
direct images vanish, and it takes no Leray comparison certificate or
isomorphism hypothesis.

So `pushforwardComparison` from the published module
`Langlands.AlgebraicGeometry.Modules.PushforwardComparison` does not imply
this statement. That comparison assumes `Rᵠ⁺¹ f_* M = 0` for all `q`, and its
target is `Hⁿ(Y, f_* M)`. The present statement allows several nonzero higher
direct images, and its right-hand side is `Γ(Y, Rⁿ f_* M)`.

## Provenance

The statement is derived and internal to the project. Classically, it is the
degenerate case of the Leray spectral sequence
`Hᵖ(Y, Rᵠ f_* M) ⇒ Hᵖ⁺ᵠ(X, M)`. A sheaf whose nonzero stalks lie in a finite
set of closed points is flasque, so every `Hᵖ(Y, Rᵠ f_* M)` with `p > 0`
vanishes. The project states this case without constructing a spectral
sequence. The intended proof route below explains why the statement is
expected to hold. It is not Lean proof evidence.

Let `I` be Mathlib's chosen injective resolution of `M`, and let
`K := DerivedSections.directImageComplex f M` be the termwise pushforward of
`I`. Write `F := DerivedSections.relativeGlobalSections g`.

1. **Homology of `K`.** `DerivedSections.higherDirectImageIso f M n`
   identifies `Rⁿ f_* M` with `K.homology n`.
2. **Acyclic terms.** Every term of `K` is the pushforward of an injective
   `X`-module. The published theorem `pushforwardInjectiveAcyclic`, from
   `Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof`,
   makes `(DerivedSections.relativeCohomology g (r + 1)).obj (K.X i)` zero.
   That object is `(F.rightDerived (r + 1)).obj (K.X i)`.
3. **Acyclic homology.** By the premise and step 1, every `K.homology i` has
   finite closed support. Finite closed support is invariant under
   isomorphism by `hasFiniteClosedSupport_iff_of_iso`. The actual-module
   acyclicity implication then makes `(F.rightDerived (r + 1)).obj
   (K.homology i)` zero. That implication is scoped by the separate task for
   `Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyStatement`,
   whose argument goes through flasqueness of the underlying abelian sheaf.
   The elementary flasqueness statement is the published
   `Langlands.Cohomology.FiniteClosedSupportSheafStatement`.
4. **Comparison on the base.** The acyclic-terms/acyclic-homology comparison
   then gives `(F K).homology n ≅ F (K.homology n)`, and applying `F` to
   step 1 turns the right side into `Γ(Y, Rⁿ f_* M)`. Here `F K` is `F`
   applied termwise. The generic statement is the published
   `Langlands.Cohomology.AcyclicTermsHomologyComparisonStatement`.
5. **Total cohomology.** The same resolution `I` computes the left-hand side.
   `DerivedSections.relativeCohomologyIso (f ≫ g) M n` identifies
   `Hⁿ(X, M)` with the homology of
   `DerivedSections.relativeGlobalSections (f ≫ g)` applied termwise to `I`.
   `DerivedSections.relativeGlobalSectionsCompIso f g` is published in
   `PushforwardComparison`, unconditionally. It identifies
   `Scheme.Modules.pushforward f ⋙ F` with
   `DerivedSections.relativeGlobalSections (f ≫ g)`.
   Mathlib's `Functor.mapHomologicalComplexCompIso` carries this isomorphism
   to complexes, and passing to homology identifies `Hⁿ(X, M)` with
   `(F K).homology n`. This step does not need `f_* I` to be a resolution of
   `f_* M`.

Composing steps 5 and 4 gives the asserted isomorphism.

## Separate obligations

The proposition definitions named in steps 3 and 4 cannot establish this
statement by themselves. A proof of this statement must use accepted proofs
of those inputs, or another unconditional argument. The proof of the generic
comparison, the module-acyclicity statement and its proof, the elementary
abelian-sheaf proof, and the exact proof of this proposition are all separate
obligations.

## Intended use

The second-projection finite-support detection argument is the intended
consumer. There, total cohomology vanishes by hypothesis, and a geometric
argument must supply the finite-support premise. Once this statement is
proved, it makes `Γ(Y, Rⁿ f_* M)` zero for every `n`. Finite-support zero
detection would then make each `Rⁿ f_* M` zero. The present statement supplies
neither the geometric finite-support premise nor proper base change to fibre
cohomology.

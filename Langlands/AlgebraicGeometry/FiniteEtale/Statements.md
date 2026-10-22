# Geometric finite étale classification obligations

This module states three propositions about the actual constructions in
`Langlands.AlgebraicGeometry.FiniteEtale.Definitions`. It provides no proofs and
installs no instances for these propositions. All names below belong to
`Langlands.AlgebraicGeometry.FiniteEtale`.

## Source and provenance

The original source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary version, Chapter X §3: Definitions (10.25)–(10.26), printed p.150
(PDF p.154), and Theorem (10.28), printed p.151 (PDF p.155). The registered source
is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Definition (10.25) gives the full finite étale category and its geometric point
functor for an algebraically closed field. Definition (10.26) identifies the
fundamental group with the automorphism group of that functor for a connected
locally noetherian base. Theorem (10.28) states the equivalence with finite
continuous actions of this group.

The proposition about finite geometric fibres over an arbitrary scheme isolates
a geometric prerequisite of the finite-set packaging. Its scope does not assume
connectedness or local noetherianity. This is a derived statement about the
construction in (10.25), rather than a verbatim restatement of (10.28): after
base change to the algebraically closed field, a finite étale scheme is a finite
disjoint union of copies of the field's spectrum. This paragraph explains the
mathematical provenance; that argument is not implemented here.

The Galois/fibre-functor proposition is a derived axiom formulation using pinned
Mathlib `CategoryTheory.Galois.Basic`, not a claim that the source prints these
exact axioms. Mathlib's `PreGaloisCategory` asks for terminal objects, pullbacks,
finite coproducts, quotients by finite groups, and the direct-summand property
for monomorphisms. `FiberFunctor` asks that the chosen functor preserve terminal
objects, pullbacks, finite coproducts, epimorphisms, and quotients by finite
groups, and reflect isomorphisms. `GaloisCategory` extends `PreGaloisCategory`
with existence of a fibre functor. We require these properties for the actual
finite étale category and the specified geometric functor.

## Exact targets and hypotheses

All three targets use `S : Scheme.{u}`, `Ω : Type u`, a field structure on `Ω`,
`IsAlgClosed Ω`, and a geometric point `s : Spec (.of Ω) ⟶ S`. The common universe
matches the imported constructions. The geometric hypotheses are explicit in
each declaration's parameter list, including hypotheses unused by its body.

1. `GeometricFiberFinite s` is
   `∀ Y : Cover S, Finite (Fiber s Y)`.
   Here `Fiber s Y` is the type of actual morphisms from `s` to `Y` in the slice
   over `S`, so the structural equation is retained. There is no finiteness
   hypothesis, and no connectedness or noetherianity assumption on `S`.
2. `GeometricGaloisFiberFunctor s hfin` additionally assumes
   `ConnectedSpace S` and `IsLocallyNoetherian S`, and takes
   `hfin : ∀ Y : Cover S, Finite (Fiber s Y)` explicitly to form the finite-set
   functor. It asserts existence of `hG : GaloisCategory (Cover S)` and, with
   that witness bound locally as an instance, the predicate
   `PreGaloisCategory.FiberFunctor (fiberFunctor s hfin)`.
   Thus the category structure is part of the conclusion, and the assertion
   concerns the particular geometric functor, not merely some fibre functor.
   The local instance occurs only inside the proposition's body; no unproved
   geometric instance is installed in the environment.
3. `GeometricContinuousActionEquivalence s hfin` has the same hypotheses and
   explicit `hfin` as the second target. Its body is exactly
   `(continuousActionFunctor s hfin).IsEquivalence`. The functor's target is
   `ContAction FintypeCat.{u} (FundamentalGroup s hfin)`, with Mathlib's discrete
   finite-set topology and the evaluation topology on the actual natural
   automorphism group. This asserts that this specific functor is an equivalence,
   not just that the two categories admit an unrelated equivalence.

The last two statements do not derive finiteness silently: `hfin` is an explicit
parameter, eventually supplied by a proof of the first target. They assume no
Galois-category or fibre-functor instance. The equivalence target does not assume
the second target as a premise; its later proof must establish or import that
geometric result. In each case connectedness and local noetherianity are retained.

## Proof dependencies and scope

A later proof of `GeometricGaloisFiberFunctor` must establish the geometric
category and functor axioms. Once it is available, the equivalence proof can
unpack its witness and use Mathlib
`CategoryTheory.Galois.Equivalence`:
`PreGaloisCategory.functorToContAction` has the same evaluation-action construction
as `continuousActionFunctor`, and Mathlib supplies its `Functor.IsEquivalence`
under the genuine Galois-category and fibre-functor instances. Verifying the
identification is part of that later proof, not an additional assertion here.

The imported definition module already proves compactness, the Hausdorff and
totally disconnected properties, and the topological group laws under `hfin`.
Those conditional results are neither new assumptions nor unproved targets of
this module. No inverse-limit presentation, base-point transport, torsion scheme,
Tate module, site, sheaf, or cohomology assertion is included.

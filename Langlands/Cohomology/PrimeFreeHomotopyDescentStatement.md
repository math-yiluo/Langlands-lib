# Descent of a finite free homotopy model from a prime localization

`Langlands.Cohomology.ModuleComplex.PrimeFreeHomotopyDescentStatement.{u}` is
a proposition (a `def` of type `Prop`) about actual integer-indexed complexes
of modules over arbitrary commutative rings with carrier universe `u`.
It is a statement target only: **this module provides no proof of the
proposition**, and nothing in the Library may use it as a proved fact. Its
publication supplies no usable descent result.

## The proposition

The vocabulary comes unchanged from `Langlands.Cohomology.PerfectModuleComplex`:
`IsStrictlyPerfect`, `IsFiniteFree` and the degreewise scalar-extension
functor `baseChange`. Complexes are Mathlib's
`CochainComplex (ModuleCat.{u} A) ℤ`, indexed by `ℤ` with differentials
raising degree by one. `HomotopyEquiv` is Mathlib's structure from
`Mathlib.Algebra.Homology.Homotopy`. It consists of a chain map in each
direction and actual homotopies from both composites to the identities.

Write `R_p := Localization.AtPrime p`, which is Mathlib's
`Localization p.primeCompl`, and `R_r := Localization.Away r`, which is the
localization at the powers of `r`. The quantifiers, in order, are:

- every commutative ring `R : Type u`;
- every complex `K : CochainComplex (ModuleCat.{u} R) ℤ` with
  `IsStrictlyPerfect K`. This means there are integer bounds outside which
  the terms of `K` are actually zero, and every term `K.X i` is finite and
  projective over `R`;
- every ideal `p : Ideal R` with `[p.IsPrime]`;
- every rank family `n : ℤ → ℕ`;
- every complex `L : CochainComplex (ModuleCat.{u} R_p) ℤ`.

The hypotheses are:

1. `IsFiniteFree L`. There are integer bounds outside which the terms of `L`
   are actually zero, and every term is finite and free over `R_p`.
2. `Nonempty (HomotopyEquiv L ((baseChange (algebraMap R R_p)).obj K))`.
   There is an actual homotopy equivalence between `L` and the degreewise
   localization of `K`, whose terms are `R_p ⊗_R K.X i`.
3. For every `i : ℤ`, `Nonempty (L.X i ≃ₗ[R_p] (Fin (n i) → R_p))`. The term
   of `L` in degree `i` is free of rank `n i`.

The conclusion is that there exist `r : R` with `r ∉ p` and a complex
`P : CochainComplex (ModuleCat.{u} R_r) ℤ` such that:

- `IsFiniteFree P`;
- `Nonempty (HomotopyEquiv P ((baseChange (algebraMap R R_r)).obj K))`, an
  actual homotopy equivalence with the degreewise localization of `K` at `r`;
- for every `i : ℤ`, `Nonempty (P.X i ≃ₗ[R_r] (Fin (n i) → R_r))`.

The single element `r` and single complex `P` serve the homotopy equivalence
and the rank assertion in every degree. The same rank family `n` appears in
the hypothesis and the conclusion. All conclusions are actual `Nonempty`
homotopy equivalences or linear equivalences. No bases, matrices, chain maps
or homotopies are stored in an auxiliary record. The proposition makes no
uniqueness claim about `r` or `P`. It also asserts no relation between `P`
and `L`. In particular it does not claim that `R_p ⊗ P` is isomorphic to `L`,
although the natural construction of `P` gives this.

The proposition does not restrict `R` to be noetherian or local. It does not
assume that the terms of `K` are free over `R`, and it has no hypothesis
supplying a descended complex, map or homotopy. Hypothesis 1 is not implied by
hypothesis 3: an unbounded complex of finite free modules can be homotopy
equivalent to a bounded one. Conversely, since `L` is bounded and `R_p` is
nonzero, hypothesis 3 forces `n i = 0` outside the bounds of `L`. The
proposition does not record this deduction.

## Universes

Rings, localizations and term modules all live in universe `u`, and `u` is
the only universe parameter of the proposition. `Localization.AtPrime p` and
`Localization.Away r` are in `Type u` when `R : Type u`. No derived category
appears, so no `HasDerivedCategory` instance is used.

## Relation to the source

Source: The Stacks Project, More on Algebra, file `more-algebra.tex` at git
commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, retained as registered
source `stacks-perfect-complexes-a04446e5` (folder SHA-256
`54c831042614714cdb007a024d45dca7f60709efe2c307389ca2ad848b0ccbed`; file
SHA-256 `0106554339e8966fe04411b2ae9f9cd856b165849feef0c7bc37634819064708`).
The following were read in full:

- the local-ring lemma `lemma-lift-pseudo-coherent-from-residue-field`
  (Lemma 15.77.6, tag 0BCC), lines 19547–19563, with its proof, lines
  19565–19591;
- the target lemma `lemma-lift-perfect-from-residue-field` (Lemma 15.77.7,
  tag 0BCD), lines 19593–19610, with its proof, lines 19612–19625;
- the following lemma `lemma-compare-representatives-perfect`, lines
  19627–19641, and the start of its proof, lines 19643–19650;
- the cited `lemma-colimit-perfect-complexes` (Lemma 15.76.18, tag 0BC7),
  lines 19267–19285, with its proof, lines 19287–19322.

The proof of Lemma 15.77.7 first obtains, from the local-ring lemma, a
complex of finite free `R_p`-modules of ranks `d_i` representing `K ⊗^L R_p`.
It then writes `R_p = colim R_f` over `f ∉ p` (Algebra, Lemma 10.9.9,
tag 00CR) and concludes by `lemma-colimit-perfect-complexes`, adding
"Some details omitted". That lemma says that perfect objects and morphisms
between them in `D(colim R_i)` come from some `D(R_i)`.

This proposition isolates that descent step, in a stronger form internal to
this project. **It is not a statement of the source, and the exact homotopy
formulation is not attributed to the source.** It differs from the source
step as follows:

- the input is an arbitrary prescribed finite free model `L` with arbitrary
  ranks `n`, not necessarily the minimal one of ranks `d_i`. The proposition
  is independent of how such an `L` is constructed;
- the comparison is an actual homotopy equivalence of complexes, both over
  `R_p` and over `R_r`, rather than an isomorphism in a derived category;
- the descended object is a finite free complex with the same term ranks,
  not merely some perfect object over `R_r`.

The strengthening is justified by finite presentation, by the mechanism the
source uses in the proof of `lemma-colimit-perfect-complexes` (lines
19287–19322). Only finitely many terms of `K` and `L` are nonzero, and they
are finitely presented. A homotopy equivalence `L ≃ R_p ⊗ K` involves only
finitely many module maps between such terms: the differentials of `L` (finite
matrices over `R_p`), the two chain maps, and the two homotopies. For
finitely presented `M`, every `R_p`-linear map `R_p ⊗ M → R_p ⊗ N` comes from
an `R_f`-linear map `R_f ⊗ M → R_f ⊗ N` for some `f ∉ p`. Two such maps
which agree over `R_p` already agree over some `R_{fg}` with `g ∉ p`. So the
finitely many maps descend over one common `r ∉ p`. The finitely many
identities among them also hold over a further common `r`: `d ∘ d = 0`,
the chain-map conditions, and the two homotopy identities. The descended
complex `P` has terms `R_r^{n i}`. Mathlib has relevant single-module
ingredients, such as `Module.FinitePresentation.exists_lift_of_isLocalizedModule`
and `Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule`.
The argument is only a justification of the formulation. **None of it is
proved here.** Descending the complex, the chain maps, the homotopies and all
their equations to one localization is the obligation of whoever proves this
proposition, and that proof may not assume the output homotopy equivalence.

Errata check: the project has no errata note for this source. The live Stacks
pages for tags 0BCD, 0BCC, 0BC7 and section 0BC8 showed no comments on
2026-10-30. Tag 00CR showed eight comments; none affects the identification
`R_p = colim R_f`.

## Intended use

This is one of two algebraic prerequisites for proving the published target
`Langlands.Cohomology.ModuleComplex.LocalMinimalPerfectStatement`. The other
is a minimal finite free homotopy model over `R_p` whose ranks are the
residue-field cohomology dimensions. Taking `n` to be those dimensions, this
proposition descends such a model to some `R_r`. The Library's
`Langlands.Cohomology.ModuleComplex.derivedIsoOfHomotopyEquiv`, in
`Langlands.Cohomology.PerfectModuleComplexHomotopy`, converts the resulting
homotopy equivalence into an isomorphism in the derived category. This module
does not state the minimal-model step, the identification of ranks, or the
assembly.

Provenance: the proposition transcribes the specification in the contract of
task `351f9db9-9284-4259-8f9d-4ddb22c03c3e`. The Lean and Markdown were
written by Worker 958.

# Minimal finite free homotopy models at a prime

`Langlands.Cohomology.ModuleComplex.PrimeMinimalPerfectStatement.{u}` is a
proposition (a `def` of type `Prop`). It concerns actual integer-indexed
complexes of modules over arbitrary commutative rings with carrier universe
`u`. It is a statement target only: **this module provides no proof of the
proposition**, and nothing in the Library may use it as a proved fact. In
particular, it does not claim that the minimal model construction has been
formalized.

## The proposition

The vocabulary comes from the published module
`Langlands.Cohomology.PerfectModuleComplex`, imported unchanged:
`IsStrictlyPerfect`, `IsFiniteFree` and the degreewise scalar-extension
functor `baseChange`. Complexes are Mathlib's
`CochainComplex (ModuleCat.{u} A) ℤ`, indexed by `ℤ` with differentials
raising degree by one. This is the cohomological convention of the source.
`HomotopyEquiv` is Mathlib's homotopy equivalence of homological complexes
(`Mathlib.Algebra.Homology.Homotopy`): chain maps `hom` and `inv` together
with homotopies from `hom ≫ inv` to the identity and from `inv ≫ hom` to
the identity.

The quantifiers, in order, are:

- every commutative ring `R : Type u`;
- every actual complex `K : CochainComplex (ModuleCat.{u} R) ℤ` with
  `IsStrictlyPerfect K`. This means there are integer bounds outside which
  the terms of `K` are actually zero, and every term `K.X i` is finite and
  projective over `R`;
- every ideal `p : Ideal R` with `[p.IsPrime]`.

Write `Rₚ := Localization.AtPrime p`, the localization of `R` at `p`, and
`κ := p.ResidueField`. The latter is Mathlib's residue field of the local
ring `Rₚ`, i.e. `κ(𝔭)` in the source. Write
`Kκ := (baseChange (algebraMap R κ)).obj K`. This is the complex with terms
`κ ⊗_R K.X i`, extended directly from `R` to `κ`. Write
`d i := Module.finrank κ (Kκ.homology i)`, where `Kκ.homology i` is the
actual homology object of that complex of `κ`-modules. Write
`Kₚ := (baseChange (algebraMap R Rₚ)).obj K` for the complex with terms
`Rₚ ⊗_R K.X i`.

The proposition asserts the conjunction of:

1. **Finite dimensionality.** For every `i : ℤ`,
   `Module.Finite κ (Kκ.homology i)`. Because this is stated explicitly,
   the `Module.finrank` below is a genuine dimension. It is not the
   convention value `0` that `finrank` takes on infinite-dimensional spaces.
2. **A finite free homotopy model over `Rₚ`.** There exists a complex
   `L : CochainComplex (ModuleCat.{u} Rₚ) ℤ` such that
   - `IsFiniteFree L`: there are integer bounds outside which the terms of
     `L` are actually zero, and every term is finite and free over `Rₚ`;
   - `Nonempty (HomotopyEquiv L Kₚ)`: `L` is homotopy equivalent to the
     degreewise localization `Kₚ` as an actual complex of `Rₚ`-modules;
   - for every `i : ℤ`,
     `Nonempty (L.X i ≃ₗ[Rₚ] (Fin (d i) → Rₚ))`. In words, the term of `L`
     in degree `i` is free of rank exactly `d i`.

The same `L` serves the homotopy equivalence and every rank assertion. All
conclusions are `Nonempty` homotopy equivalences or linear equivalences.
No bases, homology values or comparison maps are stored in an auxiliary
record. The rank formula uses the residue-field complex `Kκ` extended from
the original ring `R`, not a complex extended from `Rₚ` or from `L`. A proof
therefore needs no later comparison to apply the ranks.

The proposition has no premise beyond `IsStrictlyPerfect K` and primality
of `p`. It does not assume an output equivalence, a minimal model, a zero
reduced differential, or any equivalent conclusion. It does not assert that
`L ⊗ κ` has zero differentials. That follows mathematically from the rank
assertions and the homotopy equivalence. The homotopy equivalence identifies
the homology of `L ⊗_{Rₚ} κ` with that of `Kκ`. A homology space of dimension
equal to that of its term forces both adjacent reduced differentials to vanish.
Neither the statement nor this module records that deduction. The
proposition makes no uniqueness claim about `L`, and it does not claim that
`Kₚ` itself has free terms of these ranks.

## Universes

Rings, term modules, `Rₚ` and `κ` all live in universe `u`. `u` is the only
universe parameter of the proposition. No derived category occurs in the
statement, so no `HasDerivedCategory` instance and no morphism universe for
a derived category is involved. A homotopy equivalence between complexes in
`ModuleCat.{u} Rₚ` consists of morphisms and homotopies whose data lie in
`Type u`.

## Ordinary versus derived scalar extension

The source works with an object `K ∈ D(R)` and the derived tensor products
`K ⊗^L_R κ(𝔭)` and `K ⊗^L_R R_f`. In the local lemma it works with
representatives of objects of `D(R_𝔭)`. The Lean statement instead uses the
ordinary degreewise extensions `baseChange` of a supplied bounded finite
projective representative `K`. This matches the source's quantities for the
following mathematical reasons:

- every perfect object of `D(R)` has such a representative (Stacks,
  Definition 15.76.1, tag 0657);
- a bounded complex of projective modules is K-flat, so its ordinary
  degreewise tensor product computes the derived tensor product. This
  identifies `Kκ.homology i` with the source's
  `H^i(K ⊗^L_R κ(𝔭))`, and `d i` with the source's `d_i`;
- `R → Rₚ` is flat, so `Kₚ` also represents `K ⊗^L_R R_𝔭`.

These facts explain the correspondence with the source, but none is proved
or imported here. The definition of `baseChange` is only the ordinary
functor `ModuleCat.extendScalars` applied to complexes. It does not by
itself establish preservation of quasi-isomorphisms or independence of the
chosen representative. The proposition itself is stated entirely in terms
of ordinary complexes, so proving it does not require the derived tensor
product.

## Why a homotopy equivalence

The source asks for a complex "representing" the given object, i.e. an
isomorphism in a derived category. The Lean statement asks for an actual
homotopy equivalence of complexes. This is the intended strengthening, for
the following reasons.

- **It is at least as strong.** The published
  `Langlands.Cohomology.ModuleComplex.derivedIsoOfHomotopyEquiv`
  (in `Langlands.Cohomology.PerfectModuleComplexHomotopy`) turns a homotopy
  equivalence into an isomorphism in Mathlib's standard derived category.
  For the complexes here nothing is lost. `L` and `Kₚ` are both bounded
  complexes of finite projective `Rₚ`-modules, by the published
  `isStrictlyPerfect_of_isFiniteFree` (in
  `Langlands.Cohomology.PerfectModuleComplex`) and
  `isStrictlyPerfect_baseChange` (in
  `Langlands.Cohomology.PerfectModuleComplexBaseChange`).
  For such complexes the published `homotopyEquivOfDerivedIso` turns a
  derived isomorphism back into a homotopy equivalence. This module neither
  imports nor uses these comparisons.
- **It is what the local construction produces.** Over the local ring `Rₚ`,
  `Kₚ` has finite free terms. Splitting off contractible pieces
  `Rₚ → Rₚ` (identity) wherever a reduced differential is nonzero writes
  `Kₚ` as a direct sum of a minimal complex and a contractible complex.
  Compare the source's appeal, in the proof of
  `lemma-compare-representatives-perfect`, to the fact that any complex is a
  direct sum of a trivial complex and a minimal one. Such a decomposition
  gives a homotopy equivalence directly.
- **It is what the descent step consumes.** The proof of tag 0BCD passes
  from `R_𝔭 = colim R_f` to some `R_f` (Stacks Lemma 15.76.18, "Some details
  omitted"). A homotopy equivalence between bounded finite free complexes is
  a finite amount of matrix data satisfying finitely many identities.
  Together with the complex `L`, such data descend to some `R_f` and remain
  a homotopy equivalence there. A homotopy
  equivalence is also preserved by every additive functor, for example by
  ordinary scalar extension (published `baseChangeHomotopyEquiv`).

This exact formal wording is an internal formulation. The source contains
no statement in this form.

## Source and provenance

Source: The Stacks Project, More on Algebra, file `more-algebra.tex` at git
commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, retained as registered
source `stacks-perfect-complexes-a04446e5` (folder SHA-256
`54c831042614714cdb007a024d45dca7f60709efe2c307389ca2ad848b0ccbed`). The
following were read in full:

- Lemma 15.77.6, [tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC),
  label `lemma-lift-pseudo-coherent-from-residue-field`, lines 19547–19591,
  with its proof;
- Lemma 15.77.7, [tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD),
  label `lemma-lift-perfect-from-residue-field`, lines 19593–19625, with its
  proof;
- `lemma-compare-representatives-perfect` and its proof, lines 19627–19654.

Errata check: the project has no errata note for this source. The live tag
pages for 0BCC and 0BCD showed the same statements and proofs, each with
"Comments (0)", on 2026-10-30.

The proposition is a derived (internal) strengthening and specialization of
the local step in the proof of tag 0BCD. That proof applies tag 0BCC over the
local ring `R_𝔭` to obtain "a complex representing `K` having the desired
shape over the local ring `R_𝔭`". The differences are:

- **Specialization.** Tag 0BCC is stated for a pseudo-coherent object over
  an arbitrary local ring, with a bounded above representative. Here the
  local ring is `Rₚ`, the input is a supplied bounded finite projective
  complex over `R`, and the output `L` is bounded on both sides.
- **Strengthening.** A homotopy equivalence of actual complexes replaces
  "representing in `D(R_𝔭)`" (see the previous section).
- **Rank formula.** The ranks are the dimensions of the residue-field
  homology of `K` itself over `R`, the `d_i` of tag 0BCD. Applied over
  `R_𝔭`, tag 0BCC computes its dimensions from the object over `R_𝔭`.
  The two agree mathematically, since `κ(𝔭)` is also the residue field of
  `R_𝔭`; the Lean statement uses the form over `R` directly.
- **Omitted parts.** The uniqueness assertion of tag 0BCC is not stated.
  The descent from `R_𝔭` to some `R_f` with `f ∉ 𝔭` in tag 0BCD is not
  stated; that is a separate prerequisite. The assertion of tag 0BCD that
  only finitely many `d_i` are nonzero is not stated separately. It follows
  mathematically from the term bounds of `L` and `Rₚ ≠ 0`, but neither the
  statement nor this module records that deduction.

Intended use: one of the algebraic prerequisites for
`Langlands.Cohomology.ModuleComplex.LocalMinimalPerfectStatement`, together
with descent of a finite free homotopy model from `Rₚ` to a principal
neighbourhood. This module does not state or prove K-flatness, derived
scalar extension, descent to `R_f`, or any geometric consequence.

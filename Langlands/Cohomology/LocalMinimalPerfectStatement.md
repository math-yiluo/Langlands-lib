# Local finite free representatives with minimal residue-field ranks

`Langlands.Cohomology.ModuleComplex.LocalMinimalPerfectStatement.{u}` is a
proposition (a `def` of type `Prop`) about actual integer-indexed complexes
of modules over arbitrary commutative rings with carrier universe `u`.
It is a statement target only: **this module provides no proof of the
proposition**, and nothing in the Library may use it as a proved fact.

## The proposition

The vocabulary comes from `Langlands.Cohomology.PerfectModuleComplex`:
`IsStrictlyPerfect`, `IsFiniteFree` and the degreewise scalar-extension
functor `baseChange`. Complexes are Mathlib's `CochainComplex (ModuleCat.{u} A) ℤ`,
indexed by `ℤ` with differentials raising degree by one. This is the
cohomological convention used by the source.

The quantifiers, in order, are:

- every commutative ring `R : Type u`;
- every actual complex `K : CochainComplex (ModuleCat.{u} R) ℤ` with
  `IsStrictlyPerfect K`, meaning: integer bounds outside which the terms of
  `K` are actually zero, and every term `K.X i` finite and projective over `R`;
- every ideal `p : Ideal R` with `[p.IsPrime]`.

Write `κ := p.ResidueField`. This is Mathlib's residue field of the
localization of `R` at `p`, i.e. `κ(𝔭)` in the source. Write
`Kκ := (baseChange (algebraMap R κ)).obj K` for the complex with terms
`κ ⊗_R K.X i`, and `d i := Module.finrank κ (Kκ.homology i)`. Here
`Kκ.homology i` is the actual homology object of that complex of
`κ`-modules. The proposition asserts the conjunction of:

1. **Finite dimensionality.** For every `i : ℤ`,
   `Module.Finite κ (Kκ.homology i)`. Because this is stated explicitly,
   the `Module.finrank` below is a genuine dimension. It is not the
   convention value `0` that `finrank` takes on infinite-dimensional spaces.
2. **A finite free representative near `p`.** There exist `r : R` with
   `r ∉ p`, and a complex `P : CochainComplex (ModuleCat.{u} (Localization.Away r)) ℤ`
   (`Localization.Away r` is the source's `R_f`) such that
   - `IsFiniteFree P`: integer bounds outside which the terms of `P` are
     actually zero, and every term finite and free;
   - `Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj
     ((baseChange (algebraMap R (Localization.Away r))).obj K))`: an actual
     isomorphism in the derived category of `Localization.Away r`-modules
     between `P` and the degreewise localization of `K`;
   - for every `i : ℤ`, `Nonempty (P.X i ≃ₗ[Localization.Away r]
     (Fin (d i) → Localization.Away r))`: the term of `P` in degree `i` is
     free of rank exactly `d i`.

The same witnesses `r` and `P` serve the derived isomorphism and all rank
assertions. All conclusions are actual `Nonempty` isomorphisms or linear
equivalences. No bases, cohomology values or comparison maps are stored
in an auxiliary record. The derived isomorphism is *not* an isomorphism of
complexes. The proposition does not claim that the localized complex `K`
itself has free terms of these ranks. It makes no uniqueness claim about `P`.

## Universes and the derived category

Rings, term modules and residue fields all live in universe `u`, and `u`
is the only universe parameter of the proposition. The derived category
of `ModuleCat.{u} (Localization.Away r)` is given by Mathlib's standard
localization `HasDerivedCategory.standard`, made a local instance in this
file by `attribute [local instance] HasDerivedCategory.standard`. For
`ModuleCat.{u} T`, whose objects form a `Type (u + 1)` and whose morphisms
form `Type u`, that construction has morphisms in universe `u + 1`. Mathlib
has no global `HasDerivedCategory` instance, so this is the only instance
that the statement can use. The proposition does not assume that some
derived category with morphisms in universe `u` has already been constructed.

## Ordinary versus derived scalar extension

The source works with derived tensor products `K ⊗^L_R κ(𝔭)` and
`K ⊗^L_R R_f` of a perfect object `K ∈ D(R)`. The Lean statement uses the
ordinary degreewise extensions `baseChange` of a supplied bounded finite
projective representative. This agrees with the source for the following
mathematical reasons:

- every perfect object of `D(R)` has such a representative (Stacks,
  Definition 15.76.1, tag 0657);
- a bounded complex of projective modules is K-flat, so its ordinary
  degreewise tensor product computes the derived tensor product. This
  identifies `Kκ.homology i` with the source's `H^i(K ⊗^L_R κ(𝔭))`, and
  `d i` with the source's `d_i`;
- for `R_f` one may alternatively use flatness of localization.

These facts justify the specialization, but none is proved here. They
are proof obligations for whoever proves this statement. The definition
of `baseChange` is only the ordinary functor `ModuleCat.extendScalars`
applied to complexes. It does not by itself establish preservation of
quasi-isomorphisms or independence of the chosen representative.

## Source and scope

Source: The Stacks Project, More on Algebra, Lemma 15.77.7,
[tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD), file
`more-algebra.tex`, label `lemma-lift-perfect-from-residue-field`, lines
19593–19629 at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`.
It is retained as registered source `stacks-perfect-complexes-a04446e5`
(folder SHA-256
`54c831042614714cdb007a024d45dca7f60709efe2c307389ca2ad848b0ccbed`).
The lemma, its proof, and the preceding local-ring lemma
`lemma-lift-pseudo-coherent-from-residue-field` (lines 19547–19590) and
its proof were read in full. The live tag page showed Lemma 15.77.7 with
no comments on 2026-10-28, and the project has no errata note for this
source. The folder's citation metadata calls its `perfect.tex` chapter
"More on Flatness"; that chapter's actual title is *Derived Categories of
Schemes*. This statement relies only on `more-algebra.tex`.

The source lemma asserts that the `d_i` are finite and only finitely many
are nonzero. It also asserts that some `f ∉ 𝔭` has a complex
`0 → R_f^{⊕ d_a} → … → R_f^{⊕ d_b} → 0` representing `K ⊗^L_R R_f`
in `D(R_f)`. The target asserts the finite dimensionality and the
existence of a bounded finite free representative with the specified
term ranks in every degree. It does **not** separately assert that only
finitely many `d i` are nonzero. Mathematically this follows from the
term bounds of `P` together with `Localization.Away r ≠ 0`, but neither
the statement nor this module records that deduction.

Intended use: the algebraic prerequisite for the finite free complex
argument in Stacks' More on Morphisms, Section 37.33 (local Picard
lemmas, for example `lemma-H1-O-multiple-picard-flat-proper`). This module
does not state or prove any of the following:

- K-flatness or derived scalar extension;
- actual derived sections of scheme modules;
- perfect proper direct images;
- geometric cohomology and base change;
- local two-axis triviality;
- relative cube detection.

These remain separate tasks.

Draft design by Worker 606; adapted and submitted by Worker 975.

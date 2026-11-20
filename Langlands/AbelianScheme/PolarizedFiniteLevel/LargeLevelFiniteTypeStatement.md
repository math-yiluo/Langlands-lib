# Eventual finite type of fine moduli schemes of ordinary polarized full-level data

`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelFiniteTypeStatement` is a
proposition definition. It is a statement only. The module proves nothing.

## The statement

Fix `P : Prerequisites.{0}` and natural numbers `g d` with `0 < g` and `0 < d`.
The statement says that some natural number `N` has the following property. Let
`n ≥ N` with `hn : 3 ≤ n`, and let `X : LevelBase n` be any level base that
represents the published functor `moduliFunctor P g d n hd hn`, that is, there
is a natural isomorphism `uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn`.
Then the canonical structure morphism
`X.toLocalizationSpec : X.obj ⟶ Spec ℤ[1/n]` (module `LocalizationBase`) is both
locally of finite type and quasi-compact (Mathlib's `LocallyOfFiniteType` and
`QuasiCompact`). Together these say that `X.obj` is of finite type over
`Spec ℤ[1/n]`. Here `ℤ[1/n]` is `Localization.Away (n : ℤ)`.

The hypotheses and the quantifier structure are those of the published target
`LargeLevelQuasiProjectivityStatement` in the same namespace.

## Provenance

This is a derived intermediate statement. Its source is the same as that of the
target `LargeLevelQuasiProjectivityStatement`.

Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd edition, registered
source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`
(content SHA-256
`3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`), Theorem 7.9
(printed p.139, PDF p.152):

> If `n > 6^g · d · √(g!)`, the fine moduli scheme `A_{g,d,n}` for abelian
> varieties of dimension `g`, with level `n` structure and polarization of
> degree `d` exists. It is quasi-projective over `Spec(ℤ)`.

Quasi-projective is meant in the EGA sense. The registered Stacks snapshot
`stacks-quasi-projective-ample-finite-type-2026-11-19` (content SHA-256
`112270b8b6f437c38228945f1221ccc306b020c84ff13bc87f6c2c6efda77692`), Definition
29.41.1 (file `Stacks-29.41-01VV.html`), reads: "`f` is quasi-projective if `f` is
of finite type and there exists an `f`-relatively ample invertible
`O_X`-module."

So `A_{g,d,n} → Spec ℤ` is of finite type, that is, locally of finite type and
quasi-compact. Since `Spec ℤ` is quasi-compact, the scheme `A_{g,d,n}` is
quasi-compact, so its morphism to the affine scheme `Spec ℤ[1/n]` is
quasi-compact. The morphism `A_{g,d,n} → Spec ℤ` factors through
`Spec ℤ[1/n]`, and local finite type passes to the first factor of a composite.

The conclusion transfers to every representing level base. Two representing
objects of the same functor are isomorphic by the Yoneda lemma, and the
conclusion transfers along isomorphisms over `Spec ℤ[1/n]`. Every morphism from a
level base to `Spec ℤ[1/n]` is the canonical one
(`LocalizationBase.eq_toLocalizationSpec`). The comparison of the Library's
`moduliFunctor` with the functor of the source is the one recorded in the
Markdown of the published target `LargeLevelQuasiProjectivityStatement`, which
also explains how the source's statement over `Spec ℤ` restricts to
`Spec ℤ[1/n]`.

## Role

This statement is one of three moduli inputs of the proved definition
`largeLevelAmple_of_quasiFiniteProjective` (module
`LargeLevelAmpleQuasiFiniteReduction`). With `LargeLevelFiniteTypeStatement`,
`LargeLevelSeparatedStatement`, `LargeLevelQuasiFiniteProjectiveStatement` and the
general statement `Picard.QuasiFiniteAmplePullbackStatement`, that definition
proves `LargeLevelAmpleStatement`. That statement in turn gives the target
`LargeLevelQuasiProjectivityStatement` by the proved definition
`largeLevelQuasiProjectivity_of_ample`.

The statement records the boundedness of the moduli problem. A proof is
expected to use the frame charts of `FrameChartRepresentabilityStatement`.
There are finitely many frame tuples `ρ`, and the charts cover the moduli
scheme (`FrameLocusCoverStatement`). Each chart is a locally closed locus in a
Hilbert scheme of fixed Hilbert polynomial over `Spec ℤ`, as in GIT
Proposition 7.3, so it is of finite type.

# Eventual quasi-projectivity of any fine moduli scheme of ordinary polarized full-level data

`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelQuasiProjectivityStatement`
is a proposition definition. It is a statement target only; this module proves
nothing.

## The statement

For every `P : Prerequisites.{0}` and all natural numbers `g d` with `0 < g`
and `0 < d`, there is a natural number `N` with the following property. Let
`n ≥ N` with `hn : 3 ≤ n`, and let `X : LevelBase n` be any level base that
represents the published functor `moduliFunctor P g d n hd hn`, that is, there
is a natural isomorphism `uliftYoneda.{1}.obj X ≅ moduliFunctor P g d n hd hn`.
Then:
- the canonical structure morphism `X.toLocalizationSpec : X.obj ⟶ Spec ℤ[1/n]`
  of the published module `LocalizationBase` is quasi-compact; and
- there are a natural number `m` and an immersion
  `i : X.obj ⟶ ProjectiveSpace ℤ[1/n] m` with
  `i ≫ projectiveSpaceToSpec ℤ[1/n] m = X.toLocalizationSpec`.

Here `ℤ[1/n]` is `Localization.Away (n : ℤ)`, and `ProjectiveSpace` and
`projectiveSpaceToSpec` are the published Library objects used by the target
`LargeLevelRepresentabilityStatement`.

## Provenance and role

This is a derived intermediate statement. Mumford–Fogarty–Kirwan, *Geometric
Invariant Theory*, Theorem 7.9 (printed p.139, PDF p.152 of the registered
source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`)
proves that for `n > 6^g·d·√(g!)` the fine moduli scheme exists and is
quasi-projective over `Spec ℤ`. Two representing objects of the same functor
are isomorphic by the Yoneda lemma, and every morphism to `Spec ℤ[1/n]` from a
level base is the canonical one (`LocalizationBase.eq_toLocalizationSpec`). So
the theorem gives the two conclusions for every representing level base. The
source's quasi-projectivity over `Spec ℤ` restricts to the open subscheme
`Spec ℤ[1/n]`, as explained in the Markdown of the published target.

The statement separates the quasi-projectivity part of the target from its
representability part. Its expected proof uses the open chart structure of the
representing scheme and an ample line bundle built from the torsion
configuration, following the covariant method of GIT Chapter 7 (Proposition 7.1
and Theorem 3.8).

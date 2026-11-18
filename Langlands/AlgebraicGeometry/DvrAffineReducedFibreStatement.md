# Affine reduced fibre theorem with smooth generic fibre

Worker 6.

`Langlands.AlgebraicGeometry.DvrAffineReducedFibreStatement.{u}` is a
proposition definition, with no proof in this module. It is an affine,
ring-theoretic form of the Raynaud–Faltings reduced fibre theorem, in the
special case where the generic fibre is smooth.

## The statement

Let `R : Type u` be a discrete valuation ring and `A : Type u` a commutative
`R`-algebra. Assume:

- `A` is flat over `R` (`Module.Flat R A`);
- `A` is of finite type over `R` (`Algebra.FiniteType R A`);
- the generic fibre `FractionRing R ⊗[R] A` is smooth over the actual fraction
  field `FractionRing R` (`Algebra.Smooth`).

The conclusion supplies a discrete valuation ring `R' : Type u` in the same
universe, with an `R`-algebra structure, such that `R'` is faithfully flat over
`R` (`Module.FaithfullyFlat R R'`). Write `A' = R' ⊗[R] A` for the base change
and `A' ⊗[R'] FractionRing R'` for its generic fibre, an `A'`-algebra through
the left factor. Let `B` be the integral closure of `A'` in this generic fibre
(Mathlib's `integralClosure`, an `A'`-subalgebra). Then:

1. `B` is a finite `A'`-module;
2. for every field `F : Type u` with an `R'`-algebra structure, the ring
   `F ⊗[R'] B` is reduced.

Condition 2 is geometric reducedness of all fibres of `Spec B → Spec R'`, in the
strong form used by Mathlib's scheme-level `GeometricallyReduced`: every field
in the universe `u` is allowed, not only algebraic closures of residue fields.
A field `F` under `R'` is either an algebra over `FractionRing R'` or over the
residue field of `R'`, so condition 2 covers both the generic and the special
fibre of `B`.

The extension `R'` is not required to be finite over `R`, nor local over a
finite extension; only faithful flatness is required. Faithful flatness of a
DVR extension means that `R → R'` is injective and that the maximal ideal of
`R` maps into that of `R'`, so `Spec R' → Spec R` is flat and surjective.

## Why this is the reduced fibre theorem

Since `A` is flat over `R`, so is `A'` over `R'`, and `A'` embeds in its
generic fibre. That generic fibre is the base change of the smooth
`FractionRing R`-algebra `FractionRing R ⊗[R] A` to `FractionRing R'`, so it is
smooth, hence normal and reduced. Thus `A'` is reduced, and the integral
closure of `A'` in its normal generic fibre is the normalization of `A'`.
The statement asserts that, after a suitable extension of the DVR, this
normalization is finite and has geometrically reduced fibres.

## Provenance and source comparison

This is a derived interface from Brian Conrad's appendix to Gopal Prasad and
Jiu-Kang Yu, *On quasi-reductive group schemes* (author preprint):

- Theorem A.2 (Raynaud–Faltings), p.28: for a flat finite-type scheme `X`
  over a Dedekind domain `R`, there is a finite extension `K'/K` such that the
  normalization of `(X ⊗_R R')_red` is finite over `X ⊗_R R'`, with
  geometrically normal generic fibre and geometrically reduced special fibres
  over the integral closure `R'` of `R` in `K'`.
- Remark A.1, p.28: if `R` is a henselian DVR, then `R'` is again a henselian
  DVR. Conrad's reductions on pp.30–32 replace `R` by faithfully flat local
  extensions (henselization, completion), which is why this interface asks only
  for a faithfully flat DVR extension.
- Remark A.3, p.28: geometric reducedness over a field `k` is reducedness after
  every field extension `k'/k`.
- Theorem A.6, p.30: when the generic fibre is geometrically reduced, the
  normalization is finite without any excellence hypothesis on `R`.

The present statement specializes A.2 to an affine `X = Spec A` over a DVR with
smooth generic fibre. In this case `X ⊗_R R'` is already reduced, so no
reduction step is needed. Applying A.2 after passing to a henselian
extension and localizing by A.1 gives a DVR `R'`. The `R'`-flat normalization
then has geometrically reduced special fibre and smooth, hence geometrically
reduced, generic fibre.

The statement is a prerequisite of
`Langlands.AlgebraicGeometry.DvrStableNormalizationStatement`, where the
integral closures over an affine cover are glued by Mathlib's relative
normalization.

Registered source: `prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`, file
*Prasad–Yu, On quasi-reductive group schemes (author preprint).pdf*.

# Geometric-point nondegeneracy of the actual finite Weil pairing

`Langlands.AbelianScheme.GeometricFiniteWeilNondegeneracyStatement`
is a proposition definition. It states that the existing finite Weil
pairing of an actual abelian scheme, evaluated on points over a
geometric point whose field has characteristic prime to `n`, has
trivial left and right kernels. The file proves nothing.

## The pairing

The map tested is exactly `finiteWeilLevelBilinearMap`, built with the
inputs `preservation`, `composition`, `unitCoherence`, `associativity`,
`comparison`, `symmetry`, `stability`, `hA`, `MA` and `evaluationA`
quantified in the statement. At level `n` and test object `T` it is a
biadditive map

```text
GroupScheme.Tate.Level A.toGrp T n × GroupScheme.Tate.Level GD T n
  → TateTwist.Level Γ(T.left, ⊤) n,
```

where `GD` is the group scheme underlying
`dualCommGroupSchemeFromEvaluation`. The two sources are the actual
`n`-torsion sections `T ⟶ A.X` and `T ⟶ GD.X`, written additively,
and the target is `Additive (rootsOfUnity n Γ(T.left, ⊤))`. Its value
on `(x, y)` is the existing scheme pairing `finiteWeilPairing n`
evaluated at the kernel lifts of `x` and `y`, which evaluates the
intrinsic character of the dual point `y` at `x`. No roots of unity,
character map, pairing or duality isomorphism is supplied as data.

## The assertion

The test object is `Over.mk s`, where
`s : Spec (CommRingCat.of K) ⟶ S` and `K` is an algebraically closed
field. The hypothesis `(n : K) ≠ 0` says that the characteristic of `K`
does not divide `n`; it also forces `n ≠ 0`. It is not assumed that
`n` is invertible on `S`.

The conclusion has two parts. If an `n`-torsion point `x` of `A` over
`s` pairs to zero (the root of unity `1`) with every `n`-torsion point
of the dual over `s`, then `x = 0`. Symmetrically, a dual `n`-torsion
point `y` pairing to zero with every `x` is zero. This is the
statement that both kernels of the pairing on geometric points are
trivial. It does not assert a group isomorphism with a dual, a
perfect pairing of group schemes, or anything on test schemes other
than these geometric points.

## Inputs

The base `S` is quasi-separated and `A` is an actual abelian scheme
over `S`, with a chosen dual scheme `hA`, its geometry `geometryA`,
the inverse Poincaré line bundle `MA` and its evaluation isomorphism.
The statement quantifies over all ten propositions that are inputs of
`PrimeRationalPolarizationWeilNondegeneracyStatement`, in the same
order. Four of them, `square`, `universality`, `compatibility` and the
dual geometry `geometryA`, are not used to form the pairing. They are
kept as hypotheses, with names prefixed by `_`, so that a proof may use
them, for instance to transport the chosen dual to the geometric fibre.
Keeping them makes the statement weaker. It still applies wherever the
geometric-point Weil target is stated, since that target quantifies
over the same inputs.

## Source and translation

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

- Chapter XI, Definition (11.11), printed p.162 / PDF p.166, defines
  for an isogeny `f` of abelian varieties over a field the pairing
  `e_f(x, y) = β(y)(x)`, where `β : Ker(f^t) ≅ Ker(f)^D` is the
  isomorphism of Theorem (7.5). For `f = [n]` this is the Weil pairing
  `e_n : X[n] × X^t[n] → μ_n`.
- The discussion that follows, printed p.163 / PDF p.167, notes that
  these pairings are perfect by construction.
- Chapter VII, Theorem (7.5), printed p.100 / PDF p.104, is the
  Cartier duality `Ker(f^t) ≅ Ker(f)^D` behind that perfectness.

When `n` is prime to the characteristic of the algebraically closed
field `K`, the group schemes `X[n]` and `X^t[n]` over `K` are finite
étale. A perfect pairing between them therefore induces a perfect
pairing of their `K`-points with values in `μ_n(K)`. In particular
both kernels on `K`-points are trivial, which is the assertion here
for `X` the fibre of `A` at `s`.

The Lean target is stated for the relative constructors evaluated at
the geometric point `s` of a general base, not for an abelian variety
over `K`. A proof must therefore relate the actual relative pairing at
`Over.mk s` to the field pairing of the fibre, including base change
of the chosen dual and of its character construction, and it must
establish the field perfectness for the Library's constructors. The
literature does not prove these identifications for the Library's
constructors, and this file does not claim that it does.

The statement adds no axiom.

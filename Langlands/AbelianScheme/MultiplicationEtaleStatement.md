# Etale positive multiplication on abelian schemes

Author: Worker 299.

`Langlands.AbelianScheme.MultiplicationEtaleStatement` is a proposition target.
For every scheme `S`, every published `Langlands.AbelianScheme S` `A`, and
every natural number `n > 0` whose image in the global sections ring
`Γ(S, ⊤)` is a unit, it asserts Mathlib's `AlgebraicGeometry.Etale` for the
scheme morphism

```
(Langlands.GroupScheme.multiplication A.toGrp (n : ℤ)).hom.hom.left
  : A.X.left ⟶ A.X.left
```

This is the actual morphism of schemes underlying the imported integer
multiplication on the underlying group object `A.toGrp : Grp (Over S)`. That
multiplication is the integer power of the identity homomorphism in the
pointwise group of homomorphisms, so on `T`-points it is `x ↦ x ^ n`. The
natural number `n` is cast to `ℤ` only because the imported construction takes
an integer. Mathlib's `Etale f` asks that for every affine open `U` of the
target and every affine open `V ⊆ f⁻¹(U)` of the source the induced ring map
`Γ(A, U) → Γ(A, V)` be étale, the standard affine-local definition. The statement supplies no new scheme, morphism or
geometric property as data. The bundle `Langlands.AbelianScheme` supplies
smoothness, properness, geometrically connected fibres and explicit
commutativity; equivalence with the source definition remains a separate
obligation and is not used here.

## Source correspondence

The source is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article in the author's corrected version dated January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Printed page numbers equal the one-based PDF page numbers in this copy. The
pages below were read directly.

- Section 20, opening definition, p.42: over an arbitrary scheme `S`, an
  abelian scheme is a group scheme whose structure map is proper and smooth
  with connected geometric fibres. These are the conditions bundled in the
  imported `AbelianScheme`.
- Corollary 20.2(c), p.43: an abelian scheme is commutative. The imported
  bundle carries commutativity explicitly, which the imported multiplication
  needs; this statement does not prove commutativity.
- Proposition 20.7, p.44: for an abelian scheme `A` of relative dimension `g`
  over `S`, multiplication `n_A` is finite, flat and surjective, and "`n_A`
  (and therefore its kernel) is étale if and only if `n` is not divisible by
  any of the characteristics of the residue fields of `S`". This target is the
  forward implication of that last sentence for `n_A` itself. The proof
  derives it from Theorem 8.2.
- Theorem 8.2, p.13: for an abelian variety of dimension `g` over a field `k`
  and an integer `n > 0`, `n_A` is an isogeny of degree `n^(2g)`, étale if and
  only if the characteristic of `k` does not divide `n`. The sentence of
  Proposition 20.7 does not state a sign for `n`, but its proof invokes this
  positive-integer theorem, so the target keeps `0 < n`.

## The global-unit hypothesis

`IsUnit (n : Γ(S, ⊤))` is invertibility of the integer section on the whole
base, and makes sense for a nonaffine base. On any scheme a global section is a
unit exactly when its germ at every point is a unit, since local inverses are
unique and glue. In the local ring at `s` this holds exactly when the image of
`n` in the residue field `κ(s)` is nonzero, that is, when the characteristic of
`κ(s)` does not divide the positive integer `n`. So the hypothesis is
Milne's condition that `n` is divisible by no residue characteristic of `S`.
This reformulation is explained here and is not a theorem of the Lean module.

## Derived, dimension-free scope

The provenance is **derived**: Proposition 20.7 fixes a relative dimension `g`,
whereas this target assumes no globally constant relative dimension and omits
everything except the étaleness of `n_A`. The fixed `g` adds no hypothesis to
the étaleness conclusion. The relative dimension of the smooth structure map is
locally constant on `A`; composing with the zero section shows that the base
is covered by opens over which `A` has constant relative dimension. Over each
such open the restriction is an abelian scheme of relative dimension `g` to
which Proposition 20.7 applies, and its multiplication is the restriction of
`n_A`, so the conclusion holds because étaleness is local on the target.
Alternatively, the source argument (flatness from the fibrewise criterion plus
fibrewise étaleness from Theorem 8.2) is fibre by fibre and never compares
dimensions of different fibres. Only the order formula `n^(2g)` needs a fixed
`g`, and it is not stated here. This explains the mathematical scope; no
Lean proof is provided here.

There is no field, affineness, noetherian, connectedness, finiteness,
constant-dimension, characteristic, or ample-bundle assumption on `S` or `A`,
and no assumption that multiplication is already finite, flat or étale. The
target asserts no converse, no finiteness, flatness or surjectivity (the
separate `Langlands.GroupScheme.MultiplicationIsogenyStatement` covers these
for nonzero integers), no degree or rank formula, nothing about negative
integers, and nothing about the kernel (the separate
`Langlands.AbelianScheme.TorsionFiniteEtaleStatement` concerns positive
torsion; its proof task plans to use this target as an input).

## Formal status

The declaration is a `Prop`-valued `def` in universe `u`, not a theorem, an
axiom, or a field of the abelian-scheme bundle. Its proof is a separate
obligation after independent acceptance and publication of this statement.

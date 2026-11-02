# Statement: endomorphisms of the multiplicative group over an integral domain

Author: Worker 207.

This module states that, over the spectrum of an integral domain, every
endomorphism of the multiplicative group scheme is multiplication by a unique
integer. Only the proposition is defined here; this module proves nothing. The
declaration is in the namespace `Langlands.GroupScheme.Gm`.

## Lean statement

```lean
def EndomorphismsStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsDomain R],
    Function.Bijective (multiplication (Gm (Spec R)).toGrp)
```

- `Gm (Spec R)` is the published multiplicative group scheme over `Spec R`
  (module `Langlands.GroupScheme.Multiplicative`), and `.toGrp` is its
  underlying group object in `Over (Spec R)`.
- `multiplication G n : G ⟶ G` is the published multiplication by the integer
  `n` on a commutative group scheme, defined as the power `(𝟙 G) ^ n` in the
  pointwise group of homomorphisms (module
  `Langlands.AbelianScheme.Multiplication`). On points it is `x ↦ x ^ n`.
- The function being bijective means two things. Every group-scheme
  endomorphism of `𝔾_{m, Spec R}` equals `multiplication _ n` for some
  `n : ℤ`. Distinct integers give distinct endomorphisms.

The universe `u` of `R` is arbitrary. The only hypothesis is that `R` is an
integral domain. There are no field, characteristic or noetherian assumptions.

## Source

Milne, *Algebraic Groups* (2017), 2.22, printed p.46 (PDF p.62), over a field
`k`: "The only such elements in k[T,T⁻¹] are the powers T^n, n ∈ Z, of T, and
so the endomorphisms of Gm are the maps t ↦ t^n. Thus End(Gm) ≃ Z." Source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

## Provenance and scope

Milne states the result over a field. This statement extends it to integral
domains. The extension is standard and needs no new idea. Over a domain `R`,
the units of `R[T, T⁻¹]` are still the elements `c T^n` with `c ∈ Rˣ`. An
endomorphism sends `1` to `1`, which forces `c = 1`. The proof itself is a
separate obligation.

The hypothesis cannot be dropped entirely. Over a ring with a nontrivial
idempotent `e`, the map `t ↦ t^n` on the factor cut out by `e` and `t ↦ t^m` on
the complementary factor is an endomorphism. If `n ≠ m`, it is not of the form
`t ↦ t^k`.

This is the first step toward the character and cocharacter lattices of split
tori and of the Deligne torus over `ℂ`.

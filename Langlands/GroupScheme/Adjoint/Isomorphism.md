# Isomorphisms induced on supplied adjoint quotients

Work over an arbitrary field `k : Type u`. Let `q : G ⟶ A` and `p : H ⟶ B`
be actual homomorphisms satisfying `IsAdjointQuotient`, and let `e : G ≅ H`
be an actual isomorphism of group schemes over `k`.

This is an internal supporting construction from the existing quotient
universal property and all-test centre transport. Both quotients and the
original isomorphism are inputs. No external result is newly asserted.

## Constructed isomorphism and its square

`IsAdjointQuotient.killsCenter_iso_comp` proves that `e.hom ≫ p` kills the
full scheme-theoretic centre of `G`. Indeed an arbitrary central point maps
to a central point under `e`, by `mem_center_comp_iso`, and `p` kills that
point. All relative test schemes, including nonreduced tests, are retained.

`hq.mapIso hp e : A ≅ B` descends `e.hom ≫ p` through `q` using
`IsAdjointQuotient.desc`. Its inverse descends `e.inv ≫ q` through `p`.
The two inverse identities follow by `hom_ext`: after precomposition with
the corresponding quotient map, the factorization identities reduce them
to the two inverse identities of `e`.

The accompanying theorems give the actual quotient squares

```text
q ≫ (hq.mapIso hp e).hom = e.hom ≫ p,
p ≫ (hq.mapIso hp e).inv = e.inv ≫ q.
```

`mapIso_unique` states that the first square determines the isomorphism
uniquely. `mapIso_hom_points` evaluates that square on every test point.
`mapIso_symm` identifies the isomorphism induced by `e.symm` with the
inverse of the one induced by `e`.

## Compatibility with inner actions

For every relative test `T`, every `x : T ⟶ A.X`, and every `g : T ⟶ G.X`,
`mapIso_innerAction` proves

```text
hq.innerAction.act x g ≫ e.hom.hom.hom
  = hp.innerAction.act
      (x ≫ (hq.mapIso hp e).hom.hom.hom) (g ≫ e.hom.hom.hom).
```

The implemented proof applies
`AutomorphicAction.hom_ext_of_local_quotient_lift` to `q` and `x`.
Reductivity and adjointness make both schemes affine, so the flat
surjective quotient is fpqc. On any relative test where `x` lifts to a
point `h` of `G`, naturality and the quotient square turn the two inner
actions into conjugation by `h` and by its image under `e`, respectively.
Multiplicativity and preservation of inverses by `e` identify them.
Equality after this local lifting reflects to the original test.
No global lift of `x` is assumed.

## Scope

This unit constructs maps between supplied quotients and proves their
compatibility with supplied source isomorphisms and the actual inner
actions. It does not construct an adjoint quotient, a quasi-split model,
a cover, or an initial local isomorphism or inner discrepancy. The
unconditional `QuasiSplitInnerFormExistenceStatement` remains a separate
proof obligation.

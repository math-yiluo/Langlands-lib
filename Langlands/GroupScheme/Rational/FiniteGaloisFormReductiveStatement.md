# Statement: connected reductivity of finite-Galois forms

Author: Worker 1534.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.FiniteGaloisFormConnectedReductiveStatement.{u}`, a
`Prop`-valued `def` with one universe parameter `u`. It is a prerequisite of the
conditional infinite-field Steinberg reduction in
`Rational/QuasiSplitCocycleTorusReductionInfinite.lean`. There it shows that
the twisted group of `Rational/FiniteGaloisTwistExistenceStatement.lean` is
again connected reductive.

## Lean statement

```lean
def FiniteGaloisFormConnectedReductiveStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (G H : GroupScheme (Spec (CommRingCat.of K))),
    LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))) →
    IsConnectedReductive G → IsConnectedReductive H
```

The module imports `Langlands.GroupScheme.LocalGroupIso`,
`Langlands.GroupScheme.Reductive.Basic` and `Mathlib.FieldTheory.Galois.Basic`.

## Meaning

- `K` is an arbitrary field and `L/K` a finite Galois extension in the same
  universe. `G` and `H` are arbitrary group schemes over `Spec K`.
- The hypothesis `LocalGroupIso G H U`, for the cover `U = Spec L → Spec K`,
  is a family of group isomorphisms `G(Z) ≃* H(Z)` for every test `Z` over `K`
  with a point `Z ⟶ U`, natural in `Z` (module `LocalGroupIso`). By Yoneda this
  is an isomorphism `G_L ≅ H_L` of group schemes over `L`: `H` is an `L/K`-form
  of `G`. No compatibility with Galois descent data is required, and the family
  is only used as a hypothesis.
- `IsConnectedReductive` (module `Reductive/Basic`) asks that the structure
  morphism be smooth and affine, that the underlying space be connected, and
  that the base change to the algebraic closure `toAlgebraicClosure K` have
  trivial unipotent radical.

So the proposition says that connected reductivity passes from a group to any
of its finite-Galois forms.

## Sources and provenance

Provenance: derived.

- J. S. Milne, *Algebraic Groups* (2017), source
  `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  - Section 3.k (printed p.76, PDF p.92): "A `K/k`-form of `G` is an algebraic
    group `G'` over `k` that becomes isomorphic to `G` over `K`."
  - 6.46 (printed p.135, PDF p.151): "A connected group variety over a field
    `k` is said to be reductive if `G_{k^a}` is reductive, i.e., if its
    geometric unipotent radical `R_u(G_{k^a})` is trivial."
  - Summary 1.36 (printed p.17, PDF p.33): for an algebraic group, connected,
    irreducible and geometrically connected are equivalent.
- R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`, §10
  (printed p.78, PDF p.31). Steinberg applies 2.15 (stated for semisimple
  groups) to the twisted group `x(G)`, "a group over `k`, isomorphic to `G`
  over `K`". This is the use made of the proposition.

Derived content. No single source result states this implication. It combines
the definitions above with standard descent along `Spec L → Spec K`.
Smoothness and affineness of the structure morphism descend along this
faithfully flat quasi-compact cover. `H_L ≅ G_L` is connected because `G`,
connected with a rational point, is geometrically connected (Milne 1.36). `H` is
the continuous image of `H_L`, hence connected. The geometric unipotent radical
is computed over an algebraic closure `K̄`. Choosing a `K`-embedding
`L → K̄`, the base change of `G_L ≅ H_L` gives `G_{K̄} ≅ H_{K̄}`. So the two
geometric unipotent radicals are trivial together. The Lean hypothesis is the
concrete form of "`H` becomes isomorphic to `G` over `L`".

## What is not stated

- The converse, and invariance of semisimplicity or quasi-splitness, are not
  stated; quasi-splitness is in general not invariant under forms.
- Nothing is proved here; the implication is the obligation of a separate
  exact-target proof.

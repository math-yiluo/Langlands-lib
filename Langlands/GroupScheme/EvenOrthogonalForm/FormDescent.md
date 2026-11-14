# Descent of a form of the split `SO_{2n}` to an identity component

## Smoothness along local isomorphisms

- `smooth_of_groupIso`: an isomorphism of group schemes over `S` preserves
  smoothness of the structure morphism. The inverse isomorphism makes a
  trivial pullback square, and smoothness is stable under pullback.
- `smooth_of_localGroupIso`: if `G'` has local isomorphisms along
  `Spec N ⟶ Spec K` to a smooth group scheme `G`, then `G'` is smooth.
  Base change to `N` makes `G'` isomorphic to `G` (`toBaseChangeIso`), and
  the base change of `G` is smooth. Smoothness descends along the fpqc
  morphism `Spec N ⟶ Spec K` (published `smooth_of_baseChange` with
  `fieldExtension_fpqc`).

## The comparison and its descent

Let `N / K` be finite Galois, and let `φ` be local isomorphisms from `H` to
the split `SO_{2n}` along `Spec N ⟶ Spec K`. Let `G'` be a smooth affine
group scheme over `K` with local isomorphisms `χ` to the split `O_{2n}`
along the same cover.

- `compareLocalIso φ χ` is the family `s ↦ χ⁰(s)⁻¹ ∘ φ(s)` of local
  isomorphisms from `H` to the identity component `G'⁰`, where
  `χ⁰ = restrictIdentityComponent χ`. Its naturality follows from the
  naturality of `φ` and of the inverse of `χ⁰`.
- `nonempty_iso_identityComponent`: suppose matrices `g_σ` (`σ ∈ Aut_K(N)`)
  satisfy two conditions. First, the Galois twists of `φ` are conjugations
  by `g_σ`: `splitMatrix (ψ_σ(s) x) = s♯(g_σ) splitMatrix(x) s♯(g_σ⁻¹)`.
  Second, the matrices of the values of `χ` at `s ≫ σ*` and at `s` differ by
  the same conjugation. Then `H ≅ G'⁰`.

  Proof: by `isIndependent_of_galois`, it suffices that the comparison
  takes the same value at `s` and at `s ≫ σ*`. Since
  `φ(s ≫ σ*) = ψ_σ(s) ∘ φ(s)`, this reduces to
  `χ⁰(s ≫ σ*)(u) = ψ_σ(s)(χ⁰(s)(u))` for points `u` of `G'⁰`. Both sides
  are points of `SO_{2n}`, so it suffices to compare their matrices
  (`splitMatrix_injective`). By `restrictIdentityComponent_toFun_comp`,
  the matrix of a value of `χ⁰` is the matrix of the corresponding value of
  `χ` on `G'`. The two hypotheses then give the same matrix
  `s♯(g_σ) M s♯(g_σ⁻¹)`. The comparison is therefore independent of the
  cover point. Because `Spec N ⟶ Spec K` is fpqc, the published
  `LocalGroupIso.descend` turns it into an isomorphism of group schemes
  `H ≅ G'⁰`.

## Provenance

Derived. This is Galois descent for morphisms of group schemes, in the
form of the published fpqc descent of local group isomorphisms. It follows
the published type-`C` comparison (`SymplecticInnerForm.GroupDescent`): two
families of local isomorphisms with the same Galois discrepancy differ by
a descended isomorphism. Here the discrepancy is conjugation by the
similitude cocycle, and the identity component is handled through its
compatibility with field extension.

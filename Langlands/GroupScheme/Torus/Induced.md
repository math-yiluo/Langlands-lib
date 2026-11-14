# Induced tori

Authors: Worker 1532 and Worker 1341.

`Langlands.GroupScheme.IsInducedTorus T` is the proposition that a
commutative group scheme `T` over a field `k` is an induced torus in the
sense of Kaletha–Prasad, Definition 2.5.1. The module contains only this
definition. It records no theorems, and the explanations below are
provenance for the definition, not proved results.

## The definition

For `k : Type u` with `[Field k]` and
`T : CommGroupScheme (Spec (CommRingCat.of k))`, `IsInducedTorus T` holds
exactly when there exist

- a type `E : Type u` with `[Field E]` and `[Algebra k E]`, such that
  `FiniteDimensional k E` and `IsGalois k E`;
- a proof of `IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp)`,
  that is, the base change `T_E` is isomorphic as a group scheme over
  `Spec E` to the split torus `splitTorus _ J = 𝔾_m^J` for some finite
  type `J`;
- a type `I : Type u` and a `ℤ`-basis
  `b : Module.Basis I ℤ (characterLattice T_E)` of the character lattice
  `X^*(T_E) = Hom(T_E, 𝔾_m)`, where `T_E` is
  `(CommGroupScheme.baseChange (algebraBaseMap k E)).obj T`;

such that for every `σ : E ≃ₐ[k] E` and every `i : I` there is `j : I` with

```
characterLattice.galoisRepresentation k E T σ (b i) = b j.
```

`characterLattice.galoisRepresentation k E T` (module
`Langlands.GroupScheme.Torus.LatticeGalois`) is the existing action of
`Aut_k(E)` on `X^*(T_E)`, `(σ χ)(t) = σ (χ (σ⁻¹ t))`. Since `E/k` is
Galois, `E ≃ₐ[k] E` is `Gal(E/k)`.

The two base changes are the same term. `GaloisPointComparison.baseChanged
k E T.toGrp` is `(GroupScheme.baseChange (GaloisPointComparison.baseMap k
E)).obj T.toGrp`. Both `GaloisPointComparison.baseMap k E` and
`algebraBaseMap k E` abbreviate `Spec.map (CommRingCat.ofHom (algebraMap k
E))`, and `CommGroupScheme.baseChange` acts on underlying group schemes as
`GroupScheme.baseChange`. So the splitting condition and the lattice concern
the same group scheme over `Spec E`.

The permutation condition says that `σ` maps the set `{b i}` into itself.
The same holds for `σ⁻¹`, so each `σ` restricts to a bijection of `{b i}`.
Since `b` is injective, `σ` thus permutes the index set `I`. This is KP's
condition that the basis is invariant under the Galois group.

The index types `E` and `I` live in the universe `u` of `k`. This loses
nothing. A finite extension of `k` has an isomorphic copy in `Type u`, for
example on a `k`-vector space `k^n`. The lattice `characterLattice T_E`
itself has type `Type u`, so any basis can be reindexed by a subset of it.
Because `T_E` is split, `X^*(T_E)` is free of finite rank, so every basis
index type `I` is finite. The definition does not need to say so.

## Source and derived formulation

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page = PDF page − 31.

KP §2.5(a), Definition 2.5.1, printed p. 86 / PDF p. 117: "An `F`-torus `T`
is called induced if the lattice `X^*(T)`, equivalently `X_*(T)`, has a
`ℤ`-basis that is invariant under the Galois group of the splitting
extension of `T`." At the start of §2.5, KP define
`X^*(T) = Hom_{F^s}(T, 𝔾_m)` and `X_*(T) = Hom_{F^s}(𝔾_m, T)`, in natural
duality, with their action of `Θ = Gal(F^s/F)`. The 2024 corrections by the
same authors (`kaletha-prasad-2024-corrections`) do not change
Definition 2.5.1.

The definition is a direct transcription with two derived choices.

- **Some finite Galois splitting extension instead of the minimal one.**
  KP use the lattice over a separable closure `F^s` and the Galois group of
  the splitting extension, the minimal extension `E₀ ⊂ F^s` over which `T`
  splits. `E₀/F` is finite Galois, and `Θ` acts on `X^*(T)` through
  `Gal(E₀/F)`. Here the lattice is `X^*(T_E)` for some finite Galois
  extension `E/k` over which `T` splits. Embed `E` in `F^s`. Then
  `E₀ ⊂ E`, because `T` splits over `E`. Base change identifies `X^*(T_E)`
  with `X^*(T_{F^s})`, compatibly with the Galois actions, and `Gal(E/k)`
  acts through its quotient `Gal(E₀/k)`, which it surjects onto. So a
  basis is invariant under `Gal(E/k)` exactly when it is invariant under
  `Gal(E₀/k)`. Taking `E = E₀` gives the converse direction. Hence the
  existence of some such `E` agrees with KP's use of "the" splitting
  extension.
- **`X^*` instead of `X^*` or `X_*`.** KP allow either lattice; the
  definition uses the character lattice `X^*`. The perfect pairing of
  `X^*` and `X_*` is Galois-invariant. So if `{b i}` is a basis of `X^*`
  permuted by the Galois group, its dual basis `{b i^∨}` of `X_*` satisfies
  `σ (b i^∨) = (σ (b i))^∨` and is also permuted. The converse holds in the
  same way, so the two readings agree.

The definition includes the requirement that `T` split over `E`. It
therefore implies that `T` is a torus: it becomes isomorphic to some
`𝔾_m^J` after a finite Galois extension. No separate torus hypothesis is
imposed, and `k` is arbitrary, with no separability or perfectness
hypotheses.

## Uses

In KP §2.5(b), printed p. 87 / PDF p. 118, the base field `k` is a
discretely valued Henselian field with perfect residue field. KP
Definition 2.5.16, printed p. 91 / PDF p. 122, says that a `k`-torus `T` has
induced ramification if `T_K` is induced in the sense of Definition 2.5.1,
where `K` is the maximal unramified extension of `k`. Lemma 2.5.18 on the
same page concerns such tori. Neither is formalized in this module. A comparison of
`IsInducedTorus` with products of Weil restrictions `R_{E/F} 𝔾_m` is also
outside this module.

`IsInducedTorus.isTorus` extracts the splitting field already present in `IsInducedTorus`, proving that an induced torus is a torus. This shared lemma is used by the central-torus exactness and point-surjectivity statements.

# Galois descent of prescribed torus character values

`Langlands.GroupScheme.TorusEquivariantCharacterValueDescentStatement.{u}` is the existence half of the description of rational torus points by Galois-equivariant character values.

Let `k` and `L` be fields in the same arbitrary universe `u`, with an algebra structure `Algebra k L` and `IsGalois k L`. The extension may be infinite. Let `T` be any commutative group scheme over `Spec k`. Its actual scheme base change along `algebraBaseMap k L` is assumed to satisfy `IsSplitTorus`: it is isomorphic to a finite product of multiplicative groups over `Spec L`, including the empty product. Affineness or a separate torus hypothesis on `T` is not an additional premise.

Write `T_L` for this base change. Given any additive homomorphism

```text
φ : characterLattice T_L →+ Additive Lˣ,
```

assume, for every `k`-algebra automorphism `σ : L ≃ₐ[k] L` and every character `χ` of `T_L`, that

```text
(φ (characterLattice.galoisRepresentation k L T σ χ)).toMul
  = σ ((φ χ).toMul),
```

where the equality in the Lean hypothesis is after coercion of the units to `L`. `Additive Lˣ` writes the multiplicative group of units additively, so this is precisely a homomorphism from the character lattice to the multiplicative group of `L`.

The conclusion produces `h : Lie.AffinePoints T.toGrp k` such that, for every character `χ` of `T_L`,

```text
Lie.characterValue χ (rationalBaseChangePoint k L T h) = (φ χ).toMul.
```

This equality is in `Lˣ`. The point in its left side is the actual `L`-point of the scheme base change associated with `h`. The statement asserts existence, and contains no uniqueness claim. It imposes no finite-degree, perfectness, characteristic, or positive-rank hypothesis.

## Provenance

This is a derived formulation of classical Galois descent, specialized to the Library's actual scheme pullbacks and character action. Evaluation for a split torus identifies its `L`-points with homomorphisms from its character lattice to `Lˣ`. Equivariance makes the corresponding point Galois fixed, and affine point descent recovers a `k`-point. The Library supplies split-torus coordinates in `Torus.Lattice` and `Torus.WeightDecomposition`, the action in `Torus.LatticeGalois`, and effective affine descent for arbitrary Galois extensions in `AlgebraicGaloisPointDescent`.

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), use the induced-torus version in the proof of Lemma 6.4.10, printed pp. 227–228 (PDF pp. 258–259), and identify the quasi-split adjoint centralizer as an induced torus on printed p. 231 (PDF p. 262), before Definition 6.6.1. These passages motivate the intended consumer; they do not state this full arbitrary-Galois formulation verbatim. Source: `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The registered corrections of 1 November 2024 were searched for these locators and contain no correction naming them.

The declaration is reproduced exactly from the task context supplied by Worker 46 for Worker 4783's quasi-split adjoint simple-root transitivity application. This file states the proposition; its proof is a separate contribution.

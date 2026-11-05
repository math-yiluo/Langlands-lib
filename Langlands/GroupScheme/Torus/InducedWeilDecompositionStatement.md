# Induced tori over a prescribed finite Galois splitting field

Authors: Worker 1472 and Worker 1587. Worker 1587 supplied the exact target,
source locator and splitting-field refinement; Worker 1472 implemented the
Lean statement and this explanation.

`Langlands.GroupScheme.InducedTorusWeilDecompositionStatement.{u}` is a
Prop-valued definition in
`Langlands.GroupScheme.Torus.InducedWeilDecompositionStatement`.
It states a structural classification. This module contains no proof of that
classification.

For every field `k : Type u`, every field `L : Type u` with
`[Algebra k L] [FiniteDimensional k L] [IsGalois k L]`, and every
`T : CommGroupScheme (Spec (CommRingCat.of k))`, it asserts that

- if `IsSplitTorus (GaloisPointComparison.baseChanged k L T.toGrp)`, and
- if the existing `IsInducedTorus T` holds,

then there exist `n : ℕ` and `E : Fin n → IntermediateField k L` such that

```text
Nonempty (T ≅ WeilGm.commGroupScheme (CommRingCat.of k) (∀ i, E i)).
```

The isomorphism is in the category of commutative group schemes over
`Spec k`. The statement uses the existing `IsInducedTorus` from
`Langlands.GroupScheme.Torus.Induced` and the actual Weil restriction
`WeilGm.commGroupScheme` from
`Langlands.GroupScheme.Torus.WeilRestrictionCommutative`.
It adds no perfectness, characteristic, local-field, or affineness premise
on `T`. In particular, no additional torus premise is needed:
`IsInducedTorus` already requires splitting over a finite Galois extension.
The universe `u` is arbitrary.

Each `E i` is a field inside the prescribed `L`, containing `k`. It is
finite-dimensional and separable over `k` because `L/k` is finite Galois.
Each underlying `k`-module is consequently finite and projective. The
finite product algebra `B = ∀ i, E i` has those same module properties,
so it satisfies the hypotheses of the published Weil restriction
construction. These properties supply instances used to form the target;
they are not extra premises in the statement.

## The product-algebra packaging

The single Weil restriction from `B` expresses the usual finite product
of Weil restrictions from the fields `E i`. For every `k`-test scheme `S`,
the published `WeilGm.commPointsEquiv` identifies its points with
`(B ⊗[k] Γ(S))ˣ`. Tensor product commutes with this finite product:

```text
(∏ i, E i) ⊗[k] Γ(S) ≃ ∏ i, (E i ⊗[k] Γ(S)).
```

Taking units gives `∏ i, (E i ⊗[k] Γ(S))ˣ`, the product of the all-test
point groups of the individual Weil restrictions. The comparisons are
natural in `S`, so this is a group-scheme product description, including
nonaffine and nonreduced test schemes. This paragraph explains the derived
packaging of the target; the module does not implement a new comparison
isomorphism.

There is no positivity condition on `n`. When `n = 0`, the product
algebra is the one-element commutative `k`-algebra, and its tensor product
with `Γ(S)` again has one element. Its unit group is trivial, giving
the empty product of group schemes and the rank-zero torus.

## Original source and refinement

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023, §2.5(a), Definition 2.5.1 and the
following paragraph, printed p. 86 / PDF p. 117, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`
(SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`).
The retained original is
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023.pdf`.

That passage defines induced tori by a Galois-invariant lattice basis
and states that every induced torus is a product of restrictions
`R_{E/k} 𝔾ₘ` for possibly different finite separable extensions. The
Chapter 2 corrections in the authors' *Corrections and additions*,
version of 1 November 2024, PDF pp. 24–25, registered as
`kaletha-prasad-2024-corrections`
(SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`),
do not change Definition 2.5.1 or that classification paragraph.

Requiring the factors to be intermediate fields of any prescribed finite
Galois splitting field is a derived refinement of that source assertion.
The witness field quantified inside `IsInducedTorus T` need not be `L`,
nor need either field be given as a subfield of the other. A future proof
can compare their lattices after a common separable extension and
transport the permutation basis to the prescribed `Gal(L/k)` action.
Decomposing that finite basis into orbits, and taking the fixed field in
`L` of the stabilizer of one representative in each orbit, produces the
fields `E i`. The permutation lattices of their Weil restrictions then
give the desired isomorphism by Galois descent. This is the mathematical
provenance and a proposed proof route, not a proof supplied by this module.

The statement is a prerequisite for the induced-torus part of KP
Lemma 2.5.18. It states no local bounded-norm, valuation, topology, or
Iwahori-subgroup calculation.

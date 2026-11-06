# Maximal-torus images under central isogenies of smooth affine groups

Author: Worker 1531. The first proof adapts the published proof of
`centralIsogenyMaximalTorusImage` (`CentralIsogeny/MaximalTorusImageProof`,
Workers 1428 and 1531).

The module proves two theorems in namespace
`Langlands.GroupScheme.IsCentralIsogeny`, and records both in one
proposition, `Langlands.GroupScheme.CentralIsogenySmoothMaximalTorusImageStatement`,
proved by `Langlands.GroupScheme.centralIsogenySmoothMaximalTorusImage`.
Throughout, `k` is a field,
`π : G ⟶ H` is a central isogeny of group schemes over `k`
(`IsCentralIsogeny π`), and `G` is smooth and affine over `k`. Neither `G`
nor `H` needs to be reductive or connected.

## Statements

`IsCentralIsogeny.isMaximalTorus_of_comp_eq`: let `i : T ⟶ G` be a maximal
torus, `j : S ⟶ H` a closed subgroup with `S` a torus, and `f : T ⟶ S` a
homomorphism with `i ≫ π = f ≫ j`. Then `j` is a maximal torus of `H`,
maximal among all closed tori of `H`. Here `T` and `S` are commutative group
schemes and `f` is a homomorphism of their underlying group schemes. The
theorem does not assume `f` surjective.

`IsCentralIsogeny.exists_isMaximalTorus_image`: assume also that `H` is
affine and locally of finite type over `k`. Then every maximal torus
`i : T ⟶ G` has a maximal torus `j : S ⟶ H` and a homomorphism
`f : T ⟶ S` with `i ≫ π = f ≫ j`, such that `f` is an isogeny (finite, flat
and surjective) and its underlying morphism of schemes is flat, surjective
and quasi-compact.

`CentralIsogenySmoothMaximalTorusImageStatement` (a `Prop`-valued `def`,
universe `u`): for every field `k : Type u`, all group schemes `G`, `H` over
`Spec k` and every `π : G ⟶ H` with `G` smooth and affine and
`IsCentralIsogeny π`, the conjunction of

1. the conclusion of `isMaximalTorus_of_comp_eq`, for all commutative group
   schemes `T`, `S` and all `i`, `j`, `f` as above; and
2. the conclusion of `exists_isMaximalTorus_image`, for all `T` and `i`,
   under the additional instance hypotheses that `H` is locally of finite type
   and affine over `k`.

`centralIsogenySmoothMaximalTorusImage` proves it by applying the two
theorems.

## Proof of `isMaximalTorus_of_comp_eq`

The proof is the published proof of `centralIsogenyMaximalTorusImage` with
`CommGroupScheme.groupHom f` replaced by `f`. That proof used the
reductivity of `G` only to get smoothness and affineness of `G`, and never
used the reductivity of `H` or the surjectivity of `f`.

The first two parts of `IsMaximalTorus j` are the hypotheses. For
maximality, let `j' : S' ⟶ H` be a closed torus and `g : S ⟶ S'` a
homomorphism with `g ≫ j' = j`. We show that `g` is an isomorphism.

1. **Kernel exponent.** `IsCentralIsogeny.exists_pow_eq_one_kernel` gives
   `N > 0` with `x^N = 1` for every point `x` of the kernel of `π`. Kernel
   points are central (`IsCentralIsogeny.mem_center_of_comp_eq_one`).
2. **Power lift.** `π` is finite, flat and surjective.
   `CentralPowerLift.exists_comp_eq_multiplication_comp` gives a
   homomorphism `Φ : S' ⟶ G` with `Φ ≫ π = [2N] ≫ j'`.
   `torusImageClosedTorusStatement`, which needs `G` smooth and affine,
   factors `Φ = e ≫ z` through a closed torus `z : Z ⟶ G`.
3. **A multiple of `i` lies in `Z`.** Let `c = f ≫ g ≫ Φ`. Then
   `c ≫ π = ([2N] ≫ i) ≫ π`. On the universal point of `T`, the values `a`
   of `c` and `b` of `[2N] ≫ i` differ by a point `a b⁻¹` of the kernel. It
   is central and killed by `N`, so `a^N = b^N`. Hence
   `[2N²] ≫ i = ([N] ≫ f ≫ g ≫ e) ≫ z`.
4. **Maximality of `i`.** `exists_factor_of_multiplication_comp` gives
   `i = i' ≫ z`. Since `i` is a maximal torus, `i'` is an isomorphism, so
   `Φ = (e ≫ i'⁻¹) ≫ i`.
5. **`j'` lies in `j`.** `[2N] ≫ j' = Φ ≫ π = (e ≫ i'⁻¹ ≫ f) ≫ j`, and
   `exists_factor_of_multiplication_comp` for the torus `S'` gives
   `h' : S' ⟶ S` with `h' ≫ j = j'`.
6. **`g` is an isomorphism.** `(g ≫ h') ≫ j = j` and `(h' ≫ g) ≫ j' = j'`.
   Closed immersions are monomorphisms, so `h'` is inverse to `g`.

## Proof of `exists_isMaximalTorus_image`

`π` is finite (`IsCentralIsogeny.isFinite`). The published
`IsTorus.exists_isogeny_finiteHomImage` (`Torus/FiniteImage`), applied to
the closed torus `i` and to `π`, gives the actual schematic image `S` of
`i ≫ π`. It is a torus with closed inclusion `j : S ⟶ H`, and the
projection `f : T ⟶ S` is an isogeny with `f ≫ j = i ≫ π`. The isogeny
`f` is flat and surjective by definition and quasi-compact because it is
finite. The first theorem makes `j` a maximal torus.

## Provenance

This is a derived result for the maximal-torus isogeny reduction (Case B,
`MaximalTorusIsogenyReductionStatement`). Milne, *Algebraic Groups*, 2017
(source `milne-2017-algebraic-groups`), Proposition 17.20 (printed
pp.357–358) proves that a quotient map of connected group varieties carries
maximal tori onto maximal tori, under the standing assumption of Section 17b
(printed p.353) that the base field is algebraically closed. The theorems here hold over an
arbitrary field, without connectedness, but only for central isogenies. They
are not derived from 17.20: the proof is the finite-kernel argument over `k`
described above, which uses only Library results. The module makes no new
external assertion.

Checked with `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
over Library commit `dd78edadc914cf56ca81c595cee581a3570d415c`
(diagnostic `8fe7a90d-e5cb-4229-8911-4620b6d22e74`, Lake build): 0 errors,
0 warnings, axioms `propext`, `Classical.choice`, `Quot.sound`.

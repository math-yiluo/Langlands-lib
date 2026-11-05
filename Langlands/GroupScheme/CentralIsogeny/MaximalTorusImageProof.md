# Proof: central isogenies carry maximal tori onto maximal tori

Authors: Worker 1428, Worker 1531. Worker 1428 wrote the proof; Worker 1531
replaced its surjectivity helper by the Library lemma
`IsTorus.flat_and_surjective_multiplication` and rechecked it.

`Langlands.GroupScheme.centralIsogenyMaximalTorusImage` proves the
proposition `Langlands.GroupScheme.CentralIsogenyMaximalTorusImageStatement.{u}`
(module `CentralIsogeny/MaximalTorusImageStatement`). Let `π : G ⟶ H` be a
central isogeny of connected reductive groups over a field `k`, `i : T ⟶ G` a
maximal torus, and `j : S ⟶ H` a closed torus with `i ≫ π = f ≫ j` for some
`f : T ⟶ S` with surjective underlying morphism. Then `j` is a maximal torus
of `H`, maximal among all closed tori. The proof does not use the
reductivity of `H` or the surjectivity of `f`. Both are hypotheses of the
statement and are kept there. The module proves one helper result.

## Helper result

`exists_factor_of_multiplication_comp`: let `P` be a commutative group scheme
over `k` that is a torus, `z : Z ⟶ G` a closed subgroup and `φ : P ⟶ G` a
homomorphism. If `[n] ≫ φ = ψ ≫ z` for some `n ≠ 0` and some homomorphism
`ψ : P ⟶ Z`, then `φ = φ' ≫ z` for a homomorphism `φ' : P ⟶ Z`.

Proof. The torus `P` is integral (`IsTorus.isIntegral`). Multiplication by
`n` on `P` is surjective (`IsTorus.flat_and_surjective_multiplication`,
`Torus/Multiplication`, which also covers nonsplit tori), hence dominant, hence
schematically dominant because `P` is integral. The published
`exists_over_factor_of_schematic_precomp` (`ImageGenerationDominant`)
descends the factorization through the closed immersion `z` to a morphism of
schemes `a` with `a ≫ z = φ`. So every point of `φ` is a point of `z`, that
is, the range of `φ` lies in the range of `z`.
`SubgroupFunctor.IsRepresentedBy.factorHom` (`Rational/LeviFactorization`)
turns this into the homomorphism `φ'`.

## Main proof

The first two parts of `IsMaximalTorus j` are the hypotheses that `S` is a
torus and `j` is closed. For maximality, let `j' : S' ⟶ H` be a closed torus
and `g : S ⟶ S'` a homomorphism with `g ≫ j' = j`. We show that `g` is an
isomorphism.

1. **Kernel exponent.** `IsCentralIsogeny.exists_pow_eq_one_kernel`
   (`CentralIsogeny/KernelTorsion`) gives `N > 0` with `x^N = 1` for every
   point `x` of the kernel of `π`. Kernel points are central
   (`IsCentralIsogeny.mem_center_of_comp_eq_one`).
2. **Power lift.** `CentralPowerLift.exists_comp_eq_multiplication_comp`
   (`CentralIsogeny/PowerLift`) gives a homomorphism `Φ : S' ⟶ G` with
   `Φ ≫ π = [2N] ≫ j'`. The published `torusImageClosedTorusStatement`
   (`Torus/ImageProof`) factors `Φ = e ≫ z` through a closed torus
   `z : Z ⟶ G`.
3. **A multiple of `i` lies in `Z`.** Let `c = f ≫ g ≫ Φ : T ⟶ G`. Using
   `multiplication_naturality`, `g ≫ j' = j` and `i ≫ π = f ≫ j`, we get
   `c ≫ π = ([2N] ≫ i) ≫ π`. On the universal point of `T`, let `a` and `b`
   be the values of `c` and `[2N] ≫ i`. Then `a b⁻¹` is killed by `π`. So it
   is central and killed by `N`, which gives `a^N = (a b⁻¹)^N b^N = b^N`.
   Hence `[N] ≫ c = [2N²] ≫ i`, and so `[2N²] ≫ i = ([N] ≫ f ≫ g ≫ e) ≫ z`.
4. **Maximality of `i`.** By the helper result, `i = i' ≫ z`. Since `i` is a
   maximal torus and `Z` is a closed torus, `i'` is an isomorphism. So
   `Φ = (e ≫ i'⁻¹) ≫ i`.
5. **`j'` lies in `j`.** Now `[2N] ≫ j' = Φ ≫ π = (e ≫ i'⁻¹ ≫ f) ≫ j`, and
   the helper result for the torus `S'` gives `h' : S' ⟶ S` with
   `h' ≫ j = j'`.
6. **`g` is an isomorphism.** `(g ≫ h') ≫ j = g ≫ j' = j` and
   `(h' ≫ g) ≫ j' = h' ≫ j = j'`. Since `j` and `j'` are closed immersions,
   hence monomorphisms, `g ≫ h' = 1` and `h' ≫ g = 1`.

## Relation to the source argument

The statement's Markdown gives the source argument (Milne, *Algebraic
Groups*, 2017, source `milne-2017-algebraic-groups`): pass to an algebraic
closure by Theorem 17.82 (printed p.379), apply Proposition 17.20 (printed
pp.357–358) to the quotient map `π`, and descend by 17.82 again. The Lean
proof does not follow that route, because the Library has no proof of the
base-change criterion 17.82 (`MaximalTorusBaseChangeStatement` is unproved).
It implements instead the in-Library sketch given in the statement's
Markdown: the kernel exponent, the power lift and the closed image of a
torus, all over `k`. It does not base-change maximality. Supporting proofs
of integrality, closed torus images and surjectivity of `[n]` may use
splitting extensions. This finite-kernel argument is the image-direction
counterpart of the proof of `CentralIsogenySplitMaximalTorusLiftStatement`
(`CentralIsogeny/SplitMaximalTorusLiftProof`).

Checked with `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
over Library commit `ee0c0dd6da0a631f199c2bc0aa6040eece98f41d`
(diagnostic `eb3a7e01-134c-41a3-ba75-72e901c7807c`, Lake build): 0 errors,
0 warnings, axioms `propext`, `Classical.choice`, `Quot.sound`.

# Conditional torus reduction of quasi-split semisimple cocycles over infinite fields

Author: Worker 1534.

This module implements Steinberg's reduction (1965, §§10–11) of
`QuasiSplitCocycleTorusReductionStatement` over infinite fields. The proof is
conditional on seven named structural propositions, which remain explicit
hypotheses. It also provides the inner action of the target of a central
isogeny on its source. The finite-field case is handled separately (Lang's
theorem).

## Declarations

All are in namespace `Langlands.GroupScheme`.

- `fieldSpecMorphism_fpqc`: every morphism `Spec L' ⟶ Spec L` between spectra
  of fields (in one universe) is surjective, flat and quasi-compact. Proof:
  write it as `Spec.map φ` (`Spec.preimage`), regard `L'` as an `L`-algebra
  via `φ` and apply the published `fieldExtension_fpqc`.
- `AutomorphicAction.conjugation_kernelActsTrivially_of_isCentral`: for a
  homomorphism `π : G ⟶ A` of group schemes over any base whose kernel
  inclusion is central (`IsCentral (kernelι π)`), the kernel acts trivially in
  the conjugation action `conjugation (𝟙 G)` of `G` on itself. Proof: a kernel
  point `k` commutes with every `g` (`commute_of_mem_center`), so
  `k g k⁻¹ = g`.
- `IsCentralIsogeny.innerAction` (a `def`): for a central isogeny
  `π : G ⟶ A` over a field `K`, the action of `A` on `G` obtained by descending
  the conjugation action of `G` on itself along `π`. It is the published
  `AutomorphicAction.quotientAction` (module `ActionDescent`). That
  construction needs `π` flat, surjective and quasi-compact, which hold
  because a central isogeny is flat, surjective and finite. It also needs the
  kernel to act trivially, which is the previous lemma.
- `IsCentralIsogeny.innerAction_act_lift`: `innerAction` acts on a point
  `π h` as conjugation by `h`: `a.act (h ≫ π) g = h * g * h⁻¹`, on every test.
  Proof: `quotientAction_act_lift` followed by `conjugation_act`.
- `quasiSplitCocycleTorusReduction_of_infinite` (theorem): given proofs of
  `SimplyConnectedCoverExistenceStatement`,
  `FiniteGaloisTwistExistenceStatement`,
  `FiniteGaloisFormConnectedReductiveStatement`,
  `InfiniteFieldStronglyRegularPointStatement`,
  `QuasiSplitSimplyConnectedRegularConjugateStatement`,
  `CentralIsogenyStabilizerTorusStatement` and
  `CentralIsogenyQuasiSplitLiftStatement` (all at universe `u`), for every
  infinite field `K : Type u`, semisimple quasi-split `G` over `K`, finite
  Galois `L/K` in `Type u` and natural cocycle `ξ` of `G` on
  `Spec L → Spec K`, it gives `Nonempty ξ.TorusReduction`. This is the
  conclusion of `QuasiSplitCocycleTorusReductionStatement` with the extra
  hypothesis `Infinite K`.

## Proof of `quasiSplitCocycleTorusReduction_of_infinite`

1. The cover statement gives a simply connected central cover `π : C ⟶ G`.
   `C` is connected reductive (via `IsSimplyConnected.isSemisimple`), and `a`
   is `innerAction` of `π`, with `a(π h) = conj(h)`.
2. Twist existence, applied to the affine group `C`, the action `a` and `ξ`,
   gives a twisted group `H` and local isomorphisms `e : C_L ≅ H_L` with
   discrepancy `ξ`. The form statement makes `H` connected reductive.
3. The strongly regular point statement gives a rational point `y` of `H` whose
   centralizer lies in a closed torus `S`. The lift statement makes `C`
   quasi-split, since `G` is. The conjugacy statement then gives a strongly
   regular rational `x` of `C`, a finite Galois `L'/K`, a morphism of covers
   `r : Spec L' ⟶ Spec L` and `g ∈ C(L')` with `e_r (g x g⁻¹) = y`.
4. The stabilizer statement gives a closed torus `j' : T' ⟶ G` containing
   every point of `G` that fixes `x` under `a`.
5. The torus reduction is built with carrier `L'`, refinement `r` (fpqc by
   `fieldSpecMorphism_fpqc`), cochain `g ≫ π`, torus `T'` and inclusion
   `j'`. For the factorization clause, fix a test `Z` and points
   `b c : Z ⟶ Spec L'`. Then the twisted value
   `(b ≫ g ≫ π)⁻¹ · ξ(b ≫ r, c ≫ r) · (c ≫ g ≫ π)` fixes `x` under `a`, so it
   factors through `T'`. Indeed, pulling back `e_r(g x g⁻¹) = y` along `b` and
   `c` (naturality of `e`) gives `e_{b≫r}(x_b) = y = e_{c≫r}(x_c)`, where
   `x_d = (d ≫ g) x (d ≫ g)⁻¹`. The discrepancy law then gives
   `a(ξ(b ≫ r, c ≫ r)) x_c = x_b`, using injectivity of `e_{b≫r}`. Expanding
   with `a.act_mul_left` and `a(π h) = conj(h)` reduces the claim to a group
   identity, closed by `group`.

The theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

## Sources and provenance

Provenance: internal. The module formalizes no literature statement. It is
the bookkeeping that composes the seven structural propositions, each with its
own paired Markdown and sources, into the conclusion for infinite fields. The
route is that of R. Steinberg, *Regular elements of semi-simple algebraic
groups* (1965), source `steinberg-1965-regular-elements-semisimple-groups`,
SHA-256 `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`:
§10 (printed p.78, PDF p.31) for the infinite-field argument, and §11 (printed
p.79, PDF p.32) for passing to the simply connected covering group. Over
imperfect fields it follows Borel–Springer (1968) §8.6, source
`borel-springer-1968-rationality-properties-ii`, SHA-256
`e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`
(printed pp.483–484, PDF pp.41–42). Steinberg's §10 cochain `a⁻¹ x_γ γ(a)`
corresponds here to the twisted value of the cochain `g ≫ π`. The cochain is
taken in the cover `C` and pushed to `G` by `π`. This avoids lifting points of
the non-simply-connected group, which might need inseparable extensions.

## What is not stated or proved

- None of the seven hypotheses is proved here. Each is a separate statement
  module, and `SimplyConnectedCoverExistenceStatement` is already in the
  Library.
- The finite-field case, and the final unconditional proof of
  `QuasiSplitCocycleTorusReductionStatement`, are not in this module.

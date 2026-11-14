# Irreducible admissible components at the infinite places of a cuspidal realization

Module `Langlands.Automorphic.PlaceComponentExistence`. Worker 174 wrote it for G1 (Task 5992,
`8a7f44bc-c7bc-4ceb-96aa-6eff19b38f97`, which Worker 174 published from Task 5720). It proves the Library
statement `Langlands.Automorphic.CuspidalArchimedeanIrreducibleAdmissibleComponentStatement`
(module `Langlands.Automorphic.CuspidalArchimedeanPlaceComponent`) as
`Langlands.Automorphic.cuspidalArchimedeanIrreducibleAdmissibleComponent`. The statement is
unchanged and nothing is assumed beyond it.

Statement: let `F` be a number field with compact adele quotient, `r : ℕ`, and `T` an actual
cuspidal realization of `GL_{r+1}`. At every real place `v` there is a subspace of `T` that is
irreducible for the place actions at `v` (`PlaceComponent.IsIrreducible`) and admissible for
`O(r+1)` (`PlaceComponent.IsAdmissible`). At every complex place the same holds with `U(r+1)`.

## Proof at a real place (`CuspidalOperatorRealization.exists_realPlaceComponent`)

1. **Detection.** `T` is irreducible and nonzero. By `exists_realPlace_detection`
   (`PlaceComponentRealization`), some continuous matrix representation `τ₀` of `O(r+1)` has a
   nonzero intertwiner into every nonzero place-stable subspace of `T`.
2. **A finite-dimensional seed.**
   - Take `f₀ ≠ 0` and an open subgroup `U` fixing it (Library
     `finiteRepresentation_isSmooth`).
   - Let `E` be the compact orbit span of `f₀`. It is finite-dimensional (Library
     `compactRepresentation_isFiniteVector`), `K_∞`-stable, and `U`-fixed, since finite and
     compact translations commute.
   - In a basis `b` of `E`, let `R` be the representation of the compact factors on `ℂ^m`
     transported from `E`.
   - The inclusion `φ₀ = E ∘ b⁻¹` lies in the carrier `realCarrier v U R` and is nonzero.
3. **The carrier.**
   - It is stable under post-composition with the place actions (`isStable_realCarrier`).
   - It is admissible (`isAdmissible_realCarrier`, with joint admissibility of `T` from
     `CuspidalOperatorRealization.isJointlyAdmissible`).
   - Every nonzero stable subspace of it receives a nonzero `τ₀`-intertwiner
     (`intertwiners_ne_bot_postRep`, using the local finiteness and weak continuity of the
     place action).
4. **Minimal multiplicity.** `exists_isIrreducible_isAdmissible` (`PlaceComponentMinimal`)
   gives an irreducible admissible stable `N₀` inside the carrier.
5. **Evaluation.**
   - Choose `φ ∈ N₀` and `j` with `φ(eⱼ) ≠ 0`, and let `W` be the image of `N₀` under
     evaluation at `eⱼ`.
   - Evaluation is equivariant and nonzero on `N₀`, so `W` is irreducible
     (`isIrreducible_map`).
   - Evaluation is injective on `N₀` (`injOn_of_isIrreducible`), so `W` is admissible
     (`isAdmissible_map`).

## Complex places and the final theorem

`exists_complexPlaceComponent` is the same argument with `exists_complexPlace_detection` and
the complex carrier of `PlaceComponentCarrierComplex`.
`cuspidalArchimedeanIrreducibleAdmissibleComponent` combines the two.

## Modules of the proof

All are by Worker 174, in this directory or in `Langlands/Representation/`:

- `CompactMaschke`: invariant complements and lifting of intertwiners for compact groups.
- `PlaceComponentMinimal`: minimal multiplicity, and images under equivariant maps.
- `PlaceComponentDetection`: free sets and detection.
- `PlaceComponentRealization`: detection at an infinite place of an irreducible realization.
- `CuspidalJointAdmissibility`: joint admissibility without a central-character hypothesis.
- `PlaceComponentHom`: post-composition actions.
- `PlaceComponentCarrier` and `PlaceComponentCarrierComplex`: the admissible carriers.

## Sources

The mathematics is the archimedean part of the factorization of cuspidal automorphic
representations into irreducible admissible local components. See Getz–Hahn,
`getz-hahn-2024-automorphic-representations`, Lemma 6.3.6 and Theorem 6.3.7, pp. 165–166 (cited
in the Markdown of the target statement). The implemented proof does not use Flath's theorem.
It derives admissibility from joint admissibility, and irreducibility from a
minimal-multiplicity argument.

# Irreducible quotients detected by a dual eigenfunctional

Author: Worker 23.

This module is an internal helper for the proof of
`Langlands.GLMaximalConeJacquetQuotientStatement` (task b291a31b). It proves a
generic algebraic extraction: a finitely generated admissible representation
with a nonzero functional that is an eigenvector of a central subgroup has an
irreducible admissible quotient on which that subgroup acts by the same
character. The maximal-cone assembly (module `MaximalConeAssembly`, theorem
`PadicField.TopologicalData.exists_irreducible_oppositeJacquet_quotient`)
applies it to the whole normalized opposite Jacquet module along a dual
exponent, which yields the quotient `S` required by the target statement.

Konno 2003, proof of Theorem 3.5(i), takes an irreducible subrepresentation of
the weak `χ`-isotypic part of the Jacquet module instead. The Library statement
asks for a quotient of the whole opposite Jacquet module, so the proof uses a
different elementary construction: a nonzero eigenfunctional gives a nonzero
quotient with the prescribed character, and finite generation gives an
irreducible quotient of it. This is a derived algebraic step, not a
transcription of a numbered source result.

The fixed functional `φ` need not descend to the quotient `S`; the conclusion
asserts only the surjection and the scalar character.

## Generic extraction

In namespace `Langlands.MaximalConeQuotient`, for a group `G` acting on a complex
vector space `V` by `ρ`:

- `orbitKernel ρ φ`: for `φ : Module.Dual ℂ V`, the subrepresentation of vectors
  `v` with `φ (ρ g v) = 0` for every `g`. It is closed under the action because
  `ρ h (ρ g v) = ρ (h * g) v`. `mem_orbitKernel` unfolds membership.
- `exists_irreducible_quotient hG z hz χ ρ hfin hadm φ hφ heig`. Let `G` be a
  topological group in which every open subgroup contains a compact open
  subgroup (`hG`), and let `z : C →* G` be a homomorphism from any group `C`
  with central image (`hz : z c * g = g * z c`). Let `χ : C →* ℂ^×`, and let
  `ρ` be finitely generated over `MonoidAlgebra ℂ G` (`hfin`) and admissible
  (`hadm`). Suppose `φ ≠ 0` satisfies `φ (ρ (z c) v) = χ c * φ v`. Then there is
  `S : Rep.{uV} ℂ G` in the carrier universe of `ρ` such that `S.ρ` is
  irreducible and admissible, `Classification.HasScalarCharacter S.ρ z χ`
  holds, and some intertwiner `ρ → S.ρ` is surjective.

Proof:

1. `W = orbitKernel ρ φ` is proper, because a vector with `φ v₀ ≠ 0` is not in
   it (take `g = 1`).
2. The lattice of subrepresentations is coatomic. It is order-isomorphic to the
   lattice of group-algebra submodules (published
   `Subrepresentation.subrepresentationSubmoduleOrderIso`), which is coatomic for
   a finitely generated module. So some coatom `M` contains `W`.
3. `S` is Mathlib's quotient representation `ρ.quotient M`, and the intertwiner
   is the quotient map `mkQ`. `S` is irreducible by the published
   `CuspidalSupport.QuasicuspidalEmbedding.isIrreducible_of_isCoatom`. It is
   admissible by the published
   `Unramified.SphericalExistence.isAdmissible_of_surjective`, using `hG`.
4. Scalar character: for every `v`, the defect `ρ (z c) v - χ c • v` lies in `W`.
   Indeed, `ρ g` commutes with `ρ (z c)`, so
   `φ (ρ g (ρ (z c) v - χ c • v)) = φ (ρ (z c) (ρ g v)) - χ c * φ (ρ g v) = 0`.
   Hence the defect lies in `M`, and its image in the quotient is zero.

## Sources

T. Konno, *A note on the Langlands classification and irreducibility of induced
representations of p-adic groups* (2003), registered as
`konno-2003-langlands-classification`, proof of Theorem 3.5(i) (p.396). Konno
chooses `τ_λ` as an irreducible subrepresentation of the weak `χ`-isotypic
subspace of the opposite Jacquet module. The construction here differs and is
explained above.

# Class functions separate conjugacy classes of maximal-torus points

Worker 1800 and Worker 1401. Proof of
`Langlands.GroupScheme.ClassFunctions.TorusSeparationStatement` (module
`Langlands.GroupScheme.Rational.ClassFunctionsTorusSeparationStatement`), task
`0c854e73-f39c-45cf-9dda-31e34e1711f6`. The statement: let `G` be a semisimple
group over an algebraically closed field `k` and `j : T ⟶ G` a maximal torus.
If two points `s t ∈ T(k)` have the same image under the canonical
class-function quotient `ClassFunctions.rho G`, then `j(s)` and `j(t)` are
conjugate by a point of `G(k)`.

The argument follows the proof of Corollary 6.6, (b) implies (a), in
R. Steinberg, *Regular elements of semi-simple algebraic groups*, Publ. Math.
IHÉS 25 (1965) (source `steinberg-1965-regular-elements-semisimple-groups`,
printed p.63). Equal values of all regular class functions at `s` and `t` give
equal values at `s` and `t` of the restrictions to `T` of the characters of
the highest-weight representations. These restrictions are `W`-invariant and
triangular (Lemma 6.3, printed pp.62–63), and such functions separate
`W`-orbits in `T(k)`. Points of `T` that are `W`-conjugate are conjugate in
`G`. This module only assembles results proved elsewhere. Its own Lean
arguments are short and original.

## Ingredients

All are in the Library under these Lean names:

- `Langlands.GroupScheme.rootDatumExistence : RootDatumExistenceStatement`
  (module `Langlands.GroupScheme.Reductive.RootDatumExistence`): a split
  maximal torus of a connected reductive group over a field has a finite
  reduced root datum.
- `Langlands.GroupScheme.splitDominantHighestWeightRepresentationsExist`
  (module `Langlands.GroupScheme.Rational.DominantHighestWeightProof`): over an
  algebraically closed field, every dominant weight `lam` of a split pinning
  `p` is the highest weight of a representation `ρ : MatrixRepresentation G
  (Fin n)`, in the sense of `p.IsHighestWeight ρ lam`.
- `Langlands.GroupScheme.SplitPinning.exists_invariant_triangular_of_rho_eq`
  (module `Langlands.GroupScheme.Rational.TorusFormalCharacter`, by Worker
  1401): for `ρ` with `p.IsHighestWeight ρ lam`, and rational torus points
  `s t` with `(s ≫ p.inclusion.hom.hom) ≫ rho G = (t ≫ p.inclusion.hom.hom) ≫
  rho G`, the formal character `c` of `ρ` is invariant under each root
  reflection `p.rootDatum.reflection α`. It satisfies `c lam = 1` and
  `lam - ν ∈ p.positiveRootMonoid` whenever `c ν ≠ 0`. Its sums
  `c.sum (fun ν a => a * ν(s))` and `c.sum (fun ν a => a * ν(t))` are equal.
  Here `ν(s)` is `rationalCharacterEval` of the rational character
  corresponding to `ν`, coerced to `k`.
- `Langlands.LinearAlgebra.DominantTriangular.isInvariant_reflectionGroup_of_reflection`
  and `evalChar_apply` (module `Langlands.LinearAlgebra.InvariantOrbitSeparation`):
  invariance under every reflection `P.reflection i` gives invariance under
  the whole group `reflectionGroup P`. `evalChar φ c` is the sum
  `c.sum (fun ν a => a * φ (ofAdd ν))`.
- `Langlands.GroupScheme.characterValues_apply` and
  `Langlands.GroupScheme.ClassFunctions.torusSeparation_of_triangular`
  (module `Langlands.GroupScheme.Rational.ClassFunctionsTorusSeparationReduction`).
  `characterValues s (ofAdd ν)` is `ν(s)` as above.
  `torusSeparation_of_triangular hroot htri : TorusSeparationStatement` takes
  root datum existence `hroot` and a hypothesis `htri`. For every split pinning
  `p` over an algebraically closed field, every pair of rational torus points
  `s t` with the same `rho G` image as above, and every dominant `lam`,
  `htri` asks for some `c : characterLattice p.torus →₀ k` with four
  properties. `c` must be invariant under `reflectionGroup p.rootDatum`, have
  `c lam = 1`, have support below `lam`, and satisfy
  `evalChar (characterValues s) c = evalChar (characterValues t) c`.

## Lean proof

Namespace `Langlands.GroupScheme`.

- `SplitPinning.exists_isInvariant_triangular_of_rho_eq` proves exactly the
  `htri` conclusion for a given `p`, `s`, `t`, `h` and dominant `lam`, over an
  algebraically closed field `k`. Steps:
  1. `splitDominantHighestWeightRepresentationsExist` gives `ρ` with
     `p.IsHighestWeight ρ lam`.
  2. `exists_invariant_triangular_of_rho_eq` gives `c` with the
     reflection-invariance, normalization, support and equal-sum properties.
  3. `isInvariant_reflectionGroup_of_reflection` turns the reflection-wise
     invariance into invariance under `reflectionGroup p.rootDatum`.
  4. Rewriting both sides with `evalChar_apply` and `characterValues_apply`
     turns the equal sums into equal `evalChar` values.
- `ClassFunctions.torusSeparation : TorusSeparationStatement.{u}` is
  `torusSeparation_of_triangular rootDatumExistence` applied to
  `exists_isInvariant_triangular_of_rho_eq`.

## Scope

The theorem has exactly the type `TorusSeparationStatement.{u}`. It uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`. Of Steinberg's
Corollary 6.6 it gives only the implication (b) ⇒ (a), and only for points of
a maximal torus.

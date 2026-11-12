# Class functions separate conjugacy classes of maximal-torus points

Worker 1800 and Worker 1401 (previous TaskHub instance); Markdown refreshed by
Worker 5084. Proof of
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

## Relation to Steinberg's Corollaries 6.4 and 6.6

The statement's Markdown cites Steinberg 1965, Corollaries 6.4 and 6.6
(printed p.63, one-based PDF p.16). Steinberg proves (b) ⇒ (a) of 6.6 in three
steps: he reduces to `x, y ∈ T`; by 6.4 (the restriction
`β : C[G] → C[T/W]` is surjective) every `W`-invariant regular function on
`T` is the restriction of a regular class function, so all of them agree at
`x` and `y`; and the invariants of the finite group `W` separate its orbits
on `T` ([10, p.57, Prop. 18]). Finally, two points of `T` conjugate under
`W` are conjugate in `G` (Section 6, printed p.62).

The Lean route keeps the reduction, the orbit separation and the last step,
but does not prove Corollary 6.4 as a separate statement. It uses the input
behind 6.4 instead. Steinberg derives 6.4 from Lemma 6.3 a): for each
dominant `δ`, the restriction to `T` of the irreducible character `χ_δ` is
`sym δ` plus a combination of `sym δ'` with `δ' < δ` (7.15). Here:

- The trace of a highest-weight representation `ρ` of weight `lam` is a
  regular class function. Equal `rho G` images of `s` and `t` therefore give
  equal values of its torus restriction at `s` and `t`
  (`exists_invariant_triangular_of_rho_eq`, through
  `ClassFunctions.evaluation_eq_of_rho_eq`). Its torus restriction is the
  formal character `c` of `ρ`. This is `W`-invariant, has `c lam = 1`, and is
  supported below `lam`: the triangular form of Lemma 6.3. The Lean `ρ` is
  the one supplied by `splitDominantHighestWeightRepresentationsExist`, which
  constructs it as a covariant socle in `DominantHighestWeightProof`. The
  proof uses only `p.IsHighestWeight ρ lam`, not the classification of
  irreducible representations by highest weight.
- Inside `exists_mem_reflectionGroup_of_triangular` (used by
  `torusSeparation_of_triangular`), with `W = reflectionGroup p.rootDatum`,
  the triangular spanning lemma `isInvariant_mem_of_triangular` is applied to
  the submodule `ker (evalChar φ - evalChar ψ)`, where `φ` and `ψ` are the
  character values at `s` and `t`. That submodule contains a triangular
  invariant `c` for every dominant `lam`, so it contains every `W`-invariant
  regular function on `T`. This is the spanning half of Lemma 6.3 a), and so
  of 6.4, used only for evaluation at two points. So every `W`-invariant
  regular function on `T` takes equal values at `s` and `t`, as in
  Steinberg's use of 6.4.
- `exists_mem_eq_of_evalChar_eq` proves the orbit separation for the finite
  reflection group by an argument written for this project, valid in every
  characteristic, instead of citing [10].
- The step from `W`-conjugacy to `G(k)`-conjugacy uses `k`-points of `G`
  normalizing the torus that realize each reflection
  (`IsRootDatumOf.exists_isNormalizingPoint`). The reduction to a fixed
  maximal torus is unnecessary, because the statement already places `s` and
  `t` in an arbitrary maximal torus. That torus is split because `k` is
  algebraically closed.

Steinberg's injectivity (6.2) and the isomorphism half of 6.4 are not needed
and not proved.

## Scope

The theorem has exactly the type `TorusSeparationStatement.{u}`. It uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`. Of Steinberg's
Corollary 6.6 it gives only the implication (b) ⇒ (a), and only for points of
a maximal torus.

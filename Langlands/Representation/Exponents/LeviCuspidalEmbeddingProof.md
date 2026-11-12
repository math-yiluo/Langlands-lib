# Renard VI.2.1 for actual represented parabolics: proof

Module `Langlands.Representation.Exponents.LeviCuspidalEmbeddingProof`.

## Purpose and scope

This module proves the published proposition
`Langlands.Aubert.General.RepresentedParabolic.LeviCuspidalEmbeddingStatement`
(module `Langlands.Representation.Exponents.LeviCuspidalEmbeddingStatement`), which is
Renard, *Représentations des groupes réductifs p-adiques* (2026 version), VI.2.1,
Corollary and its proof (printed p. 139 / PDF p. 145). The theorem is

```
theorem leviCuspidalEmbedding : LeviCuspidalEmbeddingStatement.{u, v}
```

in namespace `Langlands.Aubert.General.RepresentedParabolic`. Its type is the unchanged
statement at its two universes. The field, group and representation universes stay
independent: `k : Type u`, the carriers of `π` and `ρ` are in `Type v`, the Jacquet module
stays in `Type v`, and the induced representation has carrier `Type (max u v)`. The proof
uses no premise beyond the statement's own hypotheses. These hypotheses are:

- `k` is a nonarchimedean local field (`Field`, `ValuativeRel`, `TopologicalSpace`,
  `IsNonarchimedeanLocalField`, `T2Space`);
- `G` is a connected reductive group scheme over `Spec k`;
- `G(k)` carries `RationalPointFamily.pointTopology`, with the retained
  `LocallyCompactSpace` and `NonarchimedeanGroup` instances;
- `π : SmoothRep.{0, u, v} ℂ G(k)` is irreducible.

For such `π`, the theorem gives an actual parabolic `p : P ⟶ G`, a rational Levi
`l : M ⟶ P`, a geometric unipotent radical `r : U ⟶ P` and an isomorphic multiplication
`subgroupMultiplication l r`. At this one datum it proves four things, writing
`J = (leviJacquetFunctor p l r hp hr hl hmul).obj π`:

1. `J` is nontrivial.
2. `J` satisfies the written-out supercuspidality condition: for every actual parabolic
   datum `(P', M', U', p', l', r', …)` of `M` with `¬ IsIso p'`,
   `(jacquetFunctor p' l' r' …).obj J` is a subsingleton.
3. There is an irreducible `ρ : SmoothRep.{0, u, v} ℂ M(k)` satisfying the same
   supercuspidality condition, with a surjective `J.representation.IntertwiningMap
   ρ.representation`.
4. There is an injective intertwiner from `π.representation` to the representation of
   `(leviInductionFunctor p l r hp hr hl hmul).obj ρ`.

Here `M(k)` carries `leviPointTopology l hl` and the instances
`leviPoints_locallyCompactSpace` and `leviPoints_nonarchimedeanGroup`, as in the
statement.

## Declarations

- `module_finite_comp_of_surjective`: for a representation `ρ` of a group `H` on `V` and
  a surjective homomorphism `φ : H' →* H`, if `ρ.asModule` is finitely generated over
  `MonoidAlgebra ℂ H`, then `(ρ.comp φ).asModule` is finitely generated over
  `MonoidAlgebra ℂ H'`.
- `leviJacquetFunctor_obj_finite`: Renard VI.1.3 for actual represented parabolics. It
  has the same hypotheses as the statement, together with any actual parabolic datum and
  any smooth `π`. If `π.representation.asModule` is finitely generated over
  `MonoidAlgebra ℂ G(k)`, then the representation of
  `(leviJacquetFunctor p l r hp hr hl hmul).obj π`, as a module, is finitely generated
  over `MonoidAlgebra ℂ M(k)`.
- `leviCuspidalEmbedding`: the target theorem.

The helper module `Langlands.Representation.Exponents.LeviCuspidalEmbeddingDescent` is
part of this contribution. Its theorem `leviJacquet_supercuspidal_of_minimal` is the
descent step. It takes `LeviParabolicExtensionStatement` and
`LeviParabolicTransitivityStatement` as hypotheses; see its own Markdown.

## Proof

### `module_finite_comp_of_surjective`

Let `s` be a finite set generating `ρ.asModule` over `ℂ[H]`. Let `N` be the
`ℂ[H']`-submodule of `(ρ.comp φ).asModule` spanned by the same set. Let `S` be the
subrepresentation `Subrepresentation.ofSubmodule' N` of `ρ.comp φ`. Its underlying
subspace is also stable under `ρ`, since every `g ∈ H` is `φ g'` for some `g'` and
`ρ g = (ρ.comp φ) g'`. This defines a subrepresentation `S'` of `ρ` with the same
subspace. Its submodule `S'.asSubmodule` contains `s`, so it contains the `ℂ[H]`-span of
`s`, which is everything. Hence every vector lies in `N`, and `s` generates
`(ρ.comp φ).asModule` over `ℂ[H']`.

### `leviJacquetFunctor_obj_finite`

1. **Compactness of `P(k)\G(k)`.** `compactSpace_leftQuotient_pointImage_of_dynamic`
   (module `ArbitraryParabolicFiniteSupportReduction`) takes two inputs. The first is
   `parabolicDynamic : ParabolicDynamicStatement` (module
   `Langlands.GroupScheme.Absolute.ParabolicDynamicProof`). The second is
   `BruhatTits.dynamicParabolicQuotientCompact` (module
   `Langlands.BruhatTits.Parabolic.QuotientCompactProof`). Both are published,
   unconditional proofs. The helper gives
   `CompactSpace (Induction.LeftQuotient (pointImage p))` for the literal point image of
   `p`, in the statement's point topology. This is the composition submitted as
   `arbitraryParabolicQuotientCompact` in Task 4777. It is written out here so that the
   proof depends only on the current Library.
2. **Semidirect decomposition.** `isSemidirectDecomposition_pointImage` (module
   `ArbitraryParabolicInduction`) shows that `pointImage p`, `pointImage (l ≫ p)` and
   `pointImage (r ≫ p)` form an actual semidirect decomposition.
   `isClosed_pointImage_comp` shows that the radical image is closed.
3. **Finite generation over the Levi image.**
   `JacquetFiniteGeneration.finite_of_compactQuotient` (module
   `Langlands.Representation.Aubert.General.JacquetFiniteGeneration`) gives finite
   generation over `ℂ[pointImage (l ≫ p)]` of `jacquetFunctor h hU` applied to `π`. That
   functor is `normalizedJacquetFunctor (pointImage (r ≫ p)) (pointImage (l ≫ p))`. So is
   the represented `jacquetFunctor p l r hp hr hl hmul`, up to the proofs of closedness
   and normalization, and proof irrelevance identifies the two. The argument covers
   `G(k)` by finitely many double cosets `P(k) g K`, and on the Jacquet module `P(k)`
   acts through its Levi projection.
4. **Transport to `M(k)`.** `leviJacquetFunctor` is this Jacquet functor followed by
   pullback along the group isomorphism `leviPointsEquiv p l hp hl : M(k) ≃ₜ*
   pointImage (l ≫ p)`. The pullback has the same carrier, and its representation is the
   composite with `leviPointsEquiv`. `module_finite_comp_of_surjective` then gives finite
   generation over `ℂ[M(k)]`.

### `leviCuspidalEmbedding`

1. **Finite generation of `π`.** Irreducibility of `π` makes `π.representation.asModule`
   a simple module over `ℂ[G(k)]`. Hence it is nontrivial (`IsSimpleModule.nontrivial`)
   and finitely generated (an instance).
2. **A minimal datum.** `exists_minimal_nontrivial_leviJacquet` (module
   `LeviCuspidalEmbeddingSteps`) gives a `ParabolicDatum` `(P, M, U, p, l, r, …)` with
   two properties. First, `J` is nontrivial. Second, every datum whose parabolic has
   strictly smaller all-test range `SubgroupFunctor.range` has subsingleton Jacquet
   module. The witnesses of the statement are the fields of this datum.
3. **Supercuspidality of `J`.** `leviJacquet_supercuspidal_of_minimal` is applied to the
   published proofs `leviParabolicExtension : LeviParabolicExtensionStatement` and
   `leviParabolicTransitivity : LeviParabolicTransitivityStatement`. With the minimality
   from step 2, unbundled from `ParabolicDatum`, it gives the written-out
   supercuspidality of `J`.
4. **Finite generation of `J`.** `leviJacquetFunctor_obj_finite` at this datum, applied
   to the finite generation of `π`.
5. **Quotient and embedding.** `cuspidalEmbedding_of_finite_supercuspidal` (module
   `LeviCuspidalEmbeddingSteps`) takes `J` nontrivial, finitely generated and
   supercuspidal. It returns the irreducible supercuspidal `ρ`, the surjective
   intertwiner `J → ρ` and the injective intertwiner `π → i_P^G ρ`. That proof takes a
   maximal proper subrepresentation of `J`, which exists by finite generation, and uses
   the quotient `ρ`. Exactness of the normalized Jacquet functor on surjections makes `ρ`
   supercuspidal. Frobenius reciprocity (`leviFrobeniusReciprocity`) and irreducibility
   of `π` turn the quotient map into an injective intertwiner.

The resulting tuple is exactly the conclusion of the statement.

## Comparison with the source

Renard's proof chooses a standard parabolic `P` minimal with `r_P^G(V) ≠ 0`. It derives
supercuspidality of `r_P^G(V)` from V.3.11 and Lemma VI.1.4. Lemma VI.1.3 gives finite
type, hence an irreducible quotient. Exactness of `r` makes that quotient supercuspidal,
and Frobenius reciprocity gives the embedding. The Lean proof follows the same steps,
with these differences:

- **Minimality.** Parabolics are arbitrary actual represented parabolics, not standard
  ones. Minimality is for the all-test range of the parabolic. Its existence comes from
  the Noetherian coordinate ring of `G`, not from finiteness of the set of standard
  parabolics.
- **Traces of parabolics.** V.3.11 is replaced by the published parabolic extension
  `leviParabolicExtension`. It produces a parabolic of `G` inside `P` whose trace on `M`
  is a given parabolic of `M`.
- **Finite type.** The source cites VI.1.3, whose proof uses compactness of `P\G`. Here
  finite type is proved in `leviJacquetFunctor_obj_finite` from the published dynamic
  quotient compactness. That lemma has the same content as the published
  `LeviJacquetFiniteTypeStatement`. It is stated in explicit form and is not submitted as
  a proof of that statement, whose proof task is Task 4814
  (`27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b`).
- **Supercuspidality.** It is the written-out condition of the statement: vanishing of
  the normalized Jacquet module for every actual parabolic of `M` that is not an
  isomorphism. Standard parabolics are not used.

## Authorship

The descent module `LeviCuspidalEmbeddingDescent` is Worker 59's shared draft, with the
signature proposed by Worker 947. Worker 5021 wrote the finite-generation lemmas and the
assembly.

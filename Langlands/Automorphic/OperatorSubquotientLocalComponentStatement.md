# Local components of automorphic representations of `GL_n` at every place

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module
`Langlands.Automorphic.OperatorSubquotientLocalComponentStatement` makes five
definitions, proves one membership lemma about the first, and states three
propositions. It proves none of the propositions. Everything is for
`GL_(r+1)` over a number field `F`.

Definitions:

- `Langlands.Archimedean.gkHoms` and `Langlands.Archimedean.IsGKIsotypic`
  (general `(𝔤, K)`-module vocabulary, with the lemma
  `Langlands.Archimedean.mem_gkHoms`, proved by `Iff.rfl`);
- `Langlands.Automorphic.OperatorSubquotient.IsFinitePlaceIsotypic`;
- `Langlands.Automorphic.OperatorSubquotient.IsRealPlaceIsotypic`;
- `Langlands.Automorphic.OperatorSubquotient.IsComplexPlaceIsotypic`.

Propositions:

- `Langlands.Automorphic.LocalComponentExistenceStatement` (Getz–Hahn
  Theorem 6.3.7, existence of the factors; Flath Theorem 3);
- `Langlands.Automorphic.LocalComponentEmbeddingStatement` (Flath, last
  sentence of the proof of Theorem 1; derived, see §4);
- `Langlands.Automorphic.LocalComponentDeterminationStatement` (Getz–Hahn
  Theorem 6.3.7 with the uniqueness of the factors; Flath Theorem 3).

The module also has seven `local instance` declarations. Six put the
additive group structure `Submodule.addCommGroup` on the Library's function
spaces and realization carriers, as `OperatorSubquotient.lean` does. The
seventh, `localComponentGeneralLinearTopology`, puts the canonical matrix
topology `(padicField v).canonicalGeneralLinearTopology n` on
`GL_n(F_v)`, the topology of the local category
`Correspondence.AutomorphicObject (padicField v)`, as
`IsobaricAutomorphicRepresentation.lean` does. The Library proves that it
is the topology of the completion (`FiniteAdelicGL.localGL_topology_eq`,
`Langlands/Global/FiniteAdelicGL/PadicComparison.lean`). All seven are local
to this file.

Library vocabulary used:

- `OperatorSubquotient` with `Space`, `representation` (the action of the
  whole operator algebra `automorphicOperatorAlgebra`), `localRepresentation v`
  (the finite adelic action restricted to `GL_n(F_v)` along
  `FiniteAdelicGL.localInclusion`) and `Equivalence`
  (`Langlands/Automorphic/OperatorSubquotient.lean`);
- `IrreducibleOperatorSubquotient F r`, an operator subquotient of rank
  `r + 1` whose whole operator action is irreducible
  (`IrreducibleOperatorSubquotient.lean`); its `Equivalence` is that of the
  underlying subquotients;
- `realPlaceCompactRepresentation v` and `complexPlaceCompactRepresentation v`,
  translation by `O(n)` or `U(n)` at one infinite place
  (`OperatorSubquotientPlaceAction.lean`), and `realPlaceLieAction v` and
  `complexPlaceLieAction v`, the complexified Lie algebra of `GL_n(F_v)` acting
  by right differentiation at `v` (`OperatorSubquotientLieAction.lean`);
- `OperatorSubquotient.IsJointlyAdmissible`
  (`AutomorphicAdmissibilityStatement.lean`);
- `FiniteLocalGL F n v = GL_n(F_v)`
  (`Langlands/Global/FiniteAdelicGL/LocalFactor.lean`);
- `Correspondence.AutomorphicObject (padicField v) n`, the actual
  irreducible admissible smooth representations of `GL_n(F_v)`
  (`Langlands/Correspondence/AutomorphicRelations.lean`, an abbreviation of
  `IrreducibleAdmissibleRep`, `Langlands/Representation/Category/Basic.lean`);
- `Archimedean.IsRealGKModule`, `IsComplexGKModule`,
  `IsIrreducibleGKModule` and `IsAdmissibleGKModule`
  (`Langlands/Representation/Archimedean/GKModule.lean`);
- Mathlib's `Representation.IntertwiningMap` and
  `Representation.IsIrreducible`.

**Why it is here.** This task builds the `GL_n` part (L4) of the global
automorphic library. Getz–Hahn Theorem 6.3.7 (Flath's theorem) attaches to
an automorphic representation a local representation at every place, and
says the factors are unique. Every local-global statement about automorphic
representations (strong multiplicity one, isobaric sums, the local
components used in Henniart's argument) refers to these components. The
Library has local components only for supplied tensor presentations, and
only at the finite places (§6). This module states that they exist at every
place for every irreducible operator subquotient, without a supplied
presentation.

**Proof targets.** Later proof tasks should prove the three Library
statements. `LocalComponentExistenceStatement` and
`LocalComponentDeterminationStatement` have the universe parameter `u` of
the number field. `LocalComponentEmbeddingStatement` has `u` and the
universe `uW` of the local carrier.

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered
file. In Getz–Hahn, Chapter 6, printed page = PDF page − 14. In the
Corvallis volume, Part I, printed page = PDF page + 4.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | Definition 6.3.5, Lemma 6.3.6 and Theorem 6.3.7, p.165 (PDF 179); end of Theorem 6.3.7 and its proof, p.166 (PDF 180) |
| `flath-1979-tensor-products` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | end of the proof of Theorem 1, p.180 (PDF 176); restricted tensor products (3), the tensor product of admissible representations, Theorems 2 and 3, p.181 (PDF 177); admissible `G(𝔸)`-modules and archimedean factors, p.182 (PDF 178) |

The Flath file is the Corvallis volume, Part I; the article is printed
pp.179–183.

**What Getz and Hahn state** (p.165–166):

> Definition 6.3.5. An automorphic representation of `G(𝔸_F)` is an
> irreducible admissible `(𝔤, K_∞) × G(𝔸_F^∞)`-module isomorphic to a
> subquotient of `𝒜`.
> Two automorphic representations are said to be isomorphic if they are
> isomorphic in the category of `(𝔤, K_∞) × G(𝔸_F^∞)`-modules.

> Lemma 6.3.6 Every irreducible admissible `(𝔤, K_∞) × G(𝔸_F^∞)`-module
> `(π, V)` is an algebraic tensor product
> `(π, V) = (π_∞ ⊗ π^∞, V_∞ ⊗ V^∞)` where `(π_∞, V_∞)` is an irreducible
> admissible `(𝔤, K_∞)`-module and `(π^∞, V^∞)` is an irreducible admissible
> representation of `G(𝔸_F^∞)`. The isomorphism classes of `(π_∞, V_∞)` and
> `(π^∞, V^∞)` are uniquely determined by `(π, V)`.

> Assume that `K_∞ = ∏_{v|∞} K_v` is a maximal compact subgroup of `G(F_∞)`
> and `K^∞ = ∏_{v∤∞} K_v` is a compact open subgroup of `G(𝔸_F^∞)`.
>
> Theorem 6.3.7 Every irreducible admissible `(𝔤, K_∞) × G(𝔸_F^∞)`-module
> `(π, V)` admits a factorization
> `(π, V) = (⊗_{v|∞} π_v, ⊗_{v|∞} V_v) ⊗ (⊗'_{v∤∞} π_v, ⊗'_{v∤∞} V_v)`
> where `(π_v, V_v)` is an irreducible admissible `(𝔤_v, K_v)`-module for
> `v|∞` and is an irreducible admissible representation of `G(F_v)` for
> `v ∤ ∞`. The restricted tensor product is taken with respect to a choice of
> nonzero vectors `φ_v ∈ V_v^{K_v}` for all but finitely many places `v`. The
> factors `(π_v, V_v)` are uniquely determined by `(π, V)` up to isomorphism.

The proof combines Lemma 6.3.6, "Exercise 4.14" for the archimedean
factorization and "Flath's theorem (Theorem 5.7.1)" for the finite one: "The
uniqueness statement follows from the corresponding uniqueness statements in
each of the results cited in the proof."

**What Flath states.** At the end of the proof of Theorem 1 (p.180), for
`G = G_1 × G_2` and an admissible irreducible `G`-module `W ≅ W_1 ⊗ W_2`:

> The class of `W_i` is determined by that of `W`, for the restriction of `W`
> to `G_i` is `W_i`-isotypic.

On p.181, for restricted tensor products: "if `{x'_v}` is another collection
of nonzero vectors such that `x_v` and `x'_v` lie on the same line in `W_v`
for almost all `v`, then the `A`-modules `⊗_{x_v} W_v` and `⊗_{x'_v} W_v`
are isomorphic"; and for admissible `G_v`-modules with
`dim W_v^{K_v} = 1` for almost all `v`, "The isomorphism class of `W` is in
fact independent of the choice of `x_v ∈ W_v^{K_v}`". Then:

> THEOREM 3. Every admissible irreducible representation of `G(𝔸)` is
> factorizable. The factors are unique up to equivalence.

On p.182 an admissible `G(𝔸)`-module for a number field is "both a
`(𝔤_∞, K_∞)`-module and a smooth `G(𝔸_f)`-module" whose actions commute,
with finite-dimensional `τ`-isotypic components for every continuous
irreducible `τ` of `K`; and "In Theorem 3, the factors at the archimedean
places `v` are to be admissible `(𝔤_v, K_v)`-modules."

## 2. The definitions

**`Archimedean.gkHoms ρ π ρ' π'`.** For a group `K`, a complex Lie algebra
`L`, representations `ρ` of `K` on `V` and `ρ'` on `W`, and Lie actions `π`
of `L` on `V` and `π'` on `W`, this is the subspace of linear maps
`f : V → W` with `f (ρ k x) = ρ' k (f x)` and `f (π X x) = π' X (f x)` for all
`k`, `X`, `x` (`mem_gkHoms`). These are the morphisms of `(𝔤, K)`-modules
from `V` to `W`.

**`Archimedean.IsGKIsotypic ρ π ρ' π'`.** The images of the maps in
`gkHoms ρ π ρ' π'` span `W`: `⨆ f ∈ gkHoms ρ π ρ' π', range f = ⊤`. When
`(V, ρ, π)` is irreducible this says that `W` is a sum of
`(𝔤, K)`-submodules isomorphic to `V`, that is, `W` is `V`-isotypic in
Flath's sense.

**`OperatorSubquotient.IsFinitePlaceIsotypic Q v ρ`.** For a finite place
`v` and a representation `ρ` of `GL_n(F_v)` on `W`: the ranges of the
intertwining maps from `ρ` to `Q.localRepresentation v` span `Q.Space`.
This is "the restriction of `Q` to `GL_n(F_v)` is `ρ`-isotypic".

**`OperatorSubquotient.IsRealPlaceIsotypic Q v ρ π`** and
**`IsComplexPlaceIsotypic Q v ρ π`.** For an infinite place `v`, `ρ` a
representation of `O(n)` (real `v`, `Matrix.unitaryGroup (Fin n) ℝ`) or
`U(n)` (complex `v`, `Matrix.unitaryGroup (Fin n) ℂ`) and `π` an action of
the complexified Lie algebra `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` or `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`: this is
`IsGKIsotypic` for the target `(Q.Space, Q.realPlaceCompactRepresentation v,
Q.realPlaceLieAction v)`, or its complex analogue. This is "the restriction
of `Q` to `(𝔤_v, K_v)` is `(ρ, π)`-isotypic".

When `ρ` is irreducible and `Q.Space` is nonzero, `Q` is `ρ`-isotypic at
`v` exactly when `ρ` is a local component of `Q` at `v` in the sense of
Getz–Hahn and Flath. If `Q ≅ ⊗_w π_w` with `π_v ≅ ρ`, then as a
representation of the group (or pair) at `v`, `Q ≅ π_v ⊗ U` with `U` the
tensor product of the other factors. Choosing a basis of `U` exhibits `Q` as
a direct sum of copies of `π_v`. Conversely, a `ρ`-isotypic module
determines the class of `ρ` (Flath, p.180, quoted in §1). These facts are
background. They explain the definition and are not asserted in Lean.

The definitions are not restricted to irreducible `ρ`. Without
irreducibility they are weak: every module is isotypic for itself.
Each statement therefore assumes or concludes irreducibility of the local
representations it quantifies over.

## 3. `LocalComponentExistenceStatement`, matched with Theorem 6.3.7

The statement says: for every number field `F : Type u`, every `r` and every
`Q : IrreducibleOperatorSubquotient F r` with
`Q.subquotient.IsJointlyAdmissible`,

1. for every finite place `v` there is
   `A : AutomorphicObject.{u, u} (padicField v) (r + 1)`, an irreducible
   admissible smooth representation of `GL_(r+1)(F_v)`, with
   `Q.subquotient.IsFinitePlaceIsotypic v A.obj.representation`;
2. for every real place `v` there are `V : ModuleCat.{u} ℂ`, a representation
   `ρ` of `O(r+1)` on `V` and an action `π` of `ℂ ⊗_ℝ 𝔤𝔩_(r+1)(ℝ)` on `V`
   with `IsRealGKModule (r + 1) ρ π`, `IsIrreducibleGKModule ρ π`,
   `IsAdmissibleGKModule ρ` and `Q.subquotient.IsRealPlaceIsotypic v ρ π`;
3. likewise at every complex place, with `U(r+1)`, `ℂ ⊗_ℝ 𝔤𝔩_(r+1)(ℂ)`
   and `IsComplexGKModule`.

The match with Theorem 6.3.7 for `G = GL_(r+1)`:

- **Automorphic representations.** An irreducible operator subquotient is a
  subquotient of the automorphic forms by spaces stable under
  `GL_(r+1)(𝔸_f)`, `K_∞` and the enveloping algebra, irreducible for all
  these operators together (`AutomorphicAdmissibilityStatement.md` §5). With
  joint admissibility (the Library's Hom form of admissibility,
  `AutomorphicAdmissibilityStatement.md` §2) it is an irreducible admissible
  `(𝔤, K_∞) × G(𝔸_F^∞)`-module, as in Definition 6.3.5 and in Flath's
  definition on p.182. The Library's `K_∞` is the standard product of the
  `O(r+1)` and `U(r+1)` at the infinite places.
- **The factors.** Getz–Hahn's `π_v` for `v ∤ ∞` is an irreducible
  admissible representation of `G(F_v)`, smooth since it is a factor of the
  smooth `π^∞`. The Lean `A` is an object of the Library's category of
  irreducible admissible smooth representations of `GL_(r+1)(F_v)`. For
  `v | ∞`, `π_v` is an irreducible admissible `(𝔤_v, K_v)`-module. The Lean
  `(V, ρ, π)` is a `(𝔤𝔩_(r+1)(F_v), K_v)`-module in the sense of Getz–Hahn
  Definition 4.4.6 (`IsRealGKModule`, `IsComplexGKModule`), irreducible and
  admissible.
- **"Is a factor".** Theorem 6.3.7 gives a tensor factorization. The Lean
  statement records its consequence at one place: the restriction of `Q` to
  the group or pair at `v` is isotypic of the type of the factor (§2,
  Flath's "the restriction of `W` to `G_i` is `W_i`-isotypic").
- **Universes.** The finite factors are taken in `AutomorphicObject.{u, u}`
  and the archimedean carriers in `ModuleCat.{u} ℂ`, the universe of the
  number field and of the automorphic forms. A factor of `Q` is isomorphic
  to a subspace of `Q.Space` (the image of an embedding), so it has a model
  in this universe.

## 4. `LocalComponentEmbeddingStatement` (derived)

The statement says: for `Q` as in §3,

1. for every finite place `v`, every `W : Type uW` and every irreducible
   representation `ρ` of `GL_(r+1)(F_v)` on `W`,
   `IsFinitePlaceIsotypic v ρ` holds exactly when there is a nonzero
   intertwining map from `ρ` to `Q.subquotient.localRepresentation v`;
2. at every real place `v`, for every `(V, ρ, π)` with
   `IsIrreducibleGKModule ρ π`, `IsRealPlaceIsotypic v ρ π` holds exactly when
   some nonzero map lies in `gkHoms ρ π (realPlaceCompactRepresentation v)
   (realPlaceLieAction v)`;
3. likewise at every complex place.

So a local representation is the local component exactly when it embeds
into the restriction of `Q`. No smoothness, admissibility or
`IsRealGKModule` hypothesis is made on `ρ`; it is a consequence.

**Provenance.** This is a derived statement. It follows from
`LocalComponentExistenceStatement` and elementary module theory (§7, route
2), and it is Flath's justification of the uniqueness of the factors
(p.180, quoted in §1). It is stated separately because consumers usually
know a local representation through an embedding (for example a slice of a
tensor presentation, §6) and need to conclude that it is the local
component. The universe `uW` of the local carrier is arbitrary.

## 5. `LocalComponentDeterminationStatement`, matched with Theorem 6.3.7

The statement says: for every number field `F : Type u`, every `r` and all
`Q Q' : IrreducibleOperatorSubquotient F r`, both jointly admissible,
`Nonempty (Q.Equivalence Q')` holds exactly when

1. at every finite place `v` there is an irreducible representation `ρ` of
   `GL_(r+1)(F_v)` on some `W : ModuleCat.{u} ℂ` for which both `Q` and `Q'`
   are `ρ`-isotypic at `v`;
2. at every real place `v` there is `(V, ρ, π)` with `V : ModuleCat.{u} ℂ`
   and `IsIrreducibleGKModule ρ π` for which both are `(ρ, π)`-isotypic;
3. likewise at every complex place.

The match:

- **Isomorphism.** `Q.Equivalence Q'` is a linear equivalence of the
  quotient spaces intertwining every element of `automorphicOperatorAlgebra`,
  the subalgebra generated by right translation by `GL_(r+1)(𝔸_f)`, right
  translation by `K_∞` and the enveloping algebra (`OperatorCore.lean`). A
  linear equivalence commutes with all these generators exactly when it
  commutes with the generated algebra. So this is isomorphism in Getz–Hahn's
  category of `(𝔤, K_∞) × G(𝔸_F^∞)`-modules (Definition 6.3.5).
- **"⇒".** Isomorphic automorphic representations have isomorphic factors:
  "The factors `(π_v, V_v)` are uniquely determined by `(π, V)` up to
  isomorphism" (Theorem 6.3.7), Flath's "The factors are unique up to
  equivalence" (Theorem 3).
- **"⇐".** Automorphic representations with isomorphic factors at every place
  are isomorphic. By §2 and §4, the right side says that `Q` and `Q'` have
  isomorphic local components at every place. Both are then the restricted
  tensor product of the same factors, by the factorization of Theorem 6.3.7.
  By Flath p.181 its isomorphism class does not depend on the choice of the
  vectors `φ_v ∈ V_v^{K_v}`.
- **Irreducibility on the right side.** The right side requires an
  irreducible `ρ`. Without it the right side would hold for any `Q`, `Q'`:
  both are isotypic for the direct sum of their two restrictions.
- **Universe.** The common local representations are taken in
  `ModuleCat.{u} ℂ`. By §3 the local components of `Q` have models there, so
  "⇒" loses nothing.

## 6. Relation to the Library

- **`OperatorQuotientTensorPresentation`**
  (`Langlands/Automorphic/OperatorQuotientTensorPresentation.lean`) takes a
  restricted tensor equivalence onto `Q.finiteRepresentation` as supplied
  data and builds local slices. Its Markdown says that the module "does not
  assert that every quotient has such a presentation". The present
  statements make no reference to a presentation. They assert that the
  local components exist, also at the infinite places, and characterize
  them through the restriction of `Q` itself.
- **`PresentedLocalComponent.lean`** and
  **`CuspidalAllLocalIrreduciblePresentationExistenceStatement`**
  (proved in `CuspidalAllLocalIrreduciblePresentationProof.lean`) give
  irreducible admissible local components at every finite place for
  cuspidal operator realizations with a spectral presentation. They do not
  cover non-cuspidal automorphic representations, operator subquotients or
  infinite places.
- **`IrreducibleSubquotientAdmissibilityStatement`**
  (`AutomorphicAdmissibilityStatement.lean`, stated, unproved) says that
  every irreducible operator subquotient is jointly admissible. Once it is
  proved, the joint admissibility hypotheses here can be discharged. They are
  kept so that these statements can be proved from Flath's theorem alone,
  without Harish-Chandra finiteness.
- **Restriction of equivalences.** The Library already transfers an
  equivalence to the finite, compact and Lie actions:
  `OperatorSubquotient.Equivalence.finiteRestriction`
  (`OperatorSubquotient.lean`),
  `OperatorSubquotient.Equivalence.compactRestriction`
  (`OperatorSubquotientTensorHorizontal.lean`) and
  `OperatorSubquotient.Equivalence.map_realPlaceLieAction`
  (`OperatorSubquotientLieAction.lean`, "The original equivalence intertwines
  every actual real-place quotient operator"). With §3 these give the "⇒"
  direction of §5.
- The Library's restricted tensor products of smooth representations are in
  `Langlands/Representation/RestrictedTensor/` and
  `Langlands/Representation/Smooth/Factorization/`.

## 7. Proof routes (for the proof tasks; not part of the statements)

1. **Existence.** Getz–Hahn's route: split `Q` as `π_∞ ⊗ π^∞` (Lemma
   6.3.6), factor `π^∞` by Flath's theorem for the restricted product
   `GL_(r+1)(𝔸_f)` (Theorem 2; the spherical Hecke algebras of
   `GL_(r+1)(𝒪_v)` are commutative), and factor `π_∞` over the infinite places
   (Getz–Hahn Exercise 4.14). Then `Q|_v ≅ π_v ⊗ U` is a direct sum of copies
   of `π_v`.
2. **Embedding from Existence.** Let `A` be the component given by §3. A
   nonzero intertwining map from an irreducible `ρ` is injective, because its
   kernel is invariant. Its image is a simple submodule of `Q|_v`, which is a
   sum of submodules isomorphic to the simple `A`. Such a module is
   semisimple and every simple submodule of it is isomorphic to `A`. So
   `ρ ≅ A`, and the maps from `ρ` span `Q.Space` because those from `A` do.
   Conversely, if `Q` is `ρ`-isotypic then some map from `ρ` is nonzero,
   because `Q.Space` is nonzero (`IrreducibleOperatorSubquotient.space_nontrivial`).
   The archimedean case is the same for `(𝔤, K)`-modules.
3. **Determination.** "⇒": take the components of `Q` from §3 (their
   carriers in `ModuleCat.{u} ℂ`) and transport isotypy along the given
   equivalence (§6). "⇐": by route 2 the local components of `Q` and `Q'`
   are isomorphic at every place. By the factorization in route 1 both `Q`
   and `Q'` are isomorphic to the restricted tensor product of these
   components, which does not depend on the choice of spherical vectors
   (Flath p.181). An isomorphism of `(𝔤, K_∞) × G(𝔸_F^∞)`-modules commutes
   with the generated operator algebra.

## 8. Not asserted

- a tensor product isomorphism `Q ≅ ⊗_v π_v`, or the existence of an
  `OperatorQuotientTensorPresentation` of `Q`;
- that almost all local components are unramified, or that
  `dim π_v^{K_v} = 1` for almost all `v` (Flath Theorem 2);
- Lemma 6.3.6 (the splitting `π_∞ ⊗ π^∞`) on its own;
- that a nonzero module isotypic for two irreducible types makes the types
  isomorphic (elementary module theory, background in §2);
- that the local components of a cuspidal representation are generic or
  unitary, or any statement about Hilbert space completions (Flath
  Theorem 4);
- anything for groups other than `GL_n`, for a maximal compact subgroup
  other than the Library's standard one, or for function fields.

## 9. Provenance

`LocalComponentExistenceStatement` and `LocalComponentDeterminationStatement`
are source statements: Getz–Hahn (2024) Theorem 6.3.7 and Flath (1979)
Theorem 3, for `G = GL_(r+1)` over a number field. Their existence and
uniqueness clauses are read through isotypic restriction at each place.
`LocalComponentEmbeddingStatement` is derived (§4). The following choices
belong to this formalization:

- an automorphic representation is an irreducible, jointly admissible
  `OperatorSubquotient`, with isomorphism given by `Equivalence`;
- "`π_v` is the factor of `Q` at `v`" is phrased as "`Q` restricted to the
  group or pair at `v` is `π_v`-isotypic" (Flath p.180), through the new
  definitions `IsFinitePlaceIsotypic`, `IsRealPlaceIsotypic`,
  `IsComplexPlaceIsotypic` and the general `gkHoms`, `IsGKIsotypic`;
- finite local factors are objects of `AutomorphicObject.{u, u}`, and
  archimedean factors are `(𝔤, K)`-modules on carriers in `ModuleCat.{u} ℂ`
  satisfying the Library's `IsRealGKModule` or `IsComplexGKModule`,
  `IsIrreducibleGKModule` and `IsAdmissibleGKModule`.

The Lean file was checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. The
three statements are `def`s returning `Prop`.

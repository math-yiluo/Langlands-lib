# The head as the cosocle

Author: Worker 375.

This module completes the canonical head of `Classification/CanonicalConstituents`
as the cosocle, the maximal semisimple quotient, of a finite-length
representation. It constructs no new quotient. The cosocle is the published
quotient `head ρ` of `ρ` by `headKernel ρ`, with the published surjective
projection `toHead ρ`, whose kernel is `headKernel ρ` (`ker_toHead`). The module
proves the following laws of this quotient:

- the head kernel is the radical: the intersection of the maximal
  subrepresentations, and, through the published correspondence between
  subrepresentations and group-algebra submodules, the Jacobson radical of
  `ρ.asModule`;
- for finite-length `ρ`, the head has finite length and is semisimple;
- every intertwiner from `ρ` to a semisimple representation factors uniquely
  through the projection, with no finite-length hypothesis;
- intertwiners induce maps of heads, functorially;
- for finite-length `ρ`, the head is equivalent to every maximal semisimple
  quotient;
- the head of a smooth representation is smooth, with bundled versions in the
  category of smooth representations.

## Provenance

This is a derived internal construction. Silberger, *The Langlands quotient
theorem for p-adic groups* (1978), Proposition 5.9 (printed page 102, page 8 of
the retained PDF), compares Jordan–Hölder multiplicities in the "maximum
completely reducible quotient representations" of two normalized inductions. The
present module supplies that object for an arbitrary finite-length representation
over a field. Silberger does not construct it. The definition through the radical
and its universal property are standard algebra and are not taken from the source.
The proofs reuse Mathlib's Jacobson radical of a module (`Module.jacobson`), its
behaviour for semisimple and Artinian modules, and Mathlib's equivalences between
representations and modules over the group algebra `k[G]`.

## Setting

The declarations live in namespace `Langlands.Classification`. `k : Type uk` is
an arbitrary field, `G : Type uG` is any group, and `ρ` is a representation of `G`
over `k` on `V : Type uV`. Other representations over `k` have carriers
`W : Type uW` and `U : Type uU` in independent universes. For an object
`A : Rep k G` of Mathlib's representation category, apply the results to `A.ρ`.
The head `head ρ` is a representation on `V ⧸ headKernel ρ`, which lies in the
carrier universe `uV` of `V`.

No topology is used except in the last two sections. No finite dimension over `k`,
admissibility or `p`-adic hypothesis is assumed anywhere, and no hypothesis
excludes the zero representation. Finite length means the published
group-algebra predicate `IsFiniteLength k[G] ρ.asModule`, finite composition
length of `ρ.asModule` over `k[G]`. Semisimple means Mathlib's
`Representation.IsSemisimpleRepresentation`. It is equivalent to semisimplicity
of the `k[G]`-module (`Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`).

## The head kernel is the radical

- `isIrreducible_iff_isCoatom_ker q hq`: for a surjective intertwiner
  `q : ρ → π`, `π` is irreducible exactly when the kernel `q.ker` is a coatom of
  the lattice of subrepresentations of `ρ`, that is, a maximal proper
  subrepresentation.
- `mem_headKernel_iff_forall_isCoatom ρ v`: `v` lies in the head kernel exactly
  when it lies in every maximal proper subrepresentation of `ρ`. For the converse
  direction, the quotient of `ρ` by a maximal subrepresentation `S` is an
  irreducible quotient with carrier `V ⧸ S` in `Type uV`, so the defining
  condition of `headKernel ρ` applies to it.
- `headKernel_eq_sInf_isCoatom ρ`: `headKernel ρ` is the infimum, in the published
  complete lattice of subrepresentations (`Representation/SubrepresentationLattice`),
  of the maximal proper subrepresentations. If `ρ` has none, both sides are all of
  `ρ`.
- `asSubmodule_headKernel ρ`: the `k[G]`-submodule of `ρ.asModule` corresponding to
  `headKernel ρ` is `Module.jacobson k[G] ρ.asModule`. Equivalently
  (`headKernel_eq_ofSubmodule'_jacobson`), `headKernel ρ` is the subrepresentation
  corresponding to the Jacobson radical.
- `ker_equivLinearMapAsModule_toHead ρ`: the kernel of the projection, viewed as a
  `k[G]`-linear map `ρ.asModule → (head ρ).asModule`, is the Jacobson radical.

These are proved lemmas about the existing carrier, not a second definition.

## Finite length: finite length and semisimplicity

Assume `h : IsFiniteLength k[G] ρ.asModule`.

- `isFiniteLength_head h`: `IsFiniteLength k[G] (head ρ).asModule`, because the
  head is a quotient of `ρ`.
- `isSemisimpleRepresentation_head h`: `head ρ` is semisimple. The head is Artinian
  over `k[G]`. The surjection `ρ.asModule → (head ρ).asModule` has the Jacobson
  radical as kernel, so it maps the radical of `ρ.asModule` onto the radical of the
  head, which is therefore zero. An Artinian module with zero Jacobson radical is
  semisimple.

The module asserts no semisimplicity for arbitrary `ρ`. Without finite length the
head need not be semisimple. For example, for the regular representation of the
integers over `ℚ` the group algebra is the Laurent polynomial ring, whose Jacobson
radical is zero, so the head is the whole representation, which is not
semisimple. This example is explanatory and not formalized.

## Universal factorization

Let `σ` be a representation over `k` on `W` in any universe, with
`hσ : Representation.IsSemisimpleRepresentation σ`. No finite length is assumed.

- `headKernel_le_ker_of_isSemisimpleRepresentation hσ f`: the head kernel lies in
  the kernel of every intertwiner `f : ρ → σ`. The Jacobson radical of `ρ.asModule`
  lies in the kernel of every linear map to a semisimple module.
- `headLift f hσ : head ρ → σ` is the intertwiner induced by `f` on the quotient
  (`Submodule.liftQ`). Its evaluation law is `headLift_toHead`:
  `headLift f hσ (toHead ρ v) = f v`. In bundled form,
  `(headLift f hσ).comp (toHead ρ) = f` (`headLift_comp_toHead`).
- `headLift_unique hσ hg`: every intertwiner `g : head ρ → σ` with
  `g.comp (toHead ρ) = f` equals `headLift f hσ`.
- `existsUnique_comp_toHead hσ f`: there is exactly one intertwiner
  `g : head ρ → σ` with `g.comp (toHead ρ) = f`.

The statements apply to irreducible targets.
`isSemisimpleRepresentation_of_isIrreducible` shows that an irreducible
representation is semisimple. `headKernel_le_ker_of_isIrreducible` is the
resulting kernel inclusion for every intertwiner to an irreducible
representation, in any carrier universe and without surjectivity.

## Functoriality

Let `σ` on `W` and `τ` on `U` be representations over `k`.

- `headKernel_le_comap f`: every intertwiner `f : ρ → σ` maps `headKernel ρ` into
  `headKernel σ`. Linear maps carry Jacobson radicals into Jacobson radicals.
- `headMap f : head ρ → head σ` is the induced intertwiner (`Submodule.mapQ`).
  `headMap_toHead` says `headMap f (toHead ρ v) = toHead σ (f v)`.
  `headMap_comp_toHead` is the bundled form
  `(headMap f).comp (toHead ρ) = (toHead σ).comp f`.
- `headMap_unique hg`: `headMap f` is the only intertwiner of heads with this
  property.
- `headMap_id ρ`: `headMap (id ρ) = id (head ρ)`.
- `headMap_comp f g`: for `g : σ → τ`,
  `headMap (g.comp f) = (headMap g).comp (headMap f)`.

## Uniqueness of the maximal semisimple quotient

Assume `h : IsFiniteLength k[G] ρ.asModule`. Let `π` be a semisimple
representation over `k`, with carrier in any universe, and let `q : ρ → π` be an
intertwiner. Suppose `hq` says that `q` is maximal: the kernel of `q` lies in the
kernel of every intertwiner from `ρ` to a semisimple representation with carrier
in `Type uV`.

- `headKernel_eq_ker_of_forall_le_ker h hπ q hq`: the kernel of `q` is the head
  kernel. The head is one of the tested semisimple quotients, by
  `isSemisimpleRepresentation_head`. Conversely, the head kernel lies in every such
  kernel, by the universal factorization.
- `nonempty_headEquiv_of_forall_le_ker h hπ q hsurj hq`: if moreover `q` is
  surjective, then `head ρ` and `π` are equivalent as representations. The
  equivalence is the published `headEquivOfSurjective`.

The actual object and the factorization above remain the primary interface.

## Smooth representations

Let `G` also carry a topology.

- `isSmooth_head hρ`: if `ρ` is smooth (`IsSmooth ρ`), so is `head ρ`, by the
  published `isSmooth_of_surjective` applied to the surjective projection.

The bundled versions live in namespace `Langlands.SmoothRep`. Here
`A B C : SmoothRep.{uk, uG, uV} k G` are objects of the published category of
smooth representations over `k`, and `A.headQuotient` and `A.toHeadQuotient` are
the published smooth head and its projection (`Classification/CanonicalConstituents`).
Its representation is `head A.representation` by definition.

- `HasFiniteLength.headQuotient h`: if `A.HasFiniteLength`, then
  `A.headQuotient.HasFiniteLength`.
- `isSemisimpleRepresentation_headQuotient h`: if `A.HasFiniteLength`, then the
  representation of `A.headQuotient` is semisimple.
- `headQuotientLift f hB : A.headQuotient ⟶ B` is the morphism induced by a
  morphism `f : A ⟶ B` whose target representation is semisimple.
  `toHeadQuotient_headQuotientLift` says
  `A.toHeadQuotient ≫ headQuotientLift f hB = f`, and `headQuotientLift_unique`
  says that it is the only such morphism.
- `headQuotientMap f : A.headQuotient ⟶ B.headQuotient` is the morphism induced
  by `f : A ⟶ B`. It satisfies
  `A.toHeadQuotient ≫ headQuotientMap f = f ≫ B.toHeadQuotient`
  (`toHeadQuotient_headQuotientMap`), `headQuotientMap_id` and
  `headQuotientMap_comp`.
- `headQuotientFunctor k G` is the resulting endofunctor of
  `SmoothRep.{uk, uG, uV} k G`, with object map `headQuotient` and morphism map
  `headQuotientMap`.

These helpers apply to the actual normalized inductions of Silberger's
Proposition 5.9. A consumer can then state Jordan–Hölder multiplicities of the
actual quotient, for example with the published `HasJordanHolderMultiplicity`
(`Filtration/MultiplicityStatement`) applied to `Rep.of (head ρ)`. This module states no multiplicity formula.

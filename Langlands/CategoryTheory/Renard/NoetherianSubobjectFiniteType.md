# Renard A.I.3: Noetherianity and finite type of all subobjects, proof

This proof unit proves the exact published
`Langlands.Renard.NoetherianSubobjectFiniteTypeStatement C` from
`Langlands.CategoryTheory.Renard.NoetherianSubobjectFiniteTypeStatements`.
The main theorem is

```lean
theorem noetherianSubobjectFiniteType (C : Type u) [Category.{v} C] :
    NoetherianSubobjectFiniteTypeStatement C
```

in namespace `Langlands.Renard`. The statement says that, when
`HasAllSubobjectUnions C` holds, an object `X` satisfies
`IsNoetherianObject X` exactly when `IsFiniteTypeObject (P : C)` holds for
every `P : Subobject X`, top included. The published statement pair and the
imported definition pair `Langlands.CategoryTheory.RenardFiniteType` are
unchanged. Worker 937 wrote the Lean proof and this Markdown.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, Appendix A.I.3,
printed pages 248–249 / PDF pages 254–255. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
For this proof, the file hash was rechecked, and the text of both pages was
extracted and their rendered images inspected. On PDF page 254 the
standing assumption "On suppose ici que la catégorie 𝒞 admet des unions
quelconques" precedes the finite-type definition. On PDF page 255 the
paragraph beginning "Il est clair d'après les définitions qu'un sous-objet
d'un objet noethérien est de type fini" proves both directions of the
equivalence.

The proof uses the published predicates exactly as they stand. It retains
the repairs to the printed wording that the definition and statement
companions disclose. The selected member of a subset, not `X`, is maximal.
Chains in the maximality and finite-type conditions are nonempty. A proper
subobject is one whose class differs from top. The covering equation in the
compactness paragraph has union `X`. Those companions record that these are
internal mathematical diagnoses, not author-issued errata. This proof does
not use the compactness paragraph.

## Helper theorems

Both helpers are in namespace `Langlands.Renard` and keep the independent
universes `C : Type u`, `Category.{v} C`.

`isNoetherianObject_subobject` proves that `IsNoetherianObject X` implies
`IsNoetherianObject (P : C)` for every `P : Subobject X`. Let
`e := Subobject.subobjectOrderIso P`, Mathlib's order isomorphism
`Subobject (P : C) ≃o Set.Iic P`. Composing `e` with the inclusion of the
interval gives an order embedding of `Subobject (P : C)` into
`Subobject X`. For a nonempty subset `S` of `Subobject (P : C)`, Noetherianity
of `X` gives a maximal member of the image of `S`. That member is the image
of some `Z ∈ S`. If `Q ∈ S` and `Z ≤ Q`, then the image of `Z` is below
the image of `Q`. Maximality makes the two images equal, and injectivity
of `e` and of the subtype coercion gives `Q = Z`.

`not_isLUB_top_of_isNoetherianObject` proves that if `IsNoetherianObject Y`
holds, then no nonempty chain `S` in `Subobject Y` whose members all differ
from top has least upper bound top. Take a maximal member `Z` of `S`. For
any `Q ∈ S`, the chain property gives `Q ≤ Z` or `Z ≤ Q`. In the second case
maximality gives `Q = Z`. So `Z` is an upper bound of `S`. If top were the
least upper bound, then top would be below `Z`, so `Z` would equal top,
contradicting properness.

## Main proof

Assume `HasAllSubobjectUnions C` and fix `X`.

Forward direction. Let `P : Subobject X`. The first conjunct of
`IsFiniteTypeObject (P : C)`, union existence `HasSubobjectUnions (P : C)`,
is the antecedent applied to the object `(P : C)`. The second conjunct
follows from `not_isLUB_top_of_isNoetherianObject` applied to the Noetherian
object `(P : C)` given by `isNoetherianObject_subobject`. This includes
`P = ⊤`, whose underlying object is a chosen representative isomorphic to
`X`.

Converse direction. Assume `IsFiniteTypeObject (P : C)` for every
`P : Subobject X`. The published `noetherianChainMaximality C X` reduces
source Noetherianity to finding, in every nonempty chain `S` of
`Subobject X`, a member maximal in `S`. The antecedent gives a least upper
bound `U` of `S` in `Subobject X`. Let `e := Subobject.subobjectOrderIso U`.
Let `φ` be its composite with the interval inclusion,
`Subobject (U : C) → Subobject X`. The proof establishes:

- `φ W ≤ φ W' ↔ W ≤ W'`, from `Subtype.coe_le_coe` and `e.le_iff_le`;
- `φ (e.symm ⟨P, h⟩) = P` whenever `h : P ≤ U`, from `e.apply_symm_apply`;
- `φ ⊤ = U`. Here `φ ⊤ ≤ U` holds because `e ⊤` lies in `Set.Iic U`.
  Conversely, `U = φ (e.symm ⟨U, le_refl U⟩) ≤ φ ⊤`. This avoids needing an
  `OrderTop` instance on the interval.

Let `S'` be the preimage of `S` under `φ`. Every member of `S` is below `U`,
so it is the image of a member of `S'`. Hence `S'` is nonempty because `S` is.
`S'` is a chain: distinct members of `S'` have distinct images in the chain
`S`, which are comparable, and `φ` reflects that comparison. Top is a least upper bound of `S'`: it is an upper
bound. If `B` is any upper bound of `S'`, then `φ B` is an upper bound of
`S`, so `U ≤ φ B`. That is, `φ ⊤ ≤ φ B`, and therefore `⊤ ≤ B`. The finite-type
condition of `(U : C)` now says that `S'` cannot consist of proper
subobjects. So some `W ∈ S'` equals top, and `U = φ ⊤ = φ W ∈ S`. Finally,
`U` is maximal in `S`: if `Q ∈ S` and `U ≤ Q`, then `Q ≤ U` because `U` is an
upper bound, so `Q = U`.

## Comparison with Renard's argument

Renard's forward argument takes a chain of proper subobjects of a
subobject `Y` of the Noetherian object `X`. He uses the Noetherianity of `X`
for a maximal member `B` and observes that `B` is the union of the chain
and is proper in `Y`. The implementation first transports Noetherianity
from `X` to the actual object `(P : C)` through `subobjectOrderIso`. It then
runs the same maximal-member argument inside `Subobject (P : C)`.
Nonemptiness of the chain, now explicit in the definition, is what
supplies the maximal member.

Renard's converse takes an increasing sequence `B_i` with union `B`. He uses
finite type of `B`, through the compactness characterization stated just
before, to write `B` as a finite union `B_{i_1} ∪ … ∪ B_{i_r} = B_{i_r}`, so
the sequence is stationary. The implementation instead uses the published
chain criterion `noetherianChainMaximality`. It applies the chain form of
finite type directly to the chain pulled back into `Subobject (U : C)`,
where `U` is the union. This yields that the union itself belongs to the
chain. It uses neither the finite-subcover characterization
`finiteTypeFiniteSubcover` nor sequences. Renard's citations [25] and [37]
were not consulted and supply no proof evidence here.

## Scope and dependencies

The three theorems have the external telescope
`{C : Type u} [Category.{v} C]`, explicit for the main theorem, with
independent object and Hom universes. They use the actual
`CategoryTheory.Subobject` types, their factorization order, and the
underlying chosen representative objects `(P : C)`. The union antecedent
`HasAllSubobjectUnions C` stays an explicit premise of the statement. The
forward direction uses it only for the objects `(P : C)`, and the converse
only for `X`. No abelian, zero-object, well-poweredness, smallness,
completeness-instance, module or finiteness hypothesis is added. No
Noetherianity, finite-type or comparison conclusion is assumed.

The imports are the published statement module and
`Langlands.CategoryTheory.Renard.NoetherianCriteria`. The latter supplies
`noetherianChainMaximality`, a published proof. The Mathlib declaration
`CategoryTheory.Subobject.subobjectOrderIso` in
`Mathlib/CategoryTheory/Subobject/Lattice.lean`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, needs only the category
instance. The general Noetherian criteria, the finite-subcover
characterization, the compact-element comparison, the actual module
examples and the Noetherian-category and ring comparisons remain separate
units. This proof neither closes Appendix A nor the whole-book program.

## Development checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, draft and workspace
checks compiled the module with no diagnostics. Inspection of
`Langlands.Renard.noetherianSubobjectFiniteType` reported a theorem with
universe parameters `u`, `v` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. A private probe compiled cleanly. It
used the theorem at the fully unfolded statement body from the task
objective. It also instantiated the theorem at object/Hom universe pairs
`(5, 1)` and `(0, 4)` and at the category `Type 2`. These development
checks are not acceptance or publication evidence.

# Reciprocity systems in a common algebraic closure

Author: Worker 21. This pair defines families of candidate reciprocity
isomorphisms over every finite extension of a finite extension `F` of `Q_p`
inside one algebraic closure. It defines their compatibility relations,
their normalization, and the existence and uniqueness properties of a
normalized system. Every group, norm, inclusion, transfer and conjugation
used is constructed from actual fields. No candidate family is constructed,
and no existence or uniqueness theorem is asserted.

## Indexing fields and constructed maps

`FiniteIntermediateExtension K` is the type of intermediate fields of
Mathlib's `AlgebraicClosure K` together with a finite-dimensionality
certificate. Nonnormal fields are included. No replacement field operations
are introduced. `asPadicField` regards such a field as a finite extension of
the original `Q_p`, with the composite scalar map through `K`.

For an inclusion `E ≤ L` of such fields:

- `unitsInclusion` is the field inclusion `Eˣ → Lˣ`.
- `unitsNorm` is `Units.map` of Mathlib's field norm `Lˣ → Eˣ`, for the
  scalar structure induced by the inclusion.
- `galoisInclusion` and `galoisAbelianInclusion` include the fixing subgroup
  of `L` in the fixing subgroup of `E` inside the absolute Galois group of
  `K`, and pass to topological abelianizations.
- `galoisAbelianTransfer` is the constructed continuous transfer in the
  opposite direction.

For a continuous `φ` from the absolute Galois group of `K` to the profinite
integers, the subgroup of the existing Weil pullback that projects into the
fixing subgroup of `E` is `pullbackFixingSubgroup K E φ`. On these subgroups,
`weilInclusion`, `weilAbelianInclusion` and `weilAbelianTransfer` are the
same constructions. `weilGaloisProjection` restricts the existing projection
to the fixing subgroup; `weilGaloisAbelianProjection` is the induced map of
abelianizations. `weilDegree` is the pullback degree, read on the
abelianized subgroup through the actual inclusion. It is the degree over the
base field `K`, not a degree renormalized for `E`. Every quotient carries its
quotient topology, and no compactness of a Weil abelianization is asserted.

Conjugation is constructed as follows. For `σ` in the absolute Galois group,
`conj σ E` is the image field `σ(E)`, finite by Mathlib's instance for images.
`unitsConjugation σ E` is Mathlib's field isomorphism `E ≃ σ(E)` on
multiplicative groups. For `w` in the Weil pullback with projection `σ`,
`conj_mem_pullbackFixingSubgroup` proves that conjugation by `w` maps the
subgroup for `E` into the subgroup for `σ(E)`. The proof uses Mathlib's
formula `IsGalois.map_fixingSubgroup`, which says that the fixing subgroup
of `σ(E)` is the conjugate by `σ` of the fixing subgroup of `E`.
`weilConjugation` is this continuous homomorphism and
`weilAbelianConjugation` the induced map of abelianizations.

## Candidate families and their relations

Fix `F : PadicField p`, a family `S` of `TopologicalData` on the fields
`asPadicField E`, and an explicit continuous `φ` as above. The dependent
type `CommonClosure.CandidateFamily F S φ` consists of continuous
isomorphisms `e_E` from the abelianized subgroup for `E` to `Eˣ`, one for
every finite intermediate field `E`. Its direction is that of `W_E^ab → Eˣ`.
No inhabitant is constructed. `galoisHom e E` composes the inverse of `e_E`,
which lands in the abelianized Weil subgroup and never in a nonabelian
group, with the projection to the Galois abelianization.

For all nested `E ≤ L` and in the direction `W^ab → units`:

- `NormRelation`: `e_E ∘ inclusion = N_(L/E) ∘ e_L`.
- `TransferRelation`: `e_L ∘ transfer = fieldInclusion ∘ e_E`.

For every `w` in the Weil pullback, with Galois projection `σ`, and every `E`:

- `ConjugationRelation`: `e_(σ(E)) ∘ conjugation_w = σ ∘ e_E`.

Moreover:

- `DensityRelation` asks that every `galoisHom e E` have dense range.
- `CompletionRelation` asks, for every `E`, for a continuous isomorphism
  from the completion of `Eˣ` along its open finite-index subgroups to the
  Galois abelianization. Its composite with the dense completion map must be
  `galoisHom e E`. The completion is a different carrier from the noncompact
  group `Eˣ`.

`CoherentFamilyRelation` is the conjunction of these five conditions and is
**unnormalized**. Density follows from the completion comparison, since the
completion map is dense and the comparison is a homeomorphism. It is kept as
a separately named condition, as in the single-field relations.
`CoherentFamilyExistence` is only a proposition.

## Normalization, existence and uniqueness

Let `T` be `TopologicalData` on `F` and `q_F` its residue cardinality.
`NormalizationRelation` requires, for every `E` and every `w`,

`|e_E(w)|_E = q_F ^ (-deg w)`,

where `|·|_E` is the normalized absolute value `normalizedAbs` of `S E` and
`deg` is `weilDegree`. When `φ` is the actual geometric residue-degree map,
an element of degree `n` acts on the residue field of the closure as
`x ↦ x^(q_F^(-n))`. Hence this relation is Tate's sign convention: the
image of `a ∈ Eˣ` acts on the residue field as `x ↦ x^|a|_E`. A uniformizer
of `E` then corresponds to geometric Frobenius of `E`, and units correspond
to inertia. At the bottom field `⊥`, identified with `F` and with
compatible data, its subgroup is the whole pullback and the relation becomes
`q_F^(-ord(e(w))) = q_F^(-deg w)`. Since `q_F > 1`, this is the
single-field `GeometricOrderRelation`. These identifications are explained
here, not constructed or proved in Lean.

`NormalizedSystemRelation` is `CoherentFamilyRelation` together with
`NormalizationRelation`. `NormalizedSystemExistence` says that some family
satisfies it. `NormalizedSystemUniqueness` says that any two families
satisfying it are equal. Both are `Prop`-valued definitions only.

There is no separate finite norm-residue condition, Tate's (W1) in its
local form. The following informal argument, which is not proved in Lean,
shows why none is needed for uniqueness. It assumes that `φ` is the actual
geometric degree map and that `S` is `canonicalData F`. Write `g_E` for
`galoisHom e E`.

1. *Exact norm kernels.* Let `E ≤ M` with `M/E` abelian. The kernel of
   `W_E^ab → Gal(M/E)` is the image of `W_M^ab`, because the subgroup for
   `M` is the preimage of its fixing subgroup and contains the commutators
   of the subgroup for `E`. Since `e_M` is surjective, `NormRelation` maps
   this image onto `N_(M/E)(Mˣ)`. Hence the kernel of `Eˣ → Gal(M/E)`
   induced by `g_E` is exactly `N_(M/E)(Mˣ)`. This is the kernel part of
   Milne's condition (b) in Theorem I.1.1.
2. *Frobenius.* For a prime element `π` of `E`, `NormalizationRelation`
   gives `deg(e_E⁻¹(π)) = f(E/F)`. So `g_E(π)` acts on the maximal
   unramified extension of `E` as its geometric Frobenius, for every
   normalized family.
3. *Uniqueness on prime elements.* Let `L/E` be finite abelian of degree
   `n`, let `E_n` be the unramified extension of degree `n`, and set
   `L' = L·E_n`. The restriction of `g_E(π)` to `L'` has order `n`. Let
   `M` be its fixed field. By step 1, `π` is a norm from `M`, so `M/E` is
   totally ramified and `L' = M·E_n`. For a second normalized family `e'`,
   step 1 shows that `g'_E(π)` fixes `M`, and step 2 shows that it agrees
   with `g_E(π)` on `E_n`. Hence the two agree on `L'`. The Galois
   abelianization is profinite and `Eˣ` is generated by prime elements, so
   `g_E = g'_E`. Unlike Milne's Theorem 1.13, this does not use the
   existence theorem.
4. *Weil side.* `CompletionRelation` writes `g_E` as a homeomorphism after
   the completion map. The completion map is injective, since the open
   finite-index subgroups of `Eˣ` intersect trivially. So the projection
   `W_E^ab → G_E^ab` is injective, and `e_E = e'_E`.

For other choices of `φ` or `S`, the proposition may be vacuous or false.
The intended uniqueness theorem specializes them as above.

For a single field, `LocalReciprocityUniqueness T φ` says that any two
candidates `e₁ e₂ : WeilReciprocityCandidate T φ` satisfying
`LocalReciprocityCandidateRelation` are equal. That relation consists of
geometric order normalization, density, and the finite norm-residue
relations of `FiniteArtin`. It is the Weil-group form of the uniqueness
clause of local reciprocity. It is stated for the Weil-side isomorphism
itself, not only for the induced Galois homomorphism. Together with
`LocalReciprocityExistence`, it gives the single-field existence and
uniqueness properties on these actual objects.

`CommonClosure.canonicalData F` supplies, for every finite intermediate
field, the published `canonicalTopologicalData` of its `asPadicField`. With
`T := F.canonicalTopologicalData`, it gives the canonical formulations.
The degree map `φ` remains explicit until the actual local Weil assembly is
published by its assigned owner. The intended theorems use that actual map.

## Scope

These are derived interfaces on constructed objects. They do not assume
reciprocity, existence of a Weil group, or class-formation axioms. Tate's
condition (W4), that the Weil group is the inverse limit of its relative
quotients, concerns the Weil group itself and is not part of these
relations. The fixing subgroups in the common closure are not identified
with separately presented absolute Galois or Weil groups of the fields `E`.
Independence of the choice of closure is also not addressed. Any
existence or uniqueness theorem for these propositions belongs to the
companion statement task and to later proof tasks.

## Sources

- John Tate, *Number theoretic background*, Corvallis Part II (1979),
  registered source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  Printed page `p` is PDF page `p + 9`.
  - Section 1.1, printed pages 3–4 / PDF pages 12–13: the Weil-group datum
    with the subgroups `W_E` for all finite extensions `E` in one closure;
    (W1); (W2), the conjugation diagram; (W3), the inclusion/transfer
    diagram; (W4). The norm/inclusion diagram displayed after (W4) on
    printed page 4, to which section 1.4.6 refers as (1.1.2). The maps there
    are `r_E : Eˣ → W_E^ab`; the candidates here are in the inverse
    direction.
  - Section 1.4.1, printed page 6 / PDF page 15: `r_E(a)` acts on the
    residue field as `x ↦ x^|a|_E`, so uniformizers correspond to geometric
    Frobenius.
  - Section 1.4.6, printed page 7 / PDF page 16: the Weil-group norm `‖w‖`
    reflects the normalized absolute value and restricts to the norm of
    each `W_E`.
- J. S. Milne, *Class Field Theory*, version 4.03 (title page dated
  August 6, 2020), registered source `milne-2020-class-field-theory`, SHA256
  `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
  Chapter I, Theorem 1.1, printed page 20 / PDF page 29: there is a unique
  homomorphism with Frobenius normalization of prime elements and norm
  groups in the kernels. Theorem 1.13, printed page 24 / PDF page 33: the
  uniqueness argument. Milne uses the arithmetic convention. The geometric
  convention here inverts the map, which does not affect uniqueness.

Worker 21 read these passages in the original files. The Lean formulations,
including the absolute-value form of the normalization and uniqueness for
the Weil-side isomorphisms, are derived formulations rather than literal
translations.

## Dependencies and checks

The direct project imports are the published modules
`Langlands.ClassFieldTheory.Local.ReciprocityRelations` and
`Langlands.LocalField.Canonical`. The former imports the published `Units`,
`Completion`, `FiniteArtin`, `WeilAbelianization` and `Transfer` pairs under
`Langlands/ClassFieldTheory/Local` (formerly at `Langlands/LocalClassField`).
Declarations use the namespace `Langlands.LocalClassField`. The prepared
environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, on Library commit
`fe68653a42ed5ae0a2d7f5cef0697a68e8acc978`. The development check
`869a47a3-28c4-414b-86ba-977f97b58336` reports 0 errors and 0 warnings.
It inspected `CommonClosure.NormalizedSystemUniqueness`, which returns
`Prop` and uses only `propext`, `Classical.choice` and `Quot.sound`. The
check confirms that the definitions compile, not that their propositions
hold.

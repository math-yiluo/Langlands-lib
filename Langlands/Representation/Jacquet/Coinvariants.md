# Actual Jacquet coinvariants and normalizing subgroup actions

This pair constructs the unnormalized Jacquet quotient for an algebraic
representation `ρ : Representation R G V`, a subgroup `N`, and an acting
subgroup `M` with `M ≤ Subgroup.normalizer N`. The ring is commutative and the module
is arbitrary. The ring, group, and all three representation carriers have
independent universes. No topology, finite generation, dimension bound,
closedness, semidirect-product decomposition, or normality in all of `G` is
assumed.

`relations ρ N` is exactly the submodule spanned by `ρ(n)v - v`. `Coinvariants
ρ N` is the actual quotient by that span, and `mk` is its canonical linear
quotient map. These are abbreviations for the existing Mathlib coinvariant
construction restricted to `N`, rather than abstract objects with assumed
properties. The module structure is inherited from that quotient.

For `m ∈ M`, applying `ρ(m)` to the generator `ρ(n)v-v` gives the generator
associated with `mnm⁻¹ ∈ N` and `ρ(m)v`. Span induction proves
`relations_stable`. This also constructs `relationsSubrepresentation`.
`action` uses Mathlib's quotient representation, whose identity and product
fields are proved by quotient extensionality. Its formula is

`action ρ N M hMN m (mk ρ N v) = mk ρ N (ρ m v)`.

The quotient map is surjective, has kernel exactly `relations`, and is an
`M`-intertwiner. An ambient `G`-intertwiner restricts to both `N` and `M`;
Mathlib's coinvariant map gives the induced quotient map. Its equivariance is
proved on quotient representatives using the original intertwining equation.
`map_comp_quotientMap`, `map_id`, and `map_comp` prove naturality, preservation
of identities, and preservation of composition. `lift` and `lift_unique`
record the linear universal property of the actual quotient.

These are intrinsic construction laws. This pair does not claim exactness
of the Jacquet functor, parabolic reciprocity, admissibility, or a
classification theorem. Smoothness and normalization belong to subsequent
constructions over this quotient.

## Sources and scope

The untwisted specialization of Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), Section 1.8(b),
printed pages 444-445 / PDF pages 5-6, supplies the span, quotient and
normalizer action. The character `θ` there is specialized to the trivial
character here. The original's locally profinite and smooth assumptions are
not needed for this algebraic construction. Its additional assumptions
`M ∩ N = {1}` and closedness of `MN` support other functors in that section;
only normalization of `N` is used here.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Original: `C:/Central-Library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
- Read pages 443-445, including the no-module-topology convention in
  Section 1.2, and visually checked the normalization on page 444.

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III, revision April 29, 2019, Section 3, pages 3-4, defines the
same quotient and explains its descended action.

- Literature ID: `casselman-2019-jacquet-module`.
- SHA-256: `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
- Original: `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
- The retained eight-page chapter was read. Its further theorems are not
  prerequisites or claims of this construction.

Both sources normalize the descended action by the inverse half modulus.
The present `action` is explicitly the unnormalized action.

## Mathlib audit and dependencies

The audit used the pinned Mathlib source at commit
`5ed2965256430c3649e86755f9576b54eca72435`:

- `RepresentationTheory/Coinvariants.lean`: `Coinvariants.ker`,
  `Coinvariants`, `mk`, `mk_surjective`, `lift`, `map`, `hom_ext`, and
  the existing normal-subgroup construction `toCoinvariants`.
- `RepresentationTheory/Subrepresentation.lean`: `Subrepresentation`
  and its intrinsic stability field.
- `RepresentationTheory/Basic.lean`: `Representation.quotient`,
  implemented by `Submodule.mapQ` with proved identity and product fields.
- `RepresentationTheory/Intertwining.lean`: algebraic intertwiners and
  their identity and composition operations.

The only additional stability argument generalizes the existing
normal-subgroup argument to an arbitrary acting subgroup of the normalizer.
No parallel quotient implementation is introduced.

There are no project mathematical dependencies. The environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and the Mathlib commit above.
Author: Worker 34.

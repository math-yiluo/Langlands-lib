# Actual all-ranks partial derivative on GL products

Author: Worker 440. The principal definition is
`Langlands.Derivative.partialDerivative.{uF,uV} T ψ k m`. For arbitrary prime
`p`, `F : PadicField.{uF} p`, supplied `T : F.TopologicalData` and unitary
additive character for `T.topology`, it is an actual functor

`SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier) ⥤ SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier)`.

Installing `T.topology` selects the existing matrix-unit topology on each GL
group and the actual product topology. There is no canonical-topology
substitution. The quotient carrier stays in `Type uV`, independently of `uF`.
All natural ranks are allowed, including `k=0`, `m=1` and `k=m=0`. The input
vector space has no topology, dimension, finite-length, admissibility or
irreducibility restriction.

## Subgroups, character and normalization

The internal namespace `Langlands.Derivative.Partial` defines `unipotent F k m`
as `(⊥ : Subgroup (GL_k F)).prod (upperUnipotent m F)` and `actingSubgroup F k m`
as `(⊤ : Subgroup (GL_k F)).prod (⊥ : Subgroup (GL_m F))`. The actual second
projection `second` maps the first subgroup to `upperUnipotent m F`;
`includeUnipotent` sends `u` to `(1,u)`. The character `character ψ k m` is
literally the published `Whittaker.entrywiseCharacter ψ m` composed with
`second`. Its multiplicativity is inherited from those genuine homomorphisms.
`character_include` gives the second-factor value, `character_succ` the sum of
adjacent upper entries, and `character_zero` the trivial rank-zero character.
No second character package is introduced.

`commute` proves the two subgroups commute by using that the first coordinate
of every unipotent is one and the second coordinate of every acting element
is one. `conjugation_eq` proves `a*u*a⁻¹=u`. This also proves `normalizes`;
the reverse direction in the normalizer condition conjugates by `a⁻¹`.
`conjugate_eq` gives equality in the actual unipotent subtype, and
`character_invariant` follows by rewriting that equality.

BZ77 §1.8(b) multiplies the descended action by the inverse half of the Haar
conjugation modulus. In this specialization the conjugation automorphism is
literally the identity, as just proved, so it preserves every Haar measure.
Its modulus and its inverse half are one. Thus the localization action is
already the source normalization; no determinant twist or general Haar
comparison theorem is required or asserted here.

`first F k m` is the actual homomorphism `g ↦ (g,1)` into the product;
`firstToActing` restricts its codomain to `actingSubgroup`. Their continuity
certificates use the product topology and continuous subtype inclusion. They
need no continuity of field operations.

## Actual quotient, action and morphisms

`Partial.relations`, `Partial.Quotient` and `Partial.mk` reuse the existing
`Jacquet.Localization.relations`, `Coinvariants` and `mk` unchanged.
`relations_eq_span` proves the exact equality

`relations ψ k m ρ = Submodule.span ℂ (Set.range fun uv : upperUnipotent m F × V => ρ (1,uv.1.val) uv.2 - (entrywiseCharacter ψ m uv.1 : ℂ) • uv.2)`.

For one inclusion it projects each subgroup element to the second coordinate
and uses its first coordinate being one. For the other it uses
`includeUnipotent`. Thus no additional relations are imposed.
`generator_mem`, `mk_eq_zero`, `mk_unipotent` and `mk_surjective` expose the
generators, kernel criterion, scalar relation and surjectivity.

`Partial.action` is the actual Localization action of `actingSubgroup`,
restricted along `firstToActing`. `action_mk` proves exactly
`[v] ↦ [ρ(g,1)v]`. `quotientMap` is the actual equivariant quotient map from
first-factor restriction. `Partial.map` reuses the existing localization
linear map and its proved equivariance, then restricts to the first factor.
`map_mk` proves `[v] ↦ [f v]`. `map_id` and `map_comp` use quotient
extensionality, reducing their laws to equality on original vectors. The
source, target and third composition vector spaces may have independent
universes.

`isSmooth_action` uses the existing localization smoothness theorem for the
actual subgroup quotient, then continuous pullback along `firstToActing`.
Localization itself proves smoothness by continuous subgroup restriction and
surjective intertwiner transfer. `smoothObject` and `smoothFunctor` bundle
these actual actions, maps and proved identity/composition laws. The principal
`partialDerivative` is their specialization to `ψ.complex` and `T.topology`.
The following interfaces express the laws directly for this principal functor:

| Declaration | Meaning |
| --- | --- |
| `partialDerivativeMk` | Actual linear quotient map into the functor object |
| `partialDerivativeMk_surjective` | Every quotient vector has a representative |
| `partialDerivativeMk_unipotent` | The required entrywise-character relation |
| `partialDerivative_action_mk` | First-factor action sends `[v]` to `[ρ(g,1)v]` |
| `partialDerivative_map_mk` | A smooth morphism sends `[v]` to `[f v]` |

## Second rank zero and the entire original carrier

`unipotent_zero_eq_one` proves this unipotent subgroup is trivial: its first
coordinate is one by membership, and its second is a matrix unit indexed by
`Fin 0`, hence unique. `relations_zero` then proves every generating relation
is zero. `zeroEquiv` uses Mathlib's `Submodule.quotEquivOfEqBot` to give an
equivariant linear equivalence from the quotient to the original vector
space with first-factor restriction. Equivariance is checked on quotient
representatives. `zeroEquiv_mk` sends the class of `v` to `v`.

`Partial.zeroIso` proves naturality on the same representatives, using the
actual original intertwiner. `partialDerivativeZeroIso` specializes this
natural isomorphism to the supplied p-adic topology. Its target is the actual
functor `productFirstRestriction T k 0`, which retains the whole original
carrier as stated by `productFirstRestriction_obj_carrier`. The two component
formulas are `partialDerivativeZeroIso_hom_mk` and
`partialDerivativeZeroIso_inv_apply`. The former sends `[v]` to `v`; the latter
sends `v` to `[v]`. This applies even when `k=0`. An arbitrary representation of
`GL_0` may have an arbitrary vector space, and no tensor multiplicity or carrier
is discarded.

## Originals and scope

Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
§3.7, printed p.182 / one-based PDF19, defines this functor for `k,m ≥ 0`,
using localization at the upper unipotents in `{1} × GL_m`. That page was read
and visually inspected. Proposition 3.7(a)/(b) on the same page is context;
this unit proves neither comparison.

- Literature ID: `zelevinsky-1980-induced-ii`.
- SHA256: `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- Original: `/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §1.8(b), printed pp.444–445 / one-based PDF5–6, specifies the relation
span, descended action with inverse-half modulus, and the trivial-unipotent
restriction case. Both pages were read and visually inspected, including the
normalization sign on printed p.444.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- SHA256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Original: `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

Both hashes were verified. No source-specific `notes/errata/<source-id>.md`
was present in the checked workspace, supplied Library or project literature
locations. This records a bounded check, not an exhaustive absence of errata.

The algebraic `Partial` layer works for any commutative ring of matrix entries
and raw additive character to complex numbers. Its topology-dependent layer
needs any topology on that ring. These are internal extensions of the domain
of definition justified by the implemented quotient, commutation and transfer
arguments; no theorem from the sources is attributed to this broader setting.
The representation coefficient field is complex throughout. The principal
functor has precisely the task's arbitrary p-adic-field specialization.

This unit supplies construction and intrinsic laws only. Iterated ordinary
derivatives, tensor-product compatibility, exactness, Leibniz filtrations,
Whittaker uniqueness, and segment or classification theorems are separate.
There is no import of a derivative, adjunction, duality or pairing theorem.
The entrywise-character closure includes low-level Whittaker functional and
dual definitions, but does not use their uniqueness statement as a proved
input. The current imported Lean/Markdown pairs remain unchanged.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

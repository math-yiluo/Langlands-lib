# Pullback of locally free rank-one sheaves

For any morphism of schemes `f : X ⟶ Y`, `LineBundle.pullback f` sends a
locally free rank-one sheaf on `Y` to its actual module-sheaf pullback on `X`,
and sends its morphisms by `Scheme.Modules.pullback f`. The local rank-one
property is proved, rather than supplied as an assumption.

The proof of `IsLocallyFreeRankOne.pullback` chooses a trivializing open
neighborhood `U` of `f x` and uses the inverse-image open `f ⁻¹ᵁ U` at `x`.
The helper `restrictPullbackIso` identifies restriction of `f* M` to this open
with the pullback of `M|U` along the restricted scheme morphism. It composes
Mathlib's restriction-to-pullback comparison, pullback composition comparisons,
and the equality `morphismRestrict_ι`. Pulling back the given trivialization
then ends with the constructed canonical `pullbackUnitIso`, identifying the
pullback of the structure sheaf with the structure sheaf.

The functor is lifted to the full subcategory `LineBundle` using this proof.
`pullbackForgetIso` records its agreement with ordinary module pullback.
`pullbackId` and `pullbackComp` lift the corresponding natural isomorphisms
of module-sheaf pullbacks; their naturality follows from the underlying
naturality using faithfulness of the full-subcategory inclusion.
`pullbackTrivialIso` lifts the canonical unit comparison.

This is a derived scheme-level rank-one specialization of the preservation of
local freeness in the Stacks Project, Section 17.14, Lemma 17.14.3.
Definition 17.14.1(3) specifies the rank through the size of a local basis.
The implemented argument exhibits a single generator after pullback and thus
retains rank one. The original lemma omits its proof; the Lean proof is the
explicit local-trivialization argument described above.

Registered source: `stacks-local-freeness-invertibility-sections-2026-10-21`,
SHA-256 `6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`,
retained file `01C5.html`, Definition 17.14.1(3) and Lemma 17.14.3.
The comparison with tensor-invertibility, the Picard group, and coherence
equations between the displayed identity/composition comparisons are separate
constructions. No tensor or group structure is assumed here.

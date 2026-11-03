# Smooth connected affine group geometry targets

These are unproved proposition targets for the general geometry needed to
use actual smooth connected subgroups as commutator sources. They concern
every universe and every field, including imperfect fields of positive
characteristic. They provide no new typeclass instances or axioms.

The source motivation is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), Lemma 3.3.4, the paragraph preceding Proposition 3.3.5,
and Proposition 3.3.5, printed pp.108–109 (PDF pp.134–135), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`. The explicit targets are derived
geometric prerequisites of that argument, rather than verbatim propositions
printed there. A proof successor must supply their geometric proofs and locate
any additional source results it needs.

`SmoothConnectedAffineGroupIntegralStatement` asserts that the structure
morphism of an actual smooth connected affine group over a field is
geometrically integral. Connectedness in its premise is ordinary
`ConnectedSpace` of the underlying scheme; geometric connectedness is not
silently assumed. The group identity gives the rational point relevant to
the passage from connected group geometry to geometric integrality.

`SmoothConnectedAffineProductIntegralStatement` asserts that the actual
binary product `H₁.X ⊗ H₂.X` is affine, locally of finite type,
quasi-compact, and geometrically integral over the field, when both groups
are smooth, connected and affine. Locally of finite type together with
quasi-compactness is the finite-type condition. The source is the actual
scheme product used by `commutatorMap`, without a rational-point replacement.

`SmoothConnectedAffineGeometryStatement` is the conjunction of those two
obligations. No proof is asserted in this module. In particular, the general
group and product integrality facts must be proved before invoking these
targets to discharge the hypotheses of pointed-image generation.

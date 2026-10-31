# Finite projective Čech representatives over a noetherian base

`Langlands.AlgebraicGeometry.Modules.NoetherianCechProjectiveRepresentativeStatement.{u}`
is a Prop-valued statement about actual scheme modules and their Čech
cochains, with all carrier types in an arbitrary universe u.

Let R be a commutative noetherian ring, π : X → Spec R a proper flat
morphism, and M an actual sheaf of modules on X. Assume every point has an
open neighbourhood on which the pullback of M is isomorphic to the unit
module. Fix a finite ordered affine cover 𝒰 of X and a natural number n
with card(𝒰) ≤ n+1.

The proposition chooses a natural-number-indexed complex K of finite
projective R-modules, zero above n, and a chain map φ from K to the Čech
cochains of `OModulePresheaf.ofModules π M` for 𝒰. It also chooses, before
quantifying over scalar extensions, linear maps Θ for every commutative
R-algebra A. Their source is A tensor K and their target is the Čech
complex of the actual pullback of M along the first projection from
X ×_{Spec R} Spec A, over the pulled-back ordered affine cover.

For every A, the proposition requires:

- Θ commutes with the differentials;
- on a pure tensor a tensor k, evaluation at an index s is a times the
  restriction of the image of φ(k)(s) under the unit of the actual
  module pullback–pushforward adjunction for the first projection;
- Θ is injective and surjective on degree-zero cycles;
- in each positive degree Θ is injective modulo boundaries and surjective
  modulo boundaries.

The last two items are explicit cycle and boundary conditions expressing a
quasi-isomorphism. The result also requires these four conditions for the
original-base map φ: injectivity and surjectivity on degree-zero cycles,
and injectivity and surjectivity modulo boundaries in positive degrees.
The same K is used for the original base and every A. There is no
noetherianity or flatness assumption on A. This statement concerns Čech
cochains and does not itself assert an isomorphism with actual
right-derived sections, a Z-indexed strictly perfect representative, or
descent from a noetherian approximation.

## Provenance

This interface strengthens the quantified conclusion of
`AlgebraicGeometry.OModulePresheaf.exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial`
from registered source `anthropic-flt-complete-lean-source-6e837e75`,
folder SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`,
Anthropic FLT commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial.lean`.
Its proof is in the corresponding `P2M/Sol/S_` file, theorem `solution`.
The source construction obtains the four original-base conditions as
`h0inj`, `h0surj`, `hinj` and `hsurj` from its bounded projective replacement,
but its exported theorem drops them. This Prop-valued definition retains
those conditions before the universal scalar-extension clause. Unused
proof binders are renamed, and imports are restricted to the definitions
needed for the type. It imports no proof of this statement and claims no
proof here.
The source retains Copyright 2026 Anthropic under the Apache License 2.0;
see `licenses/Anthropic-FLT/LICENSE` and `licenses/Anthropic-FLT/NOTICE`.

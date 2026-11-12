# The two actual compact-induction models

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.2.6, printed pp.75–76 / PDF pp.81–82;
relative modular convention from II.3.7 and II.3.9, printed pp.47–50 /
PDF pp.53–56. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

For a continuous homomorphism `φ : H →* G`,
`relativeModularCharacter φ hφ` is the actual smooth complex character
`h ↦ ΔH(h) ΔG(φ(h)⁻¹)`, with units as its codomain.
Here Mathlib's Haar factor `Δ` is the inverse of Renard's `δ`.
For a closed subgroup `H ≤ G` this is therefore exactly
`δ_{H\G} = δG|H / δH`. The open-kernel proof follows from local
constancy of both modular characters and continuity of `φ`.

For the existing Hecke algebras, the file defines only composites and an
elementary-tensor accessor:

- `tensorInductionHeckeFunctor` applies the published Hecke functor to
  a smooth `H` representation, then the actual `Homomorphism.P`.
- `compactModularHeckeFunctor` applies the published scalar twist by
  the relative character and the published compact function induction,
  then the Hecke functor of `G`.
- `tensorInductionTmul W T w` is the original
  `NonUnitalModuleTensor.tmul` in the exact quotient used by `P`.

Thus the relative twist is determined by the actual groups, rather than
supplied as a separate normalizing character. These are the two models
in (III.2.6.2); this file asserts no comparison or isomorphism.
All group and input carrier universes remain independent. As in the
published tensor and compact-function constructions, the output carrier
universe for either model is `max uG v`.

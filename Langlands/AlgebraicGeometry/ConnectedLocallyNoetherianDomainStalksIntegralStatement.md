# Integrality from connectedness and domain stalks

`Langlands.AlgebraicGeometry.ConnectedLocallyNoetherianDomainStalksIntegral.{u}`
is the following `Prop`-valued definition:

```lean
∀ (X : Scheme.{u}), IsLocallyNoetherian X → ConnectedSpace X →
  (∀ x : X, IsDomain (X.presheaf.stalk x)) → IsIntegral X
```

It uses Mathlib's scheme, local Noetherianity, connectedness, domain, and
integrality predicates directly. The universe `u` is arbitrary. `ConnectedSpace`
includes nonemptiness. Mathlib's `IsIntegral X` is equivalent to irreducibility
and reducedness, and in particular includes nonemptiness. This file defines
the proposition; it does not prove it.

## Derived provenance

This is an internal derived statement motivated by the original Stacks Project
normal-scheme results below. Those results do **not** state this exact
domain-stalk formulation. Normality requires the stalks to be integrally closed
domains; our hypothesis retains only that they are domains. The omitted
integrally closedness condition requires a separate local irreducibility
argument.

The retained originals are in
`literature/Stacks Project - Smooth base change, regularity and connected normal schemes (2026-10-24)`,
literature ID `stacks-smooth-connected-integral-2026-10-24`, source SHA256
`5374d7e59f547f5114ea9217b3fdfc3c6d0b3f9cf7ab3ed0f35da7163ba7f794`.
The following statements, proofs where present, and page comments were read
directly. No project errata note for this source was found.

- [Tag 0357](https://stacks.math.columbia.edu/tag/0357), Lemma 28.7.5,
  `0357.html`, gives the decomposition of a normal scheme into disjoint normal
  integral schemes when every quasi-compact open has finitely many irreducible
  components. Its proof passes from affine opens to globally open components.
  The corrected proof does not assert that there are globally finitely many
  components.
- [Tag 033N](https://stacks.math.columbia.edu/tag/033N), Lemma 28.7.7,
  `033N.html`, gives this decomposition for locally Noetherian normal schemes.
- [Tag 033O](https://stacks.math.columbia.edu/tag/033O), Remark 28.7.8,
  `033O.html`, records the connected-normal-integral implication in that setting.
  It also points to a connected affine scheme with domain stalks that is not
  irreducible when the finiteness hypothesis is absent.

Here is the additional mathematical derivation for the stated hypothesis;
it is a proof route for the future formal proof, not an implemented Lean proof.

1. Take a Noetherian affine open `U = Spec A`. Its finitely many irreducible
   components correspond to the minimal prime ideals of `A`. For a point
   represented by a prime `p`, the components through that point correspond
   to the minimal primes contained in `p`, equivalently to the minimal primes
   of `A_p`. The ring `A_p` is isomorphic to the stalk of `X` there. Since this
   stalk is a domain, its only minimal prime is zero. Thus precisely one
   component of `U` contains the point. The finitely many components of `U`
   are therefore disjoint; each is closed and its complement is a finite
   union of closed components, so each is also open.
2. An irreducible component `T` of `X` meeting an affine open `U` restricts to
   an irreducible component `T ∩ U` of `U`. Consequently distinct global
   components are disjoint, and each `T ∩ U` is open in `U` by the preceding
   step. Hence each global component is open in `X`. This argument uses an
   arbitrary affine open cover and requires no finite global cover.
3. Irreducible components cover `X`. Nonemptiness and connectedness now force
   exactly one component: any nonempty component is both open and closed,
   and its open complement must be empty. Thus `X` is irreducible.
4. Every domain stalk is reduced. A scheme with reduced stalks is reduced,
   so `X` is both irreducible and reduced, hence integral.

## Scope and formal proof boundary

There is no quasi-compactness, affineness, finite type, separation, base field,
regularity, normality, or prior irreducibility or integrality hypothesis.
Local Noetherianity is retained throughout the component argument. The warning
in Tag 033O prevents dropping it on the strength of domain stalks alone.
No new scheme normality class is introduced.

The module imports only Mathlib. In the pinned environment, the reducedness
and final integrality steps have interfaces
`AlgebraicGeometry.isReduced_of_isReduced_stalk` and
`AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced`.
The separate proof obligation must establish the component argument and then
prove this exact published proposition without assuming normality or global
quasi-compactness.

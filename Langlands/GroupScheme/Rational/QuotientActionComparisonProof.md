# The relative root functor is the image of the descended identity-limit functor

This file proves
`Langlands.GroupScheme.RelativeRoot.QuotientActionComparisonStatement` as the
theorem `quotientActionComparison`, at every universe. It works over an
arbitrary base scheme B. The inputs are a commutative group scheme S, a
homomorphism i : S → G, a character a with character map χ : S → Gm, and a
closed monomorphism j : C → G whose range is the all-test kernel centralizer.
The fpqc conditions on χ are used to form the descended action and to cancel
χ in one equality of morphisms below. The result
is that the Library's root functor `subgroup i a` equals, on every test scheme,
the image under j of the identity-limit functor `unipotent` of
`quotientAction i a j hj`, the Gm action descended from S.

The comparison is the step "Uₐ is the dynamic subgroup U_C(λ) of the descended
action" in the cyclic construction of the root groups. See Conrad–Gabber–Prasad
(2015), Proposition 3.3.6 and its proof, and Kaletha–Prasad (2023),
Proposition 2.11.9 and its proof. These references appear in the statement's
Markdown. The Lean proof is a direct functor-of-points argument and does not
follow either text line by line. All inputs are published Library results.

## Auxiliary lemmas

- `lift_orbit`: restricting the torus orbit `orbit i g` along a point
  (b, s) of T × S gives the conjugation action of s on b ≫ g. This follows from
  naturality of the action.
- `mem_kernelCentralizer_of_isOrbitExtension`: suppose the orbit of g extends
  through the character, i.e. T ◁ (χ ≫ ι) ≫ e = orbit i g, where ι : Gm → 𝔸¹
  is the unit inclusion. Then g lies in the kernel centralizer. Take a
  refinement b : V → T and a point s of the character kernel, so that s ≫ χ = 1.
  The conjugate of b ≫ g by s is then the value of e at (b, ι(1)). The same
  holds for s = 1, which fixes b ≫ g. So s fixes b ≫ g. The kernel condition
  is read from `kernelPointsEquiv`.
- `centralizerAction_act_comp`: the torus action on C is compatible with
  conjugation in G along j. This is the Library's
  `AutomorphicAction.onRepresentedFixedSubgroup_act_comp`.
- `whiskerLeft_quotientAction_orbit_comp`: for a point c of C,
  T ◁ χ ≫ (descended orbit of c) ≫ j = orbit i (c ≫ j). The proof uses
  naturality, `AutomorphicAction.quotientAction_act_lift` (the descended action
  at χ(s) is the action of s) and the previous lemma.

## The two inclusions

- `subgroup_le_map` (root functor ⊆ image). Let g be a T-point with an
  extension e, T ◁ (χ ≫ ι) ≫ e = orbit i g, and with value 1 at zero. The
  auxiliary lemma puts g in the kernel centralizer. Since j represents it,
  g = c ≫ j for a point c of C. Next, the descended orbit of c followed by j
  equals T ◁ ι ≫ e as maps T × Gm → G. Since χ is a quasi-compact flat
  surjection, the published `AutomorphicAction.hom_ext_of_local_quotient_lift`
  reduces this to points of T × Gm that lift locally along T ◁ χ. On such
  points both sides agree by `whiskerLeft_quotientAction_orbit_comp` and the
  extension equation. Because j is a closed immersion,
  `AffineLine.exists_lift_of_unitInclusion` now factors e as e' ≫ j. Cancelling
  the monomorphism j shows that e' extends the descended orbit of c and that
  e' has value 1 at zero (`Dynamic.evalZero_comp`). So c lies in the
  descended `unipotent` functor and g is its image.
- `map_le_subgroup` (image ⊆ root functor). Let c have a descended orbit
  extension e' with value 1 at zero. Then e' ≫ j is an orbit extension of
  c ≫ j through the character, by `whiskerLeft_quotientAction_orbit_comp`. Its
  value at zero is 1 ≫ j = 1.

`quotientActionComparison` combines the two inclusions by antisymmetry.

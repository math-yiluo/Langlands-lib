# Smooth maps on points over complete nontrivially normed fields

Author: Worker 208.

`CompleteFieldSmoothPointOpenStatement.{u}` states the local openness assertion
used in Conrad's proof of Theorem 4.5. For every complete nontrivially normed
field `K`, every two schemes locally of finite type over `Spec K`, and every
smooth relative morphism `f : X ⟶ Y`, actual postcomposition

```text
fun p : RingPoint K X K => p ≫ f
```

is open for `schemePointTopology K X K` and `schemePointTopology K Y K`.
`RingPoint` is the actual relative morphism carrier with test scheme `Spec K`
and the structural map induced by the identity algebra map. The topology is the
published final topology from all affine open subschemes with their
global-section evaluation topologies.

The target imposes local finite type on both structural morphisms. It imposes
neither quasi-compactness nor separatedness, and does not restrict the schemes
to affine schemes. Smoothness is Mathlib's scheme morphism property on the
actual underlying morphism `f.left`. No surjectivity or connected-fibre
hypothesis is required for this local assertion. The field can have either
characteristic; archimedean and nonarchimedean norms are both allowed. The
field and schemes use an arbitrary common universe `u`.

## Original source and related targets

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`:

- Printed p.11, the discussion following Proposition 4.4, asserts openness for
  smooth maps of algebraic schemes over a field complete for a nontrivial
  absolute value. Its proof reduces to an étale presentation and continuity of
  simple roots.
- Printed p.12, proof of Theorem 4.5, step (i), states the precise version for
  schemes locally of finite type over such a field.

`NontriviallyNormedField K` and `CompleteSpace K` express the stated
absolute-value and completeness hypotheses directly. No local compactness or
discrete-valuation hypothesis is added.

The published `SmoothRationalPointOpenMapStatement` concerns affine schemes
over a nonarchimedean local field with the identity-test evaluation topology,
and allows affine bases not of finite type. The present target retains the
source local-finite-type assumptions while covering arbitrary schemes and the
full source class of complete normed fields. The two targets therefore have
different scopes. On affine schemes the published
`schemePointTopology_eq_affine` and
`rationalPointTopology_eq_rationalSchemeTopology` identify the topologies, and
`rationalPointEquiv` identifies the actual point conventions naturally.

This is a statement unit. It supplies the full local assertion needed in the
adelic theorem; it supplies neither its proof nor the additional almost-all
integral-point surjectivity needed for adelic openness.

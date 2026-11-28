# Fixed-level smoothing on the full quotient `L²` space and its cuspidal restriction

Let \(F\) be a number field and \(G\) an affine group scheme of finite type over \(F\).
Fix central split torus data \(i : Z \to G\), with \(Z\) identified with a split torus,
such that restriction of rational characters along \(i\) is injective with finite-index
image, and assume that the canonical Haar measure on the norm-one subgroup of
\(G(\mathbb A_F)\) is right invariant. These are the hypotheses under which the Library
defines the positive rational quotient, its measure `positiveRationalQuotientHaarMeasure`
and its right action. Fix Haar measures \(m_\infty\) and \(m_f\) on the archimedean and
finite adelic points and a measure \(m\) on \(G(\mathbb A_F)\) that is the image of
\(m_\infty \times m_f\) under the product splitting (`hProduct`). Fix a continuous
compactly supported archimedean function \(f_\infty\).

## Definition

`quotientL2SmoothingAction F G mInf mFin m hProduct hf hc Z i hi I e hz g k` is the
integrated action (`haarQuotientL2IntegratedAction`) of the tensor weight
`adelicSmoothingWeight` on the full space \(L^2\) of the positive rational quotient. The
weight is the \((k+1)\)-fold convolution of \(f_\infty\) (`positiveConvolutionPower`, equal to
\(f_\infty\) at \(k = 0\)) at the archimedean component times the finite test \(g\) at the
finite component. `adelicSmoothingAction` is the same
weight integrated on the full almost-everywhere cuspidal subspace \(S\).

## Statement

`QuotientL2FixedLevelSmoothingStatement` concerns a compact open subgroup \(K\) of the
finite adelic points and a finite test \(g\). Write \(R(g, k)\) for the quotient `L²`
smoothing action and \(T = R(\operatorname{vol}(K)^{-1}\mathbf 1_K, 0)\). It asserts three
things.

1. If \(g\) is right \(K\)-invariant and \(U\) is a bounded operator commuting with \(T\),
   then \(R(g, 0)\,U\,T^k = R(g, k)\,U\) for every \(k\).
2. Let \(\Theta\) be a topological group automorphism of \(G(\mathbb A_F)\). Assume that
   \(\Theta\) preserves the positive rational subgroup, that its quotient automorphism
   preserves the quotient measure, and that it preserves \(m\). If the weight of \(R(g, k)\)
   is \(\Theta\)-invariant, then the twisting operator \(I_\Theta\) (`twistOperator`)
   commutes with \(R(g, k)\).
3. For every proof of the parabolic dynamic statement and of connected reductivity, the
   inclusion of \(S\) intertwines every power of the cuspidal smoothing action with the same
   power of the quotient `L²` smoothing action.

## Proof

- Part 1 (`quotientL2FixedLevelSmoothingPowers`) repeats the proof of
  `adelicFixedLevelSmoothingPowers`, using the quotient `L²` right action. The splitting of
  \(G(\mathbb A_F)\) is measure preserving, so `integratedIsometricAction_pullback`
  identifies \(R(g, k)\) with `smoothingPowerTensorAction` on the product group.
  `fixedLevelSmoothingPowers` then gives the identity.
- Part 2 (`commute_twistOperator_quotientL2SmoothingAction`) applies
  `commute_integratedIsometricAction_of_invariant`. The required covariance
  \(I_\Theta R(a) = R(\Theta a) I_\Theta\) of the twisting operator with right translation is
  `IsotypicTrace.twistOperator_quotientL2RightTranslate`.
- Part 3 (`subtypeL_comp_adelicSmoothingAction` and its power version): the cuspidal right
  action is the restriction of the quotient right action. The inclusion of \(S\) is a
  continuous linear map, so it commutes with the Bochner integral
  (`ContinuousLinearMap.integral_comp_comm`). Induction on the power gives the rest.

Arthur–Clozel, *Simple algebras, base change, and the advanced theory of the trace
formula* (1989), Chapter 1, §4, printed pp. 43–45, motivates these identities. Their
comparison of the ordinary and twisted trace formulas matches split tensors by ordered
convolution at a split place, separates the contributions by archimedean component and
then uses finiteness at a fixed compact open level. The convolution powers here are
internal operator identities for a smoothing approach to the same comparison; they are
not taken from the cited pages. The argument uses only the Library results named above.

Source ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.

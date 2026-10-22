# The actual complex Lie and universal enveloping differential actions

For every number field K and natural rank n, `realSmoothLieAction` packages the
constructed real-linear matrix directional differential as a real Lie
homomorphism into the complex-linear endomorphisms of `SmoothFunctions K n`.
Its bracket proof uses the actual commutator theorem; no operator law is a
hypothesis.

`complexSmoothDifferential` is the complex-linear tensor extension on the
published complexification C tensor_R RealLieAlgebra K n. On a pure tensor
z tensor X it is z times the constructed smoothDifferential X. Double tensor
induction, bilinearity of the bracket, and the real bracket theorem prove that
this extension is a complex Lie homomorphism, `complexSmoothLieAction`.
Its restriction along `complexify` is the original real differential.

`envelopingAction` is Mathlib's `UniversalEnvelopingAlgebra.lift` applied to this
complex Lie homomorphism. It is an algebra homomorphism from the actual
universal enveloping algebra to the complex-linear smooth-function
endomorphisms. The generator theorem identifies its value on each canonical
Lie generator with `complexSmoothLieAction`; on a real generator this is
precisely `smoothDifferential`. `centerAction` restricts this homomorphism
along the inclusion of the actual algebra center.

`envelopingAction_real_generator_apply` evaluates a real generator as the
actual real derivative of the coordinate extension at g in the direction
gX. The unit acts as the identity, and multiplication acts by composition
in the order D(ab)f = D(a)(D(b)f).

These constructions are derived implementations of the enveloping-algebra
action on smooth complex-valued functions in Borel–Jacquet, *Automorphic forms
and automorphic representations*, sections 1.1, 1.3, and 4.1 (printed pages
189–190 and 194; one-based PDF pages 184–185 and 189). Registered source:
`borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The source supplies the setting; the tensor extension and universal-property
implementation here are derived. Center orbit objects and full
left-translation compatibility are supplied in separate modules.

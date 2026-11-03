# Orbit extensions inside cocharacter-stable open subschemes

This internal construction lifts an actual conjugation orbit extension through
an actual open immersion that is stable under the cocharacter. Its final
construction is `Dynamic.orbitOpenLift`, with equation
`Dynamic.orbitOpenLift_fac`. It works over any field `k : Type u` and for a
group scheme separated over `Spec k`.

Write `T = Spec k`, viewed as the identity object over `Spec k`. The inputs are a
cocharacter `χ`, a point `g : T ⟶ G.X`, an extension
`e : T ⊗ AffineLine.scheme (Spec k) ⟶ G.X` of the conjugation orbit of `g`, and
an open immersion `j : U ⟶ G.X` over `Spec k`. The stability input is
`Dynamic.IsCocharacterStable χ j`: for every scheme `Q` over the base, every
`a : Q ⟶ Gm`, and every `z : Q ⟶ U`, the point
`(aχ) * (zj) * (aχ)⁻¹` factors through `j`. The final input states that the
underlying point of `evalZero e` lies in `j.left.opensRange`.
The output is a morphism `q : T ⊗ AffineLine.scheme (Spec k) ⟶ U` over the
base, and the proved equation is `q ≫ j = e`.

The all-test stability definition also applies over an arbitrary scheme base.
`isCocharacterStable_product` proves it for the multiplication presentation of
two group schemes whose ranges are normalized by the cocharacter range.
The proof uses their existing normalized conjugation morphisms to construct
both new factors; the product equation follows by group cancellation.
`IsCocharacterStable.factors_iff` uses the scalar and its inverse to prove that
a point factors through `j` exactly when its conjugate does.

For a separated group scheme, `IsOrbitExtension.scale` derives scaling
equivariance from uniqueness of extensions across the multiplicative group
inside the affine line. This extracts the scaling identity used by the
published proof of `Dynamic.HasLimit.mem_centralizer`.
`IsOrbitExtension.eval_scale` evaluates that morphism equation on every test
scheme.

The field bridge defines the test scheme of a field extension, polynomial
evaluation at an element of that field, and the multiplicative-group point
associated with a unit. Their coordinates are identified using the existing
global-sections equivalence. `IsOrbitExtension.fieldEvaluation_scale` then
identifies evaluation at `a*x` with conjugation of evaluation at `x`.

`AffineLine.fieldTest_mem_opensRange_iff` uses the unique point of a field's
spectrum: membership of that point in the open image gives inclusion of the
entire map's range. The open-immersion lifting property supplies a scheme
morphism, and its factorization equation supplies compatibility with the base.
Consequently, stability and scaling imply
`IsOrbitExtension.isScalarInvariantOpen` for the pullback open along the
polynomial presentation of `e`. This quantifies over every same-universe field
extension, so it includes the residue fields of nonclosed points and also
works over finite fields.

`AffineLine.polynomialPoint_eval_zero` identifies the polynomial zero point
with the value of `evalZero e`. The saturation and lift construction
`AffineLine.invariantOpenLift` therefore applies to the polynomial presentation:
its pullback open is scalar invariant and contains zero.
`polynomialOrbitOpenLift` packages the resulting lift as a morphism over the
base. Composing with `polynomialPointInv` produces `orbitOpenLift`; the
polynomial comparison identities prove its factorization equation.

The argument is an internal deduction from the imported orbit uniqueness,
affine-line saturation, and normalized conjugation constructions. It adds no
splitness, perfectness, characteristic, or field-cardinality premise. The
actual stable open immersion and the orbit extension remain inputs. This unit
does not prove existence of an opposite cell or an unconditional rational
Bruhat decomposition.

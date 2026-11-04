# Quotient conjugation on a vector kernel

`VectorExtensionDescent.quotientAction` constructs an actual automorphic action
of `H` on a full vector kernel `V` of `q : E ⟶ H`, using an original scheme
section `s : H.X ⟶ E.X`. The section need not be a homomorphism or take the
identity to the identity.

The construction works over every field `k : Type u`. Its inputs are group
schemes `E`, `V`, and `H` over `Spec k`, a morphism `n : V ⟶ E` monic on
underlying relative schemes, full kernel equality
`hn : range n = range (kernelι q)`, a finite vector-group presentation
`hV : IsVectorGroupOfDimension V d`, and the scheme-section identity
`hs : s ≫ q.hom.hom = 𝟙 H.X`. This part requires no affineness, flatness or
torus hypothesis beyond those already implied by being a vector group.

`action_eq_of_comp_eq` first proves that the actual ambient conjugation action
`VectorExtensionDescent.action n q hn` is constant on quotient fibers on every
scheme test. If `q(g) = q(g')`, then `g⁻¹g'` lies in the full kernel. Write it
as `n(w)`, so `g' = g n(w)`. Natural vector coordinates imply that `w` and any
kernel point `v` commute. The images `n(w)` and `n(v)` therefore commute, and
conjugation of `n(v)` by `g'` equals conjugation by `g`. Cancellation of the
monic kernel inclusion proves equality of the two actual actions on `v`.

Define `quotientAct t v` to be ambient conjugation of `v` by `s(t)`. Naturality
follows from naturality of the ambient action and precomposition with `s`.
The quotient of `s(1)` is the identity, so fiber invariance proves the identity
action law. The quotient of `s(tr)` equals that of `s(t)s(r)`, so the same
fiber argument and ambient action multiplication law prove the quotient action
multiplication law. Conjugation preserves multiplication in the kernel.
`AutomorphicAction.ofPoints` then realizes these natural operations as an
actual scheme action morphism and packages its three intrinsic laws.

`quotientAction_act` identifies this actual action on every scheme test with
ambient conjugation by `s(t)`. `quotientAction_restrict` proves the exact action
equality

```text
(quotientAction n q hn hV s hs).restrict q = action n q hn.
```

Indeed, `s(q(g))` and `g` have the same quotient, so fiber invariance applies
again. Thus scalar-linear coordinates for the quotient action restrict to
scalar-linear coordinates for the original ambient conjugation action.

`IsTorus.exists_vectorExtensionSection` assumes in addition that `E` and `H`
are affine over `k`, the underlying morphism of `q` is flat and surjective,
and `hH : IsTorus H`. It retains the explicit input
`hlinear : TorusVectorActionLinearizationStatement.{u}`. Its conclusion is an
actual group-scheme homomorphism `σ : H ⟶ E` with `σ ≫ q = 𝟙 H`.
`IsTorus.vectorExtensionSection` chooses that homomorphism, and
`IsTorus.vectorExtensionSection_comp` proves its original quotient identity.

For this final deduction, the imported
`IsVectorGroupOfDimension.exists_quotientSection` constructs the original-field
scheme section from affine split-unipotent torsor triviality. Applying the
exact torus linearization statement to the quotient action supplies natural
finite linear coordinates on `V`. Restriction along `q` and the action equality
above supply the coordinates required by `IsTorus.exists_extensionSection`,
which produces the homomorphic section over the original field.

The provenance is an internal deduction from the imported full-kernel
conjugation, natural vector-coordinate, affine torsor and arbitrary-torus
extension constructions. No characteristic, perfection, cardinality or
splitness restriction is imposed. The torus-action linearization statement is
an explicit theorem-valued hypothesis of the final section constructor; this
module does not prove it. Neither the original scheme section nor ambient
linear coordinates remain hypotheses of that constructor. Torus pullback lifts
and the full maximal-torus conjugacy theorem remain further host obligations.

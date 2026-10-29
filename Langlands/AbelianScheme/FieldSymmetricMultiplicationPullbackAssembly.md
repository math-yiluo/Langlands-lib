# Symmetric multiplication pullback from the balanced cube identity

The definition
`Langlands.GroupScheme.fieldSymmetricMultiplicationPullbackIsoOfCube`
constructs a chosen actual module-sheaf isomorphism from multiplication
pullback to the concrete tensor power. It takes a proof of the balanced
cube proposition, the field and commutative group scheme, its smoothness,
properness and geometric connectedness, a symmetric line bundle, and a
positive natural number. It applies the conditional theorem below and
uses `Classical.choice` to select the isomorphism from its `Nonempty`
conclusion. The construction makes no assertion that the choice is
canonical or natural.

`Langlands.GroupScheme.fieldSymmetricMultiplicationPullbackOfCube` proves

```text
FieldCubePullbackStatement.{u} →
  FieldSymmetricMultiplicationPullbackStatement.{u}.
```

The balanced cube proposition is an explicit premise. This supporting module
does not prove that proposition or the unconditional multiplication target.
It leaves both published statement pairs and their imports unchanged.

The conclusion retains every quantifier of the multiplication statement:
an arbitrary field `K : Type u`, an actual commutative group scheme over
`Spec K` with smooth, proper and geometrically connected structure map,
an actual line bundle `L` symmetric under pullback by multiplication by
`-1`, and every positive natural number `n`. It produces an actual
module-sheaf isomorphism, expressed with `Nonempty`, between multiplication
pullback and `tensorPow L.obj (n * n)`. No characteristic restriction is used.

## Invertibility and the concrete tensor

The private helpers `lineBundle_invertible` and
`lineBundle_pullback_invertible` apply the published theorem
`Langlands.AlgebraicGeometry.Picard.locallyFreeRankOneIffTensorInvertible`
to the local rank-one property of `L` and its actual pullbacks.
Thus tensor invertibility is proved from the line-bundle hypotheses,
using the unconditional symmetric monoidal structure on scheme-module
sheaves. No tensor-invertibility hypothesis is added.

`tensorObj_invertible` transports invertibility of the monoidal tensor
through `Langlands.Scheme.Modules.localizedTensorIso`, whose target is
the explicit sheafified `tensorObj`. Induction gives invertibility of
the right-associated `tensorPow`, including its final structure-sheaf
unit factor.

`picard_tensorObj` uses the same comparison, together with
`PicardGroup.ofObject_tensor` and `PicardGroup.ofObject_eq_iff`,
to identify the Picard class of `tensorObj M N` with the sum of the two
classes. `picard_tensorPow` then proves that the class of `tensorPow M r`
is `r` times the class of `M`. These are consequences of the constructed
categorical Picard group; no Picard power action is supplied as data.

## Initial values and recurrence

Write `m(i)` for the underlying map of `multiplication G i`, `q(k)` for
the Picard class of `m(k)^*L`, and `a` for the class of `L`.

Multiplication by zero factors through the field spectrum and the identity
section. Pull `L` back along that section and apply the published theorem
`Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality`. Actual
pullback composition and unit comparisons then trivialize `m(0)^*L`,
so `q(0) = 0`. Multiplication by one is the identity, and the actual
pullback identity comparison gives `q(1) = a`. The supplied symmetry
isomorphism gives the class of `m(-1)^*L` equal to `a`.

The private helper `picard_cube_pullback` converts the isomorphism supplied
by the cube premise into the equality of Picard classes

\[
c(fgh)+(c(f)+(c(g)+c(h)))
=c(fg)+(c(fh)+c(gh)).
\]

It proves invertibility of all seven pulled-back factors and the two
balanced tensors, applies `ofObject_eq_iff`, and expands the tensors with
`picard_tensorObj`.

The main theorem specializes this equality to
`f = m(k+1)`, `g = m(1)` and `h = m(-1)`.
The published integer-power construction gives
`m(i) * m(j) = m(i+j)`, where the pointwise product represents the group
law on the abelian variety. The four product arguments become
`m(k+1)`, `m(k+2)`, `m(k)` and `m(0)`. Substituting the initial values
and symmetry gives

\[
q(k+2)+q(k)=q(k+1)+q(k+1)+(a+a).
\]

The private additive-group lemma `quadratic_recurrence` proves
`q(k) = (k*k) • a`. Its induction keeps two consecutive values,
cancels `q(k)` in the recurrence, and uses the natural-number identity

\[
(k+2)^2+k^2=2(k+1)^2+2.
\]

Finally, `picard_tensorPow` identifies this class with that of the exact
concrete tensor power, and `PicardGroup.ofObject_eq_iff` returns the
required actual module-sheaf isomorphism. The induction also treats zero;
the published conclusion requests only positive `n`.

## Provenance and remaining obligation

This construction and its supporting theorem are internal derived content
by Worker 316. They combine the two
published statement interfaces with the published field triviality,
local rank-one comparison, multiplication, tensor comparison and
categorical Picard constructions. The recurrence and its induction are
implemented here; no new geometric cube, descent or coherence result is
asserted. The motivating original source remains the source documented
in the [multiplication statement](FieldSymmetricMultiplicationPullbackStatement.md)
and the [balanced cube statement](FieldCubePullbackStatement.md).

The field-triviality proof, including Worker 316's previously extracted
helper, is reused from the published Library by Lean name. Other workers'
published results are likewise imported by name; this module copies no
unpublished peer draft.

An unconditional proof of `FieldCubePullbackStatement.{u}` is still needed
before this assembly can yield the exact multiplication target without an
extra premise. Development compilation and review of this conditional
supporting unit do not complete the multiplication proof task.

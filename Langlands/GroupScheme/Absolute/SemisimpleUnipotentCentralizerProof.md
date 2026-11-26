# Semisimple conjugation on a commutative unipotent normal subgroup

`Langlands.GroupScheme.semisimpleUnipotentCentralizer.{u}` proves
[`Langlands.GroupScheme.SemisimpleUnipotentCentralizerStatement.{u}`](SemisimpleUnipotentCentralizerStatement.md).
The conclusions apply to every supplied representative `c : C ⟶ N` of the
centralizer in `N`. They give connectedness of the underlying space of `C`
and surjectivity of the underlying morphism of schemes `N × C → N`.

## Proof

The normal conjugation action gives the endomorphism `δ(x) = [s, x]` of `N`.
Its multiplication law follows from the commutativity of `N` and the
multiplicativity of the action on each test scheme. Postcomposing with `n`
identifies the kernel condition with commutation with the pullback of `s`.
Thus `c` and the scheme-theoretic kernel of `δ` represent the same subgroup
functor. The kernel is closed since `N` is affine over the field, so `c` is
also a closed immersion.

For a rational point `x`, suppose `y = δ(x)` lies in the kernel. In the
ambient group, with `x` and `y` viewed via `n`, the product `y⁻¹s` equals
`xsx⁻¹`. Choose a closed faithful matrix representation. Write `a` for the
endomorphism representing `s` and `b` for the one representing `y⁻¹`.
The unipotence of `N` makes `b − 1` nilpotent, and `b` commutes with `a`.
Conjugacy gives semisimplicity of `ba`, while `a` is semisimple by
hypothesis. The decompositions `ba = (b − 1)a + a` and `ba = 0 + ba`
have commuting nilpotent and semisimple parts. Additive Jordan–Chevalley
uniqueness gives `(b − 1)a = 0`, hence `b = 1`. Faithfulness and the
monomorphism `n` imply `y = 1`. Taking the quotient of two inputs shows
that `δ` is injective on its rational image.

The images of the powers of `δ` are closed by the homomorphism image theorem
for smooth connected affine groups. They form a descending chain in the
Noetherian space underlying `N`. Once two consecutive images agree, the
corresponding images on rational points agree as well. A nonempty fiber over
a rational point has a closed point, which is rational over the algebraically
closed field. Injectivity on the rational image allows cancellation of the
common iterates. Therefore for each `z ∈ N(k)` there is an `x ∈ N(k)` with
`δ²(x) = δ(z)`. The point `δ(x)⁻¹z` is in the kernel and therefore equals
`c(y)` for some `y ∈ C(k)`.

The map `f(x, y) = δ(x)c(y)` is a homomorphism by commutativity. Its image
contains every closed point, so it is dominant. The target is reduced by
smoothness. Faithful flatness of dominant homomorphisms to reduced field
groups gives surjectivity, and flatness and local finite presentation give
openness. The `C` coordinate of a rational point over a given point of `N`
is unique. Applying `δ` to two product expressions proves equality of
their first commutator factors by injectivity on the rational image.
Cancellation and monicity of `c` then give equality of their second
coordinates.

If `C` admitted a nontrivial clopen partition, the inverse images of its
parts under the second projection would be nonempty and open. Their images
under `f` would form a cover of `N` by two nonempty opens. Connectedness of
`N` forces the overlap to be nonempty. Choose a closed point in the overlap
and a rational lift in each open part of the domain. Such lifts exist by
taking a closed point of each nonempty locally closed fiber intersection.
The two lifts have second coordinates in different parts, contradicting the
uniqueness just proved.

## Source

James S. Milne, *Algebraic Groups* (2017), §16e, Lemma 16.39, printed p. 338,
and §9.19, printed p. 171. The registered source is
`milne-2017-algebraic-groups` with SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The proof uses Milne's Jordan decomposition argument for the intersection
of the commutator image with its kernel. Stabilization of the iterated images
and openness of the product homomorphism give the two geometric conclusions.

# Independence of conjugate valuation apartments from their transporter

Author: Worker 118.

Work over an arbitrary field. Let `i : S → G` and `j : S' → G` be the
actual embeddings of two commutative group schemes, with monomorphic
underlying inclusions. Supply two actual conjugation squares `(e,g,h)` and
`(e',g',h')` from `i` to the same `j`. The isomorphisms `e,e' : S ≅ S'`
and rational points `g,g' ∈ G(k)` may differ.

`transporterDifferenceNormalizer` is the original source normalizer point
with underlying rational point `n = g'⁻¹*g`. The published algebraic
transporter theorem gives its actual source automorphism
`e` followed by `e'⁻¹`. For every full root-function family `φ`,

`T(e,Int(g))(φ) = T(e',Int(g'))(n • φ)`.

Here `T` is the existing full-family transport and the action on the right
is the original source-normalizer action. The proof evaluates the two
families at every character and every rational point. The actual Weyl
action formula and the inverse torus isomorphisms identify the characters.
The rational-point inputs agree by
`n⁻¹*(g'⁻¹*u*g')*n = g⁻¹*u*g`. This comparison needs no ambient affineness
or supplied valuation data; it uses monomorphism only for the source
inclusion, to define its original normalizer action. The ratio normalizer
constructor itself requires no monomorphism.

Now assume the ambient structural morphism is affine and supply
`D : KPApartmentData i ω`, with the same scalar function `ω` for both
transports. The original normalizer stability of its carrier and the
family comparison give a common member of the two transported carriers.
The established common-member criterion identifies their entire apartment
data. Thus the transported full valuation class depends only on the
actual target embedding, among the supplied conjugation squares.

`D.conjugateApartmentIdentification` is the affine equivalence between
these two target apartments which retains every underlying valuation
family. Its derivative is the identity on their common target translation
space. The generic carrier-comparison value and derivative lemmas give
these two properties without unfolding the transported data.
On transported source points it identifies `T(e,Int(g))(x)` with
`T(e',Int(g'))(n • x)`, using exactly the original normalizer action.

Under this identity of target valuation points, their previously
constructed maps into the original quotient `D.ReducedBuilding` agree.
Indeed the two values on corresponding source coordinates are
`g • apartmentMap(x)` and `g' • apartmentMap(n • x)`. Original chart
equivariance turns the latter into `(g'*n) • apartmentMap(x)`, which is
the former. Their entire set-theoretic images consequently agree.

The provenance is internal. This is a compatibility construction from the
published actual transporter-difference theorem, full-family transport,
normalizer action, common-member criterion and conjugate quotient
realization. It assumes both actual conjugation squares and the source
apartment data. It asserts neither existence of such squares for arbitrary
target tori nor compatibility with a separately specified target
valuation class. A global assignment to all actual maximal split tori,
apartment intersections, full A2, building validity and general building
existence remain separate obligations.

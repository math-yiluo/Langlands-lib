# Quasi-finiteness from a normalized residue-field fibre

This derived internal construction supports the relative-dimension sublevel
route toward Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). The registered source
is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad's theorem motivates the construction; he does not state this
intermediate algebraic assertion. Worker 105 is the author.

For a finite-type commutative R-algebra S, a prime p of R, and a nonzero
actual fibre `p.ResidueField tensor[R] S`, `fiberQuasiFiniteCoordinates`
constructs normalization coordinates in S with an additional property:
the original R-polynomial evaluation map is quasi-finite at every point
q of Spec S mapping to p. R and S have independent universes. Neither
Noetherianity nor a domain or injectivity assumption on the original
algebra map is required.

The record `FiberQuasiFiniteCoordinates` extends
`FiberNormalizationCoordinates`. Thus it retains the finite family in S,
the finite injective evaluation map over the residue field, and the
equality of its number of variables with the actual fibre's ring Krull
dimension. Its added `quasiFiniteAt` field refers to the original map
`MvPolynomial.aeval`, with its induced algebra structure, at each such q.
The exported constructor proves this field from the constructed
normalization; it is not a caller-supplied hypothesis.

The helper `quasiFiniteAt_of_quasiFinite_base_fiber` treats a tower
R to B to S, with S finite type over B. If the actual base-changed map
`p.Fiber B` to `p.Fiber S` is quasi-finite, it proves quasi-finiteness of
B to S at any q over p. Its three rings have independent universes.
Mathlib's residue-field fibre homeomorphisms identify their actual prime
spectra. Comapping Spec of `p.Fiber B` into Spec B is injective, and
comapping commutes with the tower. The fibre of Spec S over the image
of q in Spec B therefore maps continuously and injectively into the
corresponding fibre of the base-changed map. The latter has discrete
topology by quasi-finiteness. Pulling back its open singleton gives an
open singleton in the original fibre. Mathlib's finite-type singleton
criterion then proves quasi-finiteness at q.

The polynomial helper `quasiFiniteAt_aeval_of_finite_fiber_aeval` applies
this reflection to B equal to the polynomial ring over R. S is finite
type over B by restriction of scalars. The polynomial tensor-product
equivalence identifies `p.Fiber B` with the polynomial ring over the
residue field. Polynomial extensionality proves that composing the
base-changed evaluation map with the inverse equivalence is exactly
evaluation at `1 tensor s_i`. Its assumed module finiteness implies
quasi-finiteness; quasi-finiteness of a composite reflects to the last
map. This supplies the preceding reflection lemma's hypothesis.

Finally, the constructor applies that helper to the finite normalization
already constructed in `FiberNormalizationCoordinates`. All record
fields are thereby established from finite type and a nonzero fibre.
The result controls the original polynomial map at points over one
chosen base prime. General relative-dimension sublevel openness,
retrocompactness, geometric-connectedness constructibility, and filtered
descent remain separate obligations.

# Actual content ideles and normalization of primitive vectors

This module constructs an actual idele from the local maximum coordinate norms
of a primitive adelic vector. It continues `PrimitiveAdelicHeight` using the
existing full and finite adele rings, their unit groups and local completions.
All statements retain any number field `F : Type u` and dimension `n : ℕ`.

The source is T. A. Springer, *Reduction theory over global fields* (1994), §1.8,
printed pp.209–210, especially the paragraph after properties (a)–(d) on p.210.
There Springer defines the set of vectors with local norm one at every place
and asserts that each primitive vector has an idele multiple in this set.
The source is registered as `springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
The retained original is
`literature/Reduction theory over global fields (Springer, 1994).pdf`.
As in the height module, the chosen local norms are maximum coordinate norms,
with real/complex multiplicities retained in the global height and idele norm.

## Construction

A nonzero vector in a finite product of normed fields has a coordinate whose
norm equals the maximum coordinate norm. `localContentUnit` chooses such a
coordinate and packages it as a nonzero local unit. Positivity of the local
norms of primitive vectors justifies applying this construction at every place.
The definitions `finiteContentUnit` and `infiniteContentUnit` specialize it to
the existing local projections of the actual adelic vector.

The finite-support theorem from the height module implies that the chosen
finite local unit has norm one outside a finite set. The equivalence between
norm one and valuation one places it in the unit group of the local integral
subring there. `RestrictedProduct.mkUnit` therefore assembles these local units
into an actual finite idele, `finiteContent`. The infinite local units assemble
into `infiniteContent`, and the existing finite/infinite unit-group equivalence
constructs `contentIdele` in the actual full idele group.

`norm_contentIdele_finite` and `norm_contentIdele_infinite` identify its local
norms with the original vector's local maximum norms. `full_contentIdele`
then identifies its existing normalized idelic absolute value with
`positiveHeight`. These maps involve choices of maximizing coordinates;
no continuity of the chosen maps is asserted.

## Normalization and implemented proof

Primitivity is preserved under actual invertible adelic matrices by composing
the witnessing matrices, and under scalar ideles by their actual scalar
matrices. `normalizedVector` multiplies the original vector by the inverse of
its content idele. It remains primitive. The local scalar-norm formulas and
inverse-unit identities prove that its finite and infinite local maximum
coordinate norms are all one. Finally,
`contentIdele_smul_normalizedVector` proves that multiplying this normalized
vector by the content idele recovers the original vector.

Thus the implemented map supplies the existence of an idele normalization
asserted in the cited paragraph. This unit does not prove that the set of
normalized vectors is compact, the height limit properties (c)–(d), existence
of rational height minima, Gauss reduction, rank induction or Galois descent.
The full connected reductive Siegel reduction theorem and its compatible
compact subgroup remain open obligations.

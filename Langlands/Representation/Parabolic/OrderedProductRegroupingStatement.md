# Ordered normalized product regrouping

Authors: Worker 175; Worker 157 contributed the independent-input-universe
interface used by the finite-length consumer.

`Langlands.Parabolic.OrderedProductRegrouping.{uF,uV} F T` is a
Prop-valued statement for a p-adic field `F : PadicField.{uF} p` and its selected
topological data `T`. It compares the normalized product of an original family
of smooth GL representations with the normalized product of the normalized
products in a prescribed ordered block refinement. It asserts an actual
isomorphism in the smooth representation category.

The data are two shapes `B,D : BlockShape n`, inner shapes
`S : BlockRefinement D`, a bijection
`e : (Sigma (fun j => Fin (S j).length)) ≃ Fin B.length`, and rank equalities
`h a : (S a.1).size a.2 = B.size (e a)`. The exact ambient coordinate hypothesis is
`D.index j ((S j).index k x) = B.index (e ⟨j,k⟩) (Fin.cast (h ⟨j,k⟩) x)`.
It fixes the original consecutive coordinates; an arbitrary permutation of
blocks is not included without that hypothesis.

For factors `σ i : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)`,
the target is `Nonempty` of an isomorphism from the original normalized product
to the outer normalized product of the inner products on
`τ j k := (h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩)`. These are actual equality transports of
smooth representations, not identifications of unrelated ranks. The field and
input carrier universes remain independent. The inner induced carriers and
both final carriers lie in `Type (max uF uV)`; consequently the outer product
functor is instantiated at carrier universe `max uF uV`. The statement requires
no positive total rank, irreducibility, unitarity, admissibility or analytic
temperedness. Rank zero is retained.

The provenance is an internal interface for composing the existing ordered
coordinate-normalization comparison, the finite-product induction/tensor
comparison, and intrinsic normalized induction in stages. The coordinate
hypothesis is exactly the one in
`Langlands.Group.GL.RefinementCoordinates`. The intended composition transports
the flat tensor to the refined Levi, regroups it with exact factor rank
transports, and uses the actual induction functors. This is a specialization and
composition interface for those Library constructions, not a separately quoted
literature assertion. It states neither a canonical evaluation formula nor
naturality in the factor family. This module supplies the proposition only;
publication of this statement does not prove it or any analytic grouping theorem.

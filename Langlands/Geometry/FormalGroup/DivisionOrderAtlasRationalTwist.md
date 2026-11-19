# Division-unit quasi-isogenies of actual formal atlases

Over an `𝒪[K]`-algebra, conjugate an actual formal atlas order action
`E` by `g : Dˣ` using `a ↦ g⁻¹ a g` on the actual integer order. The
twist retains the atlas and its formal transition maps. Its whole
rational action is the original algebra map precomposed with inverse
conjugation on `D`. This equality follows by agreement on the integer
order.

`atlasTwistQuasiIsogeny` uses the whole atlas rational actions of `g⁻¹`
and `g` as its forward and inverse tensors. The two whole inverse
equations follow from multiplication in `D`. On each test chart the
forward commutation equation is the one for the existing coordinate
quasi-isogeny to the twist. The atlas upgrade from forward equivariance
proves that both maps commute with the full order. Chart evaluation
recovers the complete coordinate quasi-isogeny. Coefficient extension
also commutes with the complete atlas quasi-isogeny. For an integer-order
unit acting on a special atlas this map is precisely the rationalization
of the existing integral atlas twist isomorphism.

The construction implements the division-unit quasi-isogeny appearing in
the framing formula in Drinfel'd, *Coverings of p-adic symmetric regions*
(1976), §2 A, printed p. 109. It works on atlas order actions. Preservation
of the special tangent condition for general division units and the
framing height correction require further results.

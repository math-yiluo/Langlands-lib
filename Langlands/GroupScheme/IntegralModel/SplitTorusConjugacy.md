# Split-torus conjugacy through a supplied integral model

This internal construction applies `HenselianSplitTorusConjugacy` to a supplied
`IntegralModel M` over a commutative domain `R` with fraction field `K`.
Every type has arbitrary common universe `u`; no characteristic restriction
is imposed.

For actual integral maps `i : T.toGrp → M.group` and
`i' : T'.toGrp → M.group` and supplied `A : SplitTorusConjugator i i'`,
`A.genericPoint M` is exactly `M.integralPointMap A.section_`.
`genericPoint_mem_integralPoints` witnesses its membership with that same
section. These definitions and the following equations do not require
Henselian, splitting, smoothness or maximality assumptions.

`generic_comm` proves

    M.genericHom i ≫ Int(A.genericPoint M) =
      groupHom ((baseChange (Spec.algebraMap R K)).mapIso A.torusIso).hom ≫
        M.genericHom i'.

Here the base-change functor on the source is the commutative group-scheme
functor. The actual generic source-torus isomorphism is the pullback of the
recorded integral isomorphism. The proof applies
`M.genericHom_comp_innerIso_of_isTransporter` to `A.isTransporter`, expands
`genericHom`, and uses preservation of composition under base change. It expands
the commutative base-change functor and forgets the additive notation with
`toMul_ofMul`, identifying its actual map with the group base-change map.
`inverse_generic_comm` reverses this square using the inverse of the same
point and the inverse pulled-back isomorphism. It uses
`innerIso_inv_hom`, cancellation by the inner isomorphism, and the
source-isomorphism inverse identities.

`M.henselianSplitTorusConjugator` assumes that `R` is Henselian local,
`M.IsSmooth`, `R → k` is a surjective algebra map to a field, the actual
`k`-fibre of `M.group` has connected underlying space, and `G` is connected
reductive. Both integral source tori must be split, both integral maps must
be closed immersions, and both `M.genericHom` maps must be maximal split
tori in `G`. It returns actual `SplitTorusConjugator i i'`.

The proof transports connected reductivity back across `M.genericIso`
using `IsConnectedReductive.of_iso`. It transports each maximality proof
back across the same isomorphism using `IsMaximalSplitTorus.comp_iso_iff`.
The published-input construction
`Langlands.GroupScheme.henselianSplitTorusConjugator` then applies.
The whole integral model and its residue fibre need not be reductive.
No initial model, integral torus, apartment, or special torus is constructed
here. This is derived model-specific glue, with no new literature claim.

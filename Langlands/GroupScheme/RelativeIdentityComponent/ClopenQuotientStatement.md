# Homogeneous quotient for a closed relative identity component

`Langlands.GroupScheme.RelativeIdentityComponent.ClopenQuotientStatement.{u}`
is a statement-only proposition. Let `S` be any scheme, `G → S` a smooth
separated quasi-compact group scheme, and `i : H → G` a supplied relative
identity-component representative. If `i` is a closed immersion, then
there is a `HomogeneousQuotientFromEmbedding.HomogeneousQuotient i`.
Openness is already part of `IsRelativeIdentityComponent`.

The existing `HomogeneousQuotient` structure asks for an actual scheme
`Q` over `S` and a map `p : G → Q` over `S`, with:

- `Q → S` separated, locally of finite type and quasi-compact;
- `p` smooth, surjective and quasi-compact;
- for every scheme `T` over `S` and every two `T`-points `g,h` of `G`,
  `p(g) = p(h)` if and only if `g⁻¹h` factors through `i`.

The proposition constructs neither a group law nor an étaleness proof:
the existing `HomogeneousQuotientGroup` and `OpenSubgroupQuotientEtale`
modules provide these from such data and normality. It has no reductivity
or affineness hypothesis on `H` or `G`. It does not prove that `i` is
closed.

This is a derived interface for the last step of the proof of Conrad,
*Reductive group schemes* (2014), Proposition 3.1.3, pp.82–83. After
closedness of `G⁰` is established, that proof uses only the smooth finite
presentation of `G` and the clopen relative identity component to obtain
the separated étale scheme quotient. These are precisely the premises
retained here. Smoothness of the projection comes from its being an fppf
torsor under the smooth identity component; its quasi-compactness comes
from finite presentation of that component. The all-test coset condition
is the equivalence relation represented by the quotient. The conclusion
records the geometric data needed to use the existing Library
constructions; the source's stronger étaleness conclusion is omitted.

Source read: Brian Conrad, *Reductive group schemes* (2014), Proposition
3.1.3 and proof, pp.82–83, with the finite presentation of `G⁰` recalled on
pp.81–82. Registered source `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

This module supplies no proof of quotient representability, algebraic
space schemeness, or any instance of the original clopen target.

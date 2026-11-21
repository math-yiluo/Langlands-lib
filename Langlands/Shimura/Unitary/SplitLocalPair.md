# Local algebras with exchange involution at split CM places

Choose an actual place `q` of `K` above a split finite place `p` of `E`.
For a central simple algebra `B` over the completion at `q`, `otherFactor`
is its opposite extended to the completion at `otherPlace q` along the
canonical field isomorphism over the base completion. Extension across
this isomorphism preserves the degree and local Brauer invariant, so the
other factor has the same degree as `B` and its invariant is the negative
of the invariant of `B`.

The product of these factors receives the completed center through the
two actual completion maps. The algebra isomorphism from the opposite to
the other factor is induced by the right tensor inclusion for a scalar
extension along an isomorphism. The product involution is obtained by
transporting exchange on `B × Bᵐᵒᵖ` across that isomorphism in the second
coordinate. The oriented split-center chart shows that this involution
acts on the image of the completed center by its specified CM conjugation.

`invariantFactor` chooses an actual degree-`n` factor with any specified
`n`-torsion Brauer invariant, including a primitive invariant. Together
with `otherFactor`, this realizes the signed pair of finite invariants
at a chosen split place in Clozel 1991, equation (2.3), printed p. 104,
and the prescribed-place remark attached to Proposition 2.3, pp. 105–106.
The proof uses the Library's same-universe Brauer group at the two CM
completions. The real field and the CM field can have independent
universes.

# Actions with connected fibres on reductive group schemes are inner

Workers 681 and 716.

`Langlands.GroupScheme.reductiveConnectedActionInner.{u}` proves
`Langlands.GroupScheme.ReductiveConnectedActionInnerStatement.{u}` in every
universe `u`. It takes the supplied full-centre fppf quotient `p : G ⟶ Gad`
and compatible action `c` from the statement. The base scheme may be empty
or nonreduced. The condition on the acting group `H` is connectedness of
its residue fibres. [Target statement](ConnectedActionInnerStatement.md)

The proof applies `reductiveConnectedActionInner_of_innerActionLocus` to
`reductiveInnerActionLocus`. The latter supplies an open and closed
immersion `j : K ⟶ H` and a homomorphism `φ : K ⟶ Gad` with
`c.restrict φ = a.restrict j`, together with the universal property for
compatible pairs of homomorphisms. [Inner-action locus proof](InnerActionLocusProof.md)

The range of `j` meets each residue fibre of `H` at the identity. Its
preimage in that fibre is clopen and nonempty, so connectedness makes it
the whole fibre. The reduction uses surjectivity of the open immersion
to make `j` an isomorphism of group schemes. Restriction along
`inv j ≫ φ` gives `a`. For any `x : H ⟶ Gad` with `c.restrict x = a`,
the universal property gives `f : H ⟶ K` with `f ≫ j = 𝟙 H` and
`f ≫ φ = x`. These equations force `f = inv j` and `x = inv j ≫ φ`.
[Connected-fibre reduction](ConnectedActionInnerReduction.md)

This formalizes Brian Conrad, *Reductive group schemes* (2014),
Proposition 7.2.6, p. 253. Conrad uses the separated étale outer
automorphism group of Theorem 7.1.9(1), pp. 245–246, to test innerness on
fibres. The Lean proof uses the clopen locus supplied by the automorphism
scheme and checks that its range contains every residue fibre directly.
The registered source is `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

# Field transport of Henniart's lattice maps

`Langlands.Correspondence.LatticeMap.henniartProperties_fieldPullback` proves
that the lattice-map properties of Henniart's construction are preserved under
an isomorphism of p-adic fields. Let `f : F.Carrier ≃ₐ[Padic p] E.Carrier`.
`LatticeMap.fieldPullback` transports a linear equivalence between sublattices
over `E` to one over `F`. On the Weil side it restricts along
`extensionWeilEquiv E F f.symm : W_F ≃ₜ* W_E`. On the supercuspidal side it
pulls back along the entrywise action of `f`. The new sublattices are the
images of the two old ones. `fieldPullback_apply` computes the value on an
image vector by applying the original map and then pulling back its value.

- The lattice bijections reindex the unitary bases without changing ranks or
  coefficients. This carries the pairing, degree and generator clauses to the
  new lattices. Contragredients commute with both pullbacks.
- Given a geometric reciprocity candidate over `F`,
  `LocalClassField.exists_geometric_extensionWeilEquiv` supplies one over `E`
  with `rec_E(φ w) = f(rec_F(w))` for the Weil map `φ`. A modulus-one field
  character `χ` of `F` is carried to `χ ∘ f⁻¹` on `E`. Its Weil character
  restricts to the original one along `φ`, and the determinant pullback of the
  field character has the corresponding property on general linear groups.
  These identities transport the twist and rank-one clauses. The same
  reciprocity square transports the determinant clause, using restriction of
  Weil determinants and pullback of supercuspidal central characters.
- The pair-factor proof pushes the additive character and any supplied
  self-dual measure to `E`, where they remain self-dual. On the Weil side,
  `unitaryPairLFactor_restrictUnitaryLatticeEquiv` uses preservation of the
  integral degree, and `isUnitaryPairEpsilonFactor_transport` carries an
  arithmetic epsilon certificate from the transported common-closure system
  over `E` to the supplied one over `F`. On the supercuspidal side, the two
  `isUnitaryPair…_unitaryLatticeEquiv_iff_transport` lemmas identify the local
  relations for the original and transported data. This gives the same
  epsilon coefficient and exponent on both sides for every supplied system.

The field, Weil representation, supercuspidal representation and local-constant
system universes remain independent. This is a local form of the transport in
Henniart's §3.8, applied to the full properties of a supplied lattice map.

Source for the clauses: Guy Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), §3.8 (a)–(c),
p. 451, literature ID `henniart-2000-simple-proof`, retained PDF SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

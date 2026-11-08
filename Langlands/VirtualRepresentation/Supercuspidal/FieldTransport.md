# Supercuspidal lattices along an isomorphism of topological fields

Author: Worker 84. This is a definition and construction contribution.

## Content

Fix fields `F` and `E` with topologies, in independent universes, and a
carrier universe `uV`. Let `σ : F ≃+* E` be a ring isomorphism. The
hypotheses `hσ : Continuous σ` and `hσs : Continuous σ.symm` say that `σ`
is a homeomorphism. The module transports the published supercuspidal
classes and lattices of `Langlands.VirtualRepresentation.Supercuspidal.Basic`
along `σ`. Representations of `GL_n(E)` are pulled back to `GL_n(F)`, so the
lattice maps go from `E` to `F`.

### General linear groups and block subgroups

In namespace `Langlands.GeneralLinear`:

- `fieldEquiv n σ hσ hσs : GeneralLinear n F ≃ₜ* GeneralLinear n E` applies
  `σ` to every matrix entry. Its inverse applies `σ.symm` to every entry.
  Both directions are continuous by `Continuous.generalLinearGroup_map` from
  pinned Mathlib. `fieldEquiv_apply` records the entrywise formula, and
  `fieldEquiv_symm` identifies the inverse with `fieldEquiv n σ.symm hσs hσ`.
- For a block shape `B`, `BlockShape.parabolic_comap_fieldEquiv` and
  `BlockShape.unipotentSubgroup_comap_fieldEquiv` show that the standard
  block parabolic and block unipotent subgroups over `F` are the preimages of
  the corresponding subgroups over `E`. The proofs compare the published
  membership criteria `mem_parabolic_iff` and `mem_unipotentSubgroup_iff`
  entry by entry. An entry is `0` or `1` exactly when its image under `σ` is.
- `BlockShape.unipotentSubgroup_map_fieldEquiv` gives the image form, and
  `BlockShape.conjugateUnipotent_map_fieldEquiv` shows that the image of the
  published conjugate unipotent subgroup `B.conjugateUnipotent g` is
  `B.conjugateUnipotent` of the image of `g`. The reason is that `fieldEquiv`
  is a group homomorphism, so it commutes with conjugation.
- `BlockShape.parabolic_ne_top_fieldEquiv_iff` shows that `B.parabolic F` is
  proper exactly when `B.parabolic E` is proper.

### Supercuspidality and representatives

- `isSupercuspidal_comp_fieldEquiv` shows that the pullback along
  `fieldEquiv` of a representation of `GL_n(E)` that satisfies the published
  `IsSupercuspidal` condition satisfies it over `F`. Admissibility comes
  from the published `isAdmissible_comp_continuousMulEquiv`. For the Jacquet
  condition, fix a proper block shape over `F` and `g`. The published
  `Jacquet.coinvariantsMapEquiv` identifies the coinvariants of the pullback
  along `B.conjugateUnipotent g` with the coinvariants of the original
  representation along the image subgroup. By the previous section the
  image subgroup is `B.conjugateUnipotent (fieldEquiv n σ hσ hσs g)`, whose
  coinvariants vanish by hypothesis.
- `isSupercuspidal_comp_fieldEquiv_iff` gives the converse. It applies the
  forward direction to `σ.symm` and uses that the two transports compose to
  the identity.
- `SupercuspidalRep.fieldPullback` pulls an actual supercuspidal
  representative of `GL_n(E)` back to `GL_n(F)`. It uses the published
  `SmoothRep.pullback`, and irreducibility is preserved by the published
  `isIrreducible_comp_continuousMulEquiv_iff`.
  `SupercuspidalRep.fieldPullback_representation` records the underlying
  representation. `SupercuspidalRep.fieldPullbackIso` pulls back
  isomorphisms through the published `SmoothRep.pullbackFunctor`.
  `SupercuspidalRep.fieldPullbackSymmIso` identifies the pullback along `σ`
  followed by the pullback along `σ.symm` with the original representative.
  It is the identity map of the underlying space.

### Classes

- `SupercuspidalClass.fieldPullback σ hσ hσs` is the induced map on the
  published isomorphism classes `SupercuspidalClass`.
  `fieldPullback_isoClass` computes it on a representative.
  `fieldPullback_symm_fieldPullback` and `fieldPullback_fieldPullback_symm`
  show that pullback along `σ.symm` inverts it.
- `SupercuspidalClass.fieldPullbackEquiv σ hσ hσs n` is the resulting
  bijection of rank-`n` classes, from `E` to `F`. `fieldPullbackEquiv_symm`
  identifies its inverse.
- `SupercuspidalClass.isUnitarizable_fieldPullback_iff` shows that pullback
  preserves and reflects unitarizability of classes. The forward direction
  is the published `IsUnitarizable.comp`, and the converse applies the
  forward direction to `σ.symm`.

### Bases and lattices

In namespace `Langlands.VirtualRepresentation.Supercuspidal`:

- `fieldBasisEquiv σ hσ hσs : Basis E ≃ Basis F` keeps the positive rank and
  applies `fieldPullbackEquiv` to the class. `fieldBasisEquiv_rank`,
  `fieldBasisEquiv_symm` and `fieldBasisEquiv_basisClass` give the rank, the
  inverse (pullback along `σ.symm`) and the value on the published
  `basisClass` of a representative.
- `isUnitaryClass_fieldBasisEquiv_iff` shows that the published unitary
  predicate `IsUnitaryClass` is preserved and reflected.
  `fieldUnitaryBasisEquiv σ hσ hσs : UnitaryBasis E ≃ UnitaryBasis F` is the
  restriction to unitary bases, with lemmas for the value, the inverse and
  the published `unitaryBasisClass`.
- `fieldLatticeEquiv σ hσ hσs : Lattice E ≃ₗ[ℤ] Lattice F` and
  `fieldUnitaryLatticeEquiv σ hσ hσs : UnitaryLattice E ≃ₗ[ℤ] UnitaryLattice F`
  are the published finite-support reindexing `reindex` along the two basis
  bijections. Their `single`, `generator`, `coefficient` and `symm` lemmas
  record that a generator goes to the generator of the pulled-back class,
  that coefficients are unchanged, and that the inverse is the pullback
  along `σ.symm`. `fieldLatticeEquiv_ofRepresentation` and
  `fieldUnitaryLatticeEquiv_ofUnitaryRepresentation` state the generator
  formula for the published `ofRepresentation` and
  `ofUnitaryRepresentation`.
- `includeUnitary_fieldUnitaryLatticeEquiv` shows that the published
  inclusion `includeUnitary` intertwines the two reindexings.
- `degree_fieldLatticeEquiv`, `unitaryDegree_fieldUnitaryLatticeEquiv`,
  `multiplicityPairing_fieldLatticeEquiv` and
  `unitaryPairing_fieldUnitaryLatticeEquiv` show that the published integral
  degree and the coefficient pairings are preserved. The proofs are by
  finite-support induction. On a single generator, the rank and the basis
  bijection settle the claim.

### p-adic fields

In namespace `Langlands.VirtualRepresentation.PadicSupercuspidal`, fix
`F E : PadicField p` and an isomorphism of `ℚ_p`-algebras
`f : F.Carrier ≃ₐ[Padic p] E.Carrier`. All topologies are the canonical
topologies `canonicalTopologicalData.topology`, which the published
`PadicSupercuspidal` bases and lattices use.

- `continuous_algEquiv F E f` shows that `f` is continuous. It is an
  isometry for the canonical norms by the published
  `Weil.Local.extension_isometry`.
- `unitaryBasisEquiv F E f`, `latticeEquiv F E f` and
  `unitaryLatticeEquiv F E f : UnitaryLattice E ≃ₗ[ℤ] UnitaryLattice F` are
  the constructions above for `σ = f.toRingEquiv`, with continuity of `f`
  and of `f.symm`.
- `unitaryLatticeEquiv_generator`, `unitaryLatticeEquiv_coefficient`,
  `unitaryLatticeEquiv_symm` (the inverse is `unitaryLatticeEquiv E F f.symm`),
  `includeUnitary_unitaryLatticeEquiv`, `degree_latticeEquiv`,
  `unitaryDegree_unitaryLatticeEquiv` and `unitaryPairing_unitaryLatticeEquiv`
  specialize the corresponding lemmas.

## Choices and scope

All maps are canonical given `σ`, or given `f` in the p-adic case. No choice
of representatives, forms or characters enters beyond the published lattice
constructions. The module makes no statement about Weil groups, local
Langlands parameters or L-factors. It does not compare the transport with
contragredients, twists, central characters or Rankin-Selberg factors. The
convention `σ : F ≃+* E` with separate continuity hypotheses for `σ` and
`σ.symm` matches the published `Langlands.HarmonicAnalysis.FieldTransport`.

## Sources

The construction is derived. Its purpose is the identification step of Guy
Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Invent. Math. 139 (2000), registered source
`henniart-2000-simple-proof`. In §3.7 (printed page 451) Henniart fixes a
continuous isomorphism `ι_0` from the completion `F_{v_0}` onto the given
p-adic field and uses it to identify representations of the two general
linear groups. This module turns that identification into an isometry of the
unitary supercuspidal lattices of §2.5-2.6 (printed pages 446-447). The
module `Langlands.VirtualRepresentation.Weil.GroupTransport` does the same
on the Weil side. The facts used here are elementary: transport of
representations along an isomorphism of topological groups preserves
smoothness, admissibility, irreducibility and unitarizability, and an entrywise
field isomorphism maps standard block subgroups to standard block subgroups.
They are proved here or taken from the published declarations named above.

## Dependencies

Project imports are `Langlands.VirtualRepresentation.Supercuspidal.Basic`,
`Langlands.Representation.CompactCoefficient.GroupTransport`,
`Langlands.Representation.Unitary.Restriction` and
`Langlands.Weil.Local.ExtensionResidue`. Published declarations used by Lean
name include `BlockShape.parabolic`, `BlockShape.unipotentSubgroup`,
`mem_parabolic_iff` and `mem_unipotentSubgroup_iff`
(`Langlands.Group.GL.Blocks`), `BlockShape.conjugateUnipotent`,
`IsSupercuspidal`, `supercuspidalProperty`, `SupercuspidalRep`,
`SupercuspidalRep.isoClass` and `SupercuspidalClass`
(`Langlands.Representation.Classification.Supercuspidal`),
`Jacquet.coinvariantsMapEquiv` and `isAdmissible_comp_continuousMulEquiv`
(`Langlands.Representation.CuspidalSupport.GroupTransport`),
`SmoothRep.pullback`, `SmoothRep.pullbackFunctor` and
`isIrreducible_comp_continuousMulEquiv_iff`
(`Langlands.Representation.CompactCoefficient.GroupTransport`),
`SmoothRep.mkIso` (`Langlands.Representation.Category.Basic`),
`IsUnitarizable.comp` (`Langlands.Representation.Unitary.Restriction`),
`reindex`, `generator`, `pairing` and `includeSubset`
(`Langlands.VirtualRepresentation.Integral`), the basis, lattice, degree,
pairing and representative declarations of
`Langlands.VirtualRepresentation.Supercuspidal.Basic`,
`PadicField.canonicalTopologicalData` and `PadicField.canonicalNormedField`
(`Langlands.LocalField.Definitions`) and `Weil.Local.extension_isometry`
(`Langlands.Weil.Local.ExtensionResidue`). Pinned Mathlib supplies
`Matrix.GeneralLinearGroup.map`, `Continuous.generalLinearGroup_map`,
`Subgroup.map_comap_eq_self_of_surjective`, `Subgroup.map_map`,
`Equiv.sigmaCongrRight`, `Equiv.subtypeEquiv`, `Finsupp.domLCongr_single` and
`Finsupp.induction_linear`. The environment is Lean 4.34.0 with Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. All declarations and
proofs in this module are by Worker 84.

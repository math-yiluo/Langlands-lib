# Positive bases and split pinnings from regular cocharacters

This is an internal construction from the Library's prescribed-coweight base
existence theorem, actual ordinary Galois root action, pairing invariance and
split root-line theorem. It constructs the positive base, the permutation action
on its simple roots and an initial actual split pinning from the inputs below.
No original-literature assertion is introduced here.

Let `k` and `K` be fields in an arbitrary universe `u`, with a `k`-algebra
structure on `K`. Let `T` be a commutative group scheme over `k`, let `G` be an
affine group scheme over `k`, and let `i : T.toGrp ⟶ G`. Write `T_K`, `G_K` and
`i_K` for their canonical base changes. Supply a finite root index type `J` in
universe `u` and a reduced root datum `P` on the actual character and cocharacter
lattices of `T_K`. Where required, `hP : IsRootDatumOf i_K P` identifies its
pairing with `latticePairing T_K` and its roots and coroots with those of the
actual inclusion.

Supply an actual cocharacter `ν` of `T_K` that is regular for `P`: for every
root index `a`, `P.root' a ν ≠ 0`. The base construction itself needs only the
root datum and this regularity; it does not use `i` or `hP`.

`IsRootDatumOf.regularCocharacterBase` chooses a genuine integral base using
`RootDatumCoweightFace.exists_base_support`. Its support, as stated in
`regularCocharacterBase_support`, is the set `IsAddIndecomposable.baseOf` for
`P.root` and the integral functional `P.flip.toLinearMap ν`: the positive roots
that are not sums of two positive roots. The theorem
`regularCocharacterBase_isPos` identifies positivity for this base with
`0 < latticePairing T_K (P.root a) ν`.

If `ν` is fixed by every coefficient automorphism in `K ≃ₐ[k] K`, then
`galoisRootIndexEquiv_regularCocharacterBase_isPos` proves that the ordinary
root-index action preserves these positive roots. The definition
`regularCocharacterSimpleAction` restricts that action to the constructed simple
support as a monoid homomorphism into its permutation group. Its `_root` theorem
states the actual character identity

```text
P.root (regularCocharacterSimpleAction ... σ a)
  = characterLattice.galoisRepresentation k K T σ (P.root a).
```

For a ground-field cocharacter `ν₀`, whose canonical base change is regular,
`descendedRegularCocharacterSimpleAction` constructs the same action directly.
The fixedness input is supplied by the proved
`cocharacterLattice.galoisRepresentation_baseChange` theorem. The corresponding
`_root` theorem gives the same ordinary character identity.

Finally, if `G_K` is connected reductive, `T_K` is split and `i_K` is a maximal
torus inclusion, `regularCocharacterPinning` constructs a `SplitPinning G_K` with
exactly this torus, inclusion, root index type, realized datum and selected base.
Its simple-root Lie trivializations are constructed by
`RootPinning.ofSplitMaximalTorus`, using the proved split root-line theorem.
This initial pinning construction does not require Galois fixedness of `ν`.

The proofs proceed as follows. The generic lemma
`RootPairing.Base.isPos_iff_positive_functional` shows that an integral linear
functional positive on every simple root is positive on every positive root,
by induction adding a simple root. Conversely, either a root or its negative is
positive. In the negative case linearity would make the functional negative,
contradicting its assumed positivity. Applying this lemma to the support
specified by `exists_base_support`, and using `hP` for the actual pairing,
proves the desired sign characterization. Simultaneous Galois transport
preserves the actual character/cocharacter pairing; fixedness of `ν` therefore
makes its positive roots stable. The existing
`RootPairing.Base.mem_support_equiv_iff_of_isPos` then gives stability of the
simple support using root transport alone. Restriction of the already proved
root-index action supplies its identity and multiplication laws. The pinning
assembly uses the actual root-line existence theorem for each selected simple
root.

The extension `K/k` need not be finite, Galois or separable, and neither field
needs to be perfect or infinite. Fixedness refers to the displayed automorphism
group; it is not a claim that every fixed cocharacter descends for an arbitrary
extension. The actual torus, realized reduced datum, regular cocharacter and
split maximal-torus geometry remain supplied inputs. This module does not
construct them from quasi-splitness, prove equivariance of the chosen pinning
vectors, or assert a cross-section or quotient theorem. In particular it makes
no assertion of a global rational section in even type A.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.

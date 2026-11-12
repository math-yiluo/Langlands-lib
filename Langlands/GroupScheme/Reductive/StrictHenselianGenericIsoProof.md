# Proof: generic-fibre determination over strictly Henselian local domains

Module `Langlands.GroupScheme.Reductive.StrictHenselianGenericIsoProof`.

This module proves the Library statement `StrictHenselianGenericIsoStatement`
(theorem `strictHenselianGenericIso`, at every universe `u`). Let `R` be a commutative domain
that is a Henselian local ring with separably closed residue field, and `K` a fraction field of
`R` with its given `R`-algebra structure. If two reductive group schemes `G` and `H` over
`Spec R` have isomorphic base changes to `Spec K`, then `Nonempty (G ≅ H)`. The conclusion is
an abstract isomorphism over `R`. The proof does not show that the supplied generic
isomorphism extends, and it uses that isomorphism only to compare root data.

## Helper lemma

`exists_coordinate_fibrewiseMaximalTorus_of_strictHenselian`: let `R` be a Henselian local ring
with separably closed residue field and `G` a reductive group over `Spec R`. Then there are a
finite type `I`, with a chosen `Fintype` instance, and a homomorphism
`i : splitTorus (Spec R) I ⟶ G` from the coordinate split torus such that `i` is a closed
subgroup and `IsFibrewiseMaximalTorus i` holds. That is, the base change of `i` to every
residue field of `Spec R` is a maximal torus.

Proof. The published `strictHenselianSplitMaximalTorus` gives a commutative group scheme `T`,
a closed subgroup `i : T ⟶ G` that is maximal on every residue-field fibre, and a split-torus
witness: a finite type `I` and an isomorphism `e` from `T` to the coordinate split torus
`splitTorus (Spec R) I`. Take a `Fintype` instance on `I` from `Finite I`. The new embedding is
`e.inv ≫ i`.

- `IsClosedSubgroup.iso_comp` shows that `e.inv ≫ i` is a closed subgroup.
- `isMaximalTorus_baseChange_inv_comp_iff` shows that it is maximal on every residue-field
  fibre. This lemma says that precomposing with an isomorphism of tori does not change
  maximality after base change.

## Main proof

Fix `R`, `K`, `G`, `H` and an isomorphism `f` of the `K`-base changes.

1. `IsReductive` includes smoothness and affineness of the structure morphisms (`hG.smooth`,
   `hG.isAffineHom`, and the same for `H`). The proof makes these instances available to the
   later lemmas.
2. The helper lemma gives coordinate split tori `i : splitTorus I ⟶ G` and
   `i' : splitTorus I' ⟶ H`. Both are closed subgroups and are maximal on every residue-field
   fibre.
3. `localSplitFibrewiseRootDatumExistence` (proof of
   `LocalSplitFibrewiseRootDatumExistenceStatement`) applies to `(G, i)` and `(H, i')`. It gives
   reduced root data `P` on `I → ℤ` and `Q` on `I' → ℤ` with `IsFibrewiseRootDatumOf I G i P`
   and `IsFibrewiseRootDatumOf I' H i' Q`. So `P` (resp. `Q`) is the root datum of `i`
   (resp. `i'`) on every field-valued fibre.
4. `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise` turns fibrewise maximality into
   maximality of the coordinate split tori of `G` and `H` after base change to the field `K`.
5. `IsFibrewiseRootDatumOf.nonempty_equiv_of_reductive_fieldIso` takes the two fibrewise data,
   the reductivity of `G` and `H`, the two maximality facts over `K`, and the isomorphism `f`.
   It returns `Nonempty (RootPairing.Equiv P Q)`. The statement's base-change morphism
   `Spec.algebraMap R K` matches the comparison lemma's `algebraBaseMap R K` by unfolding
   (definitional equality), so `f` is passed unchanged. The supplied isomorphism need not
   preserve the chosen tori.
6. `localSplitReducedIsomorphismTheorem` (proof of
   `LocalSplitReducedIsomorphismTheoremStatement`, the Isomorphism Theorem over a reduced local
   ring) applies because a domain is reduced. Its inputs are the two embeddings, their closed
   and fibrewise-maximal properties, the data `P` and `Q`, and the root-datum equivalence from
   step 5. It returns `Nonempty (G ≅ H)`.

The proof does not use `IsFractionRing R K`. Any field `K` with an `R`-algebra structure would
work, and the domain hypothesis on `R` enters only through `IsReduced R`. The theorem's type is
still exactly `StrictHenselianGenericIsoStatement.{u}`. The only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The route matches the derivation recorded in the statement's Markdown. That derivation is from
Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`. Over a strictly Henselian local base the group splits
(Lemma 5.1.3 and Proposition 5.1.6, PDF pp. 136–138, here supplied by
`strictHenselianSplitMaximalTorus` and `localSplitFibrewiseRootDatumExistence`). The root data
are compared on a field fibre (maximal-torus conjugacy, Theorem 3.2.6, PDF p. 94, inside the
published field comparison). Then the Isomorphism Theorem 6.1.17 (PDF p. 197) gives the
integral isomorphism (`localSplitReducedIsomorphismTheorem`). The proofs of these steps are in
the imported Library modules and their Markdown files. This module only assembles them, and
the replacement of the abstract split torus by its coordinate model is internal. The root data
are compared directly over `K`; no algebraic closure of `K` is chosen in this module.

# Finite local degree transfer and conditional total invariant tower laws

This derived supporting unit implements the summation argument in Artin–Tate,
*Class Field Theory* (2009), Chapter VII §3, printed pp.42–43, especially Lemmas
1–2. The local restriction formula and independence from the chosen upper finite
place remain explicit hypotheses. The unit proves the passage from those local
formulas to the tower laws for the existing `totalIdeleInvariantMaps`; it does
not prove those hypotheses or `GlobalInvariantStatement`.

All number fields lie in a common arbitrary `Type u`. The supplied family is the
unchanged `I : ∀ p [Fact p.Prime], InvariantFamily.{u,u} p`. The constructions use
the actual idele cohomology, completion algebras, local invariants, and tower
maps. The hypothesis `hI : ∀ p [Fact p.Prime], (I p).RelativeImages` supplies the
finite support needed by the existing `finiteIdeleInvariantVector` and
`finiteIdeleInvariantSum`.

## The two finite local premises

`FiniteIdeleInvariantPlaceIndependent I` is a proposition requiring, for every
Galois number-field extension `E/F`, finite place `v` of `F`, upper places `w,z`
of `E` above `v`, and `c ∈ H²(Gal(E/F), J_E)`, equality of
`finiteIdeleInvariant I v w c` and `finiteIdeleInvariant I v z c`.

`FiniteIdeleInvariantRestriction I` is a proposition for every compatible tower
`F → K → E` with `E/F` Galois, every chain of finite places `v,w,q` above each
other, and every actual idele cohomology class `c`. It requires

\[
 \operatorname{inv}_{w,q}(\operatorname{Res}_{K}c)
 = [K_w:F_v]\,\operatorname{inv}_{v,q}(c).
\]

The same place `q` of `E` occurs on both sides. The restriction uses the existing
`relativeIdeleRestriction F K E 2`, and the degree is the finrank of the actual
completion algebra. The induced Galois instance for `E/K` comes from tower
normality; `K/F` need not be Galois. Neither proposition is established here.
In particular, the unit asserts no new change-of-base naturality for `I`.

## Transfer and its sum

For a choice `wf` of places of `E` above each finite place of `F`,
`finiteIdeleInvariantBaseTransfer I hI (K := K) wf` is the additive map

\[
 H^2(\operatorname{Gal}(E/F),J_E)
 \longrightarrow \bigoplus_{w\text{ finite in }K}\mathbb Q/\mathbb Z
\]

obtained by composing `finiteIdeleInvariantVector I hI wf` with
`finitePlaceDegreeTransfer`. This construction itself needs only the number
fields, algebras `F → K` and `F → E`, and Galoisness of `E/F`; an algebra
`K → E` is only needed by the subsequent restriction comparison.

At `w`, degree transfer multiplies the lower vector's coordinate at
`v = w.under (𝓞 F)` by `[K_w:F_v]`. The theorem
`finiteIdeleInvariantSum_eq_finitePlaceSum` identifies the existing finite
invariant sum with `finitePlaceSum` of that vector. Consequently,
`finitePlaceSum_finiteIdeleInvariantBaseTransfer` gives

\[
 \sum_w \operatorname{Transfer}(c)_w
 = [K:F]\,\operatorname{finiteSum}_{F,E}(c).
\]

This uses the published `finitePlaceSum_degreeTransfer`, whose proof sums the
completed degrees above each lower place. No local choice or restriction premise
is required for this identity about the constructed transfer.

Under both local premises, `finiteIdeleInvariantVector_restriction_eq_transfer`
identifies the actual restricted vector, for any upper-place choice `wk` over
`K`, with this transfer. Its proof takes `q = wk w`, applies the supplied local
restriction law, and uses place independence to replace `q` over `v` by `wf v`.
Applying the sum map gives `finiteIdeleInvariantSum_relativeIdeleRestriction`.
This is precisely the finite-place summation step of Artin–Tate's Lemma 2.

## Total invariants and inflation

Place independence also yields equality of finite vectors and sums for arbitrary
choices. Combining this with the published canonical archimedean sum identity,
`totalIdeleInvariantMaps_eq_of_placeIndependent` identifies the total family
with `totalIdeleInvariant I hI wf wi` for every finite choice `wf` and infinite
choice `wi`.

For inflation, assume additionally the supplied family's existing
`InflationCompatibility` law at every prime. The proof lifts `wf` along the
upper field extension using `Reciprocity.liftFinitePlaces`, applies the published
finite inflation law for compatible choices, and then removes the compatibility
condition using place independence. Adding the canonical archimedean inflation
law proves `totalIdeleInvariantMaps_inflation`, which has the existing
`IdeleInvariantMaps.InflationCompatible` conclusion.

Finally, `totalIdeleInvariantMaps_restriction` adds the finite restriction sum
identity to the published canonical archimedean restriction identity and
uses distributivity of natural-number multiplication over addition. Its
conclusion is the existing `IdeleInvariantMaps.RestrictionCompatible`, with
factor `[K:F]`. These total-family results retain the stated local premises.
They are inputs to regular-class assembly; they do not establish the remaining
arithmetic inputs, local compatibility on idele classes, or the final existence
theorem.

Source: Artin–Tate, *Class Field Theory*, AMS Chelsea (2009), Chapter VII §3,
printed pp.42–43 (PDF pages 51–52), local components, total invariant, and Lemmas
1–2. The finite-support transfer interface is an internal formalization of the
source's degree-sum calculation. Its conditional division into local hypotheses
and summation conclusions is explicit in the Lean declarations.

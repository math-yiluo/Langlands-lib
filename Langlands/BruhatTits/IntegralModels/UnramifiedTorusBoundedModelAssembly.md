# Reduction of the unramified torus model to the maximal bounded model theorem

`UnramifiedTorusBoundedModelAssemblyStatement.{u}` is the implication
`MaximalBoundedIntegralModelStatement.{u} →
UnramifiedTorusBoundedModelStatement.{u}`.
`unramifiedTorusBoundedModelAssembly` proves this implication at arbitrary
universe `u`. The general model theorem remains an explicit premise; this
module alone does not prove the unconditional torus model statement.

## Provenance and scope

This is a derived reduction of published Library statements. Its mathematical
inputs correspond to Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
Proposition 2.5.8, printed p. 88 / PDF p. 119, identifies the unique maximal
bounded subgroup of a torus with the common character-valuation kernel.
Definition B.7.1 and Proposition B.7.2(2), printed pp. 675–676 / PDF
pp. 706–707, give a smooth integral model with this subgroup as its integral
points over the maximal unramified integers. Corollary B.7.4 states its
schematicity.

The registered corrections `kaletha-prasad-2024-corrections` (1 November
2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 24–25, correct the sign of the character valuation in Section
2.5(b); the kernel is unchanged. PDF pp. 49–50 amend Appendix B only in
Section B.10. These corrections do not change Proposition 2.5.8 or
Proposition B.7.2.

The construction specializes the general maximal-bounded-subgroup model
statement to the actual field `K = inertiaFixedField F` and ring
`O = fixedFieldIntegers F` for every nonarchimedean local field `F`.
The input torus is an actual commutative group scheme with affine underlying
scheme and `IsTorus T.toGrp`. The conclusion retains an actual
`IntegralModel O K T.toGrp`, its smoothness, and the literal subgroup
equality with `characterValuationKernel (fixedFieldValuation F) T.toGrp`.
It does not identify this existential model with the source's ft-Néron
model or assert its mapping property. Completeness and local compactness
are not imposed on `K`.

## Implemented proof

`MaximalUnramified.maximal_characterValuationKernel` proves maximality
for the integer-normalized valuation. The published theorem
`MaximalUnramified.isAlgebraicallyBounded_characterValuationKernel` gives
boundedness. For every algebraically bounded subgroup `B`, the published
`IntegerValuation.subgroup_le_characterValuationKernel_of_isAlgebraicallyBounded`
gives its containment in the kernel. Its compatibility instance is supplied
by `MaximalUnramified.valuation_compatible F`. Thus the kernel is bounded
and every bounded overgroup is contained in it.

`MaximalUnramified.maximal_fixedFieldCharacterValuationKernel` transports
this maximality using `characterValuationKernel_eq_of_isEquiv` and
`MaximalUnramified.valuation_isEquiv F`, so it concerns precisely the
valuation in the target.

`unramifiedTorusBoundedModelAssembly` installs the valuative relation
prescribed by `fixedFieldValued F`. Published arithmetic supplies that
`O` is a Henselian discrete valuation ring and that its residue field is an
algebraic closure of the residue field of `F`, hence algebraically closed.
The published `IsTorus.smooth` supplies smoothness of the generic torus.
The supplied maximal bounded model theorem then applies to the maximal
subgroup just proved.

For the base ring, the proof follows the equality transport used in
`exists_smoothVertexModel_of_maximalBounded`: a local auxiliary argument
is parametrized by a valuation subring `A` equal to the intrinsic valuation
ring of `K`, substitutes this equality, and applies the general theorem.
Finally `fixedFieldIntrinsicIntegers_eq F` instantiates this argument at
the literal ring `O`. This retains the target's exact integral model type
and integral-point equality.

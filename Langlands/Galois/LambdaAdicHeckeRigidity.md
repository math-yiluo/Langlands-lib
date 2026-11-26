# Hecke characters are determined by one member of a compatible realization

## Density lemma

`ideleClass_hom_ext_of_uniformizers_t2`: two continuous homomorphisms
`ρ₁, ρ₂` from the idele class group of a number field `K` to a Hausdorff
topological group are equal if they agree on the classes of all uniformizers
at the finite places outside a finite set `S`.

The equalizer of `ρ₁` and `ρ₂` is a closed subgroup. Its preimage `H` in the
ideles is closed and contains the principal ideles. Off `S`, a local unit `a`
of valuation `m` factors as `(a π^(m+1)) · π^(-(m+1))` with two uniformizers
`a π^(m+1)` and `π`, so `H` contains the whole local multiplicative group at
each place outside `S`. The density theorem
`Langlands.Global.IdeleDensity.eq_top_of_isClosed` then gives `H = ⊤`. This
is the Hausdorff-target form of the argument of
`Langlands.ClassFieldTheory.Global.Artin.ideleClass_hom_ext_of_uniformizers`,
which treats a discrete target.

## Rigidity of realizations

`heckeCharacter_eq_of_lambdaAdic_eq`: let `χ₁, χ₂` be Hecke characters of `K`
with compatible realizations `ψ₁, ψ₂` (`IsCompatibleLambdaAdicRealization`)
through the same complex embedding `ι` of the coefficient field `L`. If
`ψ₁ λ = ψ₂ λ` for one finite place `λ` of `L`, then `χ₁ = χ₂`.

Outside the two exceptional sets and the finitely many places with the same
residue characteristic as `λ` (`finite_setOf_residueCharacteristic_eq`),
evaluate both realizations at a geometric Frobenius lift. Equality of the
`λ`-adic characters gives equal images of the two Frobenius values
`a₁, a₂ ∈ L` in the completion, hence `a₁ = a₂`. Both characters are
unramified at such a place `v`. Their values at any uniformizer `π` equal
their values at the uniformizers of the realization
(`HeckeCharacter.finiteComponent_eq_of_valued_eq`), which are `ι a₁` and
`ι a₂`. The density lemma concludes.

This is the step "equal `λ`-adic characters have equal good Frobenius values,
hence equal Hecke characters by weak approximation" of the irreducibility
argument for Harris 1998, Proposition 4.8 (`harris-1998-local-langlands`,
pp. 202–203).

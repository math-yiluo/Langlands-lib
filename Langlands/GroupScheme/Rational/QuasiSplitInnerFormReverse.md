# Finite-Galois assembly from reverse separable-closure innerness

This internal construction connects the actual symmetry and finite-stage
descent interfaces. It works over an arbitrary field `k` in universe `u`
without restrictions on characteristic or perfectness.

`QuasiSplitInnerForm.ofSeparableClosureLocal` takes a connected reductive
group `G`, a quasi-split group `H`, a supplied full-centre adjoint quotient
`p : H ⟶ B`, and a natural local family `e : H → G` over the separable
closure with inner discrepancy for the actual inner action of `B`.
The existing supplied-quotient theorem
`adjointQuotientQuasiSplitStatement` proves quasi-splitness of `B`.
The local-family/base-change-isomorphism equivalence supplies an actual
isomorphism `e.toBaseChangeIso`, and its inverse law identifies the resulting
family with the original `e`. The published `ofSeparableClosure` constructor
then descends this specified isomorphism to a finite separable stage, reflects
its inner discrepancy from the separable closure, constructs the natural
adjoint cocycle and refines the cover to a finite Galois extension.

`QuasiSplitInnerForm.ofReverseSeparableClosure` instead takes a natural
family `e : G → H` over the separable closure and its innerness for a supplied
full-centre quotient `q : G ⟶ A`, along with `H`, its quasi-splitness and
`p : H ⟶ B`. Actual induced local transport between `A` and `B` and its
inner-action equivariance prove innerness of `e.symm` for `B`.
The first constructor produces the finite-Galois presentation.
Connected reductivity of `G` is supplied by its quotient witness.

The result is an actual `QuasiSplitInnerForm G`: the cover, natural
discrepancy cocycle and all-test local equivalences are constructed by the
invoked interfaces. The two final lemmas record that its model is exactly
`H` and its adjoint target is exactly `B`. Quasi-splitness of `B` is derived.

The provenance is internal, by composition of the existing actual
separable-closure, discrepancy-symmetry and adjoint quasi-splitness results.
Both full-centre quotients, the quasi-split model, the reverse local family
and its initial innerness are inputs. Constructing those data for every
connected reductive `G` remains required by the unconditional existence
statement.

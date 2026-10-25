# Tensor extension presentation of etale coefficient inverse systems

## Scope and provenance

Let `X : Scheme.{u}`, let `R : Type u` be a commutative ring, and let `I`
be an ideal of `R`. Coefficient module carriers have universe `u`.
All sheaves are module sheaves on the actual small etale site of `X`.
No smoothness, properness, characteristic, finiteness, flatness, or
nontriviality assumption is imposed.

This is an internal specialization and assembly of
`Langlands/Sheaf/AdicTensorComparison.lean`, the existing small-etale
coefficient systems in `EtaleAdicSystem.lean`, and the actual tensor-then-
sheafification extension functor in `EtaleScalarExtension.lean`. It is not
an independent transcription of a result from Harris. The required
sheafification and sheaf-composition instances are synthesized from the
existing Mathlib infrastructure; no sheafification comparison is an input.

## Comparison at a coefficient level

`tensorReduction X I` is a natural isomorphism from
`sheafExtendScalars (Ideal.Quotient.mk I) X` to the existing
`quotientCoefficients X I`. Both constructions use the same small etale
site. The former tensors section modules and sheafifies; the latter
quotients section modules and sheafifies. Their comparison is induced by
the natural module isomorphism `(R/I) tensor_R M ≅ M/IM`.

For `q_n : R → R/I^n`, write `L_n` for `sheafExtendScalars q_n X` and
`U_n` for `sheafRestrictScalars q_n X`. The latter restricts scalars
sectionwise, preserving sheaves. `extensionPower X I n` is the actual
endofunctor `L_n ⋙ U_n` of `EtaleDerivedSections.ModuleSheaf X R`.

`extensionPowerIso X I n`, denoted `e_n`, compares this endofunctor to the
existing `Q_n := (Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).obj (op n)`.
It first moves scalar restriction through sheafification using the generic
`extensionPowerIso`, then applies the sheafified tensor/quotient comparison.

`extensionPowerIso_unit` proves

`sheafExtensionUnit q_n X ≫ e_n.hom = quotientMap X.smallEtaleTopology I n`.

Its proof composes the two generic unit identities. In particular, the
comparison respects the actual extension/restriction adjunction unit,
whose sectionwise formula is the sheafification image of `1 tensor m`.

## Transitions and the full inverse system

For `m ≤ n`, let `q_nm : Q_n → Q_m` be the transition in the existing
sheaf quotient system. `extensionTransition X I h` is the explicitly
constructed composite

`e_n.hom ≫ q_nm ≫ e_m.inv`.

Thus its maps are determined by the actual quotient transitions. The
following intrinsic laws are proved:

- `extensionTransition_comparison`: the transition followed by `e_m.hom`
  equals `e_n.hom` followed by `q_nm`.
- `extensionTransition_refl`: the transition at an equal index is the identity.
- `extensionTransition_comp`: the composite `n → m → l` equals `n → l`.
- `extensionTransition_unit`: the unit at `n` followed by the transition
  equals the unit at `m`.

The first three proofs cancel adjacent inverse comparisons and use the
functor laws of the existing quotient diagram. For the last law, the proof
composes with the invertible comparison at `m`, applies the unit comparison
at both levels, and uses `quotientMap_transition`.

`extensionPowers X I` is the resulting functor from `ℕᵒᵖ` to sheaf
endofunctors. `extensionPowersIso X I` has components `e_n` and identifies
it naturally with the existing sheaf quotient diagram. The order is
higher powers to lower powers, and exponent zero is included.

`extensionFunctor X I` flips the coefficient-level and sheaf variables.
`extensionFunctorIso X I` is a natural isomorphism to the existing
`EtaleAdicSystem.functor X I`. Its components are the same `e_n` evaluated
on the sheaf; the two naturality conditions follow from the transition
comparison and the naturality of `e_n`, respectively.

## Boundaries

The construction concerns ordinary etale sheaves and ordinary inverse
systems. It does not assert that extension of scalars is exact, commutes
with cohomology, or preserves injectives. It does not identify an inverse
limit with an adic completion or construct a derived inverse limit.
Geometric equivariance, smooth group actions, and the identification with
the specific coefficient sheaves required by Harris remain separate work.

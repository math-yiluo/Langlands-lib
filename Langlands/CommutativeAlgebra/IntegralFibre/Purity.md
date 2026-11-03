# A purity lemma for flat algebras over Noetherian rings

This module is part of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
Over a Noetherian base it shows that injectivity of multiplication by an element of a flat
algebra can be tested on the fibres at the associated primes of a finite module.

## Definitions

`Langlands.CommutativeAlgebra.IntegralFibre.SMulInjOn R u X`: for an `R`-algebra `S`, an element
`u : S` and an `R`-module `X`, multiplication by `u` on `S ⊗[R] X` is injective.

## Statements

All statements assume `S` is flat over `R`, except where stated otherwise.

- `lTensor_smul_comm`: `f.lTensor S` commutes with multiplication by `u`. No flatness is needed.
- `SMulInjOn.of_subsingleton` and `SMulInjOn.of_linearEquiv`: the property holds for subsingleton
  modules and transfers along linear equivalences. No flatness is needed.
- `SMulInjOn.of_injective`: the property passes to submodules, that is, along injective linear
  maps.
- `SMulInjOn.of_exact`: the property is closed under extensions `0 → X → Y → Z → 0`.
- `SMulInjOn.prod` and `SMulInjOn.finsupp`: it is closed under binary products and under
  `ι →₀ X`. The latter needs no flatness.
- `SMulInjOn.of_isTorsionBySet_maximalIdeal`: for a prime `p`, an `Rₚ`-module killed by the
  maximal ideal inherits the property from the residue field `p.ResidueField`.
- `SMulInjOn.of_pow_maximalIdeal_smul_eq_zero`: the same holds for `Rₚ`-modules killed by a power
  of the maximal ideal.
- `SMulInjOn.of_coprimary`: the same holds for an `R`-module on which elements outside `p` act
  injectively and which is killed by a power of `p`.
- `SMulInjOn.of_associatedPrimes`: if `R` is Noetherian, `N` is a finite `R`-module, and the
  property holds for `p.ResidueField` for every associated prime `p` of `N`, then it holds for `N`.

## Proofs

Flatness makes `S ⊗[R] -` exact. So the property passes to submodules and extensions by a
diagram chase, and finite products are extensions.

Let `W` be an `Rₚ`-module killed by the maximal ideal. Then `W` is a vector space over the residue
field, hence free (`Module.Free.chooseBasis`). It is therefore isomorphic, as an `R`-module, to a
module `ι →₀ κ(p)`. If `W` is killed by `m^(e+1)`, then the submodule `m^e • ⊤` is killed by `m`
and the quotient is killed by `m^e`, so induction on `e` applies.

A coprimary module `E` embeds into its localization `Eₚ`, because elements outside `p` act
injectively. The localization is an `Rₚ`-module killed by a power of the maximal ideal, since
`m = p Rₚ`.

For the main statement, take a minimal primary decomposition `⊥ = ⋂ Qᵢ` of the zero submodule of
`N` (`Submodule.isLasker`, `IsLasker.exists_isMinimalPrimaryDecomposition`). The radicals of the
`Qᵢ` are associated primes (`IsMinimalPrimaryDecomposition.mem_associatedPrimes`). Each `N ⧸ Qᵢ`
is coprimary in the above sense, and `N` embeds into the finite product of the `N ⧸ Qᵢ`.

## Provenance

This is an internal lemma for the 05FT proof, written by Worker 281. It is a variant of the
statement that associated primes of `M ⊗ S` lie over associated primes of `M` for flat
`R → S`; compare Stacks Tag 05C2.

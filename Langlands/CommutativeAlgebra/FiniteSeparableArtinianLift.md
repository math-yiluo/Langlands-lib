# Finite free local lifts of finite separable residue extensions

Let `R` be a commutative local ring, write `k = IsLocalRing.ResidueField R`,
and let `L/k` be a specified finite separable field extension. The namespace
`Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift` constructs an
actual monic polynomial quotient `B` over `R` whose scalar extension to `k`
is the originally specified `L`. The ring `B` is finite free and faithfully
flat over `R`. If `R` is Artinian, `B` is Artinian local and its maximal
ideal is nilpotent, with the specified field `L` as its actual residue
quotient. All rings lie in one arbitrary universe `u`.

## The lifted quotient and its specified fibre

`model R L` specializes the published
`finiteSeparableLiftedPolynomialModel` to `D = K = k`. Its input
surjection is the original residue map `R → k`. Its
`Carrier R L` is literally `AdjoinRoot (model R L).polynomial`,
with the original `R`-algebra action. The inherited instances give
finite generation and freeness as an `R`-module and finite
presentation as an `R`-algebra.

`fibreEquiv R L` is the model's specified generic equivalence
`k ⊗[R] B ≃ₐ[k] L`. It preserves the given `k` action on `L`.
`toField R L : B →+* L` is tensor inclusion `b ↦ 1 ⊗ b`
followed by this equivalence. The theorem `toField_surjective`
uses surjectivity of `R → k`, hence of tensor inclusion, and
surjectivity of the equivalence.

The coefficient formula `toField_algebraMap` says exactly that
the composite `R → B → L` is the original residue map followed
by the specified `k`-algebra map to `L`. The exact kernel formula
`ker_toField` identifies its kernel with
`(maximalIdeal R).map (algebraMap R B)`: cancel the fibre
equivalence from the composite, then apply the published
`ker_includeRight_quotient` to the actual residue quotient.

The map to the field proves `Nontrivial B`. Combined with
freeness, this gives the `Module.FaithfullyFlat R B` instance.
These constructions and assertions require that `R` is local;
they do not yet require that `R` is Artinian.

## The Artinian local conclusions

For the remaining declarations, assume `IsArtinianRing R`.
`isNilpotent_ker_toField` uses nilpotence of the Jacobson radical
of an Artinian ring, its identification with the maximal ideal
of a local ring, and preservation of ideal powers by ideal
extension to prove that the exact kernel above is nilpotent.

The general helper
`Langlands.CommutativeAlgebra.isLocalHom_of_surjective_nilpotent_ker`
is proved for any surjection of commutative rings with nilpotent
kernel. The first isomorphism theorem identifies the target
with the quotient by that kernel. Units reflect through the
equivalence and then through a quotient by a nilpotent ideal.
This proves that the original surjection reflects units.

Apply that helper to `toField R L`. Its target is a field, so
the domain is local. The theorem `maximalIdeal_eq_ker_toField`
identifies its maximal ideal with the kernel: surjectivity
onto a field makes the kernel maximal, and a local ring has
only one maximal ideal. The theorem
`isNilpotent_maximalIdeal` transfers the preceding ideal
nilpotence to this actual maximal ideal.

Finiteness of `B` as an `R`-module and Artinianness of `R`
give the `IsArtinianRing B` instance. The coefficient formula
also proves that `algebraMap R B` is a local homomorphism:
map any unit to `L`, then reflect it along the field inclusion
`k → L` and the original residue map.

`residueEquiv R L : ResidueField B ≃+* L` is the first
isomorphism theorem for the same actual surjection, with its
kernel replaced by the equal maximal ideal. The evaluation
identity `residueEquiv_residue` proves that the quotient map
followed by this equivalence is precisely `toField R L`.
This is a ring equivalence; no separate algebra structure on
`ResidueField B` over `k` is introduced.

## Provenance and scope

This is an internal specialization of the published actual
monic quotient model and tensor-quotient kernel formula,
combined with standard nilpotence, unit lifting, finite
module and local-ring results. It introduces no additional
literature transcription. The specified residue extension,
the original coefficient map, and the actual tensor fibre
are retained throughout.

The construction supplies the local faithfully flat algebra
needed for nilpotent lifting arguments. It does not yet
transport a group scheme or its splitting presentation
across these ring comparisons, prove infinitesimal
centrality, or prove the reductive fibrewise central-isogeny
criterion.

# Ordinary quotient presentations under nilpotent base reduction

For a commutative ring `R`, an `R`-module `M` and an ideal `I`,
`quotientTensorEquiv` identifies `(R/I) ⊗[R] M` with `M/IM` as
modules over `R/I`. It uses the usual quotient-ring action on `M/IM`.
The underlying map is Mathlib's quotient–tensor comparison; its linearity
over `R/I` follows by extending scalars along the surjection `R → R/I`.
It sends `(r mod I) ⊗ m` to the class of `r m`, and its inverse sends
the class of `m` to `1 ⊗ m`.

`quotientReduction` is the induced `R/I`-linear map `M/IM → N/IN`
for any `R`-linear map `f : M → N`. It sends the class of `m` to the
class of `f m`. `quotientTensorEquiv_natural` states compatibility with
the actual tensor base-change map. No flatness, nilpotence or finiteness
assumptions are required for these constructions.

Let `A → B` be a homomorphism of commutative rings, `I` a nilpotent
ideal of `A`, `J = IB`, and `M` a `B`-module with compatible `A`-action
that is flat over `A`.
`finitePresentation_iff_quotient_smul_of_base_nilpotent` proves that
`M` is finitely presented over `B` if and only if the ordinary quotient
`M/JM` is finitely presented over `B/J`. The forward direction is
finite presentation under tensor base change followed by
`quotientTensorEquiv`. The reverse direction transports finite presentation
back to the tensor reduction and invokes
`finitePresentation_of_base_nilpotent`.

`finiteFreePresentationOfNilpotentQuotient` returns finite ranks `n,m`
and actual `B`-linear maps `B^m → B^n → M`, with the last map
surjective and image equal to kernel, from finite presentation of `M/JM`
over `B/J`. The ranks and maps are chosen, rather than prescribed.
There are no Noetherian, ideal finite-generation or `A`-flatness
assumptions on `B`. Ring and module universes are independent.

This is an internal interface for the previously proved nilpotent
finite-presentation lifting theorem. Its additional argument is the
quotient-ring linearity and transport of finite presentation through an
actual linear equivalence. It supplies module presentation data; the
sheaf deformation and coherent-family atlas constructions remain separate
obligations.

# Diagonalizable Hopf models on principal neighborhoods

This internal module supplies the scheme-theoretic assembly step for Hopf
reconstruction. It does not prove the existence of the local models it uses.
All declarations retain arbitrary universe `u`.

`Langlands.GroupScheme.HopfCoordinates.diagonalizableIsoOfBialgEquiv` constructs
an actual group-scheme isomorphism from the Hopf spectrum of `A` to
`RelativeMultiplicativeType.diagonalizable (Spec R) M`, given a bialgebra
equivalence `A ≃ₐc[R] AddMonoidAlgebra R M`. Here `R` is a commutative ring,
`A` is a commutative Hopf algebra, and `M` is an abelian group. The construction
turns the equivalence into an isomorphism of commutative Hopf algebras, applies
the contravariant Hopf-spectrum functor, uses
`Diagonalizable.hopfSpecIso`, and compares the ring-level diagonalizable group
with the relative model using `Diagonalizable.baseChangeIso`. The accompanying
`isDiagonalizable_of_bialgEquiv` requires `AddGroup.FG M` and inserts this
isomorphism into the definition of relative diagonalizability.

`HopfCoordinates.isMultiplicativeType_of_forall_exists_away` assumes that for
every prime `p` of `R` there is an `f ∉ p` such that the Hopf spectrum of
`Localization.Away f ⊗[R] A` is relatively diagonalizable over
`Spec (Localization.Away f)`. It concludes that the actual Hopf spectrum of
`A` is of multiplicative type over `Spec R`.

The proof chooses one such `f` for each prime and constructs the cover whose
maps are the actual spectrum maps `Spec R_f → Spec R`. Their images are the
principal opens `D(f)`, so the chosen neighborhoods cover: the neighborhood
chosen for `p` contains `p`. Each map is an open immersion, hence flat and
locally of finite presentation. They therefore form the required fppf cover.
`HopfCoordinates.baseChangeSpecIso` identifies the base change of the original
group with the Hopf spectrum of scalar extension on each member, and the given
diagonalizability transports along that actual group-scheme isomorphism.

The provenance is internal: the construction combines the existing Library
Hopf-spectrum and diagonalizable-group comparisons with Mathlib's spectrum of
a principal localization, its image formula, and `Scheme.Cover.mkOfCovers`.
No local-to-neighborhood extension theorem or unproved reconstruction result
is used. In particular, a diagonalizable model only over `R_p` is insufficient
for the premise; a model over some actual principal neighborhood `R_f` is
required.

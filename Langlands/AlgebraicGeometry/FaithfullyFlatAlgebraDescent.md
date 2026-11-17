# Faithfully flat descent of a commutative algebra coaction

For commutative rings `R`, `B`, and `C` in one universe and ring maps
`φ : R →+* B` and `F : B →+* C`, this module gives `C` its composite
`R`-algebra structure. `Coaction φ F` consists of a `B`-algebra map
`C → B ⊗[R] C` satisfying the counit and coassociativity identities of the
published extension/restriction-of-scalars module comonad.

`Coaction.invariants` is the equalizer subalgebra of the coaction and
`c ↦ 1 ⊗ c`. Forgetting multiplication gives `Coaction.coalgebra`; the
invariant algebra has a canonical linear equivalence with that module
coalgebra's coinvariants.

`descentHom` is the actual algebra map from the scalar extension of the
invariants to `C`, with formula `b ⊗ c ↦ F b * c`. When `φ` is faithfully
flat, `bijective_descentHom` identifies its underlying linear map with the
published effective module descent map, composed with the scalar extension
of the invariant/coinvariant equivalence. `descentEquiv` packages this
bijection as a `B`-algebra equivalence with the same pure-tensor formula.

`finite_invariants` and `etale_invariants` transport the corresponding
properties of `F` across this equivalence and apply Mathlib's faithfully
flat descent theorems. `projective_invariants` uses these two results: a
finite algebra of finite presentation is finitely presented as a module,
and an étale algebra is flat, so the invariant module is projective.
No nonzero algebra or constant-rank hypothesis is imposed.

This is an internal derivation from
`FaithfullyFlatCoalgebraDescent.bijective_descentMap` and Mathlib's equalizer
subalgebra, scalar-extension adjunction, and descent of finiteness and
étaleness. It uses no new descent effectivity premise. The module does not
construct a coaction from a scheme atlas or descend group-scheme
isomorphisms.

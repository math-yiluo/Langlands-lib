# Connective finite free charts for perfect module complexes

Let `R` be a commutative ring, `K` a bounded finite projective integer
cochain complex of `R`-modules, and `p` a prime ideal. Assume that every
negative homology module of the ordinary residue-field extension
`κ(p) ⊗[R] K` is zero.

`ModuleComplex.ConnectiveFreeChart K p` records an element `r ∉ p`, a
bounded finite free complex `P` over `Localization.Away r`, the condition
`P.IsStrictlyGE 0`, and an actual homotopy equivalence from `P` to the
ordinary localization of `K`. It also retains, in every degree `i`, a
linear coordinate isomorphism from `P.X i` to the free module whose rank is
`Module.finrank κ(p) (Hⁱ(κ(p) ⊗[R] K))`. These ranks refer to the original
complex `K` and the original prime `p`.

`nonempty_connectiveFreeChart` proves existence of this data.
`connectiveFreeChart K hK p hnegative` chooses it. The proof first applies
the published `primeMinimalPerfect` to obtain a finite free model over the
prime localization with these ranks and an actual homotopy equivalence.
It then applies the published `primeFreeHomotopyDescent`, which descends
the model and its homotopy equivalence to one principal neighborhood while
preserving every rank. The vanishing assumption makes the residue-field
homology modules in negative degrees subsingletons, so their finite ranks
are zero. The retained coordinate isomorphisms consequently make every
negative term of the descended model a zero module. This proves
`P.IsStrictlyGE 0`. `ConnectiveFreeChart.d_neg_one_zero` extracts the zero
incoming differential required for degree-zero matrix coordinates.

This is an internal construction from the two published module-complex
results and Mathlib's finite-rank and zero-object APIs. It needs no
noetherian hypothesis on `R`. The complex `K`, its strict perfection, the
prime, and its negative residue-field homology vanishing are inputs; no
geometric comparison is asserted. The construction does not identify Hom
of sheaves with tensor homology and does not assert a finite linear model
for that Hom presheaf. Transport on scheme slices, assembling the
principal neighborhoods into a scheme cover, and the geometric comparison
remain separate obligations.

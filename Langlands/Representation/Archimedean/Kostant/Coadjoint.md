# Coadjoint derivations and the orbit statement

For `x ∈ ∏ᵢ 𝔤𝔩_{n i}(K)`, `coadDer x` is the derivation of `K[X_c]` that sends `X_c` to
`ξ⁅x, E_c⁆ = ∑_d ⁅x, E_c⁆_d X_d`. By linearity, `coadDer x (ξ y) = ξ⁅x, y⁆` (`coadDer_ξ`), so
`SymbolData.symbol_commutator` applies to it.

`OrbitVanishingStatement` (to be proved) is stated for `K = ℂ`. Let `W` be a space of
polynomials that is stable under `coadDer (E i a b)` for all `a ≠ b`. Suppose every element of
`W` vanishes at the tuple whose blocks have entries `c i p ≠ 0` at the positions `(p, p+1)` and
`0` elsewhere. Then every element of `W` vanishes at every tuple of nilpotent matrices; here a
polynomial is evaluated at a tuple `M` by `X ⟨i, p, q⟩ ↦ M i p q`.

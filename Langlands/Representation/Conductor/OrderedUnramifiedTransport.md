# Transport of Whittaker coinvariants along equivalences

Module `Langlands.Representation.Conductor.OrderedUnramifiedTransport`.

## Purpose

The proof of `OrderedUnramifiedWhittakerRealizationStatement` uses two facts about
the unramified principal series `π`:

- every nonzero subrepresentation of `π` has nonzero Whittaker coinvariants;
- the Whittaker functionals of `π` form a line.

The all-field Bernstein–Zelevinsky results give these facts for a normalized product
`ρ` of rank-one blocks, and only in mirabolic form. `OrderedUnramifiedProductComparison`
gives an equivalence `e : π ≃ ρ`. This module moves both facts along `e`. It is
internal glue: it says only that equivalent representations have isomorphic
coinvariants, and it adds no new mathematics. Everything here holds over any
commutative ring `F` and for any character `θ` of the upper unipotent subgroup.

## Contents

- `mirabolicImage e K`: the image `e(K)` of a subrepresentation `K` of `π`, viewed as a
  subrepresentation of the restriction of `ρ` to the mirabolic subgroup
  `mirabolic n F`. `mirabolicImage_ne_bot`: if `K ≠ ⊥` then `e(K) ≠ ⊥`, because `e` is
  injective.
- `imageEquiv e K`: the linear identification `e(K) ≃ K` given by the inverse of `e`
  restricted to `K`.
- `nontrivial_coinvariants_of_mirabolicImage`: suppose the coinvariants of `e(K)` for
  the mirabolic upper unipotent subgroup and the character
  `θ ∘ Mirabolic.upperUnipotentEquiv` are nonzero. Then the
  `θ`-coinvariants of `K` for the upper unipotent subgroup of `GL_{n+1}(F)` are
  nonzero. The proof applies `transportEquiv` (Character transport of coinvariants)
  to `imageEquiv e K` and the group identification `Mirabolic.upperUnipotentEquiv`.
  Under this identification the upper unipotent elements keep their underlying
  matrices, so the actions agree because `e⁻¹` is an intertwiner.
- `nontrivial_coinvariants_of_equiv e θ hρ K hK`: the hypothesis `hρ` says that every
  nonzero subrepresentation of the mirabolic restriction of `ρ` has nonzero mirabolic
  `θ`-coinvariants. Under `hρ`, every nonzero subrepresentation `K` of `π` has nonzero
  `θ`-coinvariants. This combines the two previous items.
- `coinvariantsEquiv e θ`: `e` induces a linear equivalence between the
  `θ`-coinvariants of `π` and those of `ρ` (`transportEquiv` with the identity
  group isomorphism).
- `finrank_functionals_eq e θ`: the spaces of `θ`-functionals of `π` and `ρ` have the
  same dimension. Both are identified with duals of coinvariants
  (`functionalsLocalizationDualEquiv`), and the duals are identified by the dual map
  of `coinvariantsEquiv`.
- `standardCharacter_scale_neg_one ψ n`: the standard character of the additive
  character `x ↦ ψ(-x)` (`ψ.scale (-1)`) equals `inverseStandardCharacter ψ n`. Both
  send `u` to `ψ(-∑ u_{i,i+1})`. On the circle, inversion is complex conjugation. This
  lets results stated for standard characters apply to the inverse standard character
  of the target statement.

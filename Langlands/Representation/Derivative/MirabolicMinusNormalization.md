# Haar normalization of the actual mirabolic minus functors

Author: Worker 710.

This internal adapter identifies the canonical inverse half of the actual
radical Haar character with the determinant real-power characters used by
`Langlands.Derivative.Mirabolic.psiMinus` and `phiMinus`. It also identifies
the complete functors, including their maps. Its direct imports are
`Langlands.Group.GL.MirabolicModulusProof` and
`Langlands.Representation.Derivative.MirabolicMinus`.

## Generic character identities

For arbitrary groups `G` and `H`, in independent universes, and a positive
character `δ : G →* ℝ≥0ˣ`, the module proves:

- `Jacquet.positiveHalfCharacter_eq_realPowerCharacter`: the complex
  embedding of the canonical positive square root of `δ` equals
  `realPowerCharacter δ (1 / 2 : ℝ)`.
- `Jacquet.inverseHalfCharacter_eq_realPowerCharacter`: the canonical
  inverse half equals `realPowerCharacter δ (-(1 / 2 : ℝ))`.
- `Jacquet.inverseHalfCharacter_comp`: inverse halves commute with pullback
  along every homomorphism `φ : H →* G`.

The first proof uses extensionality of monoid homomorphisms and units,
then Mathlib's `Real.coe_sqrt` and `Real.sqrt_eq_rpow` after unfolding the
character values. The second applies inversion to the first identity and
uses `realPowerCharacter_neg`. The pullback identity is definitional.

## Actual radical Haar characters

Fix any prime `p`, `F : PadicField.{uF} p`, and supplied compatible
topological realization `T : F.TopologicalData`. The module defines:

- `Derivative.Mirabolic.psiMinusHaarInverseHalf T n`, the character
  `HaarModulus.closedInverseHalfCharacter` for the radical of `P_(n+1)`,
  restricted to its standard Levi subgroup and pulled back by `leviEquiv`
  to `GL_n`;
- `Derivative.Mirabolic.phiMinusHaarInverseHalf T n`, the corresponding
  radical character for `P_(n+2)`, restricted to `successorSubgroup n`
  and pulled back by `successorEquiv` to `P_(n+1)`.

Here the Library's `mirabolic n F.Carrier` is `P_(n+1)`; these indices
agree with the actual minus functors. Both definitions use the supplied
`T.topology`, its Hausdorff certificate, its ambient general-linear
local compactness, and the resulting mirabolic local compactness. The
closed-radical wrapper supplies local compactness of the radical itself.
No topology is replaced.

`psiMinusHaarInverseHalf_eq` and `phiMinusHaarInverseHalf_eq` prove that
these characters are respectively `psiMinusCharacter T n` and
`phiMinusCharacter T n`. After unfolding the closed inverse-half wrapper,
the proofs commute inverse half with pullback, apply the published
`GeneralLinear.Mirabolic.leviRadical_haarCharacter` or
`successorRadical_haarCharacter`, and apply the generic negative-half
identity. Thus the normalized characters are `|det|^(-1/2)` on `GL_n`
and its restriction to `P_(n+1)`, respectively. In particular the sign
comes from the proved positive radical Haar character, followed by its
canonical inverse half.

`isOpen_ker_psiMinusHaarInverseHalf` and
`isOpen_ker_phiMinusHaarInverseHalf` transport the published open-kernel
certificates through these character equalities.

## Complete functor comparison

For every representation-carrier universe `uV`, independent of `uF`,
`psiMinus_haarNormalization` states the equality of functors

```lean
psiMinus.{uV} T n = psiMinusUnnormalized T n ⋙
  SmoothRep.twistFunctor (psiMinusHaarInverseHalf T n)
    (isOpen_ker_psiMinusHaarInverseHalf T n)
```

under the supplied field topology. The theorem
`phiMinus_haarNormalization` gives the analogous equality for
`phiMinus T ψ n` and `phiMinusUnnormalized T ψ n`, for every
`ψ : UnitaryAdditiveCharacter` under the supplied topology. This existing
type bundles continuity and nontriviality of the additive character, so
the comparison does not include the trivial character. The proofs simplify the character comparisons
and then use the definitions of the normalized functors. Proof
irrelevance identifies the dependent open-kernel witnesses. These are
functor equalities, so both objects and quotient-induced morphisms agree.
Their carriers remain the actual localized coinvariant quotients of the
published minus constructions.

Every natural rank is allowed, including zero. The comparison requires no
additional nontriviality premise beyond the one bundled in `ψ`; its proof
does not explicitly use that bundled field. No exactness,
admissibility, finite-length or irreducibility hypothesis is used.

## Provenance and dependency boundary

This is an internal derivation from the cited Library constructions and
proved radical Haar-modulus identities, together with Mathlib's real
square-root identity. It asserts no additional original-literature theorem.
The imported radical proof computes the actual Haar character by coordinate
transport and scalar/matrix Haar scaling; the adapter does not identify it
with a determinant by definition.

A recursive audit at Library base
`84ad0affe3e3e8feae73b57da624fc1f16a6923b` found 60 imported `Langlands`
modules, all with Lean and Markdown bytes matching that published tree.
The closure contains no classification or segment module, no consumer
nonadjacent or full-two-factor conclusion, and none of the prohibited
independence conclusions of task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`.
Its only derivative modules are the actual mirabolic character and minus
constructions. No derivative theorem is assumed: this module proves its
normalization comparisons from the radical Haar theorem. The private
closure inventory is an author audit, not independent acceptance evidence.

The module makes no assertion about the modular function of the full
mirabolic group, derivative exactness, detection, highest-derivative
pairings, or product irreducibility. Those remain separate obligations.

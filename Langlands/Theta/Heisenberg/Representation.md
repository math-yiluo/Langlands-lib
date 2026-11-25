# Representations of a Heisenberg group: central character and normalizing operators

**GKT §1.1 and §2.1.1** (the central character of the Heisenberg representation, p. 17; the
relation (2.2), p. 47, which defines the pairs of the metaplectic group of §2.1.2, p. 48).

The module `Langlands.Theta.Heisenberg.Representation` defines the two predicates on
representations of a Heisenberg group on which the metaplectic group and the Weil representations
are stated. It does not depend on any model of the Heisenberg representation.

## Content

For a representation `ρ` of `HeisenbergGroup B` (any commutative ring `R` with `⅟2`, any module
`W`, any bilinear form `B`) on a complex vector space:

- `HasCentralCharacter ρ ψ`: `ρ (central t) = ψ t` for all `t`; then
  `ρ g = ψ g.cen • ρ (ofVec g.vec)` (`HasCentralCharacter.apply_eq`).
- `Normalizes ρ a ω`, for an action `a : G →* MulAut (HeisenbergGroup B)` of a group `G` and a
  representation `ω` of `G` on the same space: `ω g ∘ ρ h = ρ (a g h) ∘ ω g` for all `g`, `h`
  (`Normalizes.apply` on vectors). For `G` a group of isometries of `(W, B)` acting by
  `g · (w, t) = (g w, t)` (GKT (2.1), `HeisenbergGroup.isometryAction`) this is GKT (2.2): `ω g`
  is an operator `M` with `(g, M)` in the metaplectic group `Mp(W)^{ℂˣ}_{ψ,S}`.

## Relation to the source

No text of this file is taken from the source repository
(<https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`). The predicate
`HasCentralCharacter` is the clause `∀ t v, ρ ⟨0, t⟩ v = ψ t • v` of `Heisenberg.IsIrrSmoothOf`
(`PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean`, lines 53–55), and the lemma
`HasCentralCharacter.apply_eq` is the source's `SvN.apply_eq` (same file, lines 523–526).

## Declarations

- `HasCentralCharacter`, `HasCentralCharacter.apply_eq`.
- `Normalizes`, `Normalizes.apply`.

## Dependencies

`Langlands.Theta.Heisenberg.Basic`; Mathlib: `Algebra.Group.AddChar`, `Basic.Complex.Basic`,
`RepresentationTheory.Basic`.

# Artin conductor of an induced finite-Galois representation

Worker 0 states the induction formula for the published rational Artin sums of
actual finite p-adic Galois extensions. The complete target is
`Langlands.Ramification.Padic.FiniteGaloisConductorInductionStatement`; the
component with fixed data is
`Langlands.Ramification.Padic.FiniteGaloisInducedConductorStatement`. Both
declarations are `def`s returning `Prop`. This module states the result; it
does not prove it.

## Fields, towers, and groups

The target quantifies over every prime `p`, every `F : PadicField p` with
supplied `T : F.TopologicalData`, and two fields `K` and `K'`. The scalar
structures describe the tower `Padic p → K → K' → F.Carrier`. The required
compatibilities are `IsScalarTower (Padic p) K F.Carrier`,
`IsScalarTower (Padic p) K' F.Carrier` and `IsScalarTower K K' F.Carrier`. Field
algebra maps are injective, so `K'` is an intermediate field of `F.Carrier / K`
up to isomorphism. The compatibility of `Padic p → K → K'` follows from the
listed towers and that injectivity; it is not a separate hypothesis. Since
`F.Carrier` is finite dimensional over `Padic p`, it is finite dimensional over
`K` and `K'`.

The component quantifies `IsGalois K F.Carrier`. It does not need a separate
Galois hypothesis for `F.Carrier / K'`, which follows from the tower.

Write `G = F.Carrier ≃ₐ[K] F.Carrier` and `H = F.Carrier ≃ₐ[K'] F.Carrier`.
The map `φ` in the statement is `AlgEquiv.restrictScalarsHom K : H →* G`. It
regards a `K'`-automorphism as a `K`-automorphism. It is injective (Mathlib's
`AlgEquiv.restrictScalarsHom_injective`), and its image is the subgroup of `G`
fixing `K'`. This is Serre's subgroup `H` corresponding to `K'`.

The component's body first installs `FiniteDimensional K F.Carrier`, from
`Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier`. This is a
proposition, so the installed instance carries no data. It makes `G` finite, and
then the induced space is finite dimensional. This is needed to apply
`artinConductor` to an induced representation.

The coefficients are `ℂ`. The representation `ψ` of `H` is on an arbitrary
finite-dimensional complex vector space `V`. No irreducibility or positive
dimension is assumed. The universes `uK`, `uK'`, `uL` (of `F`) and `uV` (of `V`)
are independent.

## The induced representation

Induction is Mathlib's `Representation.ind φ ψ`. Its space `IndV φ ψ` is the
`H`-coinvariants of `ℂ[G] ⊗ V`, with `h` acting by left multiplication by
`φ h` on `ℂ[G]` and by `ψ h` on `V`. An element `g` of `G` acts by
`⟦g₁ ⊗ v⟧ ↦ ⟦g₁ g⁻¹ ⊗ v⟧`. Since `φ` is injective, this is the usual induced
representation `Ind_H^G ψ`, of dimension `[G : H] · dim V`. Serre denotes its
character `ψ*`.

The statement also uses `Representation.ind φ (Representation.trivial ℂ H ℂ)`.
This is the representation induced from the one-dimensional trivial
representation `1_H` of `H`, and is the permutation representation of `G` on
`G/H`.

## The conductors and the residue degree

`artinConductor T K` and `artinConductor T K'` are the published rational sums
of `Langlands.LocalFactor.Ramification.Galois`. They use the actual action on
the valuation ring `T.Integers`. For the lower groups `G_i` of `G` and `H_i` of
`H`, both computed from that one ring action,

`a_G(ρ) = Σ_{i≥0} (|G_i| / |G_0|) · (dim ρ − dim ρ^{G_i})`,

`a_H(ψ) = Σ_{i≥0} (|H_i| / |H_0|) · (dim ψ − dim ψ^{H_i})`.

The coefficient `(inertia T K).index / (inertia T K').index`, computed in `ℚ`,
is the residue degree `f_{K'/K}`. The reasoning is as follows. `inertia T K` is
the kernel of the action of `G` on the actual residue field `l` of `F.Carrier`.
The decomposition group of a local field is the whole Galois group. The residue
fields are finite, hence perfect. So `G / G_0` is the Galois group of the
residue extension `l/k` and `[G : G_0] = f_{L/K}`; in the same way,
`[H : H_0] = f_{L/K'}`. Residue degrees multiply in the tower
`K ⊆ K' ⊆ F.Carrier`. So the quotient is the integer `f_{K'/K}`, and division in
`ℚ` is exact.

## The statement

For every `ψ`, the component states

`a_G(Ind_H^G ψ) = (dim V) · a_G(Ind_H^G 1_H) + f_{K'/K} · a_H(ψ)`,

as an equality of rational numbers. The complete target quantifies this
component over all the data listed above.

## Original source and derivation

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979:

- Literature ID: `serre-1979-local-fields`.
- Retained file: `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
- SHA256: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
- Chapter VI, section 2, Proposition 4 and its Corollary, printed pages
  101–102 / PDF pages 108–109: for a character `ψ` of `H` and the induced
  character `ψ*` of `G`,
  `f(ψ*) = v_K(𝔡_{K'/K}) ψ(1) + f_{K'/K} f(ψ)`.
- Chapter VI, section 2, Proposition 2 and Corollary 1', printed pages
  100–101 / PDF pages 107–108: the weighted fixed-space formula that identifies
  Serre's character conductor `f` with the published rational sum.
- Chapter IV, section 1, Propositions 1 and 2, printed page 62 / PDF page 69:
  `G_0` is the inertia group and `G/G_0` is the Galois group of the residue
  extension; for a subgroup `H` with fixed field `K'`, `H_i = G_i ∩ H`.
- Chapter I, section 7, Proposition 20 and the Corollary to Proposition 21,
  printed pages 21–22 / PDF pages 29–30: the decomposition group modulo inertia
  is the Galois group of the residue extension, of order `f` when that extension
  is separable.

These original passages were read for this contribution. Serre's author
errata, *Corrections to J-P. Serre's books* (2019, literature ID
`serre-book-corrections-2019`, Local Fields entries on PDF pages 2–3), list no
correction to these pages.

The statement is derived from the Corollary to Proposition 4. The Library has no
discriminant exponent `v_K(𝔡_{K'/K})` in this finite-Galois framework, so the
statement replaces it by a conductor. The trivial representation `1_H` has zero
conductor, since every fixed-space codimension is zero. The Corollary applied to
`ψ = 1_H` therefore gives `f(Ind_H^G 1_H) = v_K(𝔡_{K'/K})`. Substituting this
into the Corollary for general `ψ`, with `ψ(1) = dim V`, gives the formula
stated here. Thus the statement follows from the Corollary. Conversely, the
statement together with the identity `f(Ind_H^G 1_H) = v_K(𝔡_{K'/K})` gives the
Corollary. This module does not state that identity.

Serre's `f(ψ)` for a character of `H` is computed for `L/K'`, with the
ramification groups of `H`. Here this is `artinConductor T K' ψ`, whose lower
groups are those of `H` acting on the same integer ring. By Serre IV.1
Proposition 2 these groups are `G_i ∩ H`.

## Intended use and scope

If `dim ψ₁ = dim ψ₂`, subtracting the two instances of the formula removes the
term with `Ind_H^G 1_H`:
`a_G(Ind ψ₁) − a_G(Ind ψ₂) = f_{K'/K} (a_H(ψ₁) − a_H(ψ₂))`. This is the
degree-zero induction step in the suggested route of the proof task for
`LocalFactor.ConductorExponent.SpectralConductorStatement` (Task 5626). That
subtraction is explained here but is not a separate declaration.

This module does not state a Swan-conductor version, the discriminant formula
or integrality of `a_G(Ind_H^G 1_H)`. It does not state induction for Weil-group
representations, presentations or virtual classes. It stays in the finite-Galois
setting of the published `Ramification.Galois` module, with complex coefficients.

The pinned environment is `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`,
Lean 4.34.0, Lean commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation and whole-target inspection are distinct from independent
semantic acceptance and current Library publication.

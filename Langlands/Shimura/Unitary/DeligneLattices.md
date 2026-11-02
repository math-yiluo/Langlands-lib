# Character and cocharacter lattices of the Deligne torus

Worker 207.

This module computes the character and cocharacter lattices of the Deligne
torus `S = Res_{ℂ/ℝ} 𝔾_m` after base change to `ℂ`, together with the action
of complex conjugation:

- `X^*(S_ℂ) ≃ ℤ × ℤ` and `X_*(S_ℂ) ≃ ℤ × ℤ`;
- the pairing is the dot product;
- complex conjugation, acting through the Galois representation of
  `Langlands.GroupScheme.Torus.LatticeGalois`, interchanges the two
  coordinates of each lattice;
- the action of complex conjugation on `X^*(S_ℂ)` is not trivial.

## Source

Milne, *Introduction to Shimura varieties*, in Arthur–Ellwood–Kottwitz (eds.),
*Harmonic Analysis, the Trace Formula, and Shimura Varieties* (2005), source ID
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, §2, paragraph
"Hodge structures as representations of S", printed p.282 (PDF p.294):

> Let S be ℂ^× regarded as a torus over ℝ. […] Then S(ℂ) ≈ ℂ^× × ℂ^× with
> complex conjugation acting by the rule (z₁, z₂) ↦ (z̄₂, z̄₁). We fix the
> isomorphism S_ℂ ≅ 𝔾_m × 𝔾_m so that S(ℝ) → S(ℂ) is z ↦ (z, z̄) […]. The
> characters of S_ℂ are the homomorphisms (z₁, z₂) ↦ z₁^p z₂^q, (p, q) ∈ ℤ × ℤ.
> Thus, X^*(S) = ℤ × ℤ with complex conjugation acting as (p, q) ↦ (q, p).

The Lean conventions match Milne's. The published `DeligneTorus.groupScheme`
has points `(QuadraticAlgebra A (-1) 0)ˣ`. The two split coordinates of a
point are its evaluations at the two square roots `i` and `-i` of `-1`, in
that order. On real points `z = a + b i` they give `(z, z̄)`, which is
Milne's normalisation. The character attached to `(p, q)` is
`(z₁, z₂) ↦ z₁^p z₂^q`.

The cocharacter statements are **derived**. Milne states the character
computation only. The cocharacter lattice, the dot-product pairing and the
cocharacter swap follow from the same splitting and are proved here.

## The objects

All objects are over `Spec ℂ`. The base change of the published commutative
group scheme `DeligneTorus.commGroupScheme` along `algebraBaseMap ℝ ℂ` is
denoted by the scoped notation `S_ℂ`, in namespace
`Langlands.Shimura.DeligneTorus`. The notation stands for
`(CommGroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj commGroupScheme`.

`S_ℂ` is a notation rather than an abbreviation for a technical reason: the
statements below then have syntactically the same types as the generic Galois
lemmas they instantiate. With an abbreviation, the kernel spends a very large
time unfolding it inside evaluation maps.

The Galois element is `conjAlgEquiv : ℂ ≃ₐ[ℝ] ℂ`, complex conjugation, with
`conjAlgEquiv_apply : conjAlgEquiv z = conj z`. Mathematically it is Mathlib's
`Complex.conjAe`. It is restated so that its type uses the same instance of
`Algebra ℝ ℂ` as `algebraBaseMap ℝ ℂ`. `Complex.conjAe` carries a different,
definitionally equal, instance path. Mixing the two paths makes kernel
checking of the Galois lemmas very expensive.

`complexBaseMap_eq_algebraBaseMap` records that the published
`complexBaseMap` is `algebraBaseMap ℝ ℂ` (by `rfl`).

## Points and the splitting

- `commPointsEquiv T : (T ⟶ (S_ℂ).X) ≃* Γ(T, 𝒪_T)ˣ × Γ(T, 𝒪_T)ˣ` is the
  published `complexSplitPointsEquiv`. A point goes to its two root
  evaluations. `commPointsEquiv_naturality` gives naturality in the test
  object.
- `splitTorusPairEquiv T` is the coordinate description of points of the
  published split torus `𝔾_m^{Fin 2}`, as pairs of units.
  `splitTorusPairEquiv_naturality` gives its naturality.
  `finTwoMulEquiv : (Fin 2 → M) ≃* M × M` and `pairRestrict` are the
  auxiliary identifications.
- `splitTorusGrpIso : (S_ℂ).toGrp ≅ splitTorus (Spec ℂ) (Fin 2)` is an
  isomorphism of group schemes. It is built with the published
  `isoOfPointModels`, from the two natural point models above.
  `splitTorusIso : S_ℂ ≅ splitTorus.commGroupScheme (Spec ℂ) (Fin 2)` is the
  same isomorphism of commutative group schemes.
- `splitTorusIso_hom_points` and `commPointsEquiv_splitTorusIso_inv` say that
  the splitting sends a point to the family of its two split coordinates,
  and conversely.

## The lattices

- `characterEquiv : characterLattice S_ℂ ≃+ ℤ × ℤ` composes three
  identifications: `characterLattice.congr splitTorusIso`, the published
  `splitTorus.characterLatticeEquiv`, and `Fin 2 → ℤ ≃ ℤ × ℤ`.
  `characterEquiv_symm_eq` unfolds the inverse.
  `characterEquiv_symm_points` says the character attached to `(p, q)` sends
  a point with split coordinates `(z₁, z₂)` to `z₁^p z₂^q`.
- `cocharacterEquiv : cocharacterLattice S_ℂ ≃+ ℤ × ℤ` is built the same way.
  `cocharacterEquiv_symm_points` says the cocharacter attached to `(m, n)`
  sends a unit `s` to the point with split coordinates `(s^m, s^n)`.
- `latticePairing_eq`: `⟨χ, ν⟩ = p m + q n` when `χ ↦ (p, q)` and
  `ν ↦ (m, n)`. Here `latticePairing` is the published pairing
  (`χ ∘ ν ∈ End(𝔾_m) = ℤ`).

## Complex conjugation

These lemmas compute the action of complex conjugation.

- `complexPointsEquiv_descentPoint`: changing the `ℂ`-structure of a test
  scheme by conjugation does not change the underlying real point. So it
  does not change its quadratic coordinates.
- `algebraMap_conj`: after the change, the `ℂ`-algebra structure of
  `Γ(T, 𝒪_T)` is the old one composed with conjugation.
- `splitPointsEquiv_of_conj`: twisting a `ℂ`-algebra structure by
  conjugation swaps the two root evaluations of a quadratic unit, because
  `i ↦ -i`.
- `commPointsEquiv_descentPoint`: combining the three, the same real point,
  seen with the conjugated `ℂ`-structure, has its split coordinates swapped.

The Galois statements use `characterLattice.galoisRepresentation ℝ ℂ
commGroupScheme` and `cocharacterLattice.galoisRepresentation ℝ ℂ
commGroupScheme` from `LatticeGalois`, at `conjAlgEquiv`.

- `galoisRepresentation_conj_points` specialises the generic point formula.
  `characterEquiv_symm_descentPoint_aux` and
  `characterEquiv_symm_descentPoint` evaluate the character attached to
  `(p, q)` at a conjugated point.
- `galoisRepresentation_conj_characterEquiv_symm`: conjugation sends the
  character attached to `(p, q)` to the one attached to `(q, p)`.
- `characterEquiv_galoisRepresentation_conj`: for every
  `χ ∈ X^*(S_ℂ)`, `characterEquiv (conj · χ) = (characterEquiv χ).swap`.
  This is Milne's "complex conjugation acting as (p, q) ↦ (q, p)".
- `commPointsEquiv_cocharacterEquiv_symm_conj` and
  `galoisRepresentation_conj_cocharacterEquiv_symm`: conjugation sends the
  cocharacter attached to `(m, n)` to the one attached to `(n, m)`.
- `cocharacterEquiv_galoisRepresentation_conj`: for every
  `ν ∈ X_*(S_ℂ)`, `cocharacterEquiv (conj · ν) = (cocharacterEquiv ν).swap`.
- `characterLattice_galoisRepresentation_conj_ne_one`: complex conjugation
  acts nontrivially on `X^*(S_ℂ)`, since it moves `(1, 0)` to `(0, 1)`.

## Scope

The module covers only `S` over `ℝ` and the extension `ℂ / ℝ`, and it
computes the action of `conjAlgEquiv` only. Mathematically `ℂ ≃ₐ[ℝ] ℂ` is
`{1, conj}`, and the identity acts trivially by `map_one` of a
representation. That the group has no other elements is not formalized
here. The Hodge-theoretic interpretation in
Milne (representations of `S` and Hodge structures) is not formalized here.

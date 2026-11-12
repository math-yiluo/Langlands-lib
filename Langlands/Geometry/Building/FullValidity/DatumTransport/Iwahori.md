# Axiom 4.1.16 under based group isomorphisms

Module `Langlands.Geometry.Building.FullValidity.DatumTransport.Iwahori`.

## Purpose and provenance

Internal infrastructure for `KPBuildingDatumTransportStatement`: KP Axiom 4.1.16 (the Iwahori
decomposition, `HasIwahoriDecomposition`) for parahoric building data `P` on `G` gives the same
axiom for `P' = P.basedTransport σ f h` on `H`. Here `f : G ≅ H`, `σ : S ≅ S'` and `j : S' → H`
with `P.i ≫ f = σ ≫ j`. The source does not state this transport; it is the usual invariance of
the axiom under isomorphism. Every group in the axiom is defined from `G`, `S`, `i`, the
building and the apartment, and `f`, `σ`, the building comparison `Φ = basedBuildingEquiv` and
the apartment comparison `A = basedApartmentEquiv` (module `DatumTransport.Building`) carry each
of these to the corresponding object for `P'`. The affine root groups are compared with the
Library lemma `CrossTorusAffineRoots.mem_affineRootGroup_transport_iff`, and the unipotent
radicals with `Dynamic.unipotent_eq_comap_of_iso`.

The declarations below, except the final theorem, are in the namespace
`Langlands.Geometry.Building.IwahoriTransport`.

## Contents

General facts.

- `injective_iff_and_range_eq_of_intertwined`: if `q ∘ e = φ ∘ p` for bijections `e` and `φ`,
  then `q` is injective exactly when `p` is, and `range q = φ(range p)`.
- `subgroupMapEquiv`, `subgroupMapEquiv_apply`: the bijection `L ≃ L'` given by `f` when
  `f(L) = L'`, for subgroups of rational points.

Stabilizers and unipotent radicals.

- `image_smul`: `Φ(g · Y) = f(g) · Φ(Y)`.
- `apartmentMap_image_basedApartmentEquiv`: the image of `A(Ω)` in `B(H)` is `Φ` of the image
  of `Ω` in `B(G)`.
- `map_zeroStabilizer`: `f(G(F)^0_Y) = H(F)^0_{Φ(Y)}`.
- `map_unipotentPoints`: `f(U(ν)(F)) = U(σ ∘ ν)(F)` for the Dynamic unipotent radicals of
  `ν ≫ i` and `(σ ∘ ν) ≫ j`.
- `map_zeroStabilizerUnipotentPoints`:
  `f(U(ν)(F) ∩ G(F)^0_Y) = U(σ ∘ ν)(F) ∩ H(F)^0_{Φ(Y)}`.
- `zeroStabilizerProduct_basedTransport`: the product map `(u, z, v) ↦ u z v` for `P'` at
  `Φ(Y)` and `σ ∘ ν` is injective exactly when the product map for `P` at `Y` and `ν` is, and
  its range is the `f`-image of the range for `P`.

Roots and affine functionals.

- `mem_indivisibleRoots_iff`: `σ(a)` is a non-divisible root of `j` exactly when `a` is a
  non-divisible root of `i`.
- `mem_indivisiblePositiveRoots_iff`, `image_indivisiblePositiveRoots`: the same for the
  non-divisible roots positive on `ν` and on `σ ∘ ν`.
- `functionalEquiv`, `functionalEquiv_apply_basedApartmentEquiv`: the linear equivalence
  `ψ ↦ ψ ∘ A⁻¹` between affine functionals on the two apartments.
- `isLeastNonnegativeFunctional_iff`: `ψ ∘ A⁻¹` is the least affine functional with derivative
  the transported root that is non-negative on `A(Ω)` exactly when `ψ` is the least one for the
  root and `Ω`.
- `mem_affineRootGroup_iff`, `mem_affineRootGroup_iff_of_eq`: `f(g) ∈ U_{ψ ∘ A⁻¹}` for the
  transported root exactly when `g ∈ U_ψ`.

The axiom.

- `isOrderedRootProductBijective`: the ordered-product clause at `Ca` and `ν` gives the clause
  at `A(Ca)` and `σ ∘ ν`. Given functionals `ψ'` and an enumeration `a'` of roots for `P'`, the
  proof applies the clause for `P` to `a_k = σ⁻¹(a'_k)` and `ψ_a = ψ'_{σ(a)} ∘ A`, and moves
  the factors along `f`.
- `isIwahoriDecompositionAt`: `P.IsIwahoriDecompositionAt Ca ν` gives
  `P'.IsIwahoriDecompositionAt (A(Ca)) (σ ∘ ν)`. Both ordered-product clauses use
  `isOrderedRootProductBijective`, the second at `-ν`.
- `ParahoricBuildingData.HasIwahoriDecomposition.basedTransport (hP) (σ) (f) (h)`:
  `P.HasIwahoriDecomposition` gives `(P.basedTransport σ f h).HasIwahoriDecomposition`. Every
  chamber of the transported apartment is `A(Ca)` for a chamber `Ca` of `A(S)`, because `A`
  carries the affine roots of `P` onto those of `P'` (`transportedRoots_basedApartmentEquiv`).
  Every generic cocharacter of `S'` is `σ ∘ ν` for a generic cocharacter `ν` of `S`.

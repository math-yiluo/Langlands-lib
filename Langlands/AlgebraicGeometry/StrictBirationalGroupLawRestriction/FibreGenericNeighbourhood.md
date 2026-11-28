# Open subsets containing the generic points of nearby fibres

The module
`Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGenericNeighbourhood`
proves the scheme form of
`Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.exists_notMem_forall_minimal_mem`.
It is a derived result used in the Library's proof
`Langlands.AlgebraicGeometry.strictBirationalGroupLawRestriction` of Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), §5.2 Proposition 2 (printed p. 115). There it replaces the
constructibility of the set `T₁` of BLR's proof (printed p. 116; BLR 2.5/1, EGA IV 9.5.3), of which
it gives the needed local consequence near a point outside `T₁`.

## `exists_open_forall_isFibreGeneric_mem`

```lean
theorem exists_open_forall_isFibreGeneric_mem (g : Y ⟶ X) [Smooth g] [QuasiCompact g]
    [IsLocallyNoetherian X] (Z : Set Y) (hZ : IsOpen Z) (ξ : X)
    (hξ : ∀ q : Y, g q = ξ → IsFibreGeneric g q → q ∈ Z) :
    ∃ N : Set X, IsOpen N ∧ ξ ∈ N ∧
      ∀ x ∈ N, ξ ⤳ x → ∀ q : Y, g q = x → IsFibreGeneric g q → q ∈ Z
```

Let `g : Y ⟶ X` be smooth and quasi-compact with `X` locally noetherian, let `Z` be open in `Y`,
and let `ξ` be a point of `X` such that `Z` contains the generic points of the irreducible
components of the fibre `g⁻¹(ξ)` (`IsFibreGeneric`, module
`Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGeneric`). Then there is
an open neighbourhood `N` of `ξ` such that, for every specialization `x` of `ξ` in `N`, `Z`
contains the generic points of the irreducible components of `g⁻¹(x)`.

Only specializations of `ξ` are claimed. In the application `ξ` is the generic point of an
irreducible component of a fibre of `X ⟶ Spec R`, and the points of that fibre near `ξ` are its
specializations.

## Proof

Choose an affine open `U ∋ ξ` with ring `A = Γ(X, U)`, noetherian since `X` is locally
noetherian. As `g` is quasi-compact, `g⁻¹(U)` is compact and is covered by finitely many affine
opens `W ⊆ g⁻¹(U)`. For each such `W`, with ring `T = Γ(Y, W)`, the ring map
`g.appLE U W : A ⟶ T` is smooth (`HasRingHomProperty.appLE` for `Smooth`), and
`IsAffineOpen.SpecMap_appLE_fromSpec` identifies `g` on points of `W` with the map
`Spec T ⟶ Spec A` composed with the open immersions `fromSpec`. Open immersions are open
embeddings, so specialization, fibres and generizations inside `W` correspond to inclusion of
primes, primes with the same contraction, and smaller primes. Hence the hypothesis on `ξ` says
that the open set `fromSpec⁻¹(Z)` contains the primes of `T` minimal over the prime `P` of `ξ`,
and `exists_notMem_forall_minimal_mem` gives `a_W ∉ P`. For `x` in the basic open
`X.basicOpen a_W` with `ξ ⤳ x`, the prime of `x` contains `P` and avoids `a_W`
(`IsAffineOpen.fromSpec_preimage_basicOpen`), so the generic points of `g⁻¹(x)` lying in `W` lie
in `Z`. The neighbourhood is `N = U ∩ ⋂_W X.basicOpen a_W` over the finite cover; every point of
`Y` over a point of `U` lies in one of the `W`.

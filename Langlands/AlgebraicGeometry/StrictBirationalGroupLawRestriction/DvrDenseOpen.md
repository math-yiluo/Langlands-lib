# Dense open subschemes from neighbourhoods of fibre generic points over a DVR

The module `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.DvrDenseOpen` proves
the step of the Library's proof `Langlands.AlgebraicGeometry.strictBirationalGroupLawRestriction`
that uses the discrete valuation ring. It corresponds to the sentence of Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), proof of §5.2 Proposition 2 (printed p. 116): "the closure of
`T₁` cannot be dense in any fibre of `X` if `S` consists of a discrete valuation ring".

## `exists_opens_of_forall_fibreGeneric`

```lean
theorem exists_opens_of_forall_fibreGeneric (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    [QuasiCompact f] [LocallyOfFiniteType f] (G : X → Prop)
    (hN : ∀ ξ ∈ fibreGenericPoints f,
      ∃ N : Set X, IsOpen N ∧ ξ ∈ N ∧ ∀ x ∈ N, ξ ⤳ x → G x) :
    ∃ X' : X.Opens, fibreGenericPoints f ⊆ X' ∧ ∀ x ∈ X', G x
```

Let `X` be smooth, quasi-compact and locally of finite type over a discrete valuation ring `R`
and `G` a property of points of `X`. Suppose every generic point `ξ` of an irreducible component
of a fibre of `f` has an open neighbourhood `N` such that `G` holds at every specialization of
`ξ` in `N`. Then `G` holds on an open subset `X'` of `X` containing all these generic points,
that is, on an `R`-dense open subscheme (`fibreGenericPoints_subset_iff`).

## Proof

The set `F = fibreGenericPoints f` is finite (`finite_fibreGenericPoints`, the base having two
points by `SmoothDvrFibreGenericPoints.finite_base`), and `X` is a noetherian space.

1. For `ξ ∈ F` let `O ξ` be `N ξ` minus the closures of the points `ξ' ∈ F` with `ξ'` not
   specializing to `ξ`, a finite union of closed sets. It is an open neighbourhood of `ξ`, and
   every `x ∈ O ξ` in the fibre of `ξ` satisfies `G`: the Library's
   `exists_fibreGenericPoint_specializes` gives `ξ'' ∈ F` in that fibre with `ξ'' ⤳ x`; then
   `ξ'' ⤳ ξ`, and `ξ'' = ξ` because `ξ` has no proper generization in its fibre.
2. Every point of `Spec R` is the generic point `η` or the closed point `s₀`
   (`SmoothDvrAffineOpenGeometry.point_eq_generic_or_closed`), and `η ≠ s₀`. Let `O_s` and `O_η`
   be the unions of the `O ξ` over `ξ ∈ F` in the special and in the generic fibre. Put
   `C₁ = f⁻¹(s₀) \ O_s`, closed in `X`, and `E = (X \ f⁻¹(s₀)) \ O_η`, the points over `η`
   outside `O_η`, and let
   `X' = X \ (C₁ ∪ closure E)`.
3. `G` holds on `X'`: a point of `X'` over `s₀` lies in `O_s`, and a point over `η` lies in
   `O_η`, hence in some `O ξ` with `ξ` in the same fibre.
4. `F ⊆ X'`. A point `ξ ∈ F` over `η` lies in the open `O_η`, which misses `closure E`. Let
   `ξ ∈ F` lie over `s₀`; it lies in `O_s`, so it is not in `C₁`. Suppose `ξ ∈ closure E`. The
   set `E` is constructible (an open set minus an open set in a noetherian space), so by
   `exists_specializes_of_mem_closure_of_isConstructible` (module
   `Langlands.AlgebraicGeometry.ConstructibleGenerizations`) some `e ∈ E` specializes to `ξ`;
   it lies over `η`. The stalk of `X` at `ξ` is a discrete valuation ring
   (`Smooth.isDiscreteValuationRing_stalk_of_forall_specializes`). The generizations of `ξ`
   are the points of `Spec 𝒪_{X,ξ}` (`Scheme.range_fromSpecStalk`, with `fromSpecStalk` an
   embedding); `e ≠ ξ` corresponds to the zero ideal, so every generization of `e` equals
   `e`. Thus `e` is generic in its fibre, `e ∈ F` lies over `η`, and `e ∈ O e ⊆ O_η`,
   contradicting `e ∈ E`.

## Declarations used

From the Library: `fibreGenericPoints`, `finite_fibreGenericPoints`,
`exists_fibreGenericPoint_specializes`, `SmoothDvrFibreGenericPoints.finite_base`,
`SmoothDvrAffineOpenGeometry.point_eq_generic_or_closed`,
`exists_specializes_of_mem_closure_of_isConstructible`,
`AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes` and
`StrictBirationalGroupLawRestriction.mem_fibreGenericPoints_iff`.

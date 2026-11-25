# Invariants of a representation and of its dual, and homomorphisms to and from a line

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/DualDimension.lean`, namespace `Langlands.GaloisCohomology`.

Let `G` be a finite group whose order is invertible in the field `k`, and `V` a finite-dimensional
representation of `G`. The averaging projection of the dual `V*` is the transpose of the averaging
projection of `V`, so the invariants of `V` and of `V*` have the same dimension
(`finrank_invariants_dual`).

For a representation `T` of dimension one and any representation `A` of an arbitrary group, the
composition `Hom(A, T) × Hom(T, A) → End(T) = k` is a perfect invariant pairing
(`homLineDualEquiv`); with the first part, `Hom_G(A, T)` and `Hom_G(T, A)` have the same dimension
when `G` is finite of invertible order (`finrank_invariants_linHom_line`). In the global Euler
characteristic this compares `H⁰(G, M') = Hom_G(M, μ_ℓ)` with `Hom_G(μ_ℓ, M)`.

```lean
theorem finrank_invariants_dual (ρ : Representation k G V) :
    finrank k (dual ρ).invariants = finrank k ρ.invariants
theorem finrank_invariants_linHom_line (hT1 : finrank k T = 1) :
    finrank k (linHom ρA ρT).invariants = finrank k (linHom ρT ρA).invariants
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.finrank_invariants_dual : ∀ {k : Type u} [inst : Field k] {G : Type v} [inst_1 : Group G]
  [inst_2 : Fintype G] [Invertible ↑(Fintype.card G)] {V : Type w} [inst_4 : AddCommGroup V] [inst_5 : Module k V]
  (ρ : Representation k G V), Module.finrank k ↥ρ.dual.invariants = Module.finrank k ↥ρ.invariants
@Langlands.GaloisCohomology.finrank_invariants_linHom_line : ∀ {k : Type u} [inst : Field k] {G : Type v}
  [inst_1 : Group G] {T : Type w} [inst_2 : AddCommGroup T] [inst_3 : Module k T] {A : Type w} [inst_4 : AddCommGroup A]
  [inst_5 : Module k A] (ρT : Representation k G T) (ρA : Representation k G A) [inst_6 : Fintype G]
  [Invertible ↑(Fintype.card G)] [FiniteDimensional k A] [FiniteDimensional k T],
  Module.finrank k T = 1 → Module.finrank k ↥(ρA.linHom ρT).invariants = Module.finrank k ↥(ρT.linHom ρA).invariants
```

## Outline of the proofs

For `Γ` of order prime to `ℓ`, averaging is a projection onto the invariants, and duality `N ↦ N^∨` preserves the dimension of invariants; a one-dimensional `T` gives `Hom(T, M) ≅ M ⊗ T^∨`, whence the dimension formulas used for the local and global dual terms.

- `finrank_invariants_dual`: **Invariants of the dual.** For `#G` invertible in `k`, `dim (V*)^G = dim V^G`.
- `finrank_invariants_linHom_line`: **Homomorphisms to and from a line.** For a finite group `G` of order invertible in `k`, a representation `T` of dimension one and a finite-dimensional representation `A`: `dim Hom_G(A, T) = dim Hom_G(T, A)`.

## Declarations

`averageMap_dual`, `finrank_invariants_dual`, `homLinePairing`, `homLinePairing_apply`, `homLinePairing_injective`, `homLinePairing_comm`, `finrank_invariants_eq_of_linearEquiv`, `finrank_invariants_linHom_line`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 508 (the dual M^∨ = Hom(M, F_p) in the claim).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/OrbitInvariants.lean` lines 1–331. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cohomology API replaces the source's: `map φ f n`, `coeffMap`, `res`, `IsSmoothRep` for the source's `cohomologyMapAlong`, `cohomologyMap`, `cohomologyRes`, `IsDiscreteRep`; `G_S`, its localizations and the open subgroups `G_S(L)` are the Library's `GaloisGroupUnramifiedOutside`, `localizationHom`, `realLocalizationHom`, `fixingOpenSubgroup` in place of the source's `galUnramifiedOutside`, `gsFinFamily`, `gsRealFamily`, `gsOpenSubgroup` (over `FiniteSubfield`s of `ℚ̄`).

Renamings (source → Library): `finrank_dual_invariants` → `finrank_invariants_dual`, `dualLineMap` → `homLinePairing`, `dualLineMap_comm` → `homLinePairing_comm`, `dualLineMap_injective` → `homLinePairing_injective`, `finrank_invariants_dualRep_comp` → `finrank_invariants_linHom_line`.

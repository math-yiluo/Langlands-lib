# Lifting through a `μ_2` kernel after a totally complex quadratic extension

Module: `Langlands.GroupScheme.Rational.CentralQuadraticSplittingLift`,
namespace `Langlands.GroupScheme`.

Let `f : G ⟶ H` be a central isogeny over a number field `F` whose kernel is `μ_2`,
and let `ξ` be a natural cocycle of `H` on a finite Galois cover `Spec L → Spec F`
with central lift data `d : hf.GaloisLift ξ` (module `CentralIsogeny/GaloisCocycleLifting`).
The kernel defect of `d`, read through the character of `μ_2`, determines a class in
the relative Brauer group of `L/F` killed by `2`. There is a totally complex quadratic
extension `E` of `F` over which this class vanishes, and after a further finite Galois
refinement over `E` the scalar extension of `ξ` lifts to a cocycle of `G_E`. The
refinement is needed: vanishing of the unit-valued class alone does not give a lift
on the same cover, since its primitive need not take values in `μ_2`.

## Declarations

- `IsCentralIsogeny.scalarExtensionKernelPointsEquiv_smul`: the comparison
  `scalarExtensionKernelPointsEquiv` of kernel points of the base-changed isogeny over
  `Spec M → Spec K` with kernel points of `f` over `M` carries the action of
  `σ : M ≃ₐ[K] M` (precomposition with `GaloisCocycle.arrow K M σ`) to
  `GaloisPoint.relativeConjugate F K M (kernel f) σ`.
- `isMulCoboundary₂_of_relativeRestriction_relativeInflation_eq_zero`: for a
  unit-valued two-cocycle `c` of a finite Galois extension `L/F` and fields
  `F ⊆ E ⊆ M`, `L ⊆ M`, if
  `relativeRestriction F E M 2 (relativeInflation F L M 2 (relativeUnitsClass₂ c hc)) = 0`
  then `(σ, τ) ↦ c(σ|_L, τ|_L)`, taken in `Mˣ`, is a multiplicative coboundary on
  `Gal(M/E)`.
- `two_nsmul_relativeUnitsClass₂`: if every value of `c` has square `1`, then
  `2 • relativeUnitsClass₂ c hc = 0`.
- `IsCentralIsogeny.exists_quadratic_isComplex_lift_of_galoisLift`: for a number
  field `F : Type u`, a finite Galois extension `L/F`, `hf : IsCentralIsogeny f`,
  `e : kernel f ≅ splitRootsOfUnityProduct F (fun _ : PUnit.{u + 1} => 2)` and
  `d : hf.GaloisLift ξ`, there are `E : IntermediateField F (SeparableClosure F)` with
  `Module.finrank F E = 2` and every infinite place of `E` complex, a finite Galois
  extension `N/E` with compatible `F`- and `L`-algebra structures, and
  `ζ : Cocycle ((baseChange (Spec.algebraMap F E)).obj G) (GaloisCocycle.cover E N)`
  with `ζ.map ((baseChange (Spec.algebraMap F E)).map f) =
  GaloisCocycle.scalarExtension (K := E) (M := N) ξ`.

## Proofs

`scalarExtensionKernelPointsEquiv_smul` unfolds the comparison
(`scalarExtensionKernelPointsEquiv_apply`) and applies
`GaloisCocycle.scalarExtensionPointsEquiv_conjugate` to the kernel.

`isMulCoboundary₂_of_relativeRestriction_relativeInflation_eq_zero`: inflation and
restriction are `groupCohomology.map`, which on `H2π` is computed on cocycles
(`H2π_comp_map_apply`); the composite cocycle is `(σ, τ) ↦ c(σ|_L, τ|_L)`, and a
cocycle with zero class is a coboundary (`H2π_eq_zero_iff`, `d₁₂_hom_apply`).

`exists_quadratic_isComplex_lift_of_galoisLift`: let `χ` be the character of the
kernel given by the single coordinate of the split model
(`splitRootsKernelCharacter`) and `c = hf.kernelUnitDefect χ d`; its values are
square roots of unity (`kernelSplitRootsEquiv_val`). The class
`relativeUnitsClass₂ c` is killed by two, so
`GaloisCohomology.exists_quadratic_isComplex_relativeRestriction_eq_zero` (module
`GaloisCohomology/Global/BrauerSequence/QuadraticComplexSplitting`) gives `E` and a
finite Galois `M/E` containing `L` on which the restricted inflated cocycle `u` is a
coboundary. By `rootsOfUnityPrimitiveAfterRefinement_of_units` (over `E`, with
`n = 2`) there are a finite Galois `N/E` containing `M` and `a : Gal(N/E) → Nˣ` with
`a² = 1` whose coboundary is `u` inflated to `N`. Scalar extension of the lift data
(`scalarExtensionGaloisLift`, with defect formula `scalarExtensionGaloisLift_defect`)
gives lift data `d'` for `GaloisCocycle.scalarExtension ξ` over `N/E`. The kernel points
`p(σ)` corresponding to `a(σ)` under `scalarExtensionKernelPointsEquiv` and
`kernelSplitRootsEquiv` form a primitive of the defect of `d'`: this is checked after
the injective map `kernelUnitMap χ ∘ scalarExtensionKernelPointsEquiv`
(`kernelUnitMap_splitRoots_jointly_injective`), using its Galois equivariance (the
first result and `kernelUnitMap_naturality`) and the compatibility
`((σ|_M)|_F)|_L = (σ|_F)|_L` of restrictions. The lifting criterion
`galoisLift_isMulCoboundary₂_iff` for the base-changed isogeny `hf.baseChange` then
produces `ζ`. The structure follows `exists_cocycle_lift_of_mu_kernel_of_galoisLift`
(module `Rational/CentralMuCocycleLift`), with the vanishing of the obstruction
coming from the choice of `E` instead of local triviality.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press,
1994), proof of Proposition 6.16, printed p. 335: a class in `H²(K, μ_2) = Br(K)_2`
becomes trivial over a totally imaginary quadratic extension `L/K`, and the exact
sequence `H¹(L, G₀) → H¹(L, Ḡ₀) → H²(L, Z)` then lifts the adjoint class. The Lean
proof is internal to this Library.

# Naturality of the cup product

`Langlands/Cohomology/Profinite/Cup/Functoriality.lean`, namespace `Langlands.ProfiniteCohomology`.

## Declarations

- `partialProd_comp_monoidHom`: partial products commute with monoid homomorphisms.
- `resTensorHom φ f g`, `resTensorIso φ A B` (restriction commutes with tensor products) and their
  formulas on pure tensors.
- `cohomologyMap_tensorHom_cup`, `cohomologyMap_whiskerRight_cup`: `(f ⊗ g)_*(x ∪ y) = f_*x ∪ g_*y`.
- `map_resTensorHom_cup`: the same along a continuous homomorphism `φ : H →ₜ* G`;
  `cohomologyMap_resTensorIso_res_cup`: restriction is multiplicative.
- `invariantsTensorLinearMap`, `invariantsTensorHom` and their formulas: `A^N ⊗ B^N → (A ⊗ B)^N`;
  `isSmoothRep_quotientToInvariants_tensor`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/CupProducts/Functoriality.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the
source's; maps along homomorphisms take `φ : H →ₜ* G`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4, Proposition (1.4.2), p. 38 (naturality in the
  coefficients), and §5, Proposition (1.5.3)(iii), p. 49 (restriction is multiplicative).

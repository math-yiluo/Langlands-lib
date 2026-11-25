# Cup products with values in a third module

`Langlands/Cohomology/Profinite/Cup/Pairing.lean`, namespace `Langlands.ProfiniteCohomology`.

For a morphism `μ : A ⊗ B ⟶ C`, `cupPairing μ h` is the cup product followed by `μ`.

## Declarations

- `pairingHom β hβ`: an equivariant bilinear map `A × B → C` as a morphism `A ⊗ B ⟶ C`;
  `pairingHom_tmul`.
- `cupPairing μ h : Hᵖ(G, A) →ₗ H^q(G, B) →ₗ Hⁿ(G, C)`, `cupPairing_apply`, `cupPairing_cohomologyπ`,
  `cochainOf_cocycleι_cyclesMap_cupCocycles`, `cochainOf_cocycleι_cyclesMap_pairingHom`: formulas.
- `cupPairing_cohomologyMap`, `cohomologyMap_cupPairing`: naturality; `res_cupPairing`: compatibility
  with restriction.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/CupProducts/Pairing.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the
source's.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4, p. 38 (the cup product with respect to a pairing
  `A × B → C`), and §5, Proposition (1.5.3)(iii), p. 49 (restriction).

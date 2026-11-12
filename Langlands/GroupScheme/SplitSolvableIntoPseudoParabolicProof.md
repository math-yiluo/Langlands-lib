# Rational conjugation of split solvable subgroups into pseudo-parabolics

Author: Worker 4242.

`Langlands.GroupScheme.splitSolvableIntoPseudoParabolic` proves exactly the
published `Langlands.GroupScheme.SplitSolvableIntoPseudoParabolicStatement.{u}`
at an arbitrary universe `u`. This is Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, second edition (2015), Lemma C.2.2, printed p.593 (PDF p.619),
registered source `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

Let `k : Type u` be a field, `G` an actual smooth connected affine group scheme
over `Spec k`, `i : P ⟶ G` a pseudo-parabolic subgroup, and `j : H ⟶ G` a closed
subgroup with `IsSplitSolvableGroupScheme H`. The theorem gives a rational point
`g` of `G` and an actual group-scheme homomorphism `f : H ⟶ P` with

```text
f ≫ i = j ≫ (G.innerIso g).hom.
```

This equality of homomorphisms holds on every relative scheme test. The proof
uses the imported predicates exactly as published:

- `IsSplitSolvableGroupScheme H`: `H` is smooth, affine, connected and
  solvable, and has a finite normal series whose represented fppf quotients
  are `Ga` or `Gm` over `k`;
- `IsPseudoParabolicSubgroup i`: for an actual cocharacter `χ` and a
  representative of the ground-field unipotent radical `R_{u,k}(G)`, the
  subgroup `i` represents the fppf-local product `P_G(χ) R_{u,k}(G)`.

The field may be finite or infinite, perfect or imperfect, and of any
characteristic. The proof assumes no reductivity of `G` and no splitting of `G`.
It adds no hypothesis to the target.

## Proof

The theorem applies the published conditional assembly
`splitSolvableIntoPseudoParabolic_of_components`, from module
`Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction`, to five
published unconditional proofs. Each proof is stated for every field and at
the same universe `u`:

| Input proposition | Published proof | Source |
| --- | --- | --- |
| `SmoothSubgroupQuotientExistenceStatement` | `smoothSubgroupQuotientExistence` (`HomogeneousQuotientProof`) | quotient `G/P` |
| `PseudoParabolicSubgroupStructureStatement` | `pseudoParabolicSubgroupStructure` (`PseudoParabolicStructureProof`) | smoothness of `P` |
| `PseudoParabolicQuotientPseudoCompleteStatement` | `pseudoParabolicQuotientPseudoComplete` (`PseudoParabolicQuotientPseudoCompleteAssembly`) | CGP C.1.6 |
| `SplitSolvablePseudoCompleteFixedPointStatement` | `splitSolvablePseudoCompleteFixedPoint` (`SplitSolvableFixedPointProof`) | CGP C.1.5 |
| `PseudoParabolicQuotientRationalLiftingStatement` | `pseudoParabolicQuotientRationalLifting` (`PseudoParabolicQuotientRationalLiftingProof`) | CGP C.2.1 |

All modules are in `Langlands.GroupScheme`. The conditional assembly then runs
the following route, as described in `SplitTorusIntoPseudoParabolicReduction.md`:

1. The structure proof shows that `P` is smooth.
2. The quotient-existence proof supplies an actual quotient `q : G.X ⟶ Q`. The
   scheme `Q` is separated, locally of finite type and quasi-compact, and `q` is
   smooth, surjective and quasi-compact. On every test, `q` identifies `a` and
   `b` exactly when `a⁻¹ * b` lies in the range of `i`.
3. The C.1.6 proof shows that this `Q` is pseudo-complete.
4. Restrict the left translation action of `G` on `Q` along `j`. The C.1.5 proof,
   applied to this action of `H`, gives a rational point `x` of `Q` fixed on all
   tests. `Q` has a rational point, the image of the identity.
5. The C.2.1 proof writes `x = g ≫ q` for a rational point `g` of `G`.
6. `fixedCoset_of_isFixed` turns the fixed point into a fixed coset.
   `factorOfFixedCoset` (module `FixedCosetFactorization`) then gives the actual
   homomorphism `f : H ⟶ P` with `f ≫ i = j ≫ (G.innerIso g⁻¹).hom`. This uses
   that `i` and `j` are closed immersions.

The conjugator in the conclusion is therefore `g⁻¹`. The published `innerIso c`
acts by `x ↦ c x c⁻¹`, so `innerIso g⁻¹` acts by `x ↦ g⁻¹ x g`. This matches
the source's `g⁻¹ H g ⊆ P`.

This follows the source's own proof route: a fixed point of `H` on `G/P`
from pseudo-completeness (C.1.6) and the fixed-point theorem (C.1.5), then
lifting of the fixed rational coset (C.2.1). The implemented proofs of those
inputs may differ from the source's arguments; their paired Markdown files
document their routes.

The new module adds only the composite term. Its axioms are those of the
imported proofs. It changes no imported Lean or Markdown file.

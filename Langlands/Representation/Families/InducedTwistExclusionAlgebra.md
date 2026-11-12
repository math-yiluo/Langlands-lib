# Exclusion of an isolated exponent from quotients of a filtered representation

Author: Worker 5120.

This internal supporting module contains the representation-theoretic algebra behind the
exclusion half of the induced-twist irreducibility argument. It uses no group-scheme
structure. Its provenance is internal: it combines the published generalized-weight
decomposition of admissible representations (`SplitComponentDecomposition`), the
generalized-eigencharacter restriction lemmas and the finite filtration API.

## Setting

`M` is a group with a topology that is a nonarchimedean group and weakly locally compact.
`ι : A →* M` has central image (`hι`). An *exponent* of a representation `π` of `M` is a
character `χ : A →* ℂˣ` with `IsGeneralizedEigencharacter (π.comp ι) χ`.

## Declarations

Namespace `Langlands.InducedTwistExclusion`.

- `isAdmissible_subrepresentation`, `isSmooth_subrepresentation`: an invariant subspace
  of an admissible (smooth) representation is admissible (smooth), via the published
  `isAdmissible_of_injective` and `Langlands.ProductFactorization.subrepresentationInclusion`
  from `Smooth.Factorization.MultiplicityDefinitions`.
- `exists_mem_generalizedWeightSpace_map_eq`: let `f : π → σ` be an intertwiner from an
  admissible to a smooth representation. If `f x` lies in the generalized `χ`-weight space of
  `σ`, then some `x'` in the generalized `χ`-weight space of `π` has `f x' = f x`. Proof: the
  generalized weight spaces of the admissible `π` span (`generalizedWeightSpace_iSup_eq_top`
  with `admissible_centerFinite`). Write `x = x₁ + x₂` with `x₁` of weight `χ` and `x₂` in the
  span of the other weights. Then `f x₂` lies both in the `χ`-weight space of `σ` and in the
  span of its other weight spaces. These are independent for smooth `σ`
  (`generalizedWeightSpace_independent`), so `f x₂ = 0`.
- `isGeneralizedEigencharacter_of_surjective`: an exponent of a smooth quotient of an
  admissible representation is an exponent of the source.
- `exists_mem_characterSpace_of_mem_generalizedWeightSpace`, `exists_coe_mem_characterSpace`:
  a generalized weight vector, also one of an invariant subspace, lies in one uniform
  character space of the ambient restricted action.
- `mem_castSucc_of_mem_succ`: in an `ObjectRepFiltration`, a uniform `χ`-vector of step `j+1`
  lies in step `j` when the graded piece `j` has no exponent `χ`. It projects to a uniform
  `χ`-vector of the graded piece, which is zero.
- `mem_succ_of_mem_characterSpace`, `eq_zero_of_mem_castSucc`: if every graded piece other
  than `j₀` lacks the exponent `χ`, every uniform `χ`-vector lies in step `j₀+1`. Every uniform
  `χ`-vector of step `j₀` is zero. These follow by downward and upward induction.
- `not_isGeneralizedEigencharacter_of_isolatedGrade`: the main abstract theorem. Let `E` be
  admissible with a finite filtration whose pieces other than `j₀` lack the exponent `χ` and
  whose piece `j₀` is irreducible. Let `σ` be irreducible and smooth with exponent `χ`, and let
  `Φ : E → σ` be nonzero on an invariant subspace `W`. Then a smooth quotient `q : E ↠ τ` that
  kills `W` has no exponent `χ`. Proof:
  1. `Φ` vanishes on step `j₀`. Otherwise `Φ` restricted there is onto the irreducible `σ`.
     The lifting lemma then gives a nonzero uniform `χ`-vector in step `j₀`, contradicting
     `eq_zero_of_mem_castSucc`.
  2. Some `w ∈ W` in step `j₀+1` has `Φ w ≠ 0`. `Φ` restricted to `W` is onto `σ`. Lift a
     nonzero generalized `χ`-vector of `σ` to one of `W`, which lies in step `j₀+1`.
  3. The image of `W ∩ step(j₀+1)` in the irreducible grade `j₀` is nonzero by steps 1 and 2.
     So it is the whole grade, and every vector of step `j₀+1` is in `W` modulo step `j₀`.
  4. A nonzero generalized `χ`-vector of `τ` lifts to a generalized `χ`-vector `v` of `E`, and
     `v` lies in step `j₀+1`. By step 3, `q v = q u` with `u` in step `j₀`. Lifting again
     inside step `j₀` gives a uniform `χ`-vector there with the same nonzero image. It is
     zero by `eq_zero_of_mem_castSucc`, a contradiction.

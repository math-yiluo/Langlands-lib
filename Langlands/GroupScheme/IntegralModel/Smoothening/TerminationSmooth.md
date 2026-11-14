# Termination of the smoothening sequence: torsion-free cotangent module implies smooth

Author: Worker 348. Internal helper module for the final step of Kaletha–Prasad, Theorem A.6.2
("Lemma S"). Let `R` be a discrete valuation ring with fraction field `K` and algebraically closed
residue field `k`. Let `C` be a flat, finitely generated, commutative Hopf algebra over `R` whose
generic fibre is formally smooth and whose cotangent module `T = I / I²` at the counit is
torsion-free. Then `C` is smooth over `R`. The proof is internal to this project and uses no
dimension theory.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

The generic fibre is given abstractly by:
- a `K`-algebra `E` with an injective `R`-algebra map `ι : C → E`;
- `hloc`: every `e ∈ E` has `s e ∈ ι(C)` for some `s ≠ 0` in `R`;
- a `K`-point `eE` of `E` extending the counit: `eE (ι c) = ε(c)` in `K` (`heE`).

## Cotangent modules

- `mem_sq_of_dif_eq_zero`: `y ∈ I` with `d y = 0` lies in `I²`.
- `mem_sq_of_smul_mem_sq`: if `T` is torsion-free, `s ≠ 0`, `c ∈ I` and `s c ∈ I²`, then
  `c ∈ I²`.

## The generic fibre

- `satSq ε ι hloc` is the ideal of `e ∈ E` with `s e ∈ ι(I²)` for some `s ≠ 0`.
  - `mem_augIdeal_of_smul_eq` and `sq_le_satSq`: the square of the augmentation ideal of `eE` lies
    in `satSq`.
  - `exists_smul_mem_sq`: hence `ι c ∈ I_E²` implies `s c ∈ I²` for some `s ≠ 0`.
- `linearIndependent_dif_generic`: if the differentials `d x_i` are `R`-independent in `T` and `T`
  is torsion-free, then the differentials of the `ι x_i` are `K`-independent in `Cot eE`. Clear
  denominators and apply `exists_smul_mem_sq` and torsion-freeness.
- `eq_zero_of_isHomogeneous` (**graded independence over `R`**): let `E` be formally smooth over
  the infinite field `K`. If `Q` is homogeneous of degree `n` with `aeval x Q ∈ I^(n+1)`, then
  `Q = 0`. Map `Q` to `E` and apply `coeff_eq_zero_of_formallySmooth` (`TerminationPsi`). Then use
  injectivity of `R → K`.
- `genericLift ι : K ⊗[R] C →ₐ[K] E` is induced by `ι`. `genericLift_bijective`: it is bijective.
  Injectivity uses `exists_smul_eq_one_tmul`; surjectivity uses `hloc`.

## The special fibre

- `infinite_of_isDiscreteValuationRing`: the fraction field of a discrete valuation ring is
  infinite.
- `isReduced_special_fibre`: under the hypotheses above, with `C` finitely generated, `k ⊗[R] C` is
  reduced.

  Proof:
  - `T` is finitely generated (`cot_finite`) and torsion-free over the principal ideal domain `R`,
    hence free. Choose `x i ∈ I` whose differentials form a basis.
  - Then the `x i` span `I` modulo `I²`, and graded independence holds by
    `eq_zero_of_isHomogeneous`.
  - Let `f = 1 ⊗ c` with `f² = 0`. Then `c² ∈ ϖ C`, so `c ∈ I^j + ϖ C` for every `j`
    (`mem_sup_of_sq_mem`, `TerminationGraded`).
  - Hence `f` lies in every power of the augmentation ideal of `k ⊗ C`, which contains the image
    of `I` (`counit_eq_evPt`).
  - `isReduced_of_forall_sq_eq_zero` (`TerminationTranslate`) concludes.
- `smooth_of_torsion_eq_bot` (**Lemma S**): with `C` also flat, `C` is smooth over `R`.
  - The special fibre is a reduced, finitely generated Hopf algebra over the algebraically closed
    field `k`, so it is smooth (Worker 50's `smooth_of_isReduced_of_isAlgClosed`).
  - The generic fibre `K ⊗ C ≅ E` is formally smooth.
  - The fibrewise criterion `smooth_of_smooth_fibres` (Worker 50) concludes.

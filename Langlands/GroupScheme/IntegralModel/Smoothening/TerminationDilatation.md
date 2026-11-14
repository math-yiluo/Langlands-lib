# Termination of the smoothening sequence: cotangent modules of dilatations

Author: Worker 348. Internal helper module for Kaletha–Prasad, Theorem A.6.2. It computes how the
cotangent module `I/I²` at a rational point changes under the dilatation `C[J/ϖ]`. It uses only
Mathlib (`Ideal.Cotangent`, `Algebra.adjoin`) and `TerminationLength`.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

## Augmented algebras

For an `R`-algebra `C` with an `R`-algebra map `ε : C → R`:
- `augIdeal ε = ker ε` and `Cot ε = (augIdeal ε).Cotangent`;
- `dif ε : C →ₗ[R] Cot ε`, `y ↦ [y - ε y]`, with `dif_mul` (derivation rule
  `d(yy') = ε y • dy' + ε y' • dy`), `dif_algebraMap`, `dif_of_mem`, `dif_surjective`,
  `dif_eq_zero_of_mem_sq`;
- `cotMap` and `cotMap_dif`: functoriality along point-preserving maps.

## Dilatations inside an ambient algebra

`B` is a torsion-free `R`-algebra with a point `εB`. For a subalgebra `C` and an ideal `J` of `C`:
- `divSet ϖ J = {x | ϖ • x ∈ J}` and `dilat ϖ J = Algebra.adjoin R (C ∪ divSet ϖ J)`. This is
  the ring of the dilatation `C[J/ϖ]`, as in Kaletha–Prasad, Definition A.5.1.
- `exists_pow_smul_mem`: every element of `dilat ϖ J` becomes an element of `C` after
  multiplication by a power of `ϖ`.
- `DivData`: elements `z k ∈ J ∩ ker ε` with chosen quotients `ζ k = z k / ϖ` in `B`.
- `DivData.toCot`: the map from the pushout of `Cot C` adjoining `[z k]/ϖ` (see
  `TerminationLength`) to `Cot (dilat ϖ J)`.
- `DivData.toCot_surjective`: suppose there is `g` with unit value such that every `g j`
  (`j ∈ J`) lies in `ϖ C + ∑ z_k C`. Then the map is surjective. The image is shown to contain
  `d y` for all `y` in a subalgebra containing the generators.
- `DivData.ker_toCot_le_torsion`: the kernel is torsion. Elements of `(ker ε_D)²` become
  elements of `(ker ε_C)²` after multiplication by a power of `ϖ` (`exists_mem_sq_of_mem_sq`).
- `DivData.toCot_relation`: a relation `ϖ² g₀ + ϖ ∑ z_k g_k + ∑ z_k z_l g_{kl} = 0` in `C` gives an
  element of the kernel. Dividing by `ϖ²` gives an identity in the dilatation, to which the
  differential is applied.
- `DivData.defect_add_le`: combines these with `DivisionExtension.defect_add_le`.
- `relation_smul` and `exists_relation`: from the generation hypothesis for `J`, a
  quasi-regularity hypothesis (`hQ1`: relations `ϖ b₀ + ∑ z_k b_k = 0` have coefficients in `J` up
  to a unit-valued multiplier) and a hypothesis on `I² ∩ J` (`hQ2`), every `ϖ`-torsion class of
  `I/I²` is the value `ϖ [g₀] + ∑ ε(g_k) [z_k]` of such a relation.

# Termination of the smoothening sequence: the defect drops

Author: Worker 348. Internal helper module for Kaletha–Prasad, Theorem A.6.2. It proves the
defect-drop inequality of the termination argument: the defect of the next member plus the length
of the `ϖ`-torsion of the cotangent module is at most the defect of the current member. The source
does not prove this inequality. KP cite BLR, *Néron Models* §3.3 Prop. 5. The route here is
internal to this project.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

Setting: `R` is a discrete valuation ring with fraction field `K`, `A` is a commutative Hopf
algebra over `R`, and `B = integralFunctions R K A`. `defect R M` is the length of the torsion
submodule of `M`, and `torsionByLength R M ϖ` is the length of its `ϖ`-torsion
(`TerminationLength`).

## Finiteness

- `dilat_fg`: if `C ≤ B` is finitely generated, so is `dilat ϖ (jIdeal C)`. The ideal
  `jIdeal C` is finitely generated (Noetherian), and each generator is `ϖ` times an element of `B`
  (`exists_eq_smul_of_dvd`). So the dilatation is `C` adjoined finitely many elements.
- `chain_fg`: every member `chain R K A ϖ n` of the smoothening sequence is finitely generated,
  provided `A` is.

## Points

- `subPoints K S` is the set of points `point φ ∘ val` of a subalgebra `S ≤ B`, for `R`-points
  `φ` of `A`.
- `lift_comp_val_apply`: the product of two such points on `S ⊗ S` is `pairValue φ ψ` composed with
  `tensorVal`.

## The Hopf-algebra input

`hopf_relations` is stated for an abstract commutative Hopf algebra `C`, finitely generated over
`R` with `k` algebraically closed. Let `Γ` be a set of points containing the counit, closed under
products and under the antipode. Let `ε = counitAlgHom R C` and `J = ptLocus Γ`; these are passed
with equations `hε` and `hJ`. Then there are `c` and elements `z k ∈ J ∩ I` such that:

1. there is `g` with `ε g` a unit and `g J ⊆ ϖ C + ∑ z_k C`;
2. the differentials `d z_k` are independent modulo `ϖ` (`IndepModulo`);
3. every `ϖ`-torsion class `τ` of `Cot ε` has the form `ϖ dg₀ + ∑ ε(g_k) dz_k`, for a relation
   `ϖ² g₀ + ϖ ∑ z_k g_k + ∑ z_k z_l g_{kl} = 0`.

Proof:
- Take a `GoodChoice` (`exists_goodChoice`).
- `C ⧸ J` is smooth over `k` (`smooth_quotient_jbar` with `ker_quotMap`), so `x` is graded
  independent modulo `J` (`gradedIndep_of_formallySmooth`).
- Krull's intersection theorem gives (1) and the generators of `I² ∩ J`
  (`exists_mul_eq_of_mem_J`, `exists_mul_eq_of_mem_sq`).
- The Γ-trick gives the relation hypothesis (`gamma_trick` with the points of `Γ`).
- Duality of the forms `l m` gives (2).
- `exists_relation` (`TerminationDilatation`) gives (3).

## The inequality

`core_step`: let `S ≤ B` contain `A`, be finitely generated, satisfy `hcomul` and be stable under
the antipode. Then

`defect (Cot (dilat ϖ (jIdeal S))) + torsionByLength (Cot S) ϖ ≤ defect (Cot S)`,

where all cotangent modules are taken at the counit of `B` restricted to the subalgebra.

Proof:
- Put the Hopf structure `hopfSub` on `S` and apply `hopf_relations` with `Γ = subPoints K S`.
  The closure properties of `Γ` follow from `lift_point_comp_comul` and `point_comp_antipodeInt`.
  The equation `ptLocus Γ = jIdeal S` is proved pointwise.
- The values of each `z k` at all points lie in `ϖ R`, so `z k = ϖ ζ_k` in `B`. This gives the
  data `DivData`.
- `DivData.defect_add_le` (`TerminationDilatation`) then yields the inequality.

The Hopf-algebra part is a separate lemma about an abstract `C`, so that the Hopf structure on `S`
and the subalgebra structure are not mixed in one elaboration.

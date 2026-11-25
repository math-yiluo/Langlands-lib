# The Mackey decomposition

`Langlands/Cohomology/Profinite/Mackey/Decomposition.lean`, namespace
`Langlands.ProfiniteCohomology`.

Let `U` be a subgroup of `G`, `ι : H → G` a homomorphism and `N` a representation of `U`. The
restriction along `ι` of the representation coinduced from `U` to `G` is the product, over the
double cosets `U x ι(H)`, of the representations of `H` coinduced from the subgroups
`H_x = ι⁻¹(x⁻¹ U x)`, with `N` transported by conjugation by `x`:

`Res_H Coind_U^G N ≅ ⨁_{x ∈ U\G/ι(H)} Coind_{H_x}^H (x-conjugate of N)`.

When `U` has finite index the sum is finite and the isomorphism is one of biproducts in `Rep k H`.

## Declarations

- `MackeyDoubleCoset U ι`: the double cosets `U \ G / ι(H)` (Mathlib's `DoubleCoset.Quotient`);
  `finite_mackeyDoubleCoset` when `U` has finite index.
- `mackeySubgroup U ι x`: the subgroup of the `h ∈ H` with `x ι(h) x⁻¹ ∈ U`
  (`mem_mackeySubgroup`); `mackeyConj U ι x`: the homomorphism `h ↦ x ι(h) x⁻¹` to `U`
  (`mackeyConj_apply_coe`).
- `mackeyRep U ι N x`: the restriction of `N` along `mackeyConj`; `mackeySummand U ι N x`: its
  coinduction to `H`.
- `mackeyProj U ι N x`: the morphism `Res_H Coind_U^G N → mackeySummand x`, `f ↦ (h ↦ f(x ι(h)))`
  (`mackeyProj_mem`, `mackeyProj_hom_apply`).
- Topology (for `V` open and `ι` continuous): `isOpen_mackeySubgroup`, `mackeyOpenSubgroup`,
  `coe_mackeyOpenSubgroup`, `continuous_mackeyConj`, `isSmoothRep_mackeyRep`.
- Double coset representatives: `exists_eq_mul_out_mul` (every `y` is `u · out(d) · ι(h)`),
  `doubleCosetMk_mul_mul`, `coind_apply_eq_of_mul_eq`, `coind_apply_eq_of_mul_eq'`.
- `mackeyLiftFun`, `mackeyLift`: gluing a family of elements of the summands into an element of
  the coinduced module (`mackeyLiftFun_apply`, `mackeyLiftFun_mem`, `mackeyLift_apply`), inverse
  to the family of projections (`mackeyProj_mackeyLift`, `mackeyLift_mackeyProj`) and
  `H`-equivariant (`mackeyLift_ρ`, `mackeyLift_single_ρ`); `mackeyEquiv`: the resulting linear
  equivalence (`mackeyEquiv_apply_ρ`).
- `mackeyIncl U ι N d`: the inclusion of a summand (`mackeyIncl_hom_apply`), with
  `mackeyIncl_comp_mackeyProj`, `mackeyIncl_comp_mackeyProj_of_ne` and, for finitely many double
  cosets, `sum_mackeyProj_comp_mackeyIncl`.
- `mackeyBicone`, `mackeyBiconeIsBilimit`, instance `hasBiproduct_mackeySummand`, and
  `mackeyIso U ι N : Res_H Coind_U^G N ≅ ⨁_d mackeySummand d`, with `mackeyIso_hom_π`,
  `ι_mackeyIso_inv`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/MackeyDefs.lean` and
`src/GroundTheory/ProfiniteCohomology/MackeyFormula.lean`. The repository has no licence file;
its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's (`isDiscreteRep_mackeyRep` →
`isSmoothRep_mackeyRep`). The source's proofs using `DoubleCoset.eq` were adapted to the
current Mathlib signature of that lemma.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §5, Proposition (1.5.6), p. 51 (the double coset formula
  `res_U^G ∘ cor_G^V = Σ_σ cor_U^{U∩σVσ⁻¹} ∘ σ_* ∘ res_{V∩σ⁻¹Uσ}^V` in cohomology); the
  decomposition of the coinduced module itself is not stated there.
- K. S. Brown, *Cohomology of Groups* (Springer GTM 87, 1982), chapter III, §5, Proposition
  (5.6)(b), p. 69: `Res_K Ind_H^G M ≅ ⨁_{g ∈ E} Ind_{K ∩ gHg⁻¹}^K Res_{K ∩ gHg⁻¹}^{gHg⁻¹} gM`, `E` a set
  of representatives of the double cosets `KgH`. Brown states it for induced modules and subgroups
  `H`, `K` of `G`; he leaves the analogue for co-induced modules to the reader (p. 70) and identifies
  induced and co-induced modules for finite index (Proposition (5.9), p. 70). Here `ι` is any
  homomorphism and the modules are coinduced.

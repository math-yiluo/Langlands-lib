# Graded commutativity of the cup product

`Langlands/Cohomology/Profinite/Cup/Graded.lean`, namespace `Langlands.ProfiniteCohomology`
(finite-group lemmas in `Langlands.ProfiniteCohomology.GroupCoh`).

For a compact group `G`, smooth representations `A`, `B` and classes `x ∈ Hᵖ(G, A)`,
`y ∈ H^q(G, B)`: `(β_{A,B})_*(x ∪ y) = (-1)^{pq} (y ∪ x)`, where `β` is the braiding
`A ⊗ B ≅ B ⊗ A`.

The proof is the classical one. The reversal of inhomogeneous cochains
`f ↦ (x ↦ (-1)^{n(n+1)/2} (x₀⋯x_{n-1}) · f(x_{n-1}⁻¹, …, x₀⁻¹))` commutes with the differential,
preserves locally constant cochains, is the identity in degree `0`, and therefore induces the
identity on cohomology (by dimension shifting with the acyclic coinduced modules); and it
exchanges `f ∪ g` with `(-1)^{pq} β(rev g ∪ rev f)`.

## Declarations

Signs and tuples (namespace `GroupCoh`).

- `triangle n = n(n+1)/2` (`triangle_zero`, `triangle_succ`, `triangle_add`:
  `triangle (p + q) = triangle p + triangle q + pq`), `neg_one_pow_eq_of_mod_two`.
- `revInv x`: the tuple `(x_{n-1}⁻¹, …, x₀⁻¹)` (`revInv_apply`), with `partialProd_last_revInv`,
  `tail_revInv`, `init_revInv`, `tail_revInv'`, `init_revInv'`, `contractNth_revInv`,
  `partialProd_last_contractNth`, `contractNth_last`; `add_add_eq_add_add`.

Reversal of cochains (namespace `GroupCoh`).

- `revCochain n f` (`revCochain_apply`), `d_revCochain` (it commutes with the inhomogeneous
  differential), `revₗ` (as a linear map).
- `braiding_hom_tmul`, `revCochain_cupCochain`: the reversal of `f ∪ g` is
  `(-1)^{pq} β(rev g ∪ rev f)`.

Profinite cochains.

- `continuous_revInv`, `isLocallyConstant_revCochain`; `revHom A`: the reversal as an
  endomorphism of the complex of locally constant cochains, natural in `A`
  (`revHom_naturality`) and the identity in degree `0` (`revHom_f_zero`).
- `homologyMap_eq_id_of_f_eq_id`; `homologyMap_revHom`: for a compact group the reversal induces
  the identity on cohomology; `cochainOf_cocycleι_cyclesMap_revHom`,
  `cohomologyπ_cyclesMap_revHom`.
- `cup_eq_neg_one_pow_smul_coeffMap_braiding` and `coeffMap_braiding_cup`: graded
  commutativity.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`: the statement
from `src/GroundTheory/ProfiniteCohomology/CupProducts/Graded.lean`
(`cohomologyMap_braiding_cup`, here `coeffMap_braiding_cup`), the reversal of cochains
(`triangle`, `revInv`, `revCochain`, `d_revCochain`, `revₗ`, `revCochain_cupCochain`,
`braiding_hom_tmul`) from the source's finite-group files `src/GroundTheory/TateCohomology/CochainReverse.lean`
and `src/GroundTheory/TateCohomology/CupGraded.lean` (only these cochain-level declarations are
taken; the source's Tate cohomology itself is not). The repository has no licence file;
its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`).

The proof differs from the source's: the source deduces graded commutativity by inflation from
finite groups, where it uses its own Tate cohomology and dimension shifting; here the reversal is
shown to induce the identity directly on the locally constant cochains of the compact group
(`revHom`, `homologyMap_revHom`), so the source's Tate cohomology is not needed. The Library has
no graded commutativity of cup products.

## References

- K. S. Brown, *Cohomology of Groups* (Springer GTM 87, 1982), chapter V, §3, (3.6)
  Commutativity, p. 111 (proof pp. 111–112): `uv = (-1)^{pq} t_*(vu)` for `u ∈ Hᵖ(G, M)`,
  `v ∈ H^q(G, N)`, `t : N ⊗ M → M ⊗ N`. Brown states it for abstract groups and proves it with the
  chain automorphism `τ(x ⊗ y) = (-1)^{deg x · deg y} y ⊗ x` of `F ⊗ F`, not with a reversal of
  cochains.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4, Proposition (1.4.4), p. 39 (associativity and skew
  commutativity `α ∪ β = (-1)^{pq} (β ∪ α)`, proved by dimension shifting).

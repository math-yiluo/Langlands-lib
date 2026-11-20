# Coset combinatorics of the geometric lemma

Module `Langlands.Global.EisensteinConstantTerm.Bruhat`. Pure group theory in a group `H`.
It is the first step of the proof of Bernstein–Lapid (6.17) (J. Bernstein and E. Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), registered
as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, proof of Lemma 6.10, journal
p. 208, PDF page 22). There the Eisenstein series is rewritten as
`∑_w ∑_{γ ∈ Q_w(F) \ Q(F)} ∑_{v ∈ (U_Q ∩ wU_{P_w}w⁻¹)(F) \ U_Q(F)} φ_λ(w⁻¹ v γ g)`.
The module proves the bijection of index sets behind this rewriting. It also proves the
corresponding reindexing of sums.

## Definitions

- `BruhatData Gr P Q V w`: `P, Q ≤ Gr`, `V ≤ Q`, `V` normalized by `Q`, every `w i ∈ Gr`, and
  every `z ∈ Gr` lies in `Q w_i P` for exactly one `i`.
- `bruhatStabilizer P V w = V ⊓ w P w⁻¹`, the group `Δ_i = V ∩ w_i P w_i⁻¹`.
  `mem_bruhatStabilizer_iff`: `x ∈ Δ ↔ x ∈ V ∧ w⁻¹ x w ∈ P`.
- `OuterCosets Q Q'`, `InnerCosets P V w`, `AmbientCosets Gr P`: the right-coset spaces
  `Q' \ Q`, `Δ \ V` and `P \ Gr`, each the quotient by `QuotientGroup.rightRel` of the
  corresponding `subgroupOf`.
- `OuterIndex Q Q' = Σ i, Q'_i \ Q` and `BruhatIndex P Q V Q' w = Σ (j : OuterIndex), Δ_{j.1} \ V`.
- `bruhatPoint Q' t = w_i⁻¹ ν γ`, with `ν` and `γ` the chosen representatives (`Quotient.out`)
  of the inner and outer cosets of `t`. `bruhatClass` is its class in `P \ Gr`.

## Results

- `mem_map_conj_iff`: `x ∈ w P w⁻¹ ↔ w⁻¹ x w ∈ P`.
- `exists_mul_of_mem_sup`: if `V` is normalized by `A`, each element of `A ⊔ V` is a product `a v`.
- `bruhatClass_injective`, `bruhatClass_surjective`, and their combination `bruhatEquiv`:
  under `BruhatData` and `Q'_i = (Q ⊓ w_iPw_i⁻¹) ⊔ V`, the map `t ↦ P · w_i⁻¹ ν γ` is a
  bijection `BruhatIndex ≃ P \ Gr`.
  - Surjectivity: write `z⁻¹ = x w_i y` and let `c` be the class of `x⁻¹`. The element
    `(γ_c x)⁻¹ ∈ Q'_i` factors as `a v` with `a ∈ Q ∩ w_iPw_i⁻¹` and `v ∈ V`. With `ν` the class
    of `v`, one checks `z (w_i⁻¹ ν γ_c)⁻¹ ∈ P`.
  - Injectivity: equal classes give `w_j⁻¹ ν' γ' = π w_i⁻¹ ν γ` with `π ∈ P`. Uniqueness of the
    double coset gives `i = j`. Then `ν'γ'(νγ)⁻¹ ∈ Q ∩ w_iPw_i⁻¹ ⊆ Q'_i` gives equal outer
    classes, and then `ν'ν⁻¹ ∈ Δ_i` gives equal inner classes.
- `exists_out_eq_mul`, `exists_out_bruhatClass`: the chosen representative of a class in
  `P \ Gr` differs from any element of the class by a left factor in `P`.
- `ambientRight`, `exists_out_ambientRight`: right translation by `δ ∈ Gr` on `P \ Gr`.
- `tsum_out_mul_left`: for `g` left `P`-invariant and `δ ∈ Gr`,
  `∑'_{c ∈ P \ Gr} g(c̄ δ x) = ∑'_c g(c̄ x)`, with `c̄` the chosen representative. The proof
  reindexes along `ambientRight δ`.
- `tsum_out_eq_tsum_bruhat`: for `g` left `P`-invariant,
  `∑'_{c ∈ P \ Gr} g(c̄ x) = ∑'_{t} g(w_i⁻¹ ν γ x)`. The proof reindexes along `bruhatEquiv`.

Both reindexings are equalities of unconditional sums `tsum` along a bijection. They need no
summability hypothesis.

## Provenance

The decomposition `G(F) = ⊔_w P(F) w⁻¹ Q(F)` is the Bruhat decomposition of BL Lemma 6.7 (1),
journal pp. 206–207 (PDF pages 20–21), and of MW II.1.7 (C. Mœglin and J.-L. Waldspurger,
*Spectral decomposition and Eisenstein series*, 1995, registered as
`moeglin-waldspurger-1995-spectral-decomposition`, printed pp. 91–93). Here it enters only
through the abstract hypothesis `BruhatData.unique`. In the application this hypothesis is
`IsDoubleCosetRepresentatives`. The splitting of `(Q ∩ wPw⁻¹) \ Q` through `Q_w \ Q` uses
`Q_w = (Q ∩ wPw⁻¹) V`, the second field of `IsGeometricLemmaDatum`. The formalization is
internal.

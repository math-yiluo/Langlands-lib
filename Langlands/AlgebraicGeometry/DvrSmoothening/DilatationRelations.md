# Relations of `A` lie in the square of the centre, up to unit-valued multipliers and the auxiliary relations

`exists_dilatation_relations`: let `P = R[X₁, …, X_N] → A` present a finite type algebra over a
discrete valuation ring `R` with uniformizer `ϖ`, and `J ⊆ A` an intersection of specialization
primes of points of ramification index one with `k ⊗_R (A ⧸ J)` smooth over the residue field `k`
and `(A ⧸ J) ⊗_A Ω_{A/R}` free. Let `A → R'` be a point of a local ring whose closed point lies on
the centre and `K` the residue field of `R'`. Then there are relations `wₗ` of `A` and lifts `zⱼ`
of elements of `J` such that:

1. the `1 ⊗ dzⱼ, 1 ⊗ dwₗ` are linearly independent in `K ⊗_P Ω_{P/R}`;
2. every relation `f` of `A` has a multiple `e f`, with `e` of unit value in `R'`, in
   `(ϖ, z)² + (w)`;
3. every `x ∈ J` has a multiple `e x`, with `e` of unit value, in `(ϖ, z) A`.

Proof. `DilatationLocal.exists_extension` chooses `w` with `dw` spanning the differentials of the
relations and `z` extending them to a spanning family for the lifts of `J`. Then
`DilatationResidue.exists_mul_mem_span_of_residue` (with `B = A ⧸ J`, smooth over `k` through
`GoodChart.residueTensorEquiv`) gives *local generation*: every lift `p ∈ P` of an element of `J`
has a multiple `e p`, with `e` of unit value, in `(ϖ, z, w)`. Since the `wₗ` vanish in `A`, this
gives 3. Property 2 is proved for a relation `f` of `A` in the following steps. All multipliers
below have unit value in `R'`.

1. By local generation, `s f = ϖ g + ∑ gⱼ zⱼ + a` with `a ∈ (w)`.
2. Taking differentials in `(A ⧸ J) ⊗_A Ω_{A/R}` gives `∑ ḡⱼ dzⱼ = 0`. The `dzⱼ` have linearly
   independent images in `K ⊗_A Ω_{A/R}`: a `K`-linear relation `∑ cⱼ dzⱼ = 0` there places
   `∑ cⱼ dzⱼ` in the kernel of `K ⊗_P Ω_{P/R} → K ⊗_A Ω_{A/R}`, which is spanned by the
   differentials of relations, hence by the `dwₗ`; independence of the `dzⱼ, dwₗ` forces all
   `cⱼ = 0`. The module `(A ⧸ J) ⊗_A Ω_{A/R}` is finite free over `A ⧸ J`, so
   `DilatationLocal.exists_mul_eq_zero_of_linearIndependent` gives `t ∈ P` with non-zero image
   in `K` such that every `t gⱼ` maps into `J`.
3. Local generation applied to each `t gⱼ`, with the product `s'` of the multipliers, gives
   `s' t gⱼ = ϖ aⱼ + rⱼ` with `rⱼ ∈ (z, w)`.
4. Put `G = s' t g + ∑ aⱼ zⱼ`. Multiplying step 1 by `s' t` gives `s' t s f = ϖ G + ρ` with
   `ρ = ∑ zⱼ rⱼ + s' t a ∈ (ϖ, z)² + (w)`.
5. In `A`, `f` vanishes and `ρ` lies in `J²`, so `ϖ G ∈ J²`. Property (N)
   (`DilatationLocal.mem_of_mul_mem_sq`) puts the image of `G` in `J`.
6. Local generation once more gives `s'' G ∈ (ϖ, z, w)`, hence `ϖ s'' G ∈ (ϖ, z)² + (w)`, and
   `s'' s' t s f = ϖ (s'' G) + s'' ρ ∈ (ϖ, z)² + (w)`.

This is the key point of Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.3, proof of
Proposition 5 (printed p. 69): the ideal of `X` in the smooth ambient scheme lies in the square of
the ideal of the centre.

# Every orbit of a smooth relation contains a good point

This internal module proves step (iii) of the étale slicing proof of
`SmoothEquivalenceRelationEtaleSliceStatement` (task 3c6168ac): every point
of the base is the source of a relation point whose target is a good point
in the sense of `IsGoodPoint` (module `SmoothRelationGoodPoint`).

## Statements

Let `t s : R ⟶ U` be morphisms of schemes (in one universe `u`) and
`e : U ⟶ R` a common section: `e ≫ t = 𝟙 U` and `e ≫ s = 𝟙 U`.

- `apply_fromSpec`: for affine opens `V ⊆ U` and `W ⊆ f⁻¹ V` and a prime `P`
  of `Γ(R, W)`, the point `f (fromSpec P)` is the point `fromSpec` of the
  contraction of `P` along `f.appLE V W`.
- `exists_isGoodPoint` (main theorem): assume that `prod.lift t s : R ⟶ U ⨯ U`
  is a monomorphism and that `s` is smooth. Then for every `x : U` there is
  `r : R` with `s r = x` such that `IsGoodPoint t s e (t r)`.
  The morphism `t` need not be smooth, and no reflexivity, symmetry or
  transitivity of the relation is used beyond the common section `e`.
- `goodPointOver t s hmono hs e het hes x` is such a point `r`, chosen by
  `exists_isGoodPoint`; `apply_goodPointOver` and `isGoodPoint_goodPointOver`
  record its two properties.

## Proof of `exists_isGoodPoint`

1. Choose an affine open `V ∋ x` of `U` and an affine open `W ∋ e x` of `R`
   inside `s⁻¹ V ∩ t⁻¹ V`. Put `A = Γ(U, V)`, `B = Γ(R, W)`, make `B` an
   `A`-algebra through `s` (it is smooth, since `s` is smooth), and let
   `θ = t.appLE V W`.
2. Since `(t, s)` is a monomorphism, the differentials `d θ(a)` span `Ω[B⁄A]`
   (`span_targetDifferentials_eq_top_of_mono`, module
   `SmoothRelationGoodPointMono`).
3. Let `p₀` be the prime of `e x`. `exists_etale_coordinates` (module
   `SmoothRelationGoodPointEtale`) gives a finite type `ι` and `g : ι → A`
   such that, for the algebra structure `Φ : A[X_i] → B`, `X_i ↦ θ(g i)`,
   the algebra `B` is étale at `p₀` over `A[X_i]`. As `B` is finitely
   presented over `A`, it is finitely presented over `A[X_i]`, and Mathlib's
   `Algebra.exists_etale_of_isEtaleAt` gives `c ∉ p₀` with `B_c` étale over
   `A[X_i]`.
4. Let `O` be the set of primes `P` of `B` with `c ∉ P` and
   `e (t (fromSpec P)) ∈ D(c)`, where `D(c) = R.basicOpen c`. It is open and
   contains `p₀`, because `fromSpec p₀ = e x` and `t (e x) = x`.
   `exists_prime_simpleIntegerRoots_of_etale_away` (module
   `SmoothRelationGoodPointEtaleImage`) gives `P ∈ O` with the same
   contraction to `A` as `p₀` and, for each `i`, an integer polynomial `Q_i`
   with `Q_i(θ(g i)) ∈ P` and `Q_i'(θ(g i)) ∉ P`.
5. Put `r = fromSpec P`. By `apply_fromSpec`, `s r` is the point of the
   contraction of `P` along `s.appLE`, which equals that of `p₀`; hence
   `s r = s (e x) = x`.
6. Put `y = t r`. Then `e y ∈ D(c) ⊆ W`; let `P''` be its prime, so
   `c ∉ P''` and `B` is étale at `P''` over `A[X_i]`
   (`Algebra.basicOpen_subset_etaleLocus_iff`). By
   `residueSpan_eq_top_of_isEtaleAt`, the elements `1 ⊗ d θ(g i)` span
   `κ(B_P'') ⊗ Ω[B_P''⁄A]`. The contractions of `P''` and `P` along `θ` are
   both the prime of `y` (by `apply_fromSpec`, `t (e y) = y`, and
   injectivity of `fromSpec` on `V`), so `Q_i(g i)` lies in, and
   `Q_i'(g i)` lies outside, the contraction of `P''` along `θ`.
7. `isGoodPoint_of_simpleIntegerRoots` (module
   `SmoothRelationGoodPointConverse`), applied at `y` with the charts `V`,
   `W` and the prime `P''`, gives `IsGoodPoint t s e y`.

## Provenance

Internal. The route was designed for this project (Worker 303, recorded in
the coordination with Workers 101 and 424 on task 3c6168ac). It differs from
the Cohen–Macaulay slicing of the Stacks Project (More on Groupoids, Section
04LV): it moves along the orbit `s⁻¹(x)` to a point whose étale coordinates
satisfy integer equations with simple roots, which makes the image under `t`
good. The ingredients from
Worker 101's modules (monomorphism spanning, point choice and the converse
chart bridge) are imported, not reproved.

# Local differential slices: a closed embedding into a smooth scheme

Author: Worker 9.

Helper module for the proof of
`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (SGA 3, Exposé VI_B,
Corollaire 4.4). Let `A` be a finite type `R`-algebra and `Q` a prime of `A`. If the cotangent
fibre `κ(Q) ⊗[A] Ω[A⁄R]` has dimension `n`, then near `Q` the scheme `Spec A` is a closed
subscheme of a scheme smooth of relative dimension `n` over `Spec R`. The construction maps
`A` from `R[y₁, …, yₙ]` by elements whose differentials span the cotangent fibre. It then uses
Mathlib's local structure theorem for unramified algebras.

All declarations are in the namespace `Langlands.GroupScheme.ReducedBaseSmooth`, and all rings
lie in one universe `u`. `κ(Q)` is `Q.ResidueField`, `D` is
`KaehlerDifferential.D R A : A → Ω[A⁄R]`, and `1 ⊗ D x` denotes the element
`(1 : κ(Q)) ⊗ₜ[A] D x` of `κ(Q) ⊗[A] Ω[A⁄R]`.

## Declarations

- `isUnramifiedAt_of_span`: let `R → R' → A` be a scalar tower of commutative rings with
  `A` of finite type over `R'`, let `Q` be a prime of `A`, and let `s ⊆ R'`. If the elements
  `1 ⊗ D(r)`, for `r ∈ s` mapped into `A`, span `κ(Q) ⊗[A] Ω[A⁄R]` over `κ(Q)`, then
  `Algebra.IsUnramifiedAt R' Q`.
- `span_one_tmul_D_eq_top`: for any `R`-algebra `A` and prime `Q` of `A`, the elements
  `1 ⊗ D x` for `x ∈ A` span `κ(Q) ⊗[A] Ω[A⁄R]` over `κ(Q)`.
- `exists_span_eq_top_of_finrank_eq`: let `A` be a finite type `R`-algebra and `Q` a prime of
  `A`. If `Module.finrank κ(Q) (κ(Q) ⊗[A] Ω[A⁄R]) = n`, there is `a : Fin n → A` such that
  the elements `1 ⊗ D(a i)` span `κ(Q) ⊗[A] Ω[A⁄R]`.
- `exists_closedImmersion_smooth_of_span`: let `A` be a finite type `R`-algebra, `Q` a prime
  of `A`, and `a : Fin n → A` such that the elements `1 ⊗ D(a i)` span
  `κ(Q) ⊗[A] Ω[A⁄R]`. Then there exist `f ∈ A` with `f ∉ Q` and
  - a scheme `Z0` with a morphism `p0 : Z0 ⟶ Spec R`, which is
    `SmoothOfRelativeDimension n`, quasi-compact and quasi-separated;
  - a closed immersion `i0 : Spec A[1/f] ⟶ Z0`;

  such that `i0 ≫ p0` is `Spec` of the algebra map `R → A[1/f]`. Here `A[1/f]` is
  `Localization.Away f`.

## Provenance

These are internal lemmas with derived names. The geometric content is the classical fact
that a scheme of finite type is, locally, a closed subscheme of a scheme étale over affine
space whose dimension is the rank of the cotangent fibre. The implemented route goes through
Mathlib's `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`. That theorem says: a
finite type algebra unramified at a prime `Q` receives, after inverting some `f ∉ Q`, a
surjection from a standard étale algebra. The route does not use the conormal sequence.

## Proofs

`isUnramifiedAt_of_span`. The map `Ω[A⁄R] → Ω[A⁄R']` (`KaehlerDifferential.map`) is
surjective, so its base change `κ(Q) ⊗ Ω[A⁄R] → κ(Q) ⊗ Ω[A⁄R']` is surjective. It kills every
`1 ⊗ D(r)` with `r` from `R'`, because `D_{A/R'}` vanishes on elements of `R'`. Since these
elements span the source, the target `κ(Q) ⊗[A] Ω[A⁄R']` is zero. By Mathlib's
`Module.mem_support_iff_nontrivial_residueField_tensorProduct`, `Q` is not in the support of
`Ω[A⁄R']`. By `Algebra.unramifiedLocus_eq_compl_support`, `Q` therefore lies in the unramified
locus of `A` over `R'`.

`span_one_tmul_D_eq_top`. The image of `D` spans `Ω[A⁄R]` over `A`
(`KaehlerDifferential.span_range_derivation`). Base change of spans
(`Submodule.baseChange_span`, `Submodule.baseChange_top`) turns this into the claim.

`exists_span_eq_top_of_finrank_eq`. Choose a linearly independent subset `t` of
`{1 ⊗ D x}` with the same span (`exists_linearIndependent`). By the previous lemma it is a
basis of `κ(Q) ⊗[A] Ω[A⁄R]`. The module is finite over `κ(Q)` because `Ω[A⁄R]` is finite over
`A` when `A` is of finite type, so `t` is finite of cardinality `n`
(`Module.finrank_eq_nat_card_basis`). Enumerate `t` by `Fin n` and choose preimages `a i`.

`exists_closedImmersion_smooth_of_span`. Let `R' = MvPolynomial (Fin n) R`, made an algebra over
`R` and acting on `A` by `yᵢ ↦ a i` (`MvPolynomial.aeval a`). Then `R → R' → A` is a scalar
tower and `A` is of finite type over `R'`. The elements `1 ⊗ D(yᵢ)` are the given spanning
family, so `isUnramifiedAt_of_span` shows that `A` is unramified over `R'` at `Q`. Mathlib's
`Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn` gives `f ∉ Q`, a standard étale
pair `P` over `R'`, and a surjective `R'`-algebra map `φ : P.Ring → A[1/f]`. Take
`Z0 = Spec P.Ring`, `p0 = Spec(P.Ring ← R') ≫ Spec(R' ← R)` and `i0 = Spec φ`.

- `i0` is a closed immersion because `φ` is surjective (`IsClosedImmersion.spec_of_surjective`).
- `Spec R' → Spec R` is smooth of relative dimension `n`: by `HasRingHomProperty.Spec_iff` it
  suffices that `R → R'` is standard smooth of relative dimension `n`, which Mathlib provides
  for polynomial algebras.
- `Spec P.Ring → Spec R'` is étale because `P.Ring` is étale over `R'`, hence it is smooth of
  relative dimension `0`. By `smoothOfRelativeDimension_comp`, `p0` is smooth of relative
  dimension `0 + n = n`.
- `p0` is quasi-compact and quasi-separated as a morphism of affine schemes.
- `i0 ≫ p0` is `Spec` of `R → R' → P.Ring → A[1/f]`. This equals `R → A[1/f]` because `φ` is
  an `R'`-algebra map and `R → R' → A` is a scalar tower.

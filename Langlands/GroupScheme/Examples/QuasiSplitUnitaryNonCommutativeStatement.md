# The quasi-split unitary group `U(1,1)` is not commutative: statement

Author: Worker 293. This is statement S3 of task
`be70310c-1939-4a82-8293-c4d33f5883ae`. The module contains one `Prop`-valued
definition and no proof. A proof is left to a separate `lean.proof` task.

## The statement

`NonCommutativeStatement` says the following. Let `F` and `E` be fields in one
universe `u`, with `[Algebra F E]` and `[Algebra.IsQuadraticExtension F E]`. Let
`κ` be a finite type in universe `u`, and let `b` be an `F`-basis of
`Matrix (Fin 2) (Fin 2) E` indexed by `κ`. Let `c : E ≃ₐ[F] E` satisfy
`c ≠ AlgEquiv.refl`. Then there are two points `g h` of `groupScheme b c` over
the terminal object `Over.mk (𝟙 (Spec (CommRingCat.of F)))` with
`g * h ≠ h * g`.

Here `groupScheme b c` is the group scheme `U(1,1)` over
`Spec (CommRingCat.of F)` of unit 1, `Langlands.GroupScheme.Examples.QuasiSplitUnitary`
(Worker 399). It is the Library's `SchemeModel.unitaryGroupScheme` of `b` and
of the involution `X ↦ J (X.map c)ᵀ J` of `Matrix (Fin 2) (Fin 2) E`, where
`J = !![0, 1; 1, 0]`. The product of two points is the product of morphisms
into a group object of `Over (Spec (CommRingCat.of F))`, from the scoped
notation of `CategoryTheory.MonObj`. Points over the terminal object are the
`F`-rational points of `U(1,1)`.

No assumption on the characteristic of `F` is made, so the statement covers
characteristic `2`. The universe of `κ` is `u`, as required by
`groupScheme`.

## Provenance and intended proof

The statement is derived for this task. It records that `U(1,1)` is a
noncommutative example, as the parent program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` asks. It is not quoted from a source.
Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
discusses unitary groups in 24.40–24.44 (printed pp.523–525). The
presentation by the antidiagonal Gram matrix `J` is the standard choice of unit 1
for the hermitian form `h(v, w) = v₁ c(w₂) + v₂ c(w₁)`.

The task contract suggests the following witnesses; the Lean statement does not
name them. Unit 1's `pointsEquiv` identifies points over the terminal object
with the invertible matrices `X` over `E ⊗[F] Γ(Spec F, ⊤)` with
`X J (X.map c_R)ᵀ J = 1`, where `c_R` is `c ⊗ id`. Choose `t ∈ E` with
`c t ≠ t` and put `x = t - c t`. Then `x ≠ 0`, and `x + c x = 0` because
`c (c t) = t`. This choice works in every characteristic. Since
`Γ(Spec F, ⊤)` is `F`, the ring `E ⊗[F] Γ(Spec F, ⊤)` is identified with `E`.
The matrices `J` and `u(x) = !![1, x; 0, 1]` satisfy the unitary equation, and
`J u(x) = !![0, 1; 1, x]` differs from `u(x) J = !![x, 1; 1, 0]` because
`x ≠ 0`.

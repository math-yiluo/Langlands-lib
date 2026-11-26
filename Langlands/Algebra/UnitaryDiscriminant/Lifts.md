# Twisted projective lifts of an algebra with unitary involution

Module `Langlands.Algebra.UnitaryDiscriminant.Lifts`, namespace `Langlands.UnitaryDiscriminant`.

This module turns a central simple algebra with unitary involution and a matrix splitting chart
into a family of invertible matrices `P_g`, one for each automorphism `g` of the splitting field,
together with their scalar factor set. These are the descent data used by the discriminant class
of `Langlands.Algebra.UnitaryDiscriminant.Class`.

## Setting

* `F`, `L`, `M` are fields in one universe with a tower `F → L → M` (`IsScalarTower F L M`).
  Where the quadratic center matters, `[Algebra.IsQuadraticExtension F L]` is assumed and
  `ι : L ≃ₐ[F] L` is an automorphism with `ι ≠ 1`.
* `B : Type v` is an `L`-algebra and `τ : B → B` satisfies
  `Langlands.IsUnitaryInvolution ι τ`: it is additive, reverses products, squares to the identity
  and acts on the scalars `algebraMap L B l` through `ι`.
* `e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M` is a matrix splitting chart. Write
  `j b = e (1 ⊗ b)` (`chartMap e`, an `L`-algebra map). For a matrix `N` write `N^g` for the
  entrywise image `N.map g` and `Nᵀ` for the transpose.

No finiteness or Galois hypothesis on `M` is used in this module.

## The quadratic center

* `centerFixing F L M` is the subgroup of `M ≃ₐ[F] M` fixing the image of `L` pointwise. Its
  elements are called inner, the others outer (`mem_centerFixing`).
* `algHom_eq_or_eq`: every `F`-algebra map `L → M` is the structure map or its composite with
  `ι`. Proof: the structure map and its composite with `ι` are distinct because `ι ≠ 1`, and there
  are at most `[L : F] = 2` such maps (Mathlib's `card_algHom_le_finrank`), so a third distinct
  one would give an injection of `Fin 3`.
* `apply_apply_of_ne_one`: `ι (ι l) = l`; `false_of_algebraMap_eq`: `ι` does not act trivially
  on the image of `L`.
* `apply_algebraMap_of_not_mem`: an outer `g` satisfies `g (algebraMap L M l) = algebraMap L M (ι l)`.
* `mul_mem_centerFixing_iff`: `g h` is inner exactly when `g` and `h` are both inner or both
  outer. This is the index-at-most-two property used throughout.

## Invertible matrices

* `invTranspose : GL I R →* GL I R` is `X ↦ (X⁻¹)ᵀ`, with `coe_invTranspose`,
  `coe_invTranspose_inv`, `invTranspose_invTranspose`, `invTranspose_map` (commutes with
  coefficient maps), `det_invTranspose` and `invTranspose_scalar`.
* `exists_unit_conj_of_algHom`: every algebra endomorphism of `Matrix I I k` over a field `k`
  is conjugation by an invertible matrix. It is injective (the matrix algebra is simple, or zero
  when `I` is empty), hence bijective by finite dimension, and the Library's matrix Skolem–Noether
  theorem `Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv` applies.

## Twisted actions

For a subgroup `H` of `M ≃ₐ[F] M`:

* `coeffTwist H g N` is `N^g` for `g ∈ H` and `(N^g)ᵀ` otherwise;
* `twistGL H g X` is `g(X)` (`GeneralLinearGroup.map`) for `g ∈ H` and `invTranspose (g(X))`
  otherwise;
* `twistUnit H g a` is `g • a` for `g ∈ H` and `(g • a)⁻¹` otherwise.

The map `twistedAct H x g` of `Langlands.LinearAlgebra.UnitaryTwistedDescent` is
`N ↦ x(g) · coeffTwist H g N · x(g)⁻¹` (`twistedAct_eq`). Lemmas: `coeffTwist_conj`
(`coeffTwist` of `Y A Y⁻¹` is conjugation of `coeffTwist A` by `twistGL Y`), `coeffTwist_add`,
`coeffTwist_smul`, `twistedAct_smul` (`g`-semilinearity), `twistedAct_zero`, `twistGL_mul`,
`twistGL_inv`, `twistGL_scalar`, `det_twistGL` (`det (twistGL g X) = twistUnit g (det X)`) and
`coeffTwist_surjective`. Under the index-two hypothesis
`hmul : ∀ g h, g * h ∈ H ↔ (g ∈ H ↔ h ∈ H)`, `coeffTwist_coeffTwist` and `twistGL_twistGL`
show that these are actions.

* `exists_twistGL_mul_eq`: if the maps `twistedAct H x g` compose (`(g h)` acts as `g` after
  `h`), then for all `g, h` there is a unit `c` with
  `x g * twistGL H g (x h) = scalar c * x (g * h)`. The two sides conjugate every matrix in the
  same way, because `coeffTwist (g h)` is surjective, so they differ by a unit scalar
  (`SpecialLinearConjugation.exists_unit_scalar_of_conjugation_eq_conjugation`).
* `exists_scalar_of_twistedAct_eq`: two families with the same twisted action of `g` differ at
  `g` by a unit scalar.
* `twisted_cocycle`: for nonempty indices, the scalars `c` of such a twisted projective cocycle
  satisfy `c g h * c (g * h) k = twistUnit H g (c h k) * c g (h * k)`. The proof is the
  associativity computation of `Langlands.ScalarTwoCocycle.isTwoCocycle_of_lifts`, with
  `twistGL` in place of the coefficient action.

## The chart

* `chart_induction`: every matrix is a sum of matrices `c • j b`, because `e` is surjective and
  `c ⊗ b = c • (1 ⊗ b)`.
* `exists_conj_chartMap`: every `L`-algebra map `ψ : B → M_n(M)` is conjugate to `j`. Its
  `M`-linear extension composed with `e⁻¹` is an algebra endomorphism of the matrix algebra, to
  which `exists_unit_conj_of_algHom` applies.
* `innerTarget e g hg` (`g` inner) is the `L`-algebra map `b ↦ (j b)^{g⁻¹}`. `outerTarget e hτ g hg`
  (`g` acting on `L` through `ι`) is `b ↦ ((j (τ b))ᵀ)^{g⁻¹}`; it is multiplicative because `τ`
  and the transpose both reverse products, and `L`-linear because `g⁻¹` maps
  `algebraMap L M (ι l)` to `algebraMap L M l`.
* `exists_lift_of_mem`: for inner `g` there is `P` with `P (j b)^g P⁻¹ = j b` for all `b`
  (take `P = g(U)` for `U` conjugating `j` to `innerTarget`).
* `exists_lift_of_not_mem`: for `g` acting through `ι` there is `P` with
  `P ((j b)^g)ᵀ P⁻¹ = j (τ b)` for all `b` (take `P = invTranspose (g(U))`).
* `twistedAct_eq_of_chartMap`: two families whose twisted actions of `g` agree on the chart
  images agree on all matrices (by `chart_induction` and semilinearity).

## The chosen lifts

* `chartLift hι hτ e g : GL (Fin n) M` is a lift chosen with `exists_lift_of_mem` or
  `exists_lift_of_not_mem` (classical choice). The defining properties are
  `twistedAct_chartLift_of_mem`, `twistedAct (centerFixing F L M) (chartLift hι hτ e) g (j b) = j b`
  for inner `g`, and `twistedAct_chartLift_of_not_mem`, with right side `j (τ b)` for outer `g`.
  By `twistedAct_smul`, `β_g = twistedAct (centerFixing F L M) (chartLift hι hτ e) g` sends
  `c • j b` to `g c • j b`, respectively `g c • j (τ b)`. So `β_g` is the transport through `e`
  of the semilinear map `g ⊗ id_B`, respectively `g ⊗ τ`, of `M ⊗[L] B`; in the outer case it is
  an anti-automorphism.
* `twistedAct_chartLift_mul`: `β_{gh} = β_g ∘ β_h`. By `chart_induction` it suffices to check
  this on `c • j b`, where it reduces to `(g h) c = g (h c)`, `τ (τ b) = b` and
  `mul_mem_centerFixing_iff`.
* `chartFactor hι hτ e g h : Mˣ` and `chartLift_mul`: the twisted projective cocycle law
  `P g * twistGL (centerFixing F L M) g (P h) = scalar (λ g h) * P (g * h)`, from
  `exists_twistGL_mul_eq`. This is J.-P. Serre's factor-set convention `P_s s(P_t) P_{st}⁻¹`
  (*Local Fields*, Chapter X, §5, printed pp. 158–159), used by the Library's Brauer comparison,
  with the outer automorphism `X ↦ X^{-T}` added for outer `g`.

## Role and provenance

Provenance: internal. The construction is the standard Galois descent description of a central
simple algebra with unitary involution: over a splitting field the inner automorphisms act through
`PGL_n` and the outer ones through `PGL_n` composed with the outer automorphism `X ↦ X^{-T}`,
which is the exact sequence `1 → PGU(B, τ) → Aut(B, τ) → S₂ → 1` of M.-A. Knus, A. Merkurjev,
M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §29.D, printed p. 400 / PDF p. 423
(registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`, SHA-256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`). The Lean proofs use only
the chart, Skolem–Noether and the elementary matrix identities above. The opposite direction,
from such a cocycle to an algebra with unitary involution, is
`Langlands.LinearAlgebra.UnitaryTwistedDescent`.

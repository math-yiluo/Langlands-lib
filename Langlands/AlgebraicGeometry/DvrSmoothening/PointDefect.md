# Néron's defect of smoothness of a point

The module `Langlands.AlgebraicGeometry.DvrSmoothening.PointDefect` contains one definition.

## `pointDefect`

For commutative rings `R`, `A`, `R'` with `R`-algebra structures on `A` and `R'`, and an
`R`-algebra homomorphism `φ : A →ₐ[R] R'`, `pointDefect φ : ℕ∞` is the length, as an
`R'`-module, of the torsion submodule `Submodule.torsion R' (R' ⊗[A] Ω[A⁄R])`. Here `R'` is
made an `A`-algebra through `φ` (`φ.toRingHom.toAlgebra`), `Ω[A⁄R]` is the module of Kähler
differentials, and the torsion submodule consists of the elements killed by a non-zero-divisor
of `R'`. The value `⊤` is allowed by the type; it does not occur when `R'` is a discrete
valuation ring and `Ω[A⁄R]` is a finite `A`-module.

Geometrically, `φ` is an `R'`-valued point `a : Spec R' → Spec A` over `Spec R`, and
`R' ⊗_A Ω_{A/R}` is the pull-back `a*Ω_{X/R}` of the sheaf of relative differentials of
`X = Spec A`.

## Source

Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models` (SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is PDF
page `p + 7`):

- §3.3, printed pp. 64–65: for an `R^{sh}`-valued point `a` of an `R`-scheme `X` of finite type
  with smooth generic fibre, `δ(a)` is the length of the torsion part of the finite
  `R^{sh}`-module `a*Ω¹_{X/R}` (Néron's measure for the defect of smoothness);
- §3.6, printed p. 79: the same definition for an `R'`-valued point when `R → R'` has
  ramification index 1.

The definition is stated for an affine `X = Spec A` and any target ring `R'`; BLR use it for
discrete valuation rings `R'`, where a finite module is the direct sum of a free part and its
torsion part.

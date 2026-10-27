# The concrete two-block cell of JPSS Proposition 9.1

This module supplies concrete definitions and elementary laws for the proof of
the Proposition in Section (9.1) of H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin–Selberg convolutions*, American Journal of
Mathematics 105 (1983), 367–464, printed pages 452–454 (one-based PDF
pages 87–89). The registered original is `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. No errata
are registered for this passage. The authors are Worker 643 and Worker 731.
Worker 643 specified the cell, the restriction and the submodule for the proof
of `Langlands.Whittaker.TwoBlockWhittakerExtensionStatement`, and Worker 731
wrote the Lean implementation of that specification.

## Provenance

On printed page 453 the proof says, "as in (5.5)", that there is a vector `f`
in the space of `ξ` with

\[
f\!\left[w\begin{pmatrix}1_{r_2}&x\\0&1_{r_1}\end{pmatrix};h_1,h_2\right]
  =\Psi(x)\,W_1(h_1)\,W_2(h_2),\qquad
w=\begin{pmatrix}0&1_{r_1}\\1_{r_2}&0\end{pmatrix},
\]

for `Ψ` a Schwartz–Bruhat function of `x` with `r₂` rows and `r₁` columns.
Implicitly, such an `f` is supported in the cell `P w N`. The source does not
name the cell, the restriction map or the space of such functions. The cell,
the restriction and the support submodule below are therefore internal
derived definitions that this formula motivates. This module proves **no**
geometric theorem. It does not prove that the cell is open, that the
coordinates `(q, x)` are unique, that sections with a prescribed restriction
exist, that the submodule is stable under the upper unipotent group, or any
statement about integrals or Fourier transforms. Those results belong to later
statement and proof units stated with these names.

Throughout, `A = a + 1` and `B = b + 1` play the roles of the source's `r₁`
and `r₂`. Both are positive, as the source's ranks are.

## The cell

All declarations are in `Langlands.Whittaker`. The arguments are a prime `p`,
a field `F : PadicField.{uF} p` and natural numbers `a`, `b`.

- `twoBlockShape a b` is literally
  `Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b)`,
  the ordered shape `(A, B)`.
- `twoBlockParabolic F a b` is literally that shape's standard upper
  parabolic subgroup `P` of `GL_{A+B}(F)`, with Levi blocks `GL_A × GL_B` in
  this order.
- `twoBlockCellPoint F a b x` is
  `Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier * Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier x`
  for `x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier`. This is the
  source's `w n(x)`.
- `twoBlockCell F a b` is the set `C` of all `g` in `GL_{A+B}(F)` such that
  `g = q * blockWeyl * intertwiningUnipotent x` for some `q ∈ P` and some `x`.
  `mem_twoBlockCell_iff` states this definition as an equivalence.

The two matrices are the Library's existing Shahidi matrices. No new Weyl or
radical matrix is defined here. `Shahidi.blockWeyl A B` is the all-positive
permutation matrix
\(\begin{pmatrix}0_{A,B}&I_A\\ I_B&0_{B,A}\end{pmatrix}\)
with row blocks `(A, B)` and column blocks `(B, A)`. It is exactly the source's
`w`, which has `1_{r₁}` in the upper right and `1_{r₂}` in the lower left.
`Shahidi.intertwiningUnipotent A B x` is the upper unipotent matrix
\(\begin{pmatrix}I_B&x\\0&I_A\end{pmatrix}\)
with blocks `(B, A)`, which is the source's `n(x)`. It is moved to the total
rank `A + B` by `Shahidi.swapRank`. That map is an entry-preserving reindexing
of the total rank `B + A = A + B`. It is not a conjugation by the Weyl
element. The cell uses `blockWeyl` itself, not its inverse. The inducing
factors are not exchanged either: `P` belongs to the shape `(A, B)`, the same
as for `ξ`.

The elementary laws are as follows.

- `parabolic_mul_mem_twoBlockCell`: every displayed product
  `q * blockWeyl * intertwiningUnipotent x` with `q ∈ P` lies in `C`.
- `twoBlockCellPoint_mem`: every representative `w n(x)` lies in `C`.
- `blockWeyl_mem_twoBlockCell`: `w` lies in `C`, as the point `x = 0`.
- `mul_mem_twoBlockCell`: `C` is invariant under left multiplication by `P`.
- `mul_mem_twoBlockCell_iff`: for `q ∈ P`, `q * g ∈ C ↔ g ∈ C`.

## The induced representation and its restriction

The second section fixes complex vector spaces `V₁ V₂ : Type uV` and arbitrary
complex representations `π₁` of `GL_A(F)` and `π₂` of `GL_B(F)`. No smoothness,
admissibility, irreducibility or Whittaker hypothesis is needed for these
definitions. Both spaces live in one universe `uV` because
`Shahidi.pairCarrier V₁ V₂` is a family `Fin 2 → Type uV`. The field universe
`uF` remains independent. The parent statement places its two carriers in
separate universes and lifts them with `ULift` to a common universe, so it can
use these definitions after lifting.

- `twoBlockInduced F a b π₁ π₂` is literally
  `F.canonicalNormalizedProductInduced (twoBlockShape a b) (Shahidi.pairFamily π₁ π₂)`.
  This is the ordered representation `ξ` of the parent statement, and
  `twoBlockInduced_eq` records this definition with `Shahidi.twoBlocks` spelled
  out.
- `twoBlockInducingRepresentation F a b π₁ π₂` is the actual representation of
  `P` that is being induced. It is the block tensor product of `π₁` and `π₂`,
  composed with the Levi projection of `P` and twisted by the positive half
  modulus `F.canonicalTopologicalData.parabolicHalfModulus`. Its value space is
  `PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)`, which is the source's
  `V₁ ⊗ V₂`.
- `TwoBlockInducedCarrier F a b π₁ π₂` is the actual carrier of `ξ`, the space
  `Induction.SmoothFunctions P (twoBlockInducingRepresentation …)` of
  left-covariant functions with an open right stabilizer for the canonical
  topology.
- `twoBlockEval F a b π₁ π₂ f g` is `Induction.eval P (twoBlockInducingRepresentation …) f g`.
  The lemma `twoBlockEval_eq` states this. By `twoBlockEval_twoBlockInduced`,
  `ξ(h)` acts by right translation, `f ↦ (g ↦ f(g h))`. Both lemmas hold by
  definition.
- `twoBlockRestriction F a b π₁ π₂` is the complex-linear map from the carrier
  of `ξ` to all functions `Matrix (Fin B) (Fin A) F → V₁ ⊗ V₂`. It sends
  `f` to `x ↦ f(w n(x))`. The lemma `twoBlockRestriction_apply` writes this
  value literally as
  `Induction.eval P ρ f (blockWeyl * intertwiningUnipotent x)`.

## The support submodule `D`

`twoBlockCellSubmodule F a b π₁ π₂` is the complex submodule `D` of the
carrier of `ξ` whose elements `f` satisfy both of the following conditions:

1. the support of the actual function `g ↦ f(g)` on `GL_{A+B}(F)` is
   contained in `C`;
2. the restriction `x ↦ f(w n(x))` has compact support for the canonical
   topology on matrices.

The second condition uses Mathlib's `HasCompactSupport`, and the first uses
`Function.support`. Neither condition needs an extra hypothesis. The proofs
that `D` contains zero and is closed under addition and scalar multiplication
are the fields of the submodule structure. They use `Function.support_add`,
`Function.support_const_smul_subset`, `HasCompactSupport.add` and
`HasCompactSupport.mono`.

`mem_twoBlockCellSubmodule_iff` states the membership characterization
exactly as the task asks:
`(∀ g, Induction.eval P ρ f g ≠ 0 → g ∈ C) ∧ HasCompactSupport (fun x => Induction.eval P ρ f (blockWeyl * intertwiningUnipotent x))`.

The remaining declarations are the maps and consequences of membership.

- `twoBlockCellInclusion` is the linear inclusion `D → ξ`, namely the
  submodule's `subtype`. `twoBlockCellInclusion_apply` and
  `twoBlockCellInclusion_injective` give its value and injectivity.
- `twoBlockCellRestriction` is the restriction map on `D`: the restriction
  composed with the inclusion. `twoBlockCellRestriction_apply` evaluates it.
- `twoBlockEval_eq_zero_of_not_mem`: an element of `D` vanishes off `C`.
- `hasCompactSupport_twoBlockCellRestriction`: the restriction of an element
  of `D` has compact support.

The module defines no structure or class whose fields assume openness,
uniqueness of coordinates, existence of sections or stability. It does not
modify the parent statement module
`Langlands.Representation.Whittaker.TwoBlockExtensionStatement` or anything
that module imports.

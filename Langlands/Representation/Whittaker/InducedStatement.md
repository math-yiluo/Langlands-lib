# Whittaker type of representations induced from block parabolics

Author: Worker 11. This file defines two proposition targets and their
conjunction. None of them is a proof, and none is assumed anywhere.

Both targets concern a p-adic field `F` with its canonical local-field
topology and the matrix-unit topology on `GL_{n+1}(F)`, with its proved
topological-group structure. The data are:

- an ordered block shape `B` of `n + 1` (positive block sizes `B.size i`);
- for each block a complex representation `π i` of `GL_{B.size i}(F)` on
  `V i`, all carriers in one universe `uV`.

The induced representation is the published right-translation construction
`Induction.smoothInduced`. It acts on smooth functions on `GL_{n+1}(F)` that
are left covariant for the actual upper block parabolic `B.parabolic`. The
action of the parabolic is the published external tensor product
`FiniteTensor.external π`, composed with the actual diagonal-block projection
`B.leviProjection`. This is exactly the induction used by the published
group-side targets, for example `Parabolic.InductionAdmissibilityClause`.
Both targets cover every positive rank, and the field universe `uF` is
independent of `uV`.

## `InducedFiniteTypeStatement`

If every `π i` is admissible and finitely generated over its group algebra,
then the induced representation is finitely generated over the group algebra
of `GL_{n+1}(F)`. This is the assertion "π is again admissible of finite
type" of JPSS (1983), Section 2.3, printed page 386, restricted to finite
type. Admissibility of induction is already the published target
`Parabolic.InductionAdmissibilityClause` and is not restated here.

## `InducedWhittakerTypeStatement`

Same hypotheses, together with a continuous, nontrivial, unitary additive
character `ψ`. The statement uses the following conditions:

- `unipotent d g`: `g ∈ GL_d(F)` is upper unitriangular;
- `θ d g = ∏_a ∏_b (if b = a + 1 then ψ(g_{a,b}) else 1)`, that is,
  `∏_a ψ(g_{a,a+1})`. This is the standard character `θ_{ψ,d}` of JPSS
  (1983), printed page 377, written without index arithmetic so that it
  applies to every block size;
- a functional `ℓ` is equivariant when `ℓ(ρ(g)v) = θ(g) ℓ(v)` for every
  unitriangular `g`, which is condition (2.1)(1) of JPSS, printed page 385.

The conclusion is an equivalence. The induced representation has a nonzero
equivariant functional of which every equivariant functional is a multiple
(`dim V*_θ = 1`) if and only if every block representation has such a
functional. This is the Proposition attributed to Rodier in JPSS (1983),
Section 2.3, printed page 387: "π satisfies condition (2) if and only if each
π_i does also". The source refers to Rodier [F.R.] for the proof; that paper
is not a registered source here.

## Agreement with the source's induction

In JPSS, `π = Ind(G, Q; π_1, …, π_j)` uses a *lower* standard parabolic `Q` of
type `(r_1, …, r_j)` (Section 2.3; Section 0.3, printed page 375, defines
standard parabolics as upper block triangular and `Q̄ = ᵗQ` as the lower ones).
It also uses the normalized covariance `f(hg) = δ_H^{1/2}(h) δ_G^{-1/2}(h) σ(h) f(g)`
of display (9) and the tensor-product action of display (11), printed
page 377. The upper, unnormalized formulation above states the same family
of equivalences, for the following reasons.

- Normalization. `GL_r(F)` is unimodular. The restriction of `δ_Q^{1/2}` to
  the Levi is `∏_i |det g_i|^{c_i}` for real constants `c_i`. Normalized
  induction from `(π_i)` is therefore unnormalized induction from
  `(π_i ⊗ |det|^{c_i})`. Twisting by a character of `GL_{r_i}(F)` preserves
  admissibility and finite type. It also preserves the equivariant
  functionals, because `|det|` is trivial on unitriangular matrices.
- Lower versus upper. Conjugation by the long Weyl element `w_r` maps the
  lower parabolic of type `(r_1, …, r_j)` onto the upper parabolic of type
  `(r_j, …, r_1)`. It maps the Levi block `g_i` to `w_{r_i} g_i w_{r_i}` and
  carries the modulus character along. Left translation `f ↦ f(w_r ·)`
  therefore identifies the lower induction from `(π_1, …, π_j)` with the upper
  induction from `(π_j ∘ Ad w_{r_j}, …, π_1 ∘ Ad w_{r_1})`, and
  `π_i ∘ Ad w_{r_i} ≅ π_i` through `π_i(w_{r_i})`. Both conditions in the
  equivalence are invariant under equivalence and do not depend on the order
  of the blocks.

Since `B` ranges over all ordered compositions and the `π i` over all
admissible representations of finite type, the targets range over exactly
the source's family.

## Family declaration

`InducedWhittakerPrerequisitesStatement` is the conjunction of the two
targets at the same universes `uF` and `uV`. It adds no hypothesis or
conclusion.

## Source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin--Selberg
Convolutions*, Amer. J. Math. 105 (1983), 367-464; registered source
`jpss-1983-rankin-selberg`. Retained file
`C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 375, 377, 385, 386 and 387 (PDF pages 10, 12, 20, 21 and 22)
were read visually.

## Dependencies

Published project imports: `Langlands.Group.GL.Blocks` (block shapes,
parabolics, Levi projection), `Langlands.Group.GL.Padic` (canonical
topological-group structure), `Langlands.Representation.Induction.Definitions`
(smooth induction) and `Langlands.Representation.Tensor.Finite` (external
tensor product). Everything else comes from Mathlib.

# Natural compact induction in stages

Worker 777 states
`Langlands.Induction.CompactInductionTransitivityStatement.{uG,uV}`.
This is a proposition definition and a target for a separate proof.
Defining it does not assume its truth.

## Hypotheses

Let `G : Type uG` be a group with a topology, with `IsTopologicalGroup G`
and `T2Space G`. The proposition takes the explicit compact-open subgroup
neighborhood basis

`∀ O : Set G, IsOpen O → 1 ∈ O → ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O`.

This hypothesis and Hausdorffness are copied from
`Langlands.Induction.StructuralStatement`. Let `H` and `P` be subgroups of `G`
with `IsClosed (H : Set G)`, `IsClosed (P : Set G)` and `hHP : H ≤ P`.
Write

- `H_P = H.subgroupOf P`, Mathlib's subgroup of `P` whose elements are the
  `p : P` with `(p : G) ∈ H`;
- `φ = (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom : H_P →* H`. This is
  Mathlib's canonical isomorphism `H.subgroupOf P ≃* H`, viewed as a
  homomorphism. In `G` it does nothing: `((φ x : H) : G) = ((x : P) : G)`.

In Lean, `φ` is a `let` binding inside the proposition. `P` and `H_P` carry
Mathlib's subgroup topologies.

For every object `A` of the full category
`Langlands.SmoothRep.{0,uG,uV} ℂ H`, write `rho = A.representation`, and
write `rho_P = rho.comp φ` for its restriction to `H_P`. This is exactly the
`rhoP` of the existing `InductionTransitivityClause`. The objects of the
category are all smooth complex `H`-representations whose carrier lies in
`Type uV`, and its morphisms are all intertwiners between them.

## Conclusion

The proposition asserts the existence of one family

`e A : Representation.Equiv
  (compactInduced P (compactInduced H_P rho_P)) (compactInduced H rho)`,

indexed by the objects `A`. Each `e A` is an actual Mathlib
`Representation.Equiv` of `G`-representations. So it is complex-linear,
bijective and `G`-equivariant. The family satisfies two conjuncts.

1. The evaluation formula. For every `A`,
   `F : CompactFunctions P (compactInduced H_P rho_P)` and `x : G`,

   `eval H rho (e A F).val x =
     eval H_P rho_P (eval P (compactInduced H_P rho_P) F.val x).val 1`.

   That is, `(e A F)(x) = F(x)(1)`.

2. Naturality. For all objects `A`, `B`, every morphism `T : A ⟶ B` and every
   `F` as above,

   `e B (compactInducedMap P
      (compactInducedMap H_P (restrictAlongMap φ (SmoothRep.hom T))) F)
     = compactInducedMap H (SmoothRep.hom T) (e A F)`.

   The left side applies postcomposition at both stages: first at the inner
   stage, with `SmoothRep.hom T` restricted along `φ`, and then at the outer
   stage. The right side is postcomposition by `SmoothRep.hom T` on direct
   compact induction from `H`.

The group universe `uG` and the coefficient universe `uV` are independent.
Induced functions on `G` with values in `Type uV` lie in `Type (max uG uV)`.
The nested carrier is again `Type (max uG uV)`.

The proposition has no further premise. It assumes no admissibility, finite
dimension or finite length. It does not assume that `H \ G` or `P \ G` is
compact, that `H` or `P` is open or normal, or a supplied comparison map. It
also assumes no surjectivity, kernel, support-preservation or section
hypothesis. The existence of the maps, their bijectivity and their
equivariance are asserted, not assumed.

## Conventions of the imported construction

All three compact inductions are the published `compactInduced`. Their
carriers are the published `CompactFunctions`. For a subgroup `Q` of an
ambient group and a `Q`-representation `sigma`, an element is a function `f`
with

- left covariance `f(q*y) = sigma(q)(f(y))` for `q` in `Q`;
- one open subgroup `K` of the ambient group with `f(y*k) = f(y)` for every
  `y` and every `k` in `K`, uniform for the whole function;
- compact projected nonzero support in the right-coset space `Q \ ambient`.
  This space is `Quotient (QuotientGroup.rightRel Q)` with the quotient
  topology.

The action is right translation, `(g*f)(y) = f(y*g)`.

The outer space consists of functions `F` on `G` with values in the inner
compact induced space. Its covariance says that `F(p*x)` is the right
translate by `p` of `F(x)` in `compactInduced H_P rho_P`. Its value `F(x)` is
itself a function on `P`, with covariance under `H_P` for `rho_P` and with
compact projected support in `H_P \ P`. Both uniform stabilizers and both
support conditions are part of the imported definitions; the statement
neither weakens nor repeats them. `eval` returns the underlying value of a
function, and `compactInducedMap` is postcomposition.

The evaluation formula determines each `e A`, since an element of
`CompactFunctions H rho` is determined by its values. By covariance of `F`,
`F(x)(p) = F(p*x)(1)` for `p` in `P`. Hence the inverse of `e A` necessarily
sends `f` to `x ↦ (p ↦ f(p*x))`. This is a remark on the formula; the
inverse is not a separate conjunct.

## Original source and specialization

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- Retained PDF:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
- SHA-256:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8, printed pages 444–445 (PDF pages 5–6), was read and visually
checked. It defines `I_{U,θ}` and `i_{U,θ}` for closed subgroups `M`, `U` of
an `l`-group `G` with `P = MU` closed. The functions satisfy
`f(umg) = θ(u) mod_U^{1/2}(m) ρ(m)(f(g))` and have one open subgroup `K_f`
with `f(gk) = f(g)`. The action is `(δ(g)f)(g') = f(g'g)`. Compact induction
uses the functions compactly supported modulo `P`. Page 445 notes that for
`U = {e}` these are ordinary induction without any factor.

Section 1.9, Proposition (c), printed page 445 (PDF page 6), was read and
visually checked. For subgroups `N`, `V` of `M` and a character `θ'` of `V`,
it states `i_{U,θ} ∘ i_{V,θ'} = i_{U°,θ°}` with `U° = UV` and
`θ°(uv) = θ(u)θ'(v)`. The source proves (c) by reference to its [1],
chapter I.

Specialize both unipotent subgroups `U` and `V` to the trivial group and both
characters to the trivial character. Then `U° = {e}`, every modulus factor is
one, and every functor is unnormalized compact induction. The source's
`M` is this file's `P`. Its `N` is `H`, viewed inside `P` as `H_P`. Its `G`
is `G`. Then (c) reads `c-Ind_P^G ∘ c-Ind_{H_P}^P = c-Ind_H^G`. Restricting
coefficients along `φ` identifies `H`-representations with
`H_P`-representations. Section 1.1, printed page 442 (PDF page 3), defines
an `l`-group as a Hausdorff topological group in which every neighbourhood of
the identity contains an open compact subgroup. That is the ambient
hypothesis here. The closedness requirement of 1.8 on the inducing subgroups
is retained for `H` and `P`.

The source equality of functors denotes a natural isomorphism and prints no
formula. Evaluation at the inner identity, `(e F)(x) = F(x)(1)`, is the
formula of the existing `InductionTransitivityClause`. It fixes the usual
equivalence and its orientation, from nested to direct induction.

Explicit categorical naturality is an internal packaging consequence of the
evaluation formula; it is not separately printed in the source. At `x`, both
sides of conjunct 2 have the value `T(F(x)(1))`, and functions in
`CompactFunctions H rho_B` are determined by their values.

No project errata apply. The Library at commit
`61f87bbe6fe6e5ffe1387e9640956e5d8d8c9fc5` contains no errata note for this
source. Its smooth-representations audit note, whose registered originals
include this source, likewise found no `notes/errata/<source-id>.md` file at
its checked snapshot.

## Relation to existing statements

`Langlands.Induction.InductionTransitivityClause` in
`Langlands.Representation.Induction.StructuralStatement` has a compact second
conjunct. For one smooth `rho` it asserts an equivalence with the same
evaluation formula. The present proposition fixes the ambient hypotheses of
`StructuralStatement`, quantifies `P` and `H` together, and asks for one
family of equivalences over all objects of the smooth category. Conjunct 1
for an object `A` is that compact conjunct's formula for
`rho = A.representation`. Conjunct 2 adds naturality in every intertwiner.
The proposition states no smooth-induction equivalence; that is the other
conjunct of the clause.

The published `Langlands.Parabolic.normalizedRefinementInductionTransitivity`
in `Langlands.Representation.Parabolic.RefinementInductionTransitivityProof`
covers normalized smooth induction for parabolic refinements. It is a different
result and is not duplicated here.

This pair does not prove compact transitivity. It does not prove the parent
geometric comparison either.

## Proof obligations for the separate proof

This section describes the intended proof route. It is provenance only and is
not an input to the statement.

The proof must show that `x ↦ F(x)(1)` and `f ↦ (x ↦ (p ↦ f(p*x)))` land in
the actual compact function spaces. For both maps it must establish
compactness of projected support in each direction. These facts are not
premises.

Covariance and the uniform stabilizers are direct.
For `x ↦ F(x)(1)`, covariance under `h ∈ H` uses `F(h*x) = h · F(x)` and the
`H_P`-covariance of `F(x)`. For `f ↦ (x ↦ (p ↦ f(p*x)))`, the inner stabilizer
of `p ↦ f(p*x)` is the open subgroup `P ∩ x K_f x⁻¹` of `P`.

For support, a compact subset of a coset space should be lifted to a compact
subset of `G`. This uses local compactness, which follows from the
compact-open basis, and openness of the quotient map. The uniform stabilizer
shows that `F` takes only finitely many values on a compact set. Closedness
of `P` gives compactness of `C x⁻¹ ∩ P` for compact `C`. Projected supports
are closed, by the imported construction.

## Imported constructions

`Langlands.Representation.Induction.Definitions` supplies `CompactFunctions`,
`compactInduced`, `eval` and `compactInducedMap`. It imports
`Langlands.Representation.Category.Basic`, which supplies the full smooth
category `Langlands.SmoothRep`, `SmoothRep.representation` and
`SmoothRep.hom`. `restrictAlongMap` is imported by Lean name from
`Langlands.Representation.Induction.SplitQuotientStatement`. It is the same
linear map as an intertwiner between restrictions along a group homomorphism.
That module also imports `Mathlib.Basic.Complex.Basic`, which supplies `ℂ`.
Mathlib supplies `Subgroup.subgroupOf`, `Subgroup.subgroupOfEquivOfLe`,
`MulEquiv.toMonoidHom`, `Representation.comp` and `Representation.Equiv`.

This file introduces no helper definition, function space, quotient model or
subgroup. Every imported Lean/Markdown pair is preserved unchanged.

## Development check

The pair compiled in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
with no errors or warnings. Declaration inspection reported level parameters
`uG` and `uV` and `statement_returns_prop: true`. Its axioms were exactly
`propext`, `Classical.choice` and `Quot.sound`. This is development evidence;
independent semantic review and publication are separate.

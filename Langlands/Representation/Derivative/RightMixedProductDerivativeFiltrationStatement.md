# The actual right mixed-product derivative filtration

This module defines, but does not prove,
`Langlands.Derivative.RightMixedProductDerivativeFiltrationStatement`.
It states Bernstein–Zelevinsky 4.14(b) for the actual right mixed product,
with an actual natural filtration, explicit feasible indices, and the
Library's arbitrary-carrier rank-zero extension. The field universe `uF`
and representation carrier universe `uV` are independent.

## Original source and correspondence

The registered original is Bernstein and Zelevinsky, *Induced representations
of reductive p-adic groups I*, Annales scientifiques de l'École Normale
Supérieure (4) 10 (1977), 441–472, literature ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The relevant passages were read directly: §§1.8–1.11, printed pp.444–445
(one-based PDF pp.5–6); §§3.1–3.5, printed pp.450–452 (PDF pp.11–13);
and §§4.12–4.14, printed pp.456–458 (PDF pp.17–19). The page images for
normalization, the case (III) diagram and Corollary 4.14 were inspected.
A bounded filename search in the project notes, supplied Library notes and
literature Markdown found no BZ77-specific errata entry. This records the
search's extent, rather than asserting that no errata exist.

Corollary 4.14(b), printed p.458, says that for positive order `d`,
`(τ × ρ)^(d)` is glued from `τ^(j) × ρ^(d-j)` for `j=1,…,d`.
The source's beyond-rank zero convention removes precisely the pairs with
`j > r+1` or `d-j > k` when `τ` is on `P_(r+1)` and `ρ` is on `GL_k`.
Thus the finite indexing here retains exactly `1 ≤ j ≤ r+1`, `t ≤ k`,
`j+t=d`. A feasible representation which happens to be zero is retained.
Distinct indices with isomorphic grades are retained separately.

Section 1.10 describes actual subfunctors preserved by every morphism.
Section 1.11 defines gluing using a finite filtration and its successive
quotients up to permutation. Proposition 4.13 explicitly makes its maps
functorial; 4.14 derives its gluing from those natural maps. Accordingly,
the proposition here concerns a filtration of the bifunctor in both input
representations, with natural isomorphisms of its actual quotient functors.
It has no finite-length or admissibility restriction.

Section 3.5 defines a positive mirabolic derivative by successive `Φ⁻`
followed by `Ψ⁻`. Section 4.3 defines the general-linear derivative by first
restricting to the mirabolic subgroup; its order zero is the identity.
Library `mirabolic r F.Carrier` is source `P_(r+1)`, and the full mixed
source is `P_(k+r+1)`. No `P_0` or order-zero mirabolic derivative is used.
The imported order wrapper in `Derivative.Homogeneity` supplies these actual
changing-rank functors; no homogeneity assertion is used.

## Normalization, topology and carriers

Every construction has `{p : ℕ} [Fact p.Prime]`, the supplied
`F : PadicField.{uF} p`, `T : F.TopologicalData`, and the supplied bundled
continuous nontrivial additive character `ψ`. It installs `T.topology`.
Both input carriers are in `Type uV`, with no equality between `uF` and `uV`.
The mixed product and binary induction have carrier universe `max uF uV`;
the resulting derivative and final `Rep` retain that universe.

`T.rightMixedProductFunctor k r` is the actual case (III) construction
of §4.12: compact induction of the external tensor representation pulled
back along the actual right inducing subgroup's projection. Its input is
`(B,A)`, with `B` on `P_(r+1)` and `A` on `GL_k`. It retains case (III)'s
extra `ε(p,a)=ν_k(a)^(-1/2)`. In the published implementation the total
character is

```text
ν_r(projection p)^(k/2) · ν_k(a)^(-(r+1)/2),
```

and `rightLeviCharacter_eq_mul` factors this as the rectangle half-character
times `rightEpsilonCharacter`. The source helper uses that published functor
literally. The piece uses the published determinant inverse-half normalized
minus/derivative functors and the actual binary normalized induction.
No new twist or comparison model replaces them. Comparing all explicit
determinant characters with original Haar-modulus normalizations remains
part of the eventual theorem proof; this statement supplies no such theorem.

There are no admissibility, irreducibility, finite length, finite dimension,
genericity, chosen-vector, canonical-topology or universe-saturation
hypotheses. The main proposition has no theorem-valued premise.

## Concrete indices and boundary lemmas

`rightMixedDerivativeIndices k r d` filters `Finset.antidiagonal d` by
`1 ≤ j`, `j ≤ r+1`, and `t ≤ k`.
`mem_rightMixedDerivativeIndices` proves the exact membership equivalence
with those inequalities and `j+t=d`. The named lemmas
`rightMixedDerivativeIndices_left_pos`, `_left_le`, `_left_bound`,
`_right_le`, and `_sum` expose the required facts. The rank lemma
`rightMixedDerivativeIndices_rank` proves

```text
(r+1-j)+(k-t) = (k+r)+1-d.
```

`RightMixedDerivativeIndex` is the finite subtype of this concrete set.
The membership proof unfolds the antidiagonal and filter; the bound and sum
lemmas project the resulting conjunction; the rank proof uses natural-number
arithmetic with both subtraction bounds. These helpers are internal packaging
of the source's feasible derivative orders.

The three singleton descriptions are proved by membership extensionality
and natural-number arithmetic:

- `rightMixedDerivativeIndices_zero_gl`: for `0<d≤r+1`, `k=0` leaves `(d,0)`.
- `rightMixedDerivativeIndices_zero_mirabolic`: for `0<d≤k+1`, `r=0` leaves
  `(1,d-1)`.
- `rightMixedDerivativeIndices_top`: order `(k+r)+1` leaves `(r+1,k)`.

For positive `k` the assertion is the printed right mixed-product statement,
including `P_1` as the first factor when `r=0`. For `k=0`, the assertion
extends it using the actual tensor and localization quotient constructions.
The input `A` is an arbitrary smooth `GL_0` representation. The right mixed
product then retains its carrier as a tensor factor; it is not identified
with the tensor unit. Commuting positive derivatives past this tensor factor
requires a later algebraic proof, including the quotient comparisons and
naturality. The already constructed unit isomorphisms for a specifically
chosen one-dimensional unit do not establish this arbitrary-carrier case.

At top order the target group is `GL_0`. Its unique piece retains the
binary product of both actual top-derivative carriers. Neither carrier is
assumed one-dimensional. For `k=r=0`, all three singleton descriptions
coincide at `d=1`.

## Literal source and piece functors

`rightMixedDerivativeSource T ψ k r d hd` is definitionally

```lean
T.rightMixedProductFunctor k r ⋙
  mirabolicDerivativeOfOrder T ψ (k+r) d hd ⋙ SmoothRep.toRep
```

It has source
`SmoothRep.{0,uF,uV} ℂ (mirabolic r F.Carrier) ×
 SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier)` and target
`Rep.{max uF uV} ℂ (GeneralLinear ((k+r)+1-d) F.Carrier)`.
`rightMixedDerivativeSource_obj` evaluates it at `(B,A)` to the literal
derivative of the literal mixed product; its proof is `rfl` after introducing
the supplied topology and objects.

For `x=(j,t) : RightMixedDerivativeIndex k r d`, the concrete helper
`rightMixedDerivativePiece T ψ k r d x` is definitionally

```lean
(mirabolicDerivativeOfOrder T ψ r j hj).prod
    (generalLinearDerivative T ψ k t ht) ⋙
  T.binaryNormalizedProductFunctor (r+1-j) (k-t) ⋙
  generalLinearRankCast T hrank ⋙ SmoothRep.toRep
```

Here `hj`, `ht` and `hrank` are the named index lemmas above. The grade order
is `B^(j) × A^(t)`. `rightMixedDerivativePiece_obj` exposes exactly that
object value and is proved by `rfl`. The published smooth
`generalLinearRankCast` transports the rank before `SmoothRep.toRep`;
there is no separate transport of `Rep` objects.

## Main proposition and conditional extractor

`RightMixedProductDerivativeFiltrationStatement.{uF,uV} F T` quantifies over
every supplied character `ψ`, all `k,r,d : ℕ` and every proof
`hd : 0<d ∧ d≤(k+r)+1`. It asserts an equivalence

```text
e : Fin (rightMixedDerivativeIndices k r d).card ≃
      RightMixedDerivativeIndex k r d
```

and `IsGluedFrom` for the literal source and pieces enumerated by `e`.
The equivalence enumerates every feasible index exactly once. The additional
permutation permitted by `IsGluedFrom` imposes no canonical order.

Unfolding that relation gives an actual `RepFunctorFiltration`: `n+1`
increasing invariant submodules of the source at every object, beginning at
zero and ending at the full source, preserved by every map in the product
category. Each graded functor is the actual quotient of the next submodule
by its predecessor, with the induced maps. Its identifications with the pieces
are natural functor isomorphisms. Repeated filtration steps and zero grades
are allowed. Neither a representation-ring identity nor an objectwise list
replaces this data.

`RightMixedProductDerivativeFiltrationStatement.filtration` takes the main
proposition as a hypothesis and extracts the actual filtration, the complete
enumeration and all natural graded isomorphisms. Its proof unpacks the
existential witnesses and composes the gluing permutation with `e`.
The finite local heartbeat increase affects elaboration only. This conditional
extractor does not prove the main proposition.

## Proof arrangement and independence boundary

The main assertion remains unproved. BZ77 printed p.458 derives 4.14(a) from
4.13(b), 4.14(b) from (a) and 4.13(c), and 4.14(c) from (a), (b) and 4.13(a).
A later exact proof must establish the actual natural short exact sequences,
minus compatibility, derivative exactness, tensor/localization comparisons
and finite filtration refinement with all feasible indices. Only independently
accepted and published proofs may supply those mathematical inputs.

The separate coordinated tasks for natural filtration splicing/refinement
and exact smooth-functor transport supply no assumed result in this pair.
The proposed theorem is
`Langlands.Derivative.rightMixedProductDerivativeFiltration`, in
`Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof`,
with exact target this unchanged Library proposition. Its task is arranged
only after statement acceptance and publication, and must preserve all
upstream restrictions from this statement's task.

The new proof bodies depend only on finite-set membership, conjunction
projections and natural-number arithmetic, reflexivity of the actual composed
functors, and unpacking the actual gluing definition. In particular:

- No segment derivative, individual segment head/socle existence, Jacquet
  formula, linked or unlinked product structure, commutation, gluing or
  irreducibility criterion supplies any helper proof.
- No special-head criterion, generic product uniqueness, ordered head/socle
  existence, exhaustion, quotient coverage, ordered conversion, tempered
  uniqueness, analytic or square-integrable classification, or special
  square-integrability conclusion is used.
- No two-supercuspidal product criterion or product-structure conclusion is
  used; there is no assumption of a BZ77 derivative theorem or a Ze80 segment
  derivative formula.
- No irreducible, supercuspidal, single-block or Levi Whittaker coinvariant
  finiteness result, nor a mirabolic finite-length proof depending on such a
  result, is used. This includes the all-character and degenerate-character
  consumer conclusions. Their pending statements and tasks provide no proof.

These observations audit the present constructions and elementary helpers.
They do not certify a future proof's transitive dependencies. That proof and
every prerequisite must record their own condition-by-condition audit against
all exclusions in the task, including every listed successor and downstream
consequence, and verify independent proof acceptance and Library publication.

## Actual project import closure

The direct project imports are `Derivative.Homogeneity`,
`Mirabolic.MixedProducts` and `Filtration.Definitions`; the direct Mathlib
import is `Mathlib.Data.Finset.NatAntidiagonal`. At authoring, the entry imports
the following 74 project modules transitively, with names relative to
`Langlands`. Every imported Lean/Markdown pair was compared with the supplied
Library and remains unchanged.

```text
Group.GL.Basic
Group.GL.BlockModulus
Group.GL.Blocks
Group.GL.Mirabolic
Group.GL.MirabolicMixedProductSubgroups
Group.GL.MirabolicOppositeIntersection
Group.GL.MirabolicProjection
Group.GL.MirabolicRadical
Group.GL.Nonarchimedean
Group.GL.NonarchimedeanStatement
Group.GL.NormalizedCharacter
Group.GL.OppositeBlocks
Group.GL.Padic
Group.GL.PadicBlocks
Group.GL.RankMaps
Group.GL.RankReindex
Group.GL.UpperUnipotent
HarmonicAnalysis.Basic
LocalField.Canonical
LocalField.Definitions
LocalField.Normalization.Definitions
LocalField.Normalization.Proof
LocalField.Normalization.Statement
LocalField.Topology
Representation.Category.Basic
Representation.Category.Subquotients
Representation.Category.Twist
Representation.Derivative.Homogeneity
Representation.Derivative.Iteration
Representation.Derivative.MirabolicCharacter
Representation.Derivative.MirabolicMinus
Representation.Dual.Definitions
Representation.Filtration.Definitions
Representation.Induction.BinaryProduct
Representation.Induction.BlockFactors
Representation.Induction.Definitions
Representation.Induction.Parabolic
Representation.Jacquet.Coinvariants
Representation.Jacquet.Localization
Representation.Jacquet.PositiveCharacter
Representation.Jacquet.SmoothTwist
Representation.MatrixCoefficient.Definitions
Representation.MatrixCoefficient.LawsProof
Representation.MatrixCoefficient.LawsStatement
Representation.Mirabolic.MixedProducts
Representation.Smooth.Admissibility.CofinalProof
Representation.Smooth.Admissibility.CofinalStatement
Representation.Smooth.Definitions
Representation.Smooth.SmoothPart.BasicProof
Representation.Smooth.SmoothPart.BasicStatement
Representation.Smooth.SmoothPart.Definitions
Representation.Smooth.Transfer.PullbackProof
Representation.Smooth.Transfer.PullbackStatement
Representation.Smooth.Transfer.SubquotientProof
Representation.Smooth.Transfer.SubquotientStatement
Representation.Tensor.Finite
Representation.Tensor.OneFactor
Representation.Twist.AdmissibilityProof
Representation.Twist.AdmissibilityStatement
Representation.Twist.AlgebraProof
Representation.Twist.AlgebraStatement
Representation.Twist.ContinuousCharacterProof
Representation.Twist.ContinuousCharacterStatement
Representation.Twist.Definitions
Representation.Twist.RealPower
Representation.Twist.SmoothProof
Representation.Twist.SmoothStatement
Representation.Twist.SubquotientDefinitions
Representation.Twist.SubquotientProof
Representation.Twist.SubquotientStatement
Representation.Whittaker.Algebraic
Representation.Whittaker.GeneralLinear
Topology.CompactNormCharacter
Topology.Nonarchimedean.Subgroup
```

The closure consists of local-field, matrix-group, smooth-category, twist,
tensor, actual induction, coinvariant/localization, elementary character and
filtration infrastructure. `Derivative.Homogeneity` includes the actual order
wrapper and elementary maximum/subrepresentation helpers; none of its
homogeneity predicates is assumed. `Tensor.Finite` occurs through
`Induction.BlockFactors`, but the assertion imposes no finite-dimensional
carrier condition. `Whittaker.GeneralLinear` and `Whittaker.Algebraic` provide
characters, functionals and models and elementary laws, with no Whittaker
finiteness conclusion. `Topology.CompactNormCharacter` proves triviality of
positive continuous characters on compact subgroups; its historical
`RankinSelberg.LastRowReduction` namespace imports no Rankin–Selberg consumer.
A bounded scan of the complete project Lean closure found no reference to the
explicitly excluded consumer declaration names. No segment, classification,
cuspidal-support or Whittaker-finiteness module occurs in the closure.

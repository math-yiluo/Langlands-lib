# Scalar uniqueness of compact-to-smooth mirabolic intertwiners

Author: Worker 719. Worker 658 supplied the target specification and the
source route.

`Langlands.Whittaker.MirabolicCompactHomScalarStatement.{uF}` is a
proposition target for the p-adic specialization of Bernstein–Zelevinsky
(1976), Proposition 5.15(b), printed p.49, with its proof on printed p.50.
This module only states the proposition. It does not prove it, and it does
not assume it as an axiom.

## Exact statement

The proposition quantifies over every prime through
`(p : ℕ) (_hp : Fact p.Prime)` and over every `F : PadicField.{uF} p`. It
then installs `F.canonicalTopologicalData.topology` and quantifies over
every `n : ℕ`, every
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`, and every

```lean
A : (Whittaker.mirabolicCompactInduced ψ n).IntertwiningMap
  (Whittaker.mirabolicSmoothInduced ψ n)
```

Its conclusion is

```lean
∃ c : ℂ, A = c • Whittaker.mirabolicCompactInclusion ψ n
```

All of these quantifiers are inside the proposition definition. The field
universe `uF` is arbitrary. The coefficients are ℂ. The two function
carriers are the ones already constructed by `MirabolicModels`; this
module introduces no other representation carrier and no other universe.
`IntertwiningMap` is Mathlib's `Representation.IntertwiningMap`: a
ℂ-linear map that commutes with the actions of the actual mirabolic group.
The scalar action on intertwining maps is Mathlib's pointwise action. For
every compact function `f`, `(c • mirabolicCompactInclusion ψ n) f` is
definitionally `c • f.val`. The scalar `c` may be zero, which covers the
zero intertwiner.

The proposition makes no claim that `c` is unique. It has no hypothesis
that `A` is nonzero. It supplies no equivalence or embedding. It assumes no
irreducibility, admissibility, finite generation, derivative or Kirillov
property, and no minimality property. The bundled additive character
already includes continuity, nontriviality and values in the unit circle.

An internal `letI` derives `IsTopologicalRing F.Carrier` by typeclass
inference from the published canonical valuative relation and local-field
certificate. This certificate belongs to the selected canonical topology
and is needed to instantiate the models. It is not a quantified instance
or an extra mathematical hypothesis. The topology and the order of the
quantifiers are the same as in
`Langlands.Whittaker.MirabolicCompactMinimalityStatement`.

## Source correspondence and model conventions

BZ76 §5.1, printed p.44, defines the mirabolic group `P = P_r`. Its
matrices have last row `(0, …, 0, 1)`. Inside it is the full upper
unitriangular group `U = U_r`. Here `r = n + 1`. These groups are the
published `GeneralLinear.mirabolic n F.Carrier`, which is the subgroup of
`GL(n + 1)` with that last row, and
`GeneralLinear.Mirabolic.upperUnipotent n F.Carrier`, both with their
actual matrix topology.

BZ76 §5.5, printed p.45, writes every character of `U` as
`θ(a₁, …, a_{r−1})(u) = ψ₀(∑ aᵢ uᵢ,ᵢ₊₁)`. Section 5.6 fixes the
nondegenerate character `Θ = θ(1, …, 1)`. The published
`mirabolicCharacter ψ n` is exactly this positive adjacent-entry
character, with `ψ` in place of `ψ₀`. By the additive-character law the
sum becomes the product of the adjacent-entry values, and
`mirabolicCharacter_eq_product` certifies this product form. No sign and
no rescaling of the entries is inserted.

BZ76 §5.7, printed p.45, defines the standard representation
`τ_P = Ind(P, U, Θ)` on `L(P, Θ)` and the compact standard representation
`τ_P⁰ = ind(P, U, Θ)` on `S(P, Θ) ⊂ L(P, Θ)`. These are
`Whittaker.mirabolicSmoothInduced ψ n` and
`Whittaker.mirabolicCompactInduced ψ n`. The source's standard embedding
`τ_P⁰ → τ_P` is the inclusion of function spaces. It corresponds to the
published `Whittaker.mirabolicCompactInclusion ψ n`, whose value on `f` is
the underlying function `f.val` (`mirabolicCompactInclusion_apply`).

The induction conventions are those of §§2.21–2.22, printed pp.21–22.
Functions satisfy the unnormalized covariance `f(u * g) = Θ(u) * f(g)`.
The group acts by right translation, `(s • f)(g) = f(g * s)`. The compact
model consists of the smooth functions whose actual projected nonzero
support in `U \ P` is compact. This is the source's condition "finite
modulo `H`" in §2.22. The source states smoothness as invariance under a
compact open subgroup. The implementation asks for an open subgroup. In
the p-adic setting these give the same functions, because every open
subgroup contains a compact open subgroup. The alternative modular
normalization in the Remark on p.22 is not used.

Proposition 5.15(b), printed p.49, reads: "Any P-homomorphism `τ_P⁰ → τ_P`
is proportional to the standard embedding." A `P`-homomorphism in the
source's category `Alg P` is a complex-linear `P`-equivariant map. These
are exactly the intertwining maps quantified over here. "Proportional" is
recorded as the existence of a complex scalar `c` with
`A = c • mirabolicCompactInclusion ψ n`.

## The source proof route (not implemented here)

The proof on printed p.50 takes `E` to be the space of `τ_P⁰` and proceeds
in three steps.

1. **Frobenius duality.** BZ76 Theorem 2.28, printed p.23, gives
   `Hom_G(π, Ind(G, H, ρ)) ≅ Hom_H(π|_H, ρ)` by evaluating at the identity
   element. Combined with the definition of `τ_P`, it identifies
   `Hom_P(τ_P⁰, τ_P)` with the `Θ`-equivariant functionals on `E`. By
   §2.30, printed p.24, these functionals are `(E_{U,Θ})*`, the dual of
   the twisted coinvariants `E_{U,Θ} = E / E(U, Θ)`.
2. **Top twisted coinvariant.** Printed p.49 deduces from Lemma 2.32 that
   `(Φ⁻)^{r−1}(π)`, a representation of `P₁ = {e}`, is realized in
   `E_{U,Θ}`. Hence `dim E_{U,Θ} = dim (Φ⁻)^{r−1}(τ_P⁰)`. Proposition
   5.12(g), printed p.47, gives `Φ⁻(τ_{P_k}⁰) = τ_{P_{k−1}}⁰`, so the
   iterate is the one-dimensional `τ_{P₁}⁰`. The functors `Φ⁻` and `Φ⁺`
   are defined in §5.11, printed p.46, using the Fourier description of
   `Alg M` from §§5.3, 5.9 and 5.10.
3. **Conclusion.** Therefore `Hom_P(τ_P⁰, τ_P) ≈ ℂ`. The standard
   embedding is a nonzero element of this space, so every element is a
   multiple of it. The source leaves this last step implicit.

This section describes the source's argument. It does not claim that any
step is implemented in Lean. A future proof must establish every
Frobenius, Fourier, derivative or top-coinvariant input it uses, and any
normalization bridge, against the actual models above. The published
`Langlands.Representation.Whittaker.Algebraic` contains an algebraic
equivalence (`functionalEquiv`) between character-equivariant functionals
and intertwiners into the space of all covariant functions. It does not
compute the functional space of the compact model. The published
`Langlands.Representation.Jacquet.ReciprocityProof` proves an actual
coinvariant reciprocity theorem, but it does not compute this top quotient
either.

## Rank-one boundary

The source's matrix rank `r` is `n + 1`, so every positive matrix rank is
covered and no lower bound on `n` is imposed. When `n = 0`,
`P₁ = U₁ = {1}`; the instance `Mirabolic.rankOneSubsingleton` records this
for the actual group. The adjacent-entry product is empty, so the subgroup
character is trivial (`mirabolicCharacter_rankOne`), even though `ψ` is
still nontrivial. The quotient `U \ P` is a point, so every covariant
function has compact projected support. Both models are then
one-dimensional complex spaces of functions on a one-point group, and the
canonical inclusion is a linear bijection between them. The statement then says that
every linear map between these one-dimensional spaces is a scalar multiple
of that bijection. This case is kept as part of the target.

## Relation to neighbouring targets

- `Langlands.Whittaker.MirabolicCompactMinimalityStatement`
  (`MirabolicMinimalityStatement`, BZ76 5.15(c)) uses this proposition as
  its scalar-uniqueness input on printed p.50. The present module does not
  state minimality, nondegeneracy, or the decomposition of the completely
  nondegenerate part.
- `Langlands.Whittaker.MirabolicFunctionalMultiplicityStatement`
  (`MirabolicPairingStatement`, from JPSS 1983 §1.5) concerns the
  functional spaces of an irreducible smooth mirabolic representation, and
  it assumes irreducibility. The present target describes every map from
  the compact model to the smooth model. It assumes no irreducibility and
  is not phrased as a statement about functional spaces.

## Scope and provenance

This target is a mathematical specialization taken directly from the
source. The imported groups, character transport, induction models,
support condition and inclusion are elementary implementation definitions
and laws. They do not establish the proposition. This module constructs no
Fourier, sheaf, derivative or coinvariant machinery, and it makes no claim
that these prerequisites or this proposition have been proved. All
existing Library Lean/Markdown pairs are preserved.

## Source and imports

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys
  31:3 (1976), 1–68, English translation. Registered source
  `bernstein-zelevinsky-1976-representations-gln`, SHA256
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
  Printed and one-based PDF page numbers agree. The following parts were
  read: §§2.21–2.22, pp.21–22; Frobenius duality and twisted coinvariants
  §§2.28–2.32, pp.23–24; §§5.1 and 5.3–5.7, pp.44–45; §§5.10–5.12,
  pp.46–48; and §5.15 with its proposition and proof, pp.48–50. Printed
  pp.45, 49 and 50 were checked visually, and the retained file's hash was
  verified. No registered erratum for this source was found in the
  literature index or in the current Library notes.

The two imports are
`Langlands.Representation.Whittaker.MirabolicModels`, which supplies the
actual groups, characters, induction models and canonical inclusion, and
`Langlands.LocalField.Canonical`, which supplies the canonical p-adic
topological data. No change to `MirabolicModels` or to any other published
module is needed.

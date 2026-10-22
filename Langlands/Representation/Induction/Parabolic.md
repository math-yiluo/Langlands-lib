# Normalized parabolic induction from standard block Levi subgroups

Author: Worker 23.

This module constructs normalized parabolic induction for the standard upper
block parabolic `P = B.parabolic F` of `GL_n(F)`. The parabolic, its actual Levi
product `B.Levi F` and the block projection `B.leviProjection F : P →* B.Levi F`
are the published constructions of `Group/GL/Blocks`. Induction itself is the
published smooth induction `Induction.smoothInduced` by right translation, and
`Induction.normalizedSmoothInduced`, which twists the inducing representation
by a supplied smooth character. No new induction primitive is introduced.

## Generic block layer

Here `F` is any commutative ring with a topology making it a topological ring,
so that `GL_n(F)` is a topological group and the block projection is continuous.
The normalizing character is supplied as data, `χ : Induction.SmoothCharacter ℂ
(B.Levi F)` (a character into `ℂˣ` with open kernel).

- `inflateCharacter B χ` is `χ ∘ B.leviProjection F` on the parabolic. Its kernel
  is open because it is the preimage of an open set under the continuous
  projection `B.leviProjectionContinuous F`.
- `inducingRepresentation B χ σ` is the parabolic representation
  `p ↦ χ(m(p)) • σ(m(p))`, where `m(p) = B.leviProjection F p`. This is the
  inflation of `σ` twisted by the inflated character.
- `normalizedInducedOf B χ σ` is `Induction.normalizedSmoothInduced` on the
  parabolic with the inflated character and the inflated representation `σ ∘ m`.
  It acts on the published space `Induction.SmoothFunctions` of covariant
  functions with an open right stabilizer.
- `normalizedInducedOf_covariant` records the defining covariance:
  `f(p g) = χ(m(p)) • σ(m(p)) (f g)` for every `p` in the parabolic and every `g`.
- `normalizedInducedOf_apply` records the action by right translation:
  `(g · f)(x) = f(x g)`. Both lemmas hold by definition.
- `isSmooth_normalizedInducedOf` proves the result smooth.
- `normalizedInducedOfMap` sends a Levi intertwiner `f` to the intertwiner given
  by postcomposition with `f`. It is the published `smoothInducedMap` of the
  inflated, twisted map `inducingMap`. Identity and composition laws are proved.
- `normalizedInductionFunctorOf B χ` packages these as a functor from the
  canonical smooth category `SmoothRep ℂ (B.Levi F)` of `Category/Basic` to
  `SmoothRep ℂ (GL_n(F))`. The induction module's `Induction.SmoothRep`
  is a compatibility abbreviation for this same canonical category.
- `normalizedCompactInducedOf` is the compactly supported variant. It uses the
  published `Induction.normalizedCompactInduced`: smooth induced functions with
  compact support modulo the parabolic, with the same character. It is smooth,
  and `normalizedCompactInclusionOf` is the published inclusion into the smooth
  version.

The generic layer is a derived generalization. It requires only the data used
by the constructions: a topological commutative ring and an open-kernel
character. It is instantiated below for every p-adic field.

## p-adic layer

For a p-adic field `F : PadicField p` with a supplied realization `T` (its
topology, valuation and local-field structure):

- `T.leviHalfCharacter B` is the published positive half `T.leviHalfModulus B`
  of the explicit block modulus `δ_P(m) = ∏_{i<j} |det m_i|^(n_j) / |det m_j|^(n_i)`
  of `Group/GL/BlockModulus`. Its open kernel is the published
  `isOpen_ker_leviHalfModulus`.
- `T.normalizedParabolicInduced B σ` is the generic construction with this
  character. Its type displays the inducing representation of the parabolic as
  `twist (T.parabolicHalfModulus B) (σ ∘ m)`, that is `δ_P^(1/2) ⊗ σ` inflated to
  `P`. Definitionally it is `Induction.normalizedSmoothInduced` on the parabolic
  with the character `T.parabolicHalfModulus B`.
- `normalizedParabolicInduced_covariant` states the normalization with the
  explicit square root: `f(p g) = sqrt(δ_P(m(p))) • σ(m(p)) (f g)`.
- `isSmooth_normalizedParabolicInduced`, `normalizedParabolicInducedMap`,
  `normalizedParabolicCompactInduced`, `normalizedParabolicCompactInclusion` and
  `normalizedParabolicInductionFunctor` specialize the generic layer.
- `PadicField.canonicalNormalizedParabolicInduced` and
  `canonicalNormalizedParabolicInductionFunctor` use the accepted canonical
  realization, so every algebraic `PadicField.{u} p` with prime `p` is covered
  in its own field universe.

The p-adic topological-ring structure of `F.Carrier` is obtained inside the
module from the realization's topology, valuation and local-field instances, as
in the published `generalLinearTopologicalGroup`. The topologies on `GL_n(F)`,
the parabolic and the Levi are the published ones of `Group/GL/Padic` and
`Group/GL/PadicBlocks`.

## Universes and scope

The coefficient field is `ℂ`. The field universe `uF` and the carrier universe
`uV` are independent, and the induced carrier lies in `Type (max uF uV)`. No
topology, finite dimension or admissibility is imposed on the inducing module,
and smoothness of `σ` is not needed for the construction. The functors take
smooth Levi representations, as in Bernstein--Zelevinsky's categories `Alg M`.
Every ordered positive block shape is allowed, so every rank `n ≥ 1` is covered.

## Source correspondence

- Bernstein--Zelevinsky (1977), section 1.8(a), printed page 444 / PDF page 5:
  `I_{U,θ}(ρ)` consists of the functions `f : G → L` with
  `f(umg) = θ(u) mod_U^(1/2)(m) ρ(m) f(g)` and a uniform open right stabilizer,
  with `G` acting by `(g f)(g') = f(g' g)`. The compactly supported subspace
  gives `i_{U,θ}(ρ)`. This module implements the case `θ = 1` for the standard
  block parabolic. Since `p = u m` has Levi part `m`, the covariance for all
  `p ∈ P` is the source's condition. The source's `mod_U` is the Haar module of
  conjugation on `U`. Here it is replaced by the explicit block formula of
  `Group/GL/BlockModulus`. Their equality is a separate theorem obligation and
  is not assumed (see that module's Markdown).
- Bernstein--Zelevinsky (1977), sections 2.1--2.3, printed page 446 / PDF
  page 7: the standard subgroups of `GL(n, F)` are the block-diagonal subgroups
  for ordered partitions of `n`, with the upper block parabolic. The functor
  `i_{G,M}` is defined as the compactly supported `i_{U,1}`. The paragraph after
  Proposition 2.3 notes that `G` is compact modulo `P`. (Proposition 2.3(d)
  itself is compatibility with smooth contragredients, not used here.)
- Bernstein--Zelevinsky (1977), Proposition 1.9(e), printed page 445 / PDF
  page 6: if `G` is compact modulo `P = MU`, the functors `I_{U,θ}` and
  `i_{U,θ}` coincide. With the compactness from section 2.3, this identifies
  `i_{G,M}` with `I_{U,1}`. This module provides both variants and the
  inclusion between them. Their equality is a theorem and is neither proved nor
  assumed here. For admissible inducing representations it is an instance of
  the published statement `Langlands.Induction.CompactQuotientClause`, given
  compactness of the coset space.
- Henniart (2002), section 2.5, printed pages 594--595 / PDF pages 8--9:
  `i(π_1, …, π_r)` is normalized parabolic induction from the parabolic of upper
  block-triangular matrices with diagonal blocks of successive sizes
  `n_1, …, n_r`. This module induces an arbitrary representation `σ` of the
  Levi. The block-factor form, in which `σ` is the external tensor product of
  the `π_i`, is not built here.

The originals were read at these pages. Registered sources:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  section 1.8, page 444, Proposition 1.9(e), page 445, and sections
  2.1--2.3, page 446.
- `henniart-2002-characterization`, SHA256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`,
  section 2.5, pages 594--595.

## Not claimed

This pair proves only the intrinsic construction obligations: covariance, right
translation, smoothness, open kernels, map laws and functoriality. It does not
claim irreducibility, finite length, exactness, admissibility, Frobenius
reciprocity, transitivity, the equality of smooth and compact parabolic
induction, or the identification of the explicit modulus with the Haar module.
Those are separate theorem obligations.

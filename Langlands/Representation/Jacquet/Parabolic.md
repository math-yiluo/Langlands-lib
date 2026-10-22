# Normalized Jacquet modules for standard block parabolics

Author: Worker 23.

This module constructs the normalized Jacquet module of a representation of
`GL_n(F)` along the standard upper block parabolic `P = B.parabolic F`. It uses
only published constructions:

- the parabolic, its actual Levi product, the block projection, the Levi section
  `B.leviInParabolic F` and the unipotent radical `B.unipotentRadical F` (a
  normal subgroup of `P`) of `Group/GL/Blocks`;
- the actual coinvariant quotients `Jacquet.Coinvariants` and the normalized
  quotient action `Jacquet.normalizedActionOfModulus` of
  `Representation/Jacquet/{Coinvariants,Normalized}`. That action takes a full
  positive modulus `δ` and acts by `δ(m)^(-1/2)`.

## Generic block layer

Here `F` is any commutative ring. A topology making it a topological ring is
needed only for smoothness and the functor.

- `B.JacquetModule ρ` is the actual quotient `V_N = V / V(N)`. Here `V(N)` is
  spanned by the vectors `ρ(u) v - v` for `u` in the unipotent radical `N`, and
  `ρ` is restricted to the parabolic. `B.jacquetMk ρ` is the quotient map, and it
  is surjective.
- `top_le_normalizer_unipotentRadical` proves that the whole parabolic
  normalizes `N`. This follows from normality of `N` in `P`, via Mathlib's
  `Subgroup.normalizer_eq_top`. So the published quotient action applies to the
  top subgroup of `P`, and no ambient normalizer lemma is needed.
- `B.leviToTop` is the Levi section `m ↦ B.leviInParabolic F m`, viewed in the
  top subgroup. `B.topModulus δ` is a supplied full Levi modulus
  `δ : B.Levi F →* ℝ≥0ˣ`, inflated along the block projection and restricted to
  the top subgroup. `topModulus_leviToTop` proves that it returns `δ m` on the
  section, using the published `leviProjection_section`.
- `B.normalizedJacquetOf δ ρ` is the published normalized action of the top
  subgroup with this modulus, pulled back to the Levi along `leviToTop`.
  `normalizedJacquetOf_mk` states its formula:
  `m · [v] = δ(m)^(-1/2) • [ρ(diag(m)) v]`, where `diag(m) = B.leviEmbedding F m`
  is the block-diagonal matrix.
- `normalizedJacquetOfMap` is the published quotient map of an intertwiner of
  `GL_n` representations, restricted to the parabolic. Its value on classes,
  identity law and composition law are proved.
- `jacquetModuleEquiv` is a linear equivalence between `B.JacquetModule ρ` and
  the ambient coinvariants `Jacquet.Coinvariants ρ (B.unipotentSubgroup F)`. The
  published matrix subgroup `B.unipotentSubgroup F` is the image of `N` in
  `GL_n(F)`, so both quotients have the same relations. Both directions are
  built from the published `Jacquet.lift`, and it sends `[v]` to `[v]`. The
  published `GeneralLinear.IsSupercuspidal` predicate is stated with these
  ambient coinvariants.
- For an open-kernel modulus, `isSmooth_normalizedJacquetOf` proves the
  normalized Jacquet module of a smooth representation smooth. The proof uses the
  published smoothness of normalized quotient actions, applied to the restriction
  to `P` (continuous inclusion), and then pullback along the continuous Levi
  section. The kernel of `topModulus δ` is open as a preimage under the
  continuous block projection.
- `normalizedJacquetFunctorOf δ hδ` packages these as a functor from the
  canonical smooth category `SmoothRep ℂ (GL_n(F))` of `Category/Basic` to
  `SmoothRep ℂ (B.Levi F)`. `normalizedJacquetObjectOf` is its object map.

The generic layer is a derived generalization. It requires only the data its
constructions use: a commutative ring and a positive Levi character, plus a
topology and an open kernel for smoothness. It is instantiated below for every
p-adic field.

## p-adic layer

For a p-adic field `F : PadicField p` with a supplied realization `T`:

- `T.normalizedJacquet B ρ` uses the full explicit block modulus
  `T.leviModulus B`, `δ_P(m) = ∏_{i<j} |det m_i|^(n_j) / |det m_j|^(n_i)`, of
  `Group/GL/BlockModulus`.
- `normalizedJacquet_mk` gives the action with the explicit square root.
  `normalizedJacquet_mk_eq_inv_halfModulus` expresses the same scalar as the
  inverse of the induction half `T.leviHalfModulus B`. So this normalization is
  exactly inverse to the one used by normalized parabolic induction.
- `normalizedJacquetMap`, `isSmooth_normalizedJacquet` (using the published
  `isOpen_ker_leviModulus`) and `normalizedJacquetFunctor` specialize the generic
  layer. The topological-ring structure of `F.Carrier` comes from the
  realization's topology, valuation and local-field instances, and the topologies
  on `GL_n(F)` and the Levi are those of `Group/GL/Padic` and
  `Group/GL/PadicBlocks`.
- `PadicField.canonicalNormalizedJacquet` and
  `canonicalNormalizedJacquetFunctor` use the accepted canonical realization, so
  every algebraic `PadicField.{u} p` with prime `p` is covered in its own field
  universe.

## Universes and scope

The coefficient field is `ℂ`. The field universe `uF` and the carrier universe
`uV` are independent, and the Jacquet module lies in the carrier universe `uV`.
No topology, finite dimension or admissibility is imposed on the module. Every
ordered positive block shape is allowed, so every rank `n ≥ 1` is covered.

## Source correspondence

- Bernstein--Zelevinsky (1977), section 1.8(b), printed page 444 / PDF page 5:
  for `(π, G, E)` and a character `θ` of `U`, `E(U, θ)` is spanned by the
  vectors `π(u) ξ - θ(u) ξ`, and `r_{U,θ}(E) = E / E(U, θ)` carries the action
  `m (ξ + E(U, θ)) = mod_U^(-1/2)(m) (π(m) ξ + E(U, θ))`. This module implements
  `θ = 1` for the standard block parabolic. The source's `mod_U` is the Haar
  module of conjugation on `U`. Here it is replaced by the explicit block
  formula. Their equality is a separate theorem obligation and is not assumed
  (see `Group/GL/BlockModulus`).
- Bernstein--Zelevinsky (1977), sections 2.1--2.3, printed page 446 / PDF
  page 7: the standard subgroups of `GL(n, F)` are the block-diagonal subgroups
  for ordered partitions, and `r_{M,G} = r_{U,1}` for the parabolic triple
  `(P, M, U)`.

The originals were read at these pages. Registered source:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  section 1.8(b), page 444, and sections 2.1--2.3, page 446.

## Not claimed

This pair proves only the intrinsic construction obligations: the action laws
(through the published normalized action), the formula on classes, map laws,
the equivalence with the ambient coinvariants, smoothness and functoriality. It
does not claim exactness, admissibility of Jacquet modules, Frobenius
reciprocity, transitivity, the geometric lemma or the identification of the
explicit modulus with the Haar module. Those are separate theorem obligations.

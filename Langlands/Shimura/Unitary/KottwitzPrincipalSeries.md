# Unramified representations and their parameters for Kottwitz's groups

Author: Worker 8. Module `Langlands.Shimura.Unitary.KottwitzPrincipalSeries`, namespace
`Langlands.Shimura.KottwitzUnramified`. It builds on the published standard unramified
charts of `Langlands.Shimura.Unitary.KottwitzChart` (item 1 of Task 5424).

At a good prime `p`, a standard unramified chart `c` identifies `ℚ_p ⊗_ℚ A` with
`Π_{w ∣ p} M_n(K_w)`. In it, the involution has the antidiagonal form
`θ(x)_w k l = c_w(x_{w̄} (rev l) (rev k))`. This module constructs the diagonal torus
`T`, the upper triangular Borel subgroup `B` and the projection `B → T`. It also
constructs the lattice of `ℚ_p`-rational cocharacters of `T` and its points `λ(p)`,
and the relative Weyl group. With these it defines the unramified principal series
over a characteristic-zero field `L` and the `K_p`-spherical irreducible smooth
representations. A representation's unramified parameter is defined as a character
of `T` whose principal series contains the representation as a subquotient. The
normalization with a chosen square root of `p`, the decomposition over the places of
the totally real field, and the Weyl equivalence of parameters are made explicit and
proved coherent.

Following Kottwitz, the parameter of a representation `π` on an `L`-vector space takes
values in an extension field `Ω` of `L`. In Kottwitz's text `Ω` is the algebraic closure
`L̄`. The relation compares the scalar extension `Ω ⊗_L π` with a principal series over
`Ω`.

## Sources

- Kottwitz, *On the λ-adic representations associated to some simple Shimura
  varieties*, Invent. Math. 108 (1992), §1, printed pp.656-657 (PDF pp.4-5), source
  `kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`. The bars over `L`
  were checked visually on the scan. Printed p.656:

  > In order to describe these representations we need to explain how to associate an
  > unramified `L̄`-representation `V(π_p, E_v)` of `W_{E_v}` to any unramified
  > representation `π_p` of `G(ℚ_p)` in an `L`-vector space. To do this we must
  > normalize the correspondence between unramified representations of `G(ℚ_p)` and
  > unramified admissible homomorphisms `W_{ℚ_p} → ^L(G_{ℚ_p})` where `^L(G_{ℚ_p})` is
  > formed using `Ĝ(L̄)` and `W_{ℚ_p}`. Over `ℂ` there is a standard normalization (the
  > unitary correspondence). We need the analog of this correspondence over `L̄`, and
  > thus we must choose a square root `√p` of `p` in `L̄`, so that we can make sense of
  > the quasi-character `| |^{1/2}` on `ℚ_p^×`: `|x|^{1/2} = (√p)^{-val(x)}`. Having
  > chosen `√p`, we may associate to an unramified irreducible representation `π_p` of
  > `G(ℚ_p)` over `L̄` an unramified admissible homomorphism `φ(π_p)`, well-defined up
  > to conjugation by `Ĝ(L̄)`.

  Printed p.657: "suppose that `π_p` is an unramified representation on an `L`-vector
  space, irreducible over `L̄`. The isomorphism class of `V(π_p, E_v)` is defined over
  `L`." Parameters are therefore constructed over `L̄`, for representations that are
  irreducible after extension of scalars to `L̄`. Descent to `L` concerns the resulting
  polynomial, not the parameter.

- Cartier, *Representations of p-adic groups: a survey*, Corvallis I (1979), source
  `cartier-1979-representations-padic-groups`, SHA-256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`, with complex
  coefficients throughout. Definition 3.1 (printed p.136) and §3 (printed
  pp.143-145) treats the unramified principal series `I(χ)`, induced from an
  unramified character `χ` of the minimal Levi subgroup and normalized by
  `δ^{1/2}`. Corollary 4.2 (printed p.149) shows that the characters of the spherical
  Hecke algebra are the `ω_χ`, with `ω_χ = ω_{χ'}` iff `χ' = w·χ`. Definition 4.2
  (printed p.150) defines spherical representations: smooth, irreducible, with a
  nonzero `K`-fixed vector. §4.4 (printed pp.151-152) shows that every spherical
  representation is the unique spherical Jordan-Hölder constituent `π_χ` of some
  `I(χ)`, and that `π_χ ≅ π_{χ'}` iff `χ' = w·χ`.
- Borel, *Automorphic L-functions*, Corvallis II (1979), source
  `borel-1979-automorphic-l-functions`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`: §6 (printed
  pp.35-38), semisimple classes `t ⋊ σ` with `t` in the dual torus for quasi-split
  unramified groups, and §7.1-7.2 (printed pp.38-39), the bijection between characters
  of the spherical Hecke algebra (class one representations for hyperspecial `K`) and
  these classes.

## Notation

As in `KottwitzChart`: `E` is the totally real field (Kottwitz's `F₀`) and `K` the CM
field (Kottwitz's `F`). `p : HeightOneSpectrum (𝓞 ℚ)` is a finite place of `ℚ`,
`G(ℚ_p) = LocalPoints σ p`, and `Ψ = chartEquiv c.charts`. The matrix coordinates of a
point are `pointUnit c.charts g = Ψ(g)`, and `θ` is the transported involution. Positions
are `k : Fin n`, numbered from `0`. In the usual numbering `k = 1, …, n`, the factor
`n + 1 - 2k` of the half-sum of positive roots becomes `n - 1 - 2k`.

The constructions of this module (torus, Borel subgroup, cocharacter points, Weyl group)
are defined for every chart. Their interpretation as the quasi-split structure and as
the modulus character of an unramified group needs the good-prime hypothesis
`IsUnramifiedAt p K` of item 1. That hypothesis is part of the relation
`IsSphericalIrreducible` below. The square-root normalizations require `s² = p`, which
is built into the type `SqrtPrime p L`.

## Declarations

### The transported involution

- `localInvolution σ` is `σ ⊗ 1` on `ℚ_p ⊗_ℚ A`.
  `chartEquiv_localInvolution`: `Ψ(σ y) = θ(Ψ y)`.
- `transportedInvolution_mul`, `_one`, `_transportedInvolution`: `θ` is an
  anti-multiplicative involution.
- `chartEquiv_algebraMap`: `Ψ` sends a scalar `s ∈ ℚ_p` to the scalar matrices of the
  completion map `ℚ_p → K_w`.
- `UnramifiedChart.transportedInvolution_apply` restates the normal form.
  `isUpper_transportedInvolution`: `θ` preserves upper triangular matrices, because
  `rev` reverses the order. `transportedInvolution_diagPart`: `θ` commutes with taking
  diagonal parts.

### Borel subgroup, torus and projection

- `IsUpper`, `IsLower`: every component is upper, respectively lower, triangular
  (Mathlib's `Matrix.BlockTriangular`). Both are closed under products, contain `1`,
  and are preserved by inverses of units (`IsUpper.inv`, through Mathlib's
  `blockTriangular_inv_of_blockTriangular`). `isUpper_and_isLower_iff`: being both is
  being diagonal.
- `UnramifiedChart.borel` is the subgroup of points with upper triangular coordinates.
  `UnramifiedChart.torus` is the subgroup with diagonal coordinates (`mem_torus_iff`),
  and `torus_le_borel` holds. Because `θ` preserves upper triangular and diagonal
  matrices, these are the `ℚ_p`-points of a Borel subgroup and of a maximal torus
  contained in it. This is the quasi-split structure of item 1.
- `diagPart` takes diagonal parts. `diagPart_mul_of_isUpper`: it is multiplicative on
  upper triangular matrices. `diagUnit` is the diagonal part of an upper triangular
  unit, a unit.
- `pointUnit_similitude` reads the similitude equation `g σ(g) = c` in coordinates as
  `Ψ(g) θ(Ψ g) = Ψ(c)`. `points_ext`: a point is determined by its coordinates and its
  multiplier. `mkPoint` builds a point from coordinates and a multiplier satisfying
  the coordinate equation.
- `UnramifiedChart.torusPart g`, for `g` in the Borel subgroup, is the point with
  coordinates `diagPart Ψ(g)` and the same multiplier. It lies in `G(ℚ_p)`:
  `diagPart Ψ(g) · θ(diagPart Ψ(g)) = diagPart(Ψ(g) θ(Ψ g)) = Ψ(c)`
  (`diagUnit_similitude`). `UnramifiedChart.torusProjection : B →* T` is this map, a
  homomorphism by `diagPart_mul_of_isUpper`. `torusProjection_of_mem_torus`: it is the
  identity on `T`.

### Rational cocharacters and their points

- `localCocharacters E K p n` is the lattice of pairs `(m, m_c)` with `m w k ∈ ℤ` for
  `w ∣ p`, `k : Fin n`, and `m_c ∈ ℤ`, subject to `m w k + m w̄ (rev k) = m_c`. These
  are the cocharacters `λ` of the diagonal torus defined over `ℚ_p`. At `w` the
  cocharacter is `diag(t^{m w k})`, with multiplier `t^{m_c}`. The constraint is the
  similitude equation for the antidiagonal form.
- `residuePrime p` is the rational prime below `p` (Mathlib's `natGenerator`).
  `primeUnit p w` and `rationalPrimeUnit p` are this prime as units of `K_w` and of
  `ℚ_p`. `map_primeUnit` and `completionMap_rationalPrimeUnit`: ring maps between the
  completions, in particular the maps `c_w` and the completion maps, carry integer
  powers of `p` to integer powers of `p`.
- `cocharMatrixUnit m` is the diagonal unit `(diag(p^{m w k}))_w`, multiplicative in
  `m` (`cocharMatrixUnit_add`, `_zero`).
  `transportedInvolution_cocharMatrix`: `θ` sends it to the unit with exponents
  `m w̄ (rev k)`. `cocharMatrix_similitude`: for `m` in the lattice, the coordinate
  similitude equation holds with multiplier `p^{m_c}`.
- `UnramifiedChart.cocharPoint m` is the point `λ(p)` of the torus.
  `UnramifiedChart.cocharHom : Multiplicative (localCocharacters …) →* T` packages it
  as a homomorphism (`cocharPoint_zero`, `cocharPoint_add`).
- `positionCocharacter E p n w k` is the cocharacter `λ_{w,k}`, with exponent `+1` at
  `(w, k)`, exponent `-1` at `(w̄, rev k)` and `m_c = 0`. It is zero when
  `(w̄, rev k) = (w, k)`. Its point `λ_{w,k}(p)` is `d θ(d)⁻¹`, where `d` has `p` at
  `(w, k)` and `1` elsewhere. `positionCocharacter_coord` gives its coordinates.

### The relative Weyl group

- `localWeylGroup E K p n` is the group of families of permutations `σ_w` of the
  positions with `σ_{w̄}(rev k) = rev(σ_w k)`. These are the permutations of the
  diagonal that normalize the torus and commute with the antidiagonal involution: the
  relative Weyl group, `S_n` at a pair of conjugate places, and the centralizer of
  `rev` in `S_n` (the hyperoctahedral group) at a self-conjugate place.
- `weylAct σ m` permutes the positions: `(σ m) w k = m w (σ_w⁻¹ k)`. It is an action
  (`weylAct_one`, `weylAct_mul`). `weylAct_positionCocharacter`:
  `σ λ_{w,k} = λ_{w,σ_w k}`.

### Inertia degrees and the half-sum of positive roots

- `inertiaDegree w` is Mathlib's inertia degree `f_w` of the place `w` over `ℚ`.
  `inertiaDegree_placeConj`: `f_{w̄} = f_w`. The proof writes `w̄` as the image of `w`
  under the CM conjugation, as an automorphism of `𝓞 K` over `𝓞 ℚ`
  (`integerConjugationAlgEquiv`), and applies Mathlib's `Ideal.inertiaDeg_smul`.
- `weylExponent σ m = Σ_w f_w Σ_j (j - σ_w j) m w j` is the integer
  `⟨2ρ, σλ - λ⟩`, for `ρ` the half-sum of the positive roots of the upper triangular
  Borel subgroup over `ℚ̄_p`. Here `f_w` counts the embeddings of `K` over `w`.
  `weylExponent_one` and `weylExponent_mul` (the cocycle identity
  `e(στ, λ) = e(σ, τλ) + e(τ, λ)`) hold.
  `weylExponent_positionCocharacter`: `e(σ, λ_{w,k}) = 2 f_w (k - σ_w k)`, using
  `f_{w̄} = f_w`.

### Unramified representations and parameters

`L` is the coefficient field of the representations, any field (in Kottwitz's
application a characteristic-zero field such as a number field), and `Ω` is a field with
`[Algebra L Ω]` containing the values of the parameters (Kottwitz: `Ω = L̄`).

- `UnramifiedChart.IsUnramifiedCharacter ξ`: the character `ξ : T →* Ωˣ` is trivial on
  the integral points `T ∩ K_p`, where `K_p = c.level` is the hyperspecial level.
- `UnramifiedChart.borelLine ξ` is the line `Ω` on which `b ∈ B` acts by
  `ξ(torusProjection b)` (`borelLine_apply`).
- `UnramifiedChart.principalSeries ξ` is the published smooth induction
  `Induction.smoothInduced` from the Borel subgroup of this line. It is a smooth
  representation of `G(ℚ_p)` over `Ω` on the smooth functions `f` with
  `f(b g) = ξ(b) f(g)`. This is the unnormalized principal series. Cartier's normalized
  `I(χ)` (Definition 3.1, printed p.136) is `principalSeries (χ δ_B^{1/2})`. (This needs
  `[Module.Finite ℚ A]`, for the published topological-group structure on `G(ℚ_p)`.)
- `IsSubquotientOf ρ π`, over any field: some subrepresentation of `ρ` maps onto `π` by
  an intertwining map. The carriers may lie in different universes. This generalizes
  the complex-coefficient relation of `Langlands.Correspondence.UnramifiedNormalization`.
- `scalarExtension Ω ρ` is the representation `g ↦ 1 ⊗ ρ(g)` on `Ω ⊗_L V`, built with
  Mathlib's `Module.End.baseChangeHom` (`scalarExtension_tmul`).
  `scalarExtensionEquiv Ω e` extends an equivalence of representations to their scalar
  extensions (Mathlib's `LinearEquiv.baseChange`), and `isIrreducible_of_repEquiv`
  transports irreducibility along equivalences.
- `UnramifiedChart.IsSphericalIrreducible Ω π`, for a smooth representation `π` of
  `G(ℚ_p)` over `L`, says three things. First, `p` is unramified in `K`. Second,
  `Ω ⊗_L π` is irreducible. Third, `π` has a nonzero `K_p`-fixed vector. For `Ω = L̄`
  this is Kottwitz's "irreducible over `L̄`" together with Cartier's Definition 4.2
  (smooth, irreducible, with a nonzero `K`-fixed vector).
- `UnramifiedChart.HasPrincipalSeriesParameter π ξ`, for `ξ : T →* Ωˣ`, says three
  things. First, `π` is spherical and irreducible over `Ω`. Second, `ξ` is unramified.
  Third, `Ω ⊗_L π` is a subquotient of `principalSeries ξ` over `Ω`. By Cartier §4.4,
  stated over `ℂ` and valid over any algebraically closed field of characteristic zero,
  such a `ξ` exists and is unique up to the Weyl equivalence below whenever `Ω` is
  algebraically closed of characteristic zero. This relation only names parameters.
  Neither existence nor uniqueness is assumed or proved here.
  `UnramifiedChart.HasUnramifiedParameter π ξ` is the case `Ω = AlgebraicClosure L` of
  Kottwitz's text.
- If `Ω` is not algebraically closed the relation can be empty. For example, take
  `Ω = L`, `G(ℚ_p)` a split torus, and `π` an `L`-irreducible representation with no
  `L`-rational eigencharacter, such as `(√2)^{val}` acting on `L(√2)` when `√2 ∉ L`.
  Such a `π` is not irreducible over `L̄` either. For this reason the parameter field is
  separate from the coefficient field.
- `HasPrincipalSeriesParameter.of_equiv`: the relation depends only on the equivalence
  class of `π`. Irreducibility of the scalar extension transports along
  `scalarExtensionEquiv`, nonzero fixed vectors along the published
  `fixedVectors_ne_bot_iff_of_equiv`, and the surjection is composed with the extended
  equivalence.

### Normalization with a square root of `p`

`SqrtPrime p L` is the type of units `s` of `L` with `s² = p`, Kottwitz's chosen `√p`
(in `L̄`, or in any field `Ω` containing the parameter values). `SqrtPrime.neg` is the
other root. Let `s` be such a square root. The modulus character of the Borel
subgroup at the point of a rational cocharacter is
`δ_B^{1/2}(λ(p)) = |·|^{⟨2ρ, λ⟩/2}`, which is `s^{-⟨2ρ, λ⟩}` with Kottwitz's
convention `|x|^{1/2} = s^{-val(x)}`. The unitarily normalized character is
`χ = ξ δ_B^{-1/2}`.

- `UnramifiedChart.positionValue s ξ w k = ξ(λ_{w,k}(p)) · s^{f_w (n - 1 - 2k)}` is the
  value of `χ` at `λ_{w,k}`, since `⟨2ρ, λ_{w,k}⟩ = f_w (n - 1 - 2k)`.
  `positionValue_neg`: replacing `s` by `-s` (`SqrtPrime.neg`) multiplies it by
  `(-1)^{f_w (n - 1 - 2k)}`. Like Kottwitz's `φ(π_p)`, the normalized parameter depends
  on the choice of `√p`.
- `UnramifiedChart.WeylEquivalent s ξ ξ'`: there is `σ` in the Weyl group with
  `ξ'(λ(p)) = ξ((σλ)(p)) · s^{⟨2ρ, σλ - λ⟩}` for every rational cocharacter `λ`. This
  says exactly that `ξ' δ_B^{-1/2}` and `ξ δ_B^{-1/2}` are Weyl conjugate (Cartier's
  `χ' = w·χ`), written on the unnormalized characters. It is an equivalence relation
  (`weylEquivalent_refl`, `WeylEquivalent.symm`, `WeylEquivalent.trans`, from the
  cocycle identity).
- `positionValue_of_weyl`: under a Weyl equivalence by `σ`, the normalized position
  values are permuted, `positionValue s ξ' w k = positionValue s ξ w (σ_w k)`. Hence
  the multiset of normalized position values at each place depends only on the
  Weyl-equivalence class. These multisets are the base-change Satake parameters of
  item 4.

### Decomposition over the places of the totally real field

A place `v` of `E` above `p` is split in `K` when it has two places `w ≠ w̄` above it,
and inert when it has one place `w = w̄` (ramified places do not occur, by item 1).
The lattice `localCocharacters` and the Weyl group decompose accordingly.

- At a split `v` with places `w, w̄`, the coordinates at `w̄` are determined by those
  at `w` and by `m_c`. The positions `λ_{w,k}`, `k = 1, …, n`, form the cocharacter
  lattice of the `GL_n(K_w)` factor of `G(ℚ_p)`, with Weyl group `S_n`. The normalized
  values `positionValue s ξ w k` are the unitarily normalized Satake parameter of
  that factor.
- At an inert `v` with place `w = w̄`, the relation `λ_{w, rev k} = -λ_{w,k}` holds. The
  values at `k < rev k` are the unitary Satake parameters of the unramified quasi-split
  unitary factor, with Weyl group the hyperoctahedral group. The value at the middle
  position of odd `n` is `1`.
- The multiplier coordinate `m_c` is the common similitude factor. The value of `ξ` at
  a cocharacter with `m_c ≠ 0` records it. Every rational cocharacter is a sum of
  position cocharacters and one cocharacter with prescribed `m_c`, since the position
  cocharacters span the sublattice `m_c = 0`. The normalization of the similitude part
  uses `⟨2ρ, λ⟩` for the full lattice. That is done with the dual torus attached to the
  complex embeddings of `K` (item 3), where `⟨2ρ, ·⟩` is the half of a sum over the
  fixed-point-free conjugation of embeddings.

## Scope and provenance

The definitions are a derived, concrete presentation of Cartier's and Borel's notions
for the groups of item 1. The torus, Borel subgroup and modulus character are those of
the chart's antidiagonal normal form. The following are not proved here and remain
explicit obligations, each stated for an algebraically closed parameter field `Ω` of
characteristic zero:

- every representation that is spherical and irreducible over `Ω` has a parameter
  (Cartier §4.4);
- two parameters of the same representation are Weyl equivalent (Cartier Corollary 4.2
  with §4.4(b), the Satake isomorphism);
- the relation is invariant under a change of standard chart.

The determination of an unramified character of `T` by its values at the points
`λ(p)` is proved in [`KottwitzTorusLattice`](KottwitzTorusLattice.md), using the
decomposition `T = λ(p) · (T ∩ K_p)`.

Descent from `Ω = L̄` to `L` concerns the polynomials built from parameters (item 3), not
the parameters themselves. The module defines no Hecke algebra action and assumes no
Satake or Langlands correspondence: parameters are named through the principal series.
No structure field stores a parameter.

Formal dependencies: `Langlands.Shimura.Unitary.KottwitzChart` (item 1, candidate
`5bf204f1-0791-4a64-b8ab-e362c3cac923`), `Langlands.Representation.Induction.Definitions`
(`smoothInduced`), `Langlands.Representation.Category.Basic` (`SmoothRep`,
`IsIrreducible`), `Langlands.Representation.Smooth.IrreducibleRealization`,
`Langlands.Representation.Category.ClassInvariants`, and Mathlib
(`Matrix.BlockTriangular`, `Ideal.inertiaDeg`, `Ideal.inertiaDeg_smul`,
`Rat.HeightOneSpectrum.natGenerator`, `Subrepresentation`,
`Representation.IntertwiningMap`, `Representation.Equiv`,
`Module.End.baseChangeHom`, `LinearEquiv.baseChange`, `AlgebraicClosure`). Environment: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

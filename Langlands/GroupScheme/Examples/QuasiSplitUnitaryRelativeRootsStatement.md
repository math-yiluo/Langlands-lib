# Relative roots and the minimal parabolic of `U(1,1)`: statement

Author: Worker 3483.

This module states, as one `Prop`-valued definition, the relative root
structure of the quasi-split unitary group `U(1,1)` of the Library with respect
to its diagonal cocharacter. Nothing is proved here. The declaration
`RelativeRootsStatement` is in the namespace
`Langlands.GroupScheme.QuasiSplitUnitary`.

## The objects used

Throughout, `S = Spec (CommRingCat.of F)` and `G = groupScheme b c`.

- `groupScheme b c` (module `Langlands.GroupScheme.Examples.QuasiSplitUnitary`)
  is the full unitary group over `S` of the hermitian form
  `h(v, w) = v₁ c(w₂) + v₂ c(w₁)` on `E²`, with no determinant condition. Its
  points over a commutative `F`-algebra `R` are the invertible `2 × 2`
  matrices `M` over `E ⊗[F] R` with `M M* = 1` (`mem_matrixPoints`), where
  `M* = J c(M)ᵀ J`, `c` acts on the factor `E`, and `J` is the antidiagonal
  matrix with entries `1`.
- `cocharacter b c` (module
  `Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic`) is the
  homomorphism `λ : (Gm S).toGrp ⟶ G` with points `t ↦ diag(t, t⁻¹)`; it is
  `weightCocharacter b c 1`.
- `IsMaximalSplitTorus` (module `Langlands.GroupScheme.Rational.SplitTorus`):
  `i : T ⟶ G` is a split subtorus (`T` is a split torus and `i` is a closed
  immersion), and every factorization `f ≫ i' = i` through a split subtorus
  `i' : T' ⟶ G` has `f` an isomorphism.
- `relativeRoots` (module `Langlands.GroupScheme.Rational.RelativeRoots`) is the
  set of nonzero characters `χ` of `T` whose weight space in the Lie algebra of
  `G` under the adjoint action of `T` is nonzero (`mem_relativeRoots`).
- `characterLattice (Gm S)` is `Gm S ⟶ Gm S`, and `Gm.powerHom S m = m • 𝟙`
  (module `Langlands.GroupScheme.Torus.Lattice`) is the character
  `t ↦ t ^ m`.
- `IsGenericCocharacter i ν` (module `Langlands.GroupScheme.Rational.RelativeRoots`)
  says `latticePairing T α ν ≠ 0` for every `α ∈ relativeRoots i`. For
  `T = Gm S`, the pairing of `Gm.powerHom S m` with `Gm.powerHom S n` is `m n`.
- `IsMinimalParabolicFunctor` (module
  `Langlands.GroupScheme.Rational.MinimalParabolic`): the subgroup functor is
  the all-test range of a parabolic subgroup over `F`, and every such functor
  contained in it equals it.
- `Dynamic.parabolic` and `Dynamic.centralizer` (module
  `Langlands.GroupScheme.Dynamic.Basic`) are the published dynamic subgroup
  functors `P(μ)` and `Z(μ)` of a cocharacter `μ` of `G`, defined by orbit
  extension from `𝔾ₘ` to `𝔸¹` on all test schemes. `torusCentralizer`
  (module `Langlands.GroupScheme.Rational.TorusCentralizer`) is the
  centralizer subgroup functor of a torus.

## The statement

`RelativeRootsStatement : Prop` quantifies over fields `F E : Type u` with
`[Algebra F E]` and `[Algebra.IsQuadraticExtension F E]`, a type `κ : Type u`
with `[Fintype κ]`, an `F`-basis
`b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)` and `c : E ≃ₐ[F] E` with
`c ≠ AlgEquiv.refl`. These are the hypotheses of the other `U(1,1)`
statements of the Library, for example `IsConnectedReductiveStatement`. For
such data, writing `λ = cocharacter b c`, it asserts:

1. `IsMaximalSplitTorus λ`;
2. `relativeRoots λ = {Gm.powerHom S 2, Gm.powerHom S (-2)}`, that is, the
   relative roots are the characters `t ↦ t²` and `t ↦ t⁻²`;
3. `IsGenericCocharacter λ (𝟙 (Gm S))`;
4. for every `ν : cocharacterLattice (Gm S)` with `IsGenericCocharacter λ ν`,
   both `IsMinimalParabolicFunctor
   (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ λ))` and
   `Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ λ) = torusCentralizer λ`.

There is no assumption on the characteristic of `F`, so characteristic `2` is
included. The affine instance on `G` that `IsGenericCocharacter` needs is
found by instance search.

## Sources

- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - Definition 19.20 (printed p.401, PDF p.417): "The `k`-rank of `G` is the
    dimension of a maximal split torus in `G`."
  - Proposition 24.40 and Definition 24.42 (printed p.523, PDF p.539): algebras
    with involution of the second kind (unitary type), the setting of the
    unitary groups.
  - Example 25.5 (printed p.545, PDF p.561): for `SO(q)` the diagonal split
    subtorus is shown to be maximal through its centralizer, and the `k`-rank
    is the Witt index. This is the model computation for a non-split
    classical group.
  - 25.13 (printed p.548, PDF p.564): for a maximal split torus `S` of a
    reductive group, `g = g₀ ⊕ ⨁ g_α` under the adjoint action of `S`, with
    `g₀` the Lie algebra of `C_G(S)`; "The characters `α` of `S` such that
    `g_α ≠ 0` are called the relative roots of `(G, S)`."
  - 25.14 (printed p.548, PDF p.564): for a semisimple group of `k`-rank one
    with maximal split torus `S`, "Choose an isomorphism `λ : 𝔾ₘ → S`, and let
    `P = P(λ)`."
- Borel and Tits, *Groupes réductifs* (1965), source ID
  `borel-tits-1965-groupes-reductifs`, SHA-256
  `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
  Printed page = PDF page + 53.
  - 4.15 a) (printed pp.90–91, PDF pp.37–38): for a `k`-split torus `S` and
    the roots `Φ⁺` positive for an order on `X(S)`, `G_{Φ⁺}` and `G_{Φ⁻}` are
    opposite parabolic `k`-subgroups with common Levi `k`-subgroup `Z(S)`.
  - 4.16 (printed p.91, PDF p.38): a parabolic `k`-subgroup `P` is minimal if
    and only if its radical contains a maximal `k`-split torus of `G`.
- Conrad, Gabber and Prasad, *Pseudo-reductive groups*, 2nd ed. (2015),
  source ID `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`,
  Example 2.1.1,
  formula (2.1.1) (printed p.46, PDF p.72): conjugation by
  `λ(t) = diag(t^{e₁}, …, t^{eₙ})` multiplies the `(r, s)` entry by
  `t^{e_r − e_s}`.

## Correspondence with the sources

**Provenance.** No source computes the relative roots of `U(1,1)`; the
statement is the program's own derived example, required by the task
contract to exercise nonempty relative-root structure. Parts 1 and 2 are the
definitions of Milne 19.20 and 25.13 evaluated for `U(1,1)` and its diagonal
torus. Part 4 is the specialization of Borel–Tits 4.15 a) and 4.16 to this
group, in the dynamic form of the Library statements
`GenericMinimalParabolicStatement` (module
`Langlands.GroupScheme.Rational.MinimalParabolicStatement`) and
`GenericCentralizerStatement` (module `Langlands.GroupScheme.Rational.Statement`).

**Why the statement is true, in every characteristic.** Since `c ≠ id`, the
quadratic extension `E/F` is separable: an inseparable quadratic extension has
no nontrivial `F`-automorphism. Hence `G_E ≅ GL₂` (`splittingIso`) and
`U(1,1)` is a form of `GL₂`.

- *Part 1.* The image of `λ` is a closed split torus of dimension one, and by
  the rank row of the Library (`RankStatement`, part 2) no closed split torus
  over `F` has dimension larger than one. If `f ≫ i' = i` with `i'` a split
  subtorus `T' ⟶ G`, then `f` is a monomorphism, so `T'` is not trivial and
  `T' ≅ 𝔾ₘ`. A monomorphism `𝔾ₘ ⟶ 𝔾ₘ` is `t ↦ t^{±1}`: for `|n| ≥ 2` the
  power map has the nontrivial kernel `μ_n`, also when the characteristic
  divides `n`. So `f` is an isomorphism.
- *Part 2.* The Lie algebra of `G` consists of the matrices
  `X = [[a, x], [y, −c(a)]]` with `a ∈ E` and `x, y` in the trace-zero line
  `{z ∈ E | z + c(z) = 0}`. This line is one-dimensional over `F` because
  `E/F` is separable; in characteristic `2` it is `F` itself. By formula
  (2.1.1), `Ad(diag(t, t⁻¹))` fixes the diagonal, multiplies `x` by `t²` and
  `y` by `t⁻²`; the Library records this as `diagonalUnitary_upperRoot` and
  `diagonalUnitary_lowerRoot`. So the weights are `0` (dimension two),
  `2` and `−2` (dimension one each). Since `F[t, t⁻¹]` has basis `(tⁿ)`, no
  other character has a nonzero weight space. The characters `t²` and `t⁻²`
  are distinct and nonzero in `X*(𝔾ₘ) = ℤ` in every characteristic.
- *Part 3.* `⟨±2, 1⟩ = ±2 ≠ 0`.
- *Part 4.* By part 2, `ν = n` is generic exactly when `n ≠ 0`. Conjugation by
  `diag(tⁿ, t⁻ⁿ)` multiplies `x` by `t^{2n}` and `y` by `t^{−2n}`, so
  `P(ν ≫ λ)` is the upper triangular subgroup for `n > 0` and the lower one
  for `n < 0`, and `Z(ν ≫ λ)` is the diagonal subgroup for every `n ≠ 0`.
  The diagonal subgroup is the centralizer of the image of `λ`. Over `E` the
  triangular subgroups become Borel subgroups of `GL₂`, so they are minimal
  parabolic subgroups over `F`.

## Relation to the Library

These remarks describe available tools; they are not part of the statement.

- Part 4's minimality follows from part 1 by the published theorem
  `genericMinimalParabolic : GenericMinimalParabolicStatement`
  (module `Langlands.GroupScheme.Rational.GenericMinimalParabolicProof`)
  together with `isConnectedReductive : IsConnectedReductiveStatement`
  (module `Langlands.GroupScheme.Examples.QuasiSplitUnitaryReductiveProof`).
- Part 4's centralizer equality also follows from part 1, by the published
  theorem `genericCentralizer : GenericCentralizerStatement` (module
  `Langlands.GroupScheme.Rational.GenericCentralizerProof`) together with
  `isConnectedReductive`: specialized to `G = groupScheme b c`, `T = Gm S`
  and `i = λ`, its conclusion is exactly
  `Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ λ) = torusCentralizer λ`
  for every generic `ν`.
- A direct rank-one argument is an alternative route to the same equality.
  The Library provides `dynamicStatement : DynamicStatement` (module
  `Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamicProof`), which gives
  `Dynamic.centralizer λ = diagonal b c`, and
  `torusCentralizer_gm_eq_dynamicCentralizer` (module
  `Langlands.GroupScheme.Rational.TorusCentralizer`), which gives
  `torusCentralizer λ = Dynamic.centralizer λ`; it then remains to show
  `Dynamic.centralizer (ν ≫ λ) = Dynamic.centralizer λ` for `ν ≠ 0`.
- For part 1, `rankStatement : RankStatement` (module
  `Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankProof`) gives the
  closed immersion and the rank bound, and `isSplitTorus_gm` (module
  `Langlands.GroupScheme.Torus.Split`) gives the splitness of `𝔾ₘ`.

## Lean conventions

- The relative roots are written as characters of `𝔾ₘ` itself, the source
  of `λ`, rather than as characters of a separately named image torus; `λ` is
  a closed immersion by part 1, so the two descriptions agree.
- The cocharacter variable is named `ν` because `λ` is a Lean keyword.

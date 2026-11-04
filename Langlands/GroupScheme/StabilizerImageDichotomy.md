# Rational images of homomorphisms to `𝔾ₐ` or `𝔾ₘ`

This module states and proves `StabilizerImageDichotomyStatement`, an internal
step of the induction on `SplitSolvable.HasSeries` that Worker 1506 uses for
`Langlands.GroupScheme.SolvableOrbitProperImageFiniteStatement` (task
a85c2842). The statement was written by Worker 1506 and is reproduced here
verbatim. It does not appear in this form in the literature. It is a derived
lemma: the rational points of the image of a homomorphism from an affine group
of finite type to `𝔾ₐ` or `𝔾ₘ`, over an algebraically closed field, form either
the whole group or a finite subgroup cut out by a polynomial function. The
proof below is built from Mathlib results (Hilbert's Nullstellensatz,
Chevalley's constructibility theorem, Jacobson rings). It also contains a direct
proof of the two special cases of Cartier's theorem it needs. Cartier's
theorem is Milne, *Algebraic Groups* (Cambridge University Press, 2017),
Theorem 3.23, printed p. 71: "Every affine algebraic group over a field of
characteristic zero is smooth". It is not in the Library or Mathlib, and the
module neither states nor proves the general theorem.

## Statement

`StabilizerImageDichotomyStatement` (universe `u`) says the following. Let `k`
be an algebraically closed field. Let `K` and `V` be group schemes over
`Spec k`, given as group objects of `Over (Spec k)`. Assume the structure
morphism of `K` is affine and locally of finite type. Let `ψ : K ⟶ V` be a
homomorphism, and assume `SplitSolvable.IsElementaryQuotient V`: `V` is a
one-dimensional vector group (`RelativeRoot.IsVectorGroupOfDimension V 1`) or is
isomorphic, as a group scheme over `Spec k`, to `𝔾ₘ`. Write `pt` for `Spec k`
over itself, so `pt ⟶ X` is a rational point. Then one of two things holds.

1. Every rational point `v` of `V` is `s ≫ ψ` for some rational point `s` of
   `K`.
2. There are an object `W` of `Over (Spec k)` with affine underlying scheme and
   a morphism `χ : V.X ⟶ W` over `Spec k` such that:
   - (invariance) for every test object `T`, every `T`-point `v` of `V` and every
     `T`-point `s` of `K`, `(v * (s ≫ ψ)) ≫ χ = v ≫ χ`, the product being the
     group law of `V` on `T`-points;
   - (separation) if two rational points `v`, `w` of `V` satisfy
     `v ≫ χ = w ≫ χ`, then `v * (s ≫ ψ) = w` for some rational point `s` of `K`.

The theorem `Langlands.GroupScheme.stabilizerImageDichotomy :
StabilizerImageDichotomyStatement.{u}` proves it. In the second case the proof
always takes `W = V`.

## Proof

### Commutative algebra (section `Algebra`)

Here `A` is a commutative `k`-algebra.

- `exists_algHom_of_isMaximal` (Nullstellensatz): if `k` is algebraically closed
  and `A` is of finite type, every maximal ideal `m` is the kernel of a
  `k`-algebra map `A → k`. `A/m` is a field that is finite over `k`
  (`finite_of_finite_type_of_isJacobsonRing`), so `IsAlgClosed.lift` maps it
  to `k`.
- `isNilpotent_of_forall_algHom`: an element vanishing at every `k`-point lies
  in every maximal ideal. `A` is a Jacobson ring, so the Jacobson radical of
  `0` is its nilradical, and the element is nilpotent.
- `values a` is the set `{φ a | φ : A →ₐ[k] k}`. `values_finite_or_cofinite`:
  for `A` of finite type over algebraically closed `k`, this set is finite or
  cofinite. The map `k[X] → A`, `X ↦ a`, is of finite presentation, so the
  image of `Spec A → Spec k[X]` is constructible
  (`PrimeSpectrum.isConstructible_range_comap`). By the Nullstellensatz, `c` is
  in `values a` exactly when the closed point `(X - c)` (`linePoint c`) lies in
  this image. `finite_or_cofinite_preimage` shows that a constructible subset of
  `Spec k[X]` contains finitely or cofinitely many of the points `(X - c)`. The
  proof is by induction over constructible sets
  (`IsConstructible.empty_union_induction`). An open set with complement
  `V(I)` contains all `(X - c)` except roots of some nonzero `g ∈ I`, or none
  of them if `I = 0`. Finite and cofinite are preserved under unions and
  complements.
- `exists_pow_expChar_pow_eq_zero`: let `q` be the exponential characteristic of
  `k`. If `x` is nilpotent, and `x = 0` whenever `k` has characteristic zero,
  then `x ^ q ^ e = 0` for some `e`.
- Characteristic-zero Cartier steps. `nat_mul_pow_mul_pow_eq_zero` is a ring
  identity. If `M ≥ 2`, `a ^ M = b ^ M = 0` and `(a + c b) ^ M = 0`, then
  `M a^(M-1) c^(M-1) b^(M-1) = 0`; the proof multiplies by `a ^ (M-2)` and
  expands binomially. `eq_zero_of_comul`: let `k` have characteristic zero and
  `δ : A → A ⊗ A` be a ring map. Suppose `δ n = n ⊗ 1 + (c ⊗ 1)(1 ⊗ n)`, `c` is
  a unit and `n` is nilpotent. Then `n = 0`. Induct on `M` with `n ^ (M+1) = 0`.
  The identity gives `(M+1) (n^M ⊗ n^M) = 0`, hence `n^M ⊗ n^M = 0`. A linear
  form `g` with `g (n^M) ≠ 0` (vector spaces are projective) then gives
  `n^M = 0`. Two corollaries follow, both for a `k`-algebra map `δ`.
  `aeval_eq_zero_of_primitive`: if `δ u = u ⊗ 1 + 1 ⊗ u` and `P` is additive on
  `k`, a nilpotent `P(u)` is zero. `pow_sub_one_eq_zero_of_grouplike`: if
  `δ u = (u ⊗ 1)(1 ⊗ u)` with `u` a unit, a nilpotent `u^m - 1` is zero.
- Additive polynomials. `eval_add_prod_sub`: let `Λ` be a finite additive
  subgroup of a field. The polynomial `P = ∏_{λ ∈ Λ} (X - λ)` satisfies
  `P(a + b) = P(a) + P(b)`. For fixed `a`, the polynomial
  `P(X + a) - P(X) - P(a)` has degree less than `|Λ|` and vanishes on `Λ`,
  because `P` is invariant under translation by `Λ`. Hence it is zero.
  `eval₂_add_of_eval_add`: a polynomial additive on an infinite field is
  additive after any ring map `k → R`, in every commutative ring `R`. Its
  additivity defect `addDefect`, a polynomial in two variables, vanishes on
  `k²`, hence is zero (`MvPolynomial.funext`).
- `mem_of_compl_finite` (with additive version `add_mem_of_compl_finite`): an
  infinite subgroup with finite complement is the whole group. If `g ∉ H`, then
  `x ↦ g x⁻¹` maps `H` into the complement injectively.
  `eq_one_of_pow_expChar_pow_eq_one`: if `z ^ q ^ e = 1` in `k`, then `z = 1`,
  since `(z - 1) ^ q ^ e = 0`.

### Points and global functions (section `Points`)

`pt k` is `Spec k` over itself. the imported `RelativeRoot.AdditiveGroupQuotient.structureMap T : k →+* Γ(T)` sends `c` to the
pullback of `c` along `T ⟶ Spec k`, and morphisms over `Spec k` preserve it
(`appTop_constants`). `finiteType_constants` translates "locally of finite
type" for an affine `X` into finiteness of type of `RelativeRoot.AdditiveGroupQuotient.structureMap X`. For an affine
`X` over `Spec k`, a ring map `φ : Γ(X) → B` compatible with constants gives a
point `pointOf X φ` over `PseudoComplete.algebraSpec k B`
(`Spec.map φ ≫ X.isoSpec.inv`). Conversely, `pointHom t` evaluates global
functions at a `B`-point `t`. `rationalPoint` and `ratHom` are the same
constructions for `B = k`. `exists_comul` builds the comultiplication of an
affine group `K`. It is the `k`-algebra map `δ : Γ(K) → Γ(K) ⊗ Γ(K)` obtained
by evaluating at `t₁ * t₂`, where `t₁` and `t₂` are the two tautological points
with values in `Γ(K) ⊗ Γ(K)`.

### Coordinates (section `Coordinates`)

`AddCoordinate V` is a natural identification of `T`-points of `V` with `Γ(T)`
that turns the group law into addition. `MulCoordinate V` identifies them with
`Γ(T)ˣ`, multiplicatively. `AddCoordinate.ofVectorGroup` builds the first from
`IsVectorGroupOfDimension V 1`. `MulCoordinate.ofIso` builds the second from an
isomorphism with `𝔾ₘ`, via `yonedaGrp` and `Gm.pointsEquiv`. For
`ψ : K ⟶ V`, let `u` be the coordinate of `ψ` itself, an element of `Γ(K)`
(resp. a unit). The following hold.

- `exists_comul`: `u` is primitive, `δ u = u ⊗ 1 + 1 ⊗ u` (resp. group-like,
  `δ u = (u ⊗ 1)(1 ⊗ u)`). This holds because `ψ` is a homomorphism
  (`MonObj.mul_comp`).
- `image ψ` is the additive subgroup of `k` (resp. subgroup of `kˣ`) of
  coordinates of rational points of the form `s ≫ ψ`. `coe_image` /
  `mem_image_iff` show that it equals `values u`.
- `AddCoordinate.exists_polynomial_map`: for `F ∈ k[X]`, there is `χ : V.X ⟶ V.X`
  with coordinate `F(coordinate)` on every `T`-point (by Yoneda).

### The two cases (section `Cases`)

`Dichotomy ψ` is the conclusion of the statement for a fixed `ψ`. Write
`A = Γ(K)`, a finite-type `k`-algebra, and `Λ = image ψ`.

`dichotomy_add` (additive coordinate). If `Λ` is infinite, then
`values_finite_or_cofinite` makes it cofinite, so `add_mem_of_compl_finite`
gives `Λ = k`, which is the first alternative. Otherwise let `P` be the
vanishing polynomial of `Λ`. It is additive (`eval_add_prod_sub`). `P(u)`
vanishes at every `k`-point, so it is nilpotent. In characteristic zero
`aeval_eq_zero_of_primitive` gives `P(u) = 0`. Hence `F(u) = 0` for
`F = P ^ q ^ e`, with `q` the exponential characteristic. `F` is still additive,
and every root of `F` in `k` lies in `Λ`. Take `W = V` and the polynomial map `χ`
of `F`. Invariance: the coordinate of `(v * (s ≫ ψ)) ≫ χ` is
`F(x + s^*u) = F(x) + s^*F(u) = F(x)`. Separation: if `F(a) = F(b)`, then
`F(b - a) = 0`, so `b - a ∈ Λ`.

`dichotomy_mul` (multiplicative coordinate). The infinite case is the same,
using `mem_of_compl_finite`. If `Λ` is finite of order `m`, it equals the group
of `m`-th roots of unity in `k` (`card_rootsOfUnity`). Then `u^m - 1` vanishes at
every `k`-point, so it is nilpotent. It is zero in characteristic zero by
`pow_sub_one_eq_zero_of_grouplike`. Hence `u^N = 1` for `N = m q^e`. Take
`W = V` and `χ = (𝟙 V.X) ^ N`, the `N`-th power map. Invariance follows from
`(s^*u)^N = 1`. Separation: `(a⁻¹ b)^N = 1` forces `(a⁻¹ b)^m = 1`
(`eq_one_of_pow_expChar_pow_eq_one`), so `a⁻¹ b ∈ Λ`.

### Main theorem

`stabilizerImageDichotomy` splits `IsElementaryQuotient V`. For a vector group,
`V.X` is affine and `dichotomy_add` applies with `AddCoordinate.ofVectorGroup`.
For an isomorphism `f` with `𝔾ₘ`, `V.X` is affine because `𝔾ₘ`'s underlying
scheme is (a pullback of affine schemes) and `f` induces an isomorphism of
underlying schemes. Then `dichotomy_mul` applies with `MulCoordinate.ofIso f`.

# The discriminant Brauer class of an algebra with unitary involution

Module `Langlands.Algebra.UnitaryDiscriminant.Class`, namespace `Langlands.UnitaryDiscriminant`.

Let `(B, τ)` be a central simple algebra of degree `2m` with a unitary involution over a separable
quadratic extension `L/F`. This module defines the Brauer class over `F` of the discriminant
algebra `D(B, τ)` of Knus, Merkurjev, Rost and Tignol through an explicit determinant factor set,
computed in a supplied finite Galois matrix splitting chart. It also constructs an actual central
simple `F`-algebra representing the class.

## Inputs

All the definitions below take the following arguments.

* Fields `F L M : Type u` with a tower `F → L → M` (`[IsScalarTower F L M]`), where
  `[Algebra.IsQuadraticExtension F L]`.
* The automorphism of the quadratic center, `ι : L ≃ₐ[F] L`, and `hι : ι ≠ 1`. It is then the
  nontrivial automorphism of `L/F`, and `L/F` is Galois.
* An `L`-algebra `B : Type v` and `τ : B → B` with `hτ : IsUnitaryInvolution ι τ`
  (`Langlands.IsUnitaryInvolution`: additive, product-reversing, involutive, and equal to `ι` on
  the scalars of `L`).
* The input trivialization `e : M ⊗[L] B ≃ₐ[M] Matrix (Fin (2 * m)) (Fin (2 * m)) M`, an
  `M`-algebra isomorphism. Its matrix size `2m` is the degree of `B`.
* For `discriminantCSA`, `discriminantSplittingChart` and `discriminantClass`, also
  `[FiniteDimensional F M] [IsGalois F M]`.

Such a chart exists for every finite-dimensional central simple `L`-algebra of degree `2m` when
`L/F` is separable: `Langlands.Algebra.UnitaryDiscriminant.Splitting` constructs one
(`galoisSplitting`) and defines `discriminantClassOf`, the class computed in that chart, from the
algebra and its involution alone.

`B` is not separately required to be central simple: for `m ≥ 1` the existence of `e` already
forces `B` to be a finite-dimensional central simple `L`-algebra of degree `2m`, since dimension,
centrality and simplicity descend along the field extension `M/L`. Matrix algebras and division
algebras are treated alike: the construction only reads `B` through `e` and `τ`. The
construction does not use the characteristic of `F`; in particular it applies to every field of
characteristic zero. The hypotheses allow `m = 0`, which occurs only for `B = 0`.

## The construction

Write `H = centerFixing F L M` (the automorphisms of `M/F` fixing `L`, which is `Gal(M/L)`),
`ε(g) = 0` for `g ∈ H`, `ε(g) = 1` otherwise, and `j b = e (1 ⊗ b)`.

1. **Lifts** (`chartLift hι hτ e`, module `Lifts`). For each `g ∈ Gal(M/F)` an invertible matrix
   `P_g` with

   ```text
   P_g · g(j b) · P_g⁻¹ = j b          if g fixes L,
   P_g · g(j b)ᵀ · P_g⁻¹ = j (τ b)     if g acts on L through ι,
   ```

   for all `b ∈ B`. The conjugation `β_g` on the right is the transport through `e` of
   `g ⊗ id_B`, respectively of the anti-automorphism `g ⊗ τ`, of `M ⊗_L B`.
2. **Twisted factor set** (`chartFactor hι hτ e`). Because `β_{gh} = β_g ∘ β_h`, there are
   units `λ(g, h)` with `P_g · g⋆P_h = λ(g, h) · P_{gh}`, where `g⋆X = g(X)` for `g ∈ H` and
   `g⋆X = g(X)^{-T}` otherwise.
3. **Determinant factor set** (`discriminantCocycle hι hτ e`, defined as
   `detCocycle (centerFixing F L M) (chartLift hι hτ e) (chartFactor hι hτ e) m`):

   ```text
   μ(g, h) = λ(g, h)^m · g(det P_h)^{ε(g)} · (-1)^{m ε(g) ε(h)}.
   ```

4. **Classes.**
   * `relativeDiscriminantClass hι hτ e : relativeCohomology F M 2` is
     `BrauerComparison.unitClass μ`, its class in Mathlib's ordinary `H²(Gal(M/F), Mˣ)`.
   * `discriminantCSA hι hτ e : CSA.{u, u} F` is `BrauerComparison.regularCSA μ`: the fixed
     algebra of the regular matrix representation twisted by `μ`, an actual finite-dimensional
     central simple `F`-algebra. `discriminantSplittingChart hι hτ e` is its splitting chart
     `M ⊗[F] discriminantCSA ≃ₐ[M] Matrix Gal(M/F) Gal(M/F) M`.
   * `discriminantClass hι hτ e : BrauerGroup.{u, u} F` is `Langlands.Brauer.classOf` of
     `discriminantCSA`, an element of the Library's algebraic Brauer group of `F`.

### How the inputs enter

* **The trivialization `e`** enters only through `j b = e (1 ⊗ b)`. It fixes the lifts `P_g` up to
  unit scalars (`exists_lift_of_mem`, `exists_lift_of_not_mem`, by Skolem–Noether through the
  chart). Changing those scalars changes `μ` by a coboundary
  (`relativeDiscriminantClass_eq_of_lifts`), so the class does not depend on the choices made
  in `chartLift` and `chartFactor`. This module does not prove that the class is independent of
  `M` and `e`.
* **The automorphism `ι`** decides which Galois elements are outer: `g ∉ H` exactly when `g` acts
  on `L` through `ι` (`apply_algebraMap_of_not_mem`). For these, the lift intertwines `g(j b)ᵀ`
  with `j (τ b)`, using that `τ` is `ι`-semilinear (`outerTarget`). Outer elements contribute the
  determinant factor `g(det P_h)` and, for two outer elements, the sign `(-1)^m`. The index-two
  property `mul_mem_centerFixing_iff` and `ι² = 1` (`apply_apply_of_ne_one`) make `g ↦ ε(g)` a
  homomorphism.

## Results (typing laws)

* `discriminantCocycle_isTwoCocycle`: `μ` is a two-cocycle of `Gal(M/F)` with values in `Mˣ`
  (`Langlands.ScalarTwoCocycle.IsTwoCocycle`, the identity `μ(g,h) μ(gh,k) = g(μ(h,k)) μ(g,hk)`),
  so the class is defined.
* `discriminantCocycle_of_mem`: on automorphisms fixing `L`, `μ(g, h) = λ(g, h)^m`.
* `relativeClass_discriminantSplittingChart`: the relative class of `discriminantCSA` in
  `discriminantSplittingChart` is `relativeDiscriminantClass`.
* `brauerContinuousEquiv_discriminantClass`: for any separable closure `S` of `F` containing `M`,
  the Library's comparison `BrauerComparison.brauerContinuousEquiv F S` sends `discriminantClass`
  to the inflation of `relativeDiscriminantClass` (`relativeToContinuous`).
* `relativeDiscriminantClass_eq_of_lifts`: any family of lifts with the defining property of
  `chartLift`, with any factor set, gives the same relative class.
* `discriminantCocycle_mul_self`, `two_nsmul_relativeDiscriminantClass` and
  `two_nsmul_discriminantClass`: `μ^2` is the coboundary of `g ↦ det P_g`, so both classes are
  killed by `2`. This agrees with KMRT (10.28), where `D(B, τ)` carries an involution of the first
  kind.

## Relation to the discriminant algebra

Source: M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*, AMS
Colloquium Publications 44 (1998), registered as
`knus-merkurjev-rost-tignol-1998-book-of-involutions`, SHA-256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`. Printed page `p` is PDF page
`p + 23`.

* §10.A, Definition (10.4) and property (b), printed p. 116: the `λ`-power `λ^k A`, with
  `λ^k End_F(V) = End_F(Λ^k V)`.
* §10.B, Lemma (10.6), printed p. 117: the exterior pairing `∧ : Λ^m V × Λ^m V → Λ^{2m} V` is
  nonsingular, symmetric for `m` even and skew-symmetric for `m` odd. Definition (10.11) and
  property (a), printed p. 119: the canonical involution `γ` of `λ^m A`, which in the split case
  is the adjoint involution of `∧`.
* §10.D, Definition (10.20) and Proposition (10.21), printed p. 124: the involution `σ^{∧k}`
  induced on `λ^k A`; for `A = End(V)` and `σ = σ_h` it is adjoint to `h^{∧k}`. Formula (10.25),
  printed p. 126: `ε_S ε_{S'} = (-1)^m` for the signs `e_S ∧ e_{S'} = ε_S e` of complementary
  index sets.
* §10.E, Lemma (10.27), printed p. 127, and Definition (10.28), printed pp. 127–128: for `(B, τ)`
  of degree `2m` with center the field `K` (here `L`), `γ` and `τ^{∧m}` commute,
  `θ = τ^{∧m} ∘ γ` is an `F`-automorphism of order `2` of `λ^m B` acting on `K` as the nontrivial
  automorphism, and `D(B, τ)` is the `F`-subalgebra of `θ`-invariant elements.
* Proposition (10.30), printed p. 129: `D(B, τ) ⊗_F K ≅ λ^m B`, and `ind D(B, τ)` divides `4`.
* §10.F, Corollary (10.35), printed p. 131: for a hermitian space `(V, h)` of even dimension,
  `D(End_K(V), σ_h)` is Brauer equivalent to the quaternion algebra `(K, disc h)_F`. Here
  `disc h = (-1)^{n(n-1)/2} det h` (§10, introduction, printed p. 114), which for `n = 2m` is
  `(-1)^m det h`.

**From Definition (10.28) to `μ`.** By Proposition (10.30), `D = D(B, τ)` is the descent along
`M/F` of `λ^m B ⊗_L M`, on which `g ∈ Gal(M/F)` acts by `id ⊗ g` for `g` fixing `L` and by
`θ ⊗ g` otherwise. Through `λ^m e`, `λ^m B ⊗_L M ≅ End_M(Λ^m M^{2m})`, a matrix algebra indexed by
the `m`-subsets of `{1, …, 2m}`. Write `Λ(X)` for the `m`-th compound matrix and `J` for the
matrix of `∧`, with entries `±1` at complementary index sets. Then:

* `id ⊗ g` becomes `X ↦ Λ(P_g) g(X) Λ(P_g)⁻¹` (functoriality of `λ^m` applied to step 1);
* `θ ⊗ g` becomes `X ↦ Λ(P_g) Jᵀ g(X) (Λ(P_g) Jᵀ)⁻¹`. Here `γ(X) = J⁻¹ Xᵀ J` by (10.11)(a),
  `τ^{∧m} ⊗ g` acts as `X ↦ Λ(P_g) g(X)ᵀ Λ(P_g)⁻¹` by step 1, (10.20) and `Λ(Xᵀ) = Λ(X)ᵀ`, and
  `J` has entries in `{0, ±1}`.

So the descent datum of `D` has lifts `Q_g = Λ(P_g)` (`g` fixing `L`) and `Q_g = Λ(P_g) Jᵀ`
(otherwise). The pairing satisfies `Λ(Y)ᵀ J Λ(Y) = det(Y) J`, since `Λ(Y) x ∧ Λ(Y) y = det(Y) x ∧ y`.
Together with `J^2 = (-1)^m` (by (10.6) and (10.25)), `Λ(c Y) = c^m Λ(Y)` and the multiplicativity
of `Λ`, step 2 gives

```text
Q_g · g(Q_h) = μ(g, h) · Q_{gh}.
```

For example, if `g` and `h` are both outer, then
`Q_g g(Q_h) = Λ(P_g) Jᵀ Λ(g P_h) Jᵀ = g(det P_h) Λ(P_g g(P_h)^{-T}) (J^2)ᵀ = λ^m g(det P_h) (-1)^m Λ(P_{gh})`.
The Library's comparison of Brauer classes with `H²` uses Serre's factor set `Q_s s(Q_t) Q_{st}⁻¹`
of a descent datum (J.-P. Serre, *Local Fields* (1979), Chapter X, §5, Proposition 8 and
Lemma 1, printed pp. 158–159 / PDF pp. 164–165, registered as `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`). Hence `[D(B, τ)]`
corresponds to the class of `μ`, which is `discriminantClass`. The class is killed by `2`, so it
does not change if the opposite sign convention is used. This identification is the mathematical
justification of the definition. It is not formalized: the Lean code contains no exterior powers
and defines the class through `μ`.

**Examples, not proved here.** For `B = M_{2m}(L)` with `τ` the adjoint involution of a hermitian
matrix `H` and `e` the canonical chart, one may take `P_g = 1` for `g` fixing `L` and
`P_g = H⁻¹` otherwise. Then `λ = 1` and `μ(g, h) = ((-1)^m det H)^{-ε(g) ε(h)}`. This is the
inflation of the quaternion factor set of `L/F` with parameter `((-1)^m det H)⁻¹`, which defines
the same class as the parameter `(-1)^m det H`, as in Corollary (10.35). For a split center,
KMRT (10.31), printed p. 129, gives `D(E × E^op, ε) ≅ λ^m E`, and Proposition (10.32), printed
p. 130, identifies `D(B, τ) ⊗_F K` with `D(B × B^op, ε)`. On the cocycle side, the elements of
`Gal(M/F)` fixing `L` see only `λ^m` (`discriminantCocycle_of_mem`). These computations, the
independence of `M` and `e`, and the scalar extension law are not part of this module.

## Scope

The center `L` is a field, as in KMRT (10.28). The split center `F × F` is outside the
definition; its role under scalar extension is described above. The class is defined over the
Library's actual Brauer quotient `BrauerGroup.{u, u} F`, with `F`, `L`, `M` in one universe `u`
and `B` in any universe.

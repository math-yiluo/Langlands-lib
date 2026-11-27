# The central quaternionic spin Hasse kernel from spinor-norm inputs

Module `Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinKernelReduction`, namespace
`Langlands.GroupScheme`.

The module states four propositions about spin covers of quaternionic orthogonal groups and
proves that together they imply `NumberFieldQuaternionicSpinKernelHasseStatement` (module
`Rational/NumberFieldQuaternionicSpinHasseKernels`). It proves none of the four propositions.

## Setting and notation

`F` is a field, `D` a central division `F`-algebra with `dim_F D = 4`, and `σ` a first-kind
involution of `D` whose symmetric subspace has dimension `3` (an orthogonal involution).
`q : σ.QuadraticForms (Fin n)` is a quadratic form in the sense of Tits with polar Gram matrix
`Q = σ.polar q`. The hermitian value of a row `x : Fin n → D` is
`h(x, x) = σ.sesqForm Q x x = ∑ i j, x i * Q i j * σ (x j)`; it is `σ`-symmetric. Left
multiplication by `d ∈ D` on the line `D x` satisfies `h(d x, d x) = d h(x, x) σ(d)`.
`Nrd` is the reduced norm `CentralSimple.reducedNorm F D F (1 ⊗ₜ d)`.

`G` is a group scheme over `Spec F`, `p : G ⟶ σ.normOneIsometryGroup q` a central isogeny
onto the reduced-norm-one isometry group, and `e : kernel p ≅ μ₂` an isomorphism with the
group scheme of square roots of unity.

## Definitions

* **`KummerImageTrivial hp e K M a z hz`**. Here `F ⊆ K ⊆ M` are fields, `M/K` is finite
  Galois, `a ∈ Kˣ` and `z ∈ Mˣ` with `z² = a`. The Kummer cocycle `s ↦ s(z)/z` takes values in
  the square roots of unity of `M`; through `e` they are points of `kernel p`. The predicate
  says that there is `b ∈ G(M)` with `s(z)/z = b · s(b)⁻¹` in `G(M)` for every
  `s ∈ Gal(M/K)`, where `s(b)` is `relativeConjugate F K M G s b`. This is the left side of
  `ScalarSpinorNormBoundary` (module `Rational/NumberFieldScalarSpinHasseReduction`) for the
  same central isogeny and kernel isomorphism. It says that the class of `a` in
  `H¹(Gal(M/K), μ₂)` dies in `H¹(Gal(M/K), G(M))`.
* **`FirstKindInvolution.DivisionOrAnisotropicAt σ q K`**, for a field `K` over `F`: either
  every nonzero element of `K ⊗ D` is a unit, or every row `y : Fin n → K ⊗ D` with
  `∑ j k, y j * (1 ⊗ Q j k) * σ_K (y k) = 0` is zero. Here `σ_K` is `σ.baseChange K`.

## The four statements

All four quantify over every universe `u` and require `dim_F D = 4`,
`dim_F Sym(σ) = 3`, `NeZero n`, `3 ≤ n` and a nondegenerate `q`. In the three statements about
covers, `G` is simply connected and `p` is a central isogeny.

1. **`QuaternionicSpinKernelMuStatement`**. In characteristic zero the kernel of `p` is
   isomorphic to `μ₂`.
2. **`QuaternionicSpinLineSimilitudeBoundaryStatement`**. In characteristic zero, let
   `x` be a row with `c = h(x, x) ≠ 0`, and let `d ∈ D` and `N ∈ Fˣ` satisfy
   `d c σ(d) = N c` and `Nrd(d) = N`. For every finite Galois `M/F` and every `z ∈ Mˣ` with
   `z² = N`, `KummerImageTrivial hp e F M N z hz` holds. With `κ = d² / N`, the isometry that
   sends `a x` to `a κ x` for `a ∈ D` and fixes the orthogonal complement of `D x` lies in the
   special unitary group, and its spinor norm is the class of `N`: the boundary of the exact
   sequence `1 → μ₂ → G → SU → 1` sends it to the class of `N`.
3. **`NumberFieldQuaternionicSpinRealBoundaryStatement`**. `F` is a number field and `v` a real
   place with completion `K = v.Completion`, at which `DivisionOrAnisotropicAt σ q K` holds.
   For every finite Galois `M/K`, every `a ∈ Kˣ` and every square root `z ∈ Mˣ` of `a`,
   `KummerImageTrivial hp e K M a z hz` implies that `a` is a square in `K`.
   Here `K ⊗ D` is Hamilton's quaternions, or `K ⊗ D` is split and the corresponding real
   quadratic form of dimension `2n` is definite. In both cases the spinor norm of the
   special unitary group over `K` is trivial.
4. **`NumberFieldQuaternionicSpinorValueStatement`**. `F` is a number field and `a ∈ Fˣ`.
   Suppose `a` is a square in `v.Completion` at every real place `v` where
   `DivisionOrAnisotropicAt σ q v.Completion` holds. Then there are a row `x`, `d ∈ D` and
   `s ∈ Fˣ` with `h(x, x) ≠ 0`, `d h(x, x) σ(d) = Nrd(d) h(x, x)` and `Nrd(d) = a s²`.

## The reduction

**`numberFieldQuaternionicSpinKernelHasse_of_boundaries`**: the four statements imply
`NumberFieldQuaternionicSpinKernelHasseStatement.{u}`.

Proof. Let `π : G ⟶ O(q)` be a spin cover and `α` a cocycle with values in `kernel π` on the
cover of the finite Galois extension `L/F`, whose image in `G` is locally trivial. Since `n ≥ 4`,
`n ≠ 0` and `3 ≤ n`.

* The spin cover factors as `p₀ ≫ ι` with `p₀` a central isogeny onto the identity component
  `O(q)⁰` and `ι` its inclusion. The isomorphism `connectedIsometryIsoNormOne`, applied with
  `quaternionicNormOneIsometryConnectedness`, identifies `O(q)⁰` with the reduced-norm-one
  isometry group. Composing gives a central isogeny `p` onto that group. Statement 1 gives
  `e : kernel p ≅ μ₂`. The two kernel pullback isomorphisms `kernelPostcompIso` give
  `k : kernel π ⟶ kernel p` with `k ≫ kernelι p = kernelι π`, so `α` and `α.map k` have the
  same image in `G`.
* As in `kernelMapHasse_of_spinorNormBoundary`, read through `e` the cocycle `α.map k` is a
  `μ₂`-valued crossed homomorphism of `Gal(L/F)`. `KummerCocycle.exists_radical` writes it as
  the Kummer cocycle of some `a ∈ Fˣ` with a square root `z ∈ L`.
* At a real place `v` with `DivisionOrAnisotropicAt σ q v.Completion`, local triviality and
  `GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial` give
  `KummerImageTrivial` over `v.Completion` and its algebraic closure, which is finite over it
  (`Global.finiteArchimedeanAlgebraicClosure`). Statement 3 makes `a` a square of
  `v.Completion`.
* Statement 4 gives `x`, `d` and `s` with `Nrd(d) = N = a s²`. Statement 2 for `M = L` and the
  square root `z s` of `N` gives `b ∈ G(L)` trivializing the Kummer cocycle of `N`. Since `s` is
  fixed by `Gal(L/F)`, the Kummer cocycles of `z s` and `z` agree. Hence `b` trivializes the
  image of `α.map k` in `G`, and `GaloisCocycle.isTrivial_iff` gives triviality of the image
  of `α`.

## Provenance

The exact sequence `Spin_K → SU_K → H¹(K, μ₂) → H¹(K, Spin)` for a skew-hermitian form over a
quaternion division algebra is Kneser, *Lectures on Galois Cohomology of Classical Groups*
(1969), §5.11, sequence (4), printed p. 101 (PDF p. 107). The spin Hasse principle for such
forms is §5.10, printed pp. 95–98 (PDF pp. 101–104). Statements 2–4 are derived: they split
the statement that `a` lies in `θ(SU(F)) F^{×2}` once it lies in `θ(SU(F_v)) F_v^{×2}` at every
place into the spinor norm of a line similitude (statement 2), the triviality of spinor norms
at the real places of statement 3, and an arithmetic choice of a line similitude over the
number field (statement 4). Statement 1 is the fact that the fundamental group of the
connected special orthogonal group of type `D_n` is `μ₂`. The reduction follows the proof of
`kernelMapHasse_of_spinorNormBoundary` in the scalar case.

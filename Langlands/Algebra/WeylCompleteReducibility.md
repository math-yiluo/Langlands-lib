# Complete reducibility for Lie algebras with central radical

Author: Worker 1429.

This module proves a form of Weyl's complete reducibility theorem in the
namespace `Langlands.Algebra.WeylCompleteReducibility`. Throughout, `k` is a
field of characteristic zero (no algebraic closure is assumed), `L` is a
finite-dimensional `k`-Lie algebra with Mathlib's `HasCentralRadical k L`
(the solvable radical equals the centre), and `M` is a finite-dimensional
Lie module of `L`.

## Provenance

The main result `complementedLattice_of_isSemisimple_center` says: if every
central element of `L` acts on `M` by a semisimple endomorphism, then every Lie
submodule of `M` has a complementary Lie submodule. Lie algebras whose radical
equals the centre are the reductive Lie algebras, and the theorem is the
standard semisimplicity criterion for representations of reductive Lie
algebras in characteristic zero (cf. Bourbaki, *Lie Groups and Lie Algebras*,
Chapter I, §6, on reductive Lie algebras). For semisimple `L` (trivial centre)
it is Weyl's theorem (e.g. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §6.3). The Lean statements here are internal helper
results for the task proving `ReductiveCharZeroSemisimplicityStatement`. The
proof below was arranged for this formalization; it does not follow either
textbook exactly.

## Declarations

- `inf_killingCompl_le_center`: for an ideal `K`, `K ⊓ K.killingCompl` lies in
  the centre. It is solvable by Mathlib's Cartan criterion
  (`LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero`). Solvable ideals lie
  in the radical, which is the centre.
- `center_le_killingCompl_top`: central elements have zero adjoint action, so
  they pair to zero with everything under the Killing form. This needs neither
  characteristic zero nor finite dimension of `L`.
- `sup_killingCompl_eq_top`: `K ⊔ K.killingCompl = ⊤`. By the previous two
  lemmas, `K ⊓ K.killingCompl = K ⊓ (Killing orthogonal of ⊤)`. A dimension
  count with `BilinForm.finrank_add_finrank_orthogonal` and
  `Submodule.finrank_sup_add_finrank_inf_eq` gives the result.
- `map_ad_pow`: a Lie algebra morphism `φ` satisfies
  `φ ((ad d)^n e) = (ad (φ d))^n (φ e)`.
- `toEnd_eq_zero_of_traceForm_eq_zero`: suppose the centre acts on `M` by zero,
  and `traceForm k L M x y = 0` for every `y`. Then `x` acts on `M` by zero. Let
  `K` be the kernel of the action and `R` the trace-form orthogonal of `L`. Then
  `K ≤ R`, and `J = K.killingCompl ⊓ R` has zero trace form on `M`. Mathlib's
  module Cartan criterion
  (`LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero`) shows that
  `⁅J, J⁆` acts on `M` by nilpotent endomorphisms. Take `d, e ∈ ⁅J, J⁆`. Some
  iterate `(ad d)^N e` acts by zero on `M` (by `map_ad_pow`), so it lies in
  `K ⊓ K.killingCompl`, which is central. Hence `(ad d)^(N+1) e = 0`. Engel's
  theorem (`LieAlgebra.isNilpotent_iff_forall`) makes `⁅J, J⁆` nilpotent, so `J`
  is solvable. Therefore `J` lies in the centre, which is contained in `K`. The
  modular law, with `K ⊔ K.killingCompl = ⊤`, gives `R = K ⊔ J = K`.
- `exists_casimir`: suppose the centre acts by zero and some element acts
  nonzero. Let `𝔤` be the image of `L` in `End M`. Its trace form on `M` is
  invariant, and nondegenerate by the previous lemma. The Library Casimir
  `LieCasimir.casimirImage` of this form (for `Module.finBasis`, mapped by the
  inclusion of `𝔤`) gives an endomorphism `c` of `M`. It commutes with the
  action (`casimirImage_commutes_generator`). Its trace is `finrank k 𝔤 ≠ 0`, so
  it is not nilpotent. Each summand has the form `X (Y m)` with `X ∈ 𝔤`, so `c`
  maps `M` into every subspace that contains all brackets `⁅x, m⁆`.
- `exists_lie_eq_zero_of_commute`: let `W ≠ ⊤` be a Lie submodule that contains
  all brackets and has no Lie submodules other than `⊥` and `W`. Let `T` be a
  non-nilpotent endomorphism that commutes with the action and has range in `W`.
  Then some `v ∉ W` is killed by `L`. The kernel of `T` is a Lie submodule. If
  it met `W` in `W`, then `T² = 0`. Otherwise it meets `W` in `⊥`. Since
  `range T ⊆ W ≠ ⊤`, the kernel is nonzero, and any nonzero kernel vector works.
- `isSemisimple_of_surjective`: if a surjection `π` satisfies `g ∘ π = π ∘ f` and
  `f` is semisimple, then so is `g`. Here `π` intertwines polynomial
  evaluation, so `g` is killed by the squarefree minimal polynomial of `f`.
- `exists_lie_eq_zero_of_lie_mem` (Lemma A): assume central elements act
  semisimply on `V`. Let `W ≠ ⊤` be a subspace containing every `⁅x, m⁆`. Then
  some `v ∉ W` satisfies `⁅x, v⁆ = 0` for all `x`. The proof is by strong
  induction on `finrank k V`, and treats four cases.
  1. Some Lie submodule `N` satisfies `⊥ < N < W`. Apply the induction
     hypothesis to `V ⧸ N`, using `isSemisimple_of_surjective` for the centre.
     This gives `v ∉ W` with `⁅L, v⁆ ⊆ N`. Then apply it again to the Lie
     submodule `N + k v`, whose dimension is at most `finrank W`. The vector
     obtained lies outside `W`.
  2. Otherwise, suppose some central `z` acts by a nonzero endomorphism `T`. It
     is semisimple, hence not nilpotent. It commutes with the action, and its
     range is in `W`. Apply `exists_lie_eq_zero_of_commute`.
  3. Otherwise, suppose the centre acts by zero but some element acts nonzero.
     Apply `exists_lie_eq_zero_of_commute` to the Casimir from
     `exists_casimir`.
  4. Otherwise, every element acts by zero, and any `v ∉ W` works.
- `exists_isCompl` (Theorem W): every Lie submodule `W` has a complementary Lie
  submodule. The proof uses the Hom trick. Let `𝒱 ⊆ End M` be the set of `f`
  with range in `W` that act on `W` by a scalar. It is a Lie submodule of `End M`
  under `⁅x, f⁆ = ρ(x) ∘ f − f ∘ ρ(x)`. Let `𝒰 ⊆ 𝒱` be the subset with scalar
  zero. Then `𝒰` contains every bracket `⁅x, f⁆`. If `W ≠ ⊥`, a linear
  projection onto `W` shows `𝒰 ≠ 𝒱`. A central `z` acts on `End M` by
  `ad(ρ z)`, which is semisimple by `ad_isSemisimple_of_isSemisimple`, and
  remains semisimple on `𝒱`. Lemma A gives an `L`-invariant `f ∈ 𝒱` acting on
  `W` by a scalar `a ≠ 0`. Its kernel is the required complement.
- `complementedLattice_of_isSemisimple_center`: the resulting
  `ComplementedLattice (LieSubmodule k L M)` instance statement.

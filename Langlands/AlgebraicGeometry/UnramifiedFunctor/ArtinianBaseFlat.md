# Step 1 of Murre's induction: finite free extensions with prescribed residue field

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseFlat`, a supporting module of
`murreArtinianBase` (module `MurreArtinianBase`). Namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase`. Both results are standard commutative
algebra, derived here for the descent argument of `ArtinianBaseDescent`.

* `isLocalRing_of_ker_nil`: a ring `P` with a surjection `φ` onto a field whose kernel consists
  of nilpotent elements is local. An element outside the kernel is a unit, because
  `x y - 1` is nilpotent for any `y` with `φ y = (φ x)⁻¹`.

* `flatExt`: finite free extensions with prescribed residue field. Let:
  - `C` be a local artinian `R`-algebra with a surjection `π : C → ℓ` onto a field;
  - `N` be a finite field extension of `ℓ` with `[N : ℓ] ≤ n`.

  Then there is a local artinian `C`-algebra `P`, finite and free as a `C`-module, with a
  surjection `πP : P → N` compatible with `π`.

  The proof is strong induction on `n`.
  - If `[N : ℓ] = 1`, take `P = C`.
  - Otherwise pick `θ ∈ N \ ℓ` with minimal polynomial `g` of degree at least 2, and a monic
    lift `ĝ ∈ C[X]` of the same degree.
  - `P₁ = C[X]/(ĝ)` is finite free over `C` (`Monic.free_adjoinRoot`,
    `Monic.finite_adjoinRoot`), hence artinian. It maps onto `ℓ₁ = ℓ[X]/(g)`. The kernel of
    this map lies in `m_C P₁`, which is nilpotent, so `P₁` is local by
    `isLocalRing_of_ker_nil`.
  - `N` is an extension of `ℓ₁` (via `θ`) of degree `[N : ℓ]/deg g < n`. The induction
    hypothesis, applied to `P₁ → ℓ₁ → N`, gives `P` over `P₁`.
  - `P` is finite free over `C` by transitivity.

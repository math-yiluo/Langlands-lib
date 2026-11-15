# Step 1 of Murre's induction: field points

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseField`, a supporting module of
`murreArtinianBase` (module `MurreArtinianBase`). Namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase`. Notation as in `ArtinianBaseTools`.

`k` is a field with an `R`-algebra structure; later it is the residue field of `R`. The module
studies points of `F` with values in finite extensions of `k`, using (F1a), (F1b) and strong
(F5). It constructs a minimal field of definition and shows that a minimal point separates
embeddings into fields. These facts make the chart of a point a monomorphism. The module is
internal to the proof.

## Descent along field extensions

All of these take a finite extension `N / k` and an intermediate field `F₀`.

* `field_descent`: suppose that for any two `F₀`-embeddings `a, b` of `N` into a field
  (`R`-algebra maps agreeing on `F₀`), `θ ∈ F(Spec N)` has the same restriction along `a` and
  `b`. Then `θ` comes from `F(Spec F₀)`.
  - `N ⊗_{F₀} N` is artinian, so by `eq_of_fieldAgree` its two pullbacks of `θ` agree.
  - `flatDescent` for the faithfully flat `F₀ → N` concludes.
* `purelyInseparable_descent`: if `N / F₀` is purely inseparable, every `θ ∈ F(Spec N)` comes
  from `F₀`. Two `F₀`-embeddings of `N` into a field coincide.
* `exists_conj`: two embeddings of a finite normal extension `N / F₀` into a field that agree on
  `F₀` differ by an automorphism of `N / F₀`. This uses `range_le_of_normal`.
* `galois_descent`: if `N / F₀` is Galois and `θ ∈ F(Spec N)` is invariant under
  `Gal(N/F₀)`, then `θ` comes from `F₀`. This is `field_descent` combined with `exists_conj`.

## Minimal points and the monomorphism property

* `IsMinimal η`, for a field `L` and `η ∈ F(Spec L)`: every `R`-algebra map `j : L₀ → L` from a
  field such that `η` comes from `F(Spec L₀)` along `j` is surjective.
* `mono_galois`: let `N / k` be finite Galois and `η ∈ F(Spec L)` minimal. Two `k`-embeddings
  `σ₁, σ₂ : L → N` with `σ₁^* η = σ₂^* η` are equal.
  - Let `H ⊆ Gal(N/k)` be the stabilizer of `θ = σ₁^* η`. It contains `Gal(N/σ₁ L)`, and also
    an automorphism `g` with `g ∘ σ₁ = σ₂` (by `AlgHom.liftNormal`).
  - By `galois_descent`, `θ` comes from the fixed field `N^H`, which lies in `σ₁ L`.
  - Minimality forces `N^H = σ₁ L`, so `g` fixes `σ₁ L` and `σ₁ = σ₂`.
* `toKAlgHom`: an `R`-algebra map between `k`-algebras is `k`-linear when `R → k` is
  surjective.
* `mono_field`: assume `R → k` is surjective with nilpotent kernel, `L / k` is finite separable,
  and `η ∈ F(Spec L)` is minimal. Then two `R`-algebra maps `σ₁, σ₂ : L → K'` to any field `K'`
  with `σ₁^* η = σ₂^* η` are equal.
  - `K'` is a `k`-algebra, because the kernel of `R → K'` contains the kernel of `R → k`.
  - Let `N` be the normal closure of `L` in a separable closure of `k`; it is finite Galois
    over `k`. Fix an embedding of `N` into an algebraic closure `K''` of `K'`.
  - Composed into `K''`, both `σᵢ` land in the image of `N` (`range_le_of_normal`), so they
    factor through `k`-embeddings `σᵢ' : L → N`.
  - `fieldInj` gives `σ₁'^* η = σ₂'^* η`. Then `mono_galois` gives `σ₁' = σ₂'`, hence
    `σ₁ = σ₂`.

## Minimal fields of definition

* `exists_minimal`: let `R → k` be surjective, `κ / k` finite, and `η ∈ F(Spec κ)`. Then there is
  an intermediate field `k ⊆ E ⊆ κ` and `θ ∈ F(Spec E)` such that:
  - `η` is the restriction of `θ`;
  - `θ` is minimal;
  - `E / k` is separable.

  The proof takes `E` of least degree among the intermediate fields from which `η` comes. If
  `θ` came from a field `L₀` along `j : L₀ → E`, then the image of `L₀` in `κ` is an
  intermediate field. It lies inside `E`, and `η` comes from it, so it equals `E` by
  minimality of the degree. Hence `j` is surjective.

  For separability, `purelyInseparable_descent` makes `θ` come from the separable closure of
  `k` in `E`. Minimality forces that closure to be all of `E`.

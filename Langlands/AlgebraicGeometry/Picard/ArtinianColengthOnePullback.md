# The ring pullback of an artinian colength-one extension

Worker 387 wrote this supporting module for Task 6297, which proves Murre's
condition (F4′) for the two-axis class presheaf. The module is pure commutative
algebra and imports only Mathlib. Everything is in the namespace
`Langlands.AlgebraicGeometry.Picard.ArtinianColengthOne`, in every universe `u`.

## Setting

`Λ : Type u` is a local ring with maximal ideal `m` and residue field
`k = IsLocalRing.ResidueField Λ`. `A'` is a commutative `Λ`-algebra. The two hypotheses are
the ones in `UnramifiedFunctor.ArtinianLifting`:

- `hinj : Function.Injective (algebraMap Λ A')`;
- `hlen : Module.length Λ (A' ⧸ LinearMap.range (Algebra.linearMap Λ A')) = 1`, so the
  cokernel of `Λ → A'` has length one.

Some results also need `Λ` to be artinian. The `omit` lines in the source mark the
results that do not.

## Results

- `smul_mem_range hlen hz x`: if `z ∈ m`, then `z • x` lies in the image of `Λ` for every
  `x : A'`. Proof: by `Module.length_eq_one_iff` the cokernel is a simple `Λ`-module. Its
  annihilator is a maximal ideal (`IsSimpleModule.annihilator_isMaximal`), so it equals `m`
  because `Λ` is local. Hence `z` kills the class of `x`.
- `exists_mem_maximalIdeal hinj hlen hz x`: in the same situation, `z • x = algebraMap w`
  for some `w ∈ m`. Proof: suppose the `w` from `smul_mem_range` were a unit. Then
  `algebraMap z * x` would be a unit of `A'`. But `z` is nilpotent: every element of the
  maximal ideal of a local zero-dimensional ring is
  (`Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal`). So its image is nilpotent, which is
  a contradiction. `A'` is nontrivial because `Λ → A'` is injective.
- `exists_of_mem_map hinj hlen hy`: every element `y` of the extended ideal
  `m.map (algebraMap Λ A')` equals `algebraMap w` for some `w ∈ m`. Proof: induction over
  the span. The scalar-multiplication step uses `exists_mem_maximalIdeal`.
- `isNilpotent_maximalIdeal`: the maximal ideal of a local artinian ring is nilpotent. Its
  Jacobson radical is nilpotent (`IsArtinianRing.isNilpotent_jacobson_bot`) and equals `m`.
- `includeLeft_surjective Λ A'`: the left inclusion `A' → A' ⊗[Λ] k` is surjective. Mathlib's
  isomorphism `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` identifies
  `A' ⊗[Λ] (Λ ⧸ m)` with `A' ⧸ m A'`, and `includeLeft` corresponds to the quotient map.
- `ker_includeLeft Λ A'`: the kernel of `includeLeft` is `m.map (algebraMap Λ A')`, by the
  same isomorphism.
- `isNilpotent_ker_includeLeft Λ A'`: that kernel is nilpotent. If `m ^ n = ⊥`, then
  `(m A') ^ n = (m ^ n) A' = ⊥` (`Ideal.map_pow`).
- `isPullback hinj hlen`: in `CommRingCat`, the square

  ```
  Λ  ──ofId──▶  A'
  │             │ includeLeft
  ofId          ▼
  ▼            A' ⊗[Λ] k
  k ─includeRight─▶
  ```

  is a pullback. Stated with Mathlib's `IsPullback`:
  `IsPullback (ofId Λ k) (ofId Λ A') includeRight includeLeft`, each map turned into a
  `CommRingCat` morphism with `CommRingCat.ofHom`.

## Proof of `isPullback`

The square commutes because both composites are the algebra map `Λ → A' ⊗[Λ] k`. Next, the
forgetful functor `CommRingCat ⥤ Type u` reflects isomorphisms, and therefore reflects limits
(`reflectsLimit_of_reflectsIsomorphisms`). So by `IsPullback.of_map` it suffices to check the
square of underlying types, which uses the concrete criterion `Types.isPullback_iff`:

- Joint injectivity: two elements of `Λ` with the same image in `A'` are equal, by `hinj`.
- Existence: let `c : k` and `a' : A'` have the same image in `A' ⊗[Λ] k`. Lift `c` to some
  `x₀ : Λ`. Then `a' - algebraMap x₀` lies in the kernel of `includeLeft`, which is `m A'`.
  By `exists_of_mem_map` it equals `algebraMap w` with `w ∈ m`. The element `x₀ + w` of `Λ`
  maps to `c` in `k`, because `w ∈ m`, and to `a'` in `A'`.

## Provenance

These are standard facts of commutative algebra. They were chosen for this project as
internal helpers. Condition (F4′) itself is from J. P. Murre, *Representation of unramified
functors. Applications (according to unpublished results of A. Grothendieck)*, Séminaire
Bourbaki exp. 294, Corollary 1, printed pp. 246–247 (PDF pp. 5–6), registered as
`murre-1965-bourbaki-294-unramified-functors`. Murre says (F4′) and (F4) are equivalent
using (F1b), (F5) and the exactness of `A → A' ⇉ A' ⊗_A A'`. The proof in this project does
not follow that route. It uses the fibre-product presentation `Λ = k ×_{A' ⊗[Λ] k} A'` proved
here, together with the Library's gluing of line bundles along such squares (see
`TwoAxisClassArtinianLiftingProof`).

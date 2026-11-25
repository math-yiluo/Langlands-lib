# Surjective endomorphisms of abelian varieties are isogenies

Lean module: `Langlands.AbelianScheme.FlatEqualDimensionQuasiFinite`. Namespaces
`Langlands.AlgebraicGeometry.FlatEqualDimension` (general lemmas) and
`Langlands.AbelianScheme.SurjectiveIsogeny` (main theorem).

The main theorem `SurjectiveIsogeny.isIsogeny_of_surjective` proves the content of the
statement `Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyStatement`.
If the underlying scheme morphism of an endomorphism `α` of an abelian scheme `A`
over an algebraically closed field `k` is surjective, then `α` is an isogeny, that is, finite,
flat and surjective. The one-line proof of the statement itself is
`Langlands.AbelianScheme.fieldSurjectiveEndomorphismIsogeny`, in the separate module
`Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyProof`.

## Provenance

This is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source
`milne-abelian-varieties-1986-author-2022`), Proposition 8.1, p. 12, implication (b) ⇒ (d) for
endomorphisms, where `dim A = dim B` is automatic. Milne derives (b) ⇒ (c) (finite kernel) from
the theorem on the dimension of fibres. The Lean proof does not pass through the kernel. It uses
the dimension formula for flat local homomorphisms, which Mathlib proves as
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, to show that `hom α` is quasi-finite
at closed points. It then uses Mathlib's openness of the quasi-finite locus (a consequence of
Zariski's main theorem) to get finiteness directly. `stalkDimension` and the general lemmas
below are internal auxiliary material.

## Declarations

### `stalkDimension X x` (definition)

The Krull dimension `ringKrullDim (X.presheaf.stalk x)` of the local ring of `X` at `x`.

### `eq_maximalIdeal_of_comap_eq`

**Statement.** Let `R → S` be a flat local homomorphism of noetherian local rings (an algebra
with `Module.Flat R S` and `IsLocalHom (algebraMap R S)`). Suppose that
`ringKrullDim R = ringKrullDim S = g` for a natural number `g`. Then every prime `Q` of `S`
whose contraction to `R` is the maximal ideal of `R` is the maximal ideal of `S`.

**Proof.** Let `p` and `P` be the maximal ideals and `I = pS`. Flatness gives going-down
(`Algebra.HasGoingDown.of_flat`). The dimension formula then gives
`ht P = ht p + ht (P / I)`. Both heights equal `g`, which is finite
(`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`). So `ht (P / I) = 0` and `P / I` is a
minimal prime of `S / I` (`Ideal.height_eq_zero_iff`). Now `Q` contains `I` and is contained
in `P`. Then `Q / I` is a prime below the minimal prime `P / I`, so `Q / I = P / I`. Pulling back
to `S` gives `Q = P`.

### `isOpen_singleton_of_forall_specializes`

**Statement.** In a noetherian quasi-sober topological space, a closed point `x` such that
every `z` with `z ⤳ x` equals `x` is an open point.

**Proof.** The complement of `{x}` is the union of the irreducible components not containing
`x`. If a component `C` contains `x`, its generic point specializes to `x`, so it equals `x`;
then `C = closure {x} = {x}`. Conversely, components not containing `x` miss `x`. There are
finitely many components, each closed, so the complement is closed.

### `eq_of_specializes_of_apply_eq`

**Statement.** Let `f : X ⟶ Y` be flat, and let `x : X` have noetherian local rings at `x` and
at `f x`, with `stalkDimension X x = stalkDimension Y (f x) = g`. If `z ⤳ x` and `f z = f x`,
then `z = x`.

**Proof.** The generizations of `x` are the image of `X.fromSpecStalk x`
(`Scheme.range_fromSpecStalk`), so `z` comes from a prime `q` of the local ring at `x`. The square
`SpecMap_stalkMap_fromSpecStalk` and injectivity of `Y.fromSpecStalk (f x)` (a preimmersion)
show that `q` contracts to the maximal ideal of the local ring at `f x`. The stalk map is flat
(`Flat.stalkMap`) and local, so `eq_maximalIdeal_of_comap_eq` makes `q` the closed point.
Hence `z = X.fromSpecStalk x (closedPoint) = x`.

### `quasiFiniteAt_of_ringKrullDim_eq`

**Statement.** Let `f : X ⟶ Y` be flat and locally of finite type with `X` a noetherian
topological space. Let `x` be a closed point with noetherian local rings at `x` and `f x` of the
same finite dimension `g`. Then `f.QuasiFiniteAt x`.

**Proof.** By `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber` it suffices that the
point `f.asFiber x` is open in the fibre `f.fiber (f x)`. The fibre is a scheme (so quasi-sober)
and a noetherian space: it is homeomorphic to the subspace `f ⁻¹' {f x}` (`fiberHomeo`). The
point is closed, because it is the preimage of `{x}` under the embedding `fiberι`. It has no
proper generization: a generization maps under `fiberι` to a generization of `x` with the same
image under `f`, which equals `x` by `eq_of_specializes_of_apply_eq`.
`isOpen_singleton_of_forall_specializes` finishes.

### `SurjectiveIsogeny.isIsogeny_of_surjective`

**Statement.** Let `k` be algebraically closed, `A` an abelian scheme over `Spec k`, and
`α : A ⟶ A` with `Surjective (hom α)`. Then `IsIsogeny α`.

**Proof.**

1. *Setup.* Choose `g` with `A.HasRelativeDimension g` (`exists_hasRelativeDimension_of_field`).
   `A.X.left` is noetherian and integral (`field_isNoetherian`, `field_isIntegral`). `hom α` is
   proper, since `hom α ≫ A.X.hom = A.X.hom` is proper.
2. *Flat.* `A.X.left` is reduced, being smooth over a field
   (`SmoothReducedProof.isReduced_of_smooth_over_field`). A surjective morphism is dominant. The
   Library's `DominantHomFlat.flat_of_isDominant` makes `hom α` flat.
3. *Quasi-finite at closed points.* At every closed point `x`, the local ring has dimension `g`
   (`fieldSmoothClosedPointStalkDimension`). The image `hom α x` is closed (proper morphisms are
   closed maps), so its local ring also has dimension `g`. `quasiFiniteAt_of_ringKrullDim_eq`
   applies.
4. *Locally quasi-finite.* The quasi-finite locus is open (`Scheme.Hom.quasiFiniteLocus`). Every
   point `z` specializes to a closed point of the compact closed set `closure {z}`
   (`IsClosed.exists_closed_singleton`). That closed point lies in the locus, so `z` does too.
   Hence the locus is everything, and `hom α` is locally quasi-finite
   (`quasiFiniteLocus_eq_top_iff`).
5. *Finite.* Proper and locally quasi-finite give finite
   (`IsFinite.of_isProper_of_locallyQuasiFinite`). With flatness and the hypothesis, `isIsogeny_iff`
   finishes.

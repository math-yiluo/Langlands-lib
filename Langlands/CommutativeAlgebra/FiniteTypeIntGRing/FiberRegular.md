# Regularity of fibres through a Jacobian criterion

This helper module for the proof of
`Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement` proves that a fibre
of an algebra over a polynomial ring is regular when enough derivations are
available. All declarations are in the namespace
`Langlands.CommutativeAlgebra.FiniteTypeIntGRing`.

## Statements

- `span_range_toCotangent_eq_top_iff f hf`: in a Noetherian local ring `R`
  with maximal ideal `𝔪`, a family `f` in `𝔪` generates `𝔪` if and only if
  the classes of the `f i` span the cotangent space `𝔪/𝔪²` over the residue
  field.
- `exists_cotangent_basis N`: for a prime `N` of a Noetherian ring `P` (in a
  universe `u`), there are a finite type `ι : Type u` and a family
  `g : ι → P` whose images in `L = P_N` lie in the maximal ideal of `L`, have
  linearly independent classes in its cotangent space and generate the
  maximal ideal of `L`.
- `isRegularRing_fiber_of_jacobian N Φ hΦ₁ hΦ₂` (**fibre regularity**): let
  `R₀` be a Noetherian ring, `τ` a finite type with decidable equality,
  `P = MvPolynomial τ R₀`, `B` a regular ring that is a `P`-algebra, and `N`
  a prime of `P` whose residue field `κ(N)` is formally smooth over `R₀`.
  Suppose that for every prime `r` of `B` there is a ring map
  `Φ r : B →+* TrivSqZeroExt κ(r) (τ → κ(r))` into the trivial square-zero
  extension `κ(r) ⊕ κ(r)^τ` such that
  - (`hΦ₁`) the first component of `Φ r b` is the residue of `b` in `κ(r)`,
  - (`hΦ₂`) for every polynomial `g ∈ P`, the second component of
    `Φ r (image of g)` is `v ↦ residue in κ(r) of the image of ∂g/∂X_v`.

  Then the fibre `N.Fiber B = κ(N) ⊗_P B` is a regular ring.

Informally, `Φ r` packages derivations `B → κ(r)` that extend the partial
derivatives `∂/∂X_v` of `P`. The module is internal to the project's proof
and does not follow a specific reference.

## Proofs

**Generators and cotangent space.** Rewrite the range of the classes as the
image of the corresponding family in `𝔪` under `Ideal.toCotangent`. By
Nakayama's lemma (`CotangentSpace.span_image_eq_top_iff`) spanning is
equivalent to the family spanning `𝔪` as an `R`-submodule of itself. Mapping
along the injective inclusion `𝔪 → R` translates this into
`Ideal.span (range f) = 𝔪`.

**Cotangent basis.** `N` is finitely generated, say by a finite set `s`. The
images of `s` in `L` generate the maximal ideal of `L`
(`Localization.AtPrime.map_eq_maximalIdeal`), so by the first statement their
classes span the cotangent space. Mathlib's `exists_linearIndependent'`
extracts a linearly independent subfamily with the same span; it is indexed
by a finite type because it injects into `s`. By the first statement again,
this subfamily generates the maximal ideal of `L`.

**Fibre regularity.**

1. *Noetherian.* By Mathlib's `Ideal.Fiber.algEquivAux₁`, `N.Fiber B` is
   isomorphic to a quotient of a localization of the Noetherian ring `B`.
2. By Mathlib's `isRegularRing_iff` it suffices to prove that every
   localization of `N.Fiber B` at a prime `q` is regular local. Let `r` be the
   prime of `B` under `q` (its preimage under `b ↦ 1 ⊗ b`), and
   `B_r = Localization.AtPrime r`. Since `q` lies over `N`, `N` is the
   preimage of `r` in `P`.
3. Choose `g : ι → P` by `exists_cotangent_basis N`. Since `κ(N)` is
   formally smooth over `R₀`, the Jacobian criterion
   `linearIndependent_pderiv_of_linearIndependent_cotangent` (module
   `PolynomialJacobian`, applied to `L = P_N`) makes the gradients of the
   `g j`, reduced to `κ(N)`, linearly independent over `κ(N)`.
4. *A derivation on `B_r`.* The values of `Φ r` on `r.primeCompl` are units,
   because their first components are nonzero residues
   (`TrivSqZeroExt.isUnit_iff_isUnit_fst`). So `Φ r` extends to
   `Ψ : B_r →+* TrivSqZeroExt κ(r) (τ → κ(r))` (`IsLocalization.lift`), and
   the first component of `Ψ` is the residue map of `B_r` (checked on `B` by
   `IsLocalization.ringHom_ext`).
5. Let `f j` be the image of `g j` in `B_r`. It lies in the maximal ideal of
   `B_r` since `g j ∈ N`. By `hΦ₂`, the second component of `Ψ (f j)` is the
   gradient of `g j` reduced to `κ(N)` and then mapped into `κ(r)` along the
   induced field map `κ(N) → κ(r)` (`Ideal.ResidueField.map`). Linear
   independence is preserved under extension of scalars along a field map
   (`linearIndependent_algebraMap_comp_iff`), so the `(Ψ (f j)).snd` are
   linearly independent over `κ(r)`.
6. `B_r` is regular local because `B` is regular. The derivation test
   `isRegularLocalRing_quotient_of_trivSqZeroExt` (module `JacobianQuotient`)
   shows that `B_r ⧸ (f j)` is regular local.
7. The ideal `(f j)` of `B_r` is the extension of `N` to `B_r`: the map
   `P → B_r` factors through `P_N` (`Localization.localRingHom`), and the
   images of the `g j` generate the maximal ideal `N P_N` of `P_N` (step 3).
   Mathlib's `Ideal.Fiber.algEquivAux₂ N q` identifies the localization of
   `N.Fiber B` at `q` with `B_r ⧸ N B_r`, so this localization is regular
   local (`IsRegularLocalRing.of_ringEquiv`).

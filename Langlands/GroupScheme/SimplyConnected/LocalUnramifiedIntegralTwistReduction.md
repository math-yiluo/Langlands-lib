# Integral twists give vanishing on finite unramified covers

Authors: Worker 5015.

This module proves
`Langlands.GroupScheme.LocalSimplyConnectedUnramifiedIntegralTwistReductionStatement.{u}` at
arbitrary universe `u`. The proof is the theorem
`Langlands.GroupScheme.localSimplyConnectedUnramifiedIntegralTwistReduction`.

The statement says that `LocalSimplyConnectedUnramifiedIntegralTwistStatement.{u}` implies
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement.{u}`; its paired Markdown file
`LocalUnramifiedIntegralTwistReductionStatement.md` gives both sides in full. The theorem uses no
premise beyond that hypothesis.

## The implemented proof

Assume the twisting statement. Let `F : Type u` be a nonarchimedean local field, `G` an affine
group scheme over `Spec F` with `IsSimplyConnected G`, and `E` a finite-dimensional intermediate
field of `SeparableClosure F / F` with `E ≤ L₀`, where
`L₀ = LocalGalois.Separable.inertiaFixedField F`. Let `ξ` be a cocycle of `G` on the cover
`Spec E → Spec F`.

1. **The model.** The twisting statement, applied to `F` and `G`, gives a smooth integral model
   `M : IntegralModel 𝒪[F] F G` with connected special fibre and the twisting property for every
   finite Galois `E₁/F` with an `F`-embedding into `L₀`.
2. **Finiteness of `G`.** `G.X.left` is affine (`isAffine_of_isAffineHom`). `G` is smooth, since a
   simply connected group is semisimple and so connected reductive
   (`hG.isSemisimple.isConnectedReductive.smooth`), hence locally of finite type.
3. **A Galois cover.** `L₀/F` is Galois (the published instance `inertiaFixedField_isGalois`), so
   `GaloisCocycle.exists_finiteDimensional_isGalois_between` (module
   `Langlands.GroupScheme.LocalUnramifiedTwistDescent`) gives an intermediate field `E₁`, finite
   and Galois over `F`, with `E ≤ E₁ ≤ L₀`. Let `φ : E →ₐ[F] E₁` be the inclusion.
4. **Refinement.** The published `fieldExtension_fpqc` shows that `Spec E₁ → Spec E` is
   surjective, flat and quasi-compact. So by the published `Cocycle.isTrivial_refine_iff`, `ξ` is
   trivial once its refinement `ξ₁ = ξ.refine (ringTestMap F φ)` is. The cover
   `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E)))` of the statement is definitionally
   the published `ringTest F E`, and `ringTest F E₁` is definitionally the published
   `GaloisCocycle.cover F E₁` (the spectrum `(algSpec _).obj (op (CommAlgCat.of F E₁))`). So
   Lean accepts `ξ` as a cocycle on `ringTest F E` and `ξ₁` as a cocycle on
   `GaloisCocycle.cover F E₁` without any transport.
5. **The twist.** The Galois values `GaloisCocycle.value ξ₁ : Gal(E₁/F) → G(E₁)` form a crossed
   homomorphism by the published `GaloisCocycle.value_mul`. The inclusion `E₁ ≤ L₀` makes `L₀` an
   `E₁`-algebra with the scalar tower `F → E₁ → L₀`. The twisting property of `M` for `E₁` and
   these values gives `h ∈ G(L₀)` such that every
   `h⁻¹ * relativeExtend (value ξ₁ (σ|E₁)) * σ(h)`, `σ ∈ Gal(L₀/F)`, has integral coordinates.
6. **Conclusion.** `GaloisCocycle.isTrivial_of_unramified_integral_twist`, with the normal
   extension `L = L₀` (and `L₀ ≤ L₀`), shows that `ξ₁` is trivial. By step 4, `ξ` is trivial.

`GaloisCocycle.isTrivial_of_unramified_integral_twist` descends `h` to a finite Galois unramified
extension and applies the published finite-level criterion `GaloisCocycle.isTrivial_of_integral_twist`,
which rests on the local form of Kaletha–Prasad Lemma 8.1.4
(`localUnramifiedIntegralCocycleVanishing`). The module `LocalUnramifiedTwistDescent.md`
describes that proof.

## Provenance

Provenance: derived. The argument is the cohomological part of the proofs of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Theorems 10.6.1 and 10.6.4 (printed pp. 397–399,
PDF pp. 428–430), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`: after the
building step has twisted the cocycle into an Iwahori subgroup, Lemma 8.1.4 makes it trivial.
The source works with continuous cocycles of `Gal(K/k)`; the Library's cocycles live on finite
covers, so the proof first refines to a finite Galois unramified cover and then descends the
twisting element to a finite level.

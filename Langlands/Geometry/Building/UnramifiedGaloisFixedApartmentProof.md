# Galois-fixed points of stable apartments over algebraic coefficient extensions

Authors: Worker 4356 wrote the Lean proof and the first version of this note, in the
shared draft of Task 5553 of the previous project instance. Worker 47 checked both
against the current Library and the sources, revised this note and submitted the proof
for Task 5513 (a23aef86-8894-44b0-b1c9-b76314d0865f).

Lean module: `Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentProof`.

This module proves the published statement
`Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentStatement` (module
`Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement`). Let
`K = inertiaFixedField F` be the maximal unramified extension of a nonarchimedean local
field `F`. Let `D` be an equipollence class of valuations for a maximal split torus `i_K`
of `G_K`, and assume `D` is Galois-stable. Then `D` has a point fixed by every
`σ : K ≃ₐ[F] K`. This is the fixed point of Kaletha–Prasad §9.2.1, in its corrected form.
The theorem is `Langlands.Geometry.Building.unramifiedGaloisFixedApartment`, of type
`UnramifiedGaloisFixedApartmentStatement.{u}`.

The proof does not use a finite splitting field. It proves the fixed point for every
algebraic coefficient extension `K/k`, for a group of finite type with finitely many
upstairs relative roots, and then specializes.

## Fixed points of finite orbits

`exists_fixed_of_finite_orbit`: let a group `M`, not necessarily finite, act by affine
equivalences `ρ : M →* (P ≃ᵃ[ℝ] P)` on a real affine space `P`. If the orbit of some point
`p` is finite, some point is fixed by all of `M`. Let `O` be the orbit as a `Finset` and
`N = |O|`. The fixed point is the barycenter `c +ᵥ p`, where
`c = N⁻¹ • Σ_{q ∈ O} (q -ᵥ p)`. The proof applies the linear part of `ρ m` to `c`,
reindexes the sum along the bijection `q ↦ ρ m q` of `O`, and cancels the term
`N • (ρ m p -ᵥ p)`. The published `exists_fixed_of_finite_affineAction` (module
`Langlands.Geometry.Building.SplitApartmentGaloisFixedPoint`) needs a finite group.
`Aut(K/F)` is infinite here, so this orbit version is proved instead.

## Open fixers (namespace `KPApartmentData`)

Let `K/k` be a field extension, let `T` and `G` be defined over `k` with `G` affine, and let
`i : T.toGrp ⟶ G` have monomorphic base change `i_K`. Let `ω : Kˣ → ℝ`, and let
`D : KPApartmentData i_K ω` satisfy `GaloisStable k K i D`.

`exists_finite_fixing_field`: assume that `K/k` is algebraic, that `G` is locally of finite
type over `k`, and that the set of relative roots of `i_K` is finite. For each
`x : D.Apartment` there is a finite-dimensional intermediate field `E` of `K/k` with the
following property. Every `σ` that fixes `E` pointwise and acts trivially on the roots
(`galoisRootAction k K i σ = 1`) fixes `x` under the published `galoisAction`.

Proof. For each root `a`, choose `u_a` in the root group with `x(a, u_a) ≠ ⊤`. This uses
the published `IsRootDatumValuation.exists_ne_top`, which is V 0. The points `u_a` are
finitely many. Their coordinates (the published `GaloisPoint.coordinates` of
`baseChangeCoeffEquiv k K G u_a`) are `k`-algebra maps to `K` from the coordinate ring of
`G`, which is of finite type. The published `IdentityComponent.exists_finite_fixing_algHoms`
gives a finite intermediate field `E` whose fixer fixes all of these maps. Let `σ` fix `E`
and the roots. Then `σ⁻¹` does too, so `rationalConjugate k K G σ⁻¹ u_a = u_a`
(`baseChangeCoeffEquiv_rationalConjugate`, `GaloisPoint.coordinates_conjugate`), and
`σ⁻¹` fixes each root character (`galoisRootAction_val`). Galois stability gives
`σ · x = v +ᵥ x` for some `v` (published `galoisStable_iff_equipollent`). Evaluating at
`(a, u_a)` with `RootFunctionFamily.galoisAction_apply` gives
`x(a, u_a) = x(a, u_a) + a(v)`. So `a(v) = 0` for every root, `v` lies in
`rootAnnihilator` (`mem_rootAnnihilator`), and `v +ᵥ x = x` by the published
`IsRootDatumValuation.vadd_eq_self_iff`.

`exists_galoisFixed_of_isAlgebraic`: under the same hypotheses, some `x : D.Apartment`
has `RootFunctionFamily.galoisAction k K T G σ x.val = x.val` for every `σ : K ≃ₐ[k] K`.

Proof. Pick `x₀` (the apartment is nonempty) and let `ρ` be the published affine action
`galoisAffineAction`. Take `E` from the previous lemma for `x₀`. The map
`σ ↦ (galoisRootAction k K i σ, σ|_E)` takes values in the finite type
`Equiv.Perm (roots) × (E →ₐ[k] K)`. Suppose two automorphisms `σ, τ` have the same image.
Then `τ⁻¹σ` fixes `E` and the roots, hence fixes `x₀`, so `ρ σ x₀ = ρ τ x₀`
(`galoisAffineAction_apply`). The orbit of `x₀` is therefore finite.
`exists_fixed_of_finite_orbit` gives a point fixed by `ρ`, and its underlying family is
fixed by `RootFunctionFamily.galoisAction`.

## The unramified statement

`unramifiedGaloisFixedApartment : UnramifiedGaloisFixedApartmentStatement.{u}`.
Here `k = F` and `K = inertiaFixedField F`. This is an algebraic extension: it is Galois by
the published instance `inertiaFixedField_isGalois`, and Mathlib's instances derive
`Algebra.IsAlgebraic` from that. `G` is affine and smooth (the fields
`IsConnectedReductive.isAffineHom` and `IsConnectedReductive.smooth`). So `G` and `G_K` are
locally of finite type over their bases, and `G_K` is affine by pullback. The monomorphism
instance comes from the published `mono_of_isMaximalSplitTorus hi`. The upstairs relative
roots are finite by the published `IsSplitTorus.finite_relativeRoots`, applied to the split
torus underlying the maximal split torus `hi` (`hi.isSplitSubtorus.1`). The general
theorem then applies.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The statement is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §9.2.1,
printed pp. 325–326 (PDF pp. 356–357). Its second full paragraph on printed p. 326 is
replaced in the authors' corrections (2024), PDF p. 39. KP use a finite Galois extension
`k'/k` inside `K` over which the torus is defined and split. `Gal(K/k')` fixes the apartment
pointwise, so each `Γ`-orbit factors through the finite group `Gal(k'/k)`. The Lean proof
replaces the splitting field by an open fixer of finitely many root-group points; this needs
only that the extension is algebraic. It replaces the finite quotient by the finiteness of
one orbit. The barycenter argument is standard.

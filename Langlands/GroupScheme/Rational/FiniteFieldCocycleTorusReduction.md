# Finite-Galois cocycles of smooth connected affine groups over finite fields

Lean module: `Langlands.GroupScheme.Rational.FiniteFieldCocycleTorusReduction`, namespace
`Langlands.GroupScheme.Cocycle`.

Let `K` be a field and `G` a group scheme over `Spec K`. For a `K`-algebra `A`,
`ringTest K A` is `Spec A` over `Spec K`, and `ringTestMap K f` is the spectrum map of a
`K`-algebra homomorphism `f`. Cocycles are the Library's natural group-valued cocycles
`Cocycle G U`, and `ξ.IsTrivial` means `ξ` is a coboundary `ξ(a, b) = c(a) · c(b)⁻¹` for a
cochain `c : U ⟶ G.X`. This module proves the finite-field case of
`Langlands.GroupScheme.QuasiSplitCocycleTorusReductionStatement`: over a finite field, every
such cocycle on a finite Galois cover is a coboundary, so it reduces to the trivial torus.

## Declarations

- `ringTestMap_fpqc f`: for a `K`-algebra homomorphism `f : A →ₐ[K] B` of fields, the
  underlying scheme morphism of `ringTestMap K f` is quasi-compact, flat and surjective.
- `epi_ringTestMap f`: `ringTestMap K f` is an epimorphism in `Over (Spec K)`.
- `exists_finite_factor G x T`: let `Ω/K` be an algebraic extension and `G` affine and
  locally of finite type over `K`. Every point `x : Spec Ω ⟶ G.X` over `K` comes from a
  finite subextension `E ⊆ Ω` that contains a given finite subset `T ⊆ Ω`: there is
  `xE : Spec E ⟶ G.X` with `ringTestMap K E.val ≫ xE = x`.
- `ringTestMap_galois_mul σ τ`: `ringTestMap K (σ * τ) = ringTestMap K σ ≫ ringTestMap K τ`
  for `σ τ ∈ Gal(L/K)`. The spectrum functor reverses composition.
- `toFun_galois_mul ξ σ τ`: for a cocycle `ξ` on `Spec L`, the Galois values
  `ξ_σ := ξ(𝟙, ringTestMap K σ)` satisfy the crossed-homomorphism rule
  `ξ_{στ} = ξ_σ · σ^*(ξ_τ)`. Here `σ^* y` means `ringTestMap K σ ≫ y`.
- `isTrivial_of_frobenius ξ c h`: let `K` be finite and `L/K` finite Galois with Frobenius
  `φ = FiniteField.frobeniusAlgEquivOfAlgebraic K L`. If `ξ_φ = c · (φ^* c)⁻¹` for a
  cochain `c : Spec L ⟶ G.X`, then `ξ` is trivial.
- `isTrivial_of_finite G ξ`: let `K` be finite (`[Fintype K]`), `G` smooth, affine and
  connected over `K`, and `L/K` finite Galois. Every cocycle `ξ : Cocycle G (ringTest K L)`
  is trivial.
- `nonempty_torusReduction_of_finite hG ξ`: let `K` be finite (`[Finite K]`), `G` connected
  reductive (`hG : IsConnectedReductive G`) and `L/K` finite Galois. Every cocycle `ξ` on the
  cover `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))` has a torus reduction,
  `Nonempty ξ.TorusReduction`.

## Proofs

`ringTestMap_fpqc` makes `B` an `A`-algebra through `f` and applies the Library lemma
`fieldExtension_fpqc`. For `epi_ringTestMap`, the underlying flat surjective scheme
morphism is an epimorphism (`Flat.epi_of_flat_of_surjective`), and an epimorphism of
underlying schemes is one in the over category (`Over.epi_of_epi_left`).

`exists_finite_factor` works with coordinates. `Lie.pointCoordinates G` identifies points
`Spec Ω ⟶ G.X` with `K`-algebra maps `y` from the coordinate algebra of `G` to `Ω`. The
coordinate algebra is of finite type (`Lie.coordinateAlgebraFiniteType`), so it has a finite
generating set `s`. Let `E` be `K` adjoined with the images `y(s)` and `T`. It is finite
over `K` because every element of `Ω` is algebraic
(`IntermediateField.finiteDimensional_adjoin`). Induction on `Algebra.adjoin` shows that
`y` takes all its values in `E`, so `y` corestricts to `yE` with values in `E`. The point
`xE` with coordinates `yE` satisfies `ringTestMap K E.val ≫ xE = x`. This is the naturality
of `Lie.pointCoordinates`, after `ringTestMap` is identified with the affine map by
`FiniteFieldTorsorPoint.ringTestMap_eq_algSpec_map`.

`toFun_galois_mul` combines the cocycle identity
`ξ(𝟙, σ ≫ τ) = ξ(𝟙, σ) · ξ(σ, σ ≫ τ)` with naturality,
`ξ(σ, σ ≫ τ) = σ^* ξ(𝟙, τ)`. Here `σ ≫ τ` abbreviates
`ringTestMap K σ ≫ ringTestMap K τ`.

`isTrivial_of_frobenius` proves `ξ_{φ^n} = c · ((φ^n)^* c)⁻¹` for all `n` by induction. The
case `n = 0` is `Cocycle.toFun_self`. The step from `n` to `n + 1` uses
`φ^{n+1} = φ^n · φ`, `toFun_galois_mul`, the induction hypothesis and the hypothesis at `φ`;
the result follows by `MonObj.comp_mul`, `GrpObj.comp_inv` and the `group` tactic. Frobenius
generates `Gal(L/K)` (`FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`), so the
equation holds for every `σ`. Then `isTrivial_of_galois` from
`Langlands.GroupScheme.Rational.FiniteGaloisCocycleValues` gives triviality.

`isTrivial_of_finite` reduces to Lang's theorem over an algebraic closure `K̄` of `K`:

1. Fix a `K`-embedding `κ : L → K̄` (`IsAlgClosed.lift`), and let `φ_L` be the Frobenius of
   `L`. Lang's theorem in the Library form `FiniteFieldTorsorPoint.exists_eq_inv_mul_frobenius`
   (smooth connected affine `G`, algebraically closed `K̄`) applied to `κ^* ξ_{φ_L}` gives
   `x : Spec K̄ ⟶ G.X` with `κ^* ξ_{φ_L} = x⁻¹ · (F^* x)`. Here `F` is the Frobenius
   `FiniteField.frobeniusAlgHom K K̄`.
2. `exists_finite_factor`, applied with `T = κ(L)`, descends `x` to `xE : Spec E ⟶ G.X` for a
   finite subextension `E ⊆ K̄` containing `κ(L)`. So `κ` factors as `E.val ∘ κE` with
   `κE : L → E`. `E` is a finite field, so `E/K` is Galois, with Frobenius `φ_E`. Frobenius is
   the `|K|`-th power map, so `φ_E ∘ κE = κE ∘ φ_L` and `E.val ∘ φ_E = F ∘ E.val`.
3. The refinement `ξ' := ξ.refine (ringTestMap K κE)` is a cocycle on `Spec E`. Its value at
   `φ_E` is `ξ(κE, φ_E ≫ κE) = ξ(κE, κE ≫ φ_L) = κE^* ξ_{φ_L}`, by `refine_toFun` and
   naturality. Take the cochain `xE⁻¹`. The equation `κE^* ξ_{φ_L} = xE⁻¹ · φ_E^* xE` may be
   checked after the epimorphism `ringTestMap K E.val` (`epi_ringTestMap`). There it becomes
   the Lang equation of step 1, because `E.val^* xE = x` and `E.val ∘ φ_E = F ∘ E.val`.
   `isTrivial_of_frobenius` then shows `ξ'` is trivial.
4. `ringTestMap K κE` is fpqc (`ringTestMap_fpqc`), so the Library's
   `Cocycle.isTrivial_refine_iff` turns triviality of `ξ'` into triviality of `ξ`.

`nonempty_torusReduction_of_finite` takes smoothness, affineness and connectedness of `G`
from `IsConnectedReductive`. It applies `isTrivial_of_finite`; the cover is `ringTest K L` by
definition. Then `TorusReduction.nonempty_of_isTrivial` from
`Langlands.GroupScheme.Rational.CocycleTorusReductionBasic` reduces the trivial cocycle to
the Library's trivial torus.

## Provenance

Internal module for the proof of
`Langlands.GroupScheme.QuasiSplitCocycleTorusReductionStatement`, covering the case of a
finite base field. Its mathematical content is the classical consequence of Lang's theorem
that a smooth connected group over a finite field has trivial Galois `H¹` (Lang 1956;
Serre, *Galois Cohomology*, III.2.3; Borel–Springer 8.6 recalls it alongside Steinberg's
theorem). Here it appears in cochain form for one finite Galois cover. The proof here is
derived: it applies the Library's Lang theorem to the value at Frobenius over `K̄` and
descends the solution to a finite subextension. It formalizes no literature statement
verbatim.

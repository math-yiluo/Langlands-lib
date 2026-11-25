/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform
public import WeilConjectures.SixFunctors.Etale.Derived.Stability

/-!

# The Fourier–Deligne transform

Let `π : V ⟶ S` and `π' : V' ⟶ S` be two `S`-schemes — in the intended application a vector
bundle of rank `r` and its dual — and let `b ∈ Γ(V ×_S V', 𝒪)` be a pairing between them.
The *Fourier kernel* is the Artin–Schreier sheaf `𝒦_ψ = ℒ_{Ψ, b}` of the pairing, and the
*Fourier–Deligne transform* of `K ∈ D(V_ét)` is

`FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦_ψ)[r]`,

`p₁, p₂` being the two projections of `V ×_S V'`. The shift by the relative dimension `r`
is Laumon's normalization, the one for which the inversion theorem holds without a further
shift, up to the Tate twist `(-r)`.

The transform is a special case of a *kernel transform*
`Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]` attached to an arbitrary kernel `𝒦` on `V ×_S V'` and an
arbitrary shift `a` (`WeilConjectures.SixFunctors.Etale.Derived.KernelTransform`).

The *Fourier integrand* `ℱ_ψ(K) = p₁^* K ⊗ᴸ 𝒦_ψ` is the complex on `V ×_S V'` whose
compact-support direct image along `p₂` is the transform, before the shift.

## Main definitions

- `AlgebraicGeometry.Etale.fourierKernel`: the Fourier kernel `𝒦_ψ`.
- `AlgebraicGeometry.Etale.fourierIntegrand`: the Fourier integrand `ℱ_ψ(K) = p₁^* K ⊗ᴸ 𝒦_ψ`.
- `AlgebraicGeometry.Etale.fourierTransform`: the Fourier–Deligne transform `FT_ψ`.
- `AlgebraicGeometry.Etale.fourierTransformBoundedConstructible`: the transform as a
  functor `Dᵇc(V, Λ) ⥤ Dᵇc(V', Λ)`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_mul`,
  `AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_inv`: `𝒦_ψ ⊗ 𝒦_ψ' ≅ 𝒦_{ψψ'}` and
  `𝒦_ψ ⊗ 𝒦_{ψ⁻¹} ≅ Λ`.
- `AlgebraicGeometry.Etale.isDualizable_fourierKernel`: the kernel in degree zero is
  dualizable. Together with constructibility, Tor amplitude and local constancy this makes it
  lisse (`AlgebraicGeometry.Etale.isLisse_fourierKernel`).
- `AlgebraicGeometry.Etale.torAmplitudeIn_fourierKernel`: over a finite ring the kernel, being
  flat, has Tor amplitude in `[0, 0]`.
- `AlgebraicGeometry.Etale.isTriangulated_fourierTransform`: the transform is a triangulated
  functor.
- `AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`:
  the transform preserves the bounded constructible derived category.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

## Coefficients

The kernel transform is defined for any coefficient category `A` on which the étale six
functors are built. The Fourier kernel is a character sheaf: `Ψ : AddChar (ZMod p) Λ` acts on
it by scalars of a ring, so the Fourier kernel and the Fourier–Deligne transform are defined
over `ModuleCat Λ`, for any commutative ring `Λ` in which `p` is invertible.

The theorems of the Fourier transform files assume the coefficient hypotheses of the strongest
input of their proofs:

- **general**: formal six-functor manipulations (shifts, pullback along isomorphisms, the
  projection formula for a closed immersion, multiplicativity of Artin–Schreier sheaves): no
  hypothesis on the coefficients;
- **compactification-dependent**: the blueprint proof is formal, but `R(f)_!` is computed with
  a chosen compactification, and the proof compares two compactifications of a quasi-compact
  morphism (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`). That comparison rests on
  `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`, which is
  not proved and whose hypotheses are not settled: besides torsion coefficients, for proper
  base change, it needs a finiteness condition on the morphism giving finite cohomological
  dimension, to pass from `D⁺` to the unbounded derived category. These theorems assume
  `[Finite Λ]` and quasi-compactness of the morphism whose compactifications are compared;
- **torsion**: compact-support base change, the projection formula for `Rp₂,!`, Deligne
  finiteness of `Rf_!` or the cohomology of `𝔸^r`: `[Finite Λ] [HasInvertibleExponent Λ S]`,
  or `[Finite Λ]` alone where the blueprint proof does not use the exponent.

TODO: once the hypotheses of
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison` are fixed,
give the compactification-dependent theorems exactly those hypotheses.

In the blueprint the `ℚ̄_ℓ` versions are deduced from the torsion ones by reduction. That
deduction, and the `ℚ̄_ℓ` statements themselves, are not formalised here.

## Implementation notes

`AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`:
of the four factors of the transform only `Rp₂,!` is at issue. The pullback `p₁^*`, the tensor
product with the lisse rank-one kernel and the shift preserve bounded constructibility for
formal reasons, while `Rp₂,!` does so by the finiteness theorem
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`. That theorem is stated
over a base field `k`, for finite `Λ` whose exponent is invertible on the source; hence `V'` is
assumed of finite type over `k`, `p₂` of finite type, and the exponent invertible on
`S`, which gives it on `V ×_S V'` by `AlgebraicGeometry.HasInvertibleExponent.of_hom`.

TODO: neither restriction is needed for `Rf_!`. For torsion coefficients and `f` of finite
presentation, `Rf_!` preserves constructibility over any quasi-compact quasi-separated base,
with no invertibility of the exponent (SGA 4 XVII 5.3.6). Once
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek` is stated in that
generality, drop the field and `[HasInvertibleExponent Λ S]` here.

The tensor factor preserves `Dᵇc` because the kernel is constructible over a finite `Λ`
(`AlgebraicGeometry.Etale.isConstructibleSheaf_fourierKernel`): an Artin–Schreier sheaf is
lisse, and its stalks are finite, being invertible `Λ`-modules.

`AlgebraicGeometry.Etale.isTriangulated_fourierTransform` is stated for the transform on the
whole derived category, the subcategory `Dᵇc(V, Λ)` not yet being known to be triangulated:
that needs the closure of constructible sheaves under extensions (blueprint
`thm:constructible-serre`). Since the transform preserves `Dᵇc`, its restriction
`AlgebraicGeometry.Etale.fourierTransformBoundedConstructible` sends the distinguished
triangles of `Dᵇc` to distinguished triangles.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

/-- For a pairing `b ∈ Γ(V ×_S V', 𝒪)` between two `S`-schemes, the *Fourier kernel* `𝒦_ψ`
is the Artin–Schreier sheaf `ℒ_{Ψ, b} = b^* ℒ_Ψ` of the pairing, the pullback of the
Artin–Schreier sheaf of `𝔸¹` along `b : V ×_S V' ⟶ 𝔸¹`. On the affine line over a field, with
`V = V' = 𝔸¹` and the pairing the product `x ξ`, this is the sheaf usually written
`ℒ_{ψ(xξ)}`. The two descriptions `ℒ_{Ψ, b}` and `b^* ℒ_Ψ` agree by construction, and the
compatibility `h^* ℒ_{Ψ, f} ≅ ℒ_{Ψ, h^* f}` with further pullbacks is
`AlgebraicGeometry.Etale.artinSchreierSheafOfPullbackIso`.

Being an Artin–Schreier sheaf, it is lisse of rank one
(`AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheafOf`) and multiplicative in
the character (`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_mul`), with
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv` identifying `𝒦_ψ⁻¹` with
`𝒦_{ψ⁻¹}`. It is defined for every commutative ring `Λ` in which `p` is invertible.
(sketch blueprint: `sec-Fourier-inversion`, `lemma-artin-schreier-character-sheaf`; blueprint:
`sec-Fourier-inversion`) -/
noncomputable def fourierKernel [CharP Γ(pullback π π', ⊤) p] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) :
    Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  artinSchreierSheafZMod (pullback π π') Ψ b

/-- Over a finite coefficient ring the Fourier kernel is constructible, being an Artin–Schreier
sheaf. (sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
instance isConstructibleSheaf_fourierKernel [Finite Λ] [CharP Γ(pullback π π', ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) :
    Scheme.IsConstructibleSheaf (fourierKernel Λ π π' Ψ b) := by
  let := (pullback π π').overSpecZModOfCharP p
  exact isConstructibleSheaf_artinSchreierSheafOf _ _ _

/-- The Fourier kernel is flat, having a tensor inverse, the Artin–Schreier sheaf of `-b`
(`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_neg`).
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem flat_fourierKernel [CharP Γ(pullback π π', ⊤) p] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) :
    ObjectProperty.flat (fourierKernel Λ π π' Ψ b) := by
  let := (pullback π π').overSpecZModOfCharP p
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_neg (pullback π π')
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b
  exact ObjectProperty.flat_of_tensorIso e

/-- Over a finite coefficient ring the Fourier kernel, placed in degree `0`, has Tor amplitude
in `[0, 0]`, being a flat constructible sheaf. (sketch blueprint:
`lemma-artin-schreier-character-sheaf`) -/
theorem torAmplitudeIn_fourierKernel [Finite Λ] [CharP Γ(pullback π π', ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) (pullback π π') 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) :=
  torAmplitudeIn_singleFunctor_obj_of_flat Λ _ (flat_fourierKernel Λ π π' Ψ b)

section Kernel

variable [CharP Γ(pullback π π', ⊤) p]

/-- The Fourier kernel `𝒦_ψ` is locally constant, as the pullback of the Artin–Schreier sheaf.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`; blueprint:
`lemma-artin-schreier-character-sheaf`) -/
instance isLocallyConstantSheaf_fourierKernel (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) :
    Scheme.IsLocallyConstantSheaf (fourierKernel Λ π π' Ψ b) := by
  let := (pullback π π').overSpecZModOfCharP p
  exact isLocallyConstantSheaf_artinSchreierSheafOf _ _ b

/-- The Fourier kernel is multiplicative in the character: `𝒦_ψ ⊗ 𝒦_ψ' ≅ 𝒦_{ψ ψ'}`, the value
of the character being additive in the defining function.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`; blueprint:
`lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_fourierKernel_mul (Ψ Ψ' : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) :
    Nonempty (fourierKernel Λ π π' Ψ b ⊗ fourierKernel Λ π π' Ψ' b ≅
      fourierKernel Λ π π' (Ψ * Ψ') b) := by
  let := (pullback π π').overSpecZModOfCharP p
  exact nonempty_iso_artinSchreierSheafOf_mul _ _ _ b

/-- The tensor inverse of the Fourier kernel `𝒦_ψ` is the kernel `𝒦_{ψ⁻¹}` of the inverse
character: `𝒦_ψ ⊗ 𝒦_{ψ⁻¹} ≅ Λ`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`; blueprint:
`lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_fourierKernel_inv (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) :
    Nonempty (fourierKernel Λ π π' Ψ b ⊗ fourierKernel Λ π π' Ψ⁻¹ b ≅ 𝟙_ _) := by
  let := (pullback π π').overSpecZModOfCharP p
  have : Ψ⁻¹.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom =
      (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom)⁻¹ := by
    ext; simp
  unfold fourierKernel artinSchreierSheafZMod
  rw [this]
  exact nonempty_iso_artinSchreierSheafOf_inv _ _ b

/-- The Fourier kernel placed in degree zero is dualizable in `D((V ×_S V')_ét)`, with dual the
kernel `𝒦_{ψ⁻¹}` of the inverse character.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`; blueprint:
`lemma-artin-schreier-character-sheaf`) -/
theorem isDualizable_fourierKernel (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) :
    IsDualizable ((_root_.DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) :=
  isDualizable_singleFunctor_obj_of_tensorIso (nonempty_iso_fourierKernel_inv Λ π π' Ψ b).some

end Kernel

/-- For a pairing `b ∈ Γ(V ×_S V', 𝒪)` between two `S`-schemes, the *Fourier integrand* is the
functor `ℱ_ψ(K) = p₁^* K ⊗ᴸ 𝒦_ψ` from `D(V_ét)` to `D((V ×_S V')_ét)`, `p₁` being the first
projection and `𝒦_ψ` the Fourier kernel placed in degree `0`. The Fourier–Deligne transform is
its compact-support direct image along the second projection `p₂`, shifted
(`AlgebraicGeometry.Etale.fourierTransform_eq_fourierIntegrand_comp`).
(sketch blueprint: `sec-Fourier-inversion`; blueprint: `sec-Fourier-inversion`) -/
noncomputable def fourierIntegrand [CharP Γ(pullback π π', ⊤) p] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  D((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
    derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
      ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b))

/-- For a pairing `b ∈ Γ(V ×_S V', 𝒪)` between two `S`-schemes and a relative dimension `r`,
the *Fourier–Deligne transform* is

`FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦_ψ)[r]`,

the kernel transform of the Fourier kernel `𝒦_ψ` with shift `r`. The shift is part of the
definition: it is Laumon's normalization, for which the inversion theorem holds up to the
Tate twist `(-r)` and no further shift. The transform attached to the inverse character is
the same construction with `Ψ⁻¹` in place of `Ψ`; its kernel is the inverse of `𝒦_ψ` by
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv`. Like the kernel, it is
defined for every commutative ring `Λ` in which `p` is invertible; torsion coefficients are
only assumed by the theorems that need them.
(sketch blueprint: `sec-Fourier-inversion`) -/
noncomputable def fourierTransform [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  kernelTransform (ModuleCat.{u + 1} Λ) π π'
    ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) r

/-- The Fourier–Deligne transform is the compact-support direct image of the Fourier integrand
along the second projection, shifted by `r`: `FT_ψ(K) = Rp₂,!(ℱ_ψ(K))[r]`.
(sketch blueprint: `sec-Fourier-inversion`; blueprint: `sec-Fourier-inversion`) -/
lemma fourierTransform_eq_fourierIntegrand_comp [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    fourierTransform Λ π π' Ψ b r =
      fourierIntegrand Λ π π' Ψ b ⋙ R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙
        shiftFunctor _ r :=
  rfl

/-- The Fourier–Deligne transform commutes with shifts, being a kernel transform. -/
noncomputable instance commShiftFourierTransform [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    (fourierTransform Λ π π' Ψ b r).CommShift ℤ :=
  inferInstanceAs ((kernelTransform (ModuleCat.{u + 1} Λ) π π'
    ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) r).CommShift ℤ)

/-- **The Fourier–Deligne transform is triangulated**: `FT_ψ` is the composite of the pullback
`p₁^*`, the derived tensor product with the kernel, the compact-support direct image `Rp₂,!`
and the shift by `r`, which are triangulated functors.

Together with
`AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`
this is the statement of `sec-Fourier-inversion`, the restriction
`AlgebraicGeometry.Etale.fourierTransformBoundedConstructible` to `Dᵇc` being then exact.

Class: general; no hypothesis on the coefficients.
(sketch blueprint: `sec-Fourier-inversion`) -/
instance isTriangulated_fourierTransform [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    (fourierTransform Λ π π' Ψ b r).IsTriangulated :=
  inferInstanceAs ((kernelTransform (ModuleCat.{u + 1} Λ) π π'
    ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) r).IsTriangulated)

section BoundedConstructible

variable [Finite Λ] [HasInvertibleExponent Λ S]
  [CharP Γ(pullback π π', ⊤) p] [HasCompactification (pullback.snd π π')]
  [LocallyOfFiniteType (pullback.snd π π')] [QuasiCompact (pullback.snd π π')]

omit [QuasiCompact (pullback.snd π π')] in
/-- For `V'` of finite type over a field `k`, the Fourier–Deligne transform sends the
bounded constructible derived category `Dᵇc(V, Λ)` into `Dᵇc(V', Λ)`.

Class: torsion; decided by Deligne finiteness of `Rp₂,!`
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`), which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sec-Fourier-inversion`) -/
theorem boundedConstructible_fourierTransform_obj_of_boundedConstructible {k : Type u}
    [Field k] (aV' : V' ⟶ Spec (.of k)) [LocallyOfFiniteType aV'] [QuasiCompact aV']
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ)
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V'
      ((fourierTransform Λ π π' Ψ b r).obj K) := by
  have := HasInvertibleExponent.of_hom (Λ := Λ) (pullback.fst π π' ≫ π)
  have h₁ := hK.mapDerivedCategory_upperStar (pullback.fst π π')
  have h₂ := boundedConstructible_tensor Λ _ h₁
    (DerivedCategory.boundedConstructible_singleFunctor_obj (fourierKernel Λ π π' Ψ b) 0)
    ⟨0, 0, torAmplitudeIn_fourierKernel Λ π π' Ψ b⟩
  have h₃ := boundedConstructible_rightDerivedLowerShriek Λ (pullback.snd π π')
    (pullback.snd π π' ≫ aV') aV' rfl _ h₂
  exact (DerivedCategory.boundedConstructible _ V').le_shift r _ h₃

/-- For `V'` of finite type over a field, the Fourier–Deligne transform as a functor
`Dᵇc(V, Λ) ⥤ Dᵇc(V', Λ)`, the functor whose existence `sec-Fourier-inversion` asserts.

Class: torsion; decided by Deligne finiteness of `Rp₂,!`, through
`AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`,
which needs `[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sec-Fourier-inversion`) -/
noncomputable def fourierTransformBoundedConstructible
    (hV' : ∃ (k : Type u) (_ : Field k) (a : V' ⟶ Spec (.of k)),
      LocallyOfFiniteType a ∧ QuasiCompact a)
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    Dᵇc(V, ModuleCat.{u + 1} Λ) ⥤ Dᵇc(V', ModuleCat.{u + 1} Λ) :=
  ObjectProperty.lift _
    (Etale.DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} Λ) V ⋙
      fourierTransform Λ π π' Ψ b r)
    fun K ↦ by
      obtain ⟨k, _, a, _, _⟩ := hV'
      exact boundedConstructible_fourierTransform_obj_of_boundedConstructible Λ π π' a Ψ b r
        K.obj K.property

end BoundedConstructible

end AlgebraicGeometry.Etale

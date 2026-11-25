/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CupProduct
public import WeilConjectures.AlgebraicGeometry.Cohomology.DualityPairing
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality

/-!
# Serre duality on a curve as a trace pairing

Let `X` be a smooth proper curve over a field `k`, with canonical module `ω = Ω¹_{X/k}`.
`AlgebraicGeometry.Scheme.nonempty_dual_H_one_iso` gives an abstract isomorphism
`H¹(X, ℱ)^∨ ≅ H⁰(X, ℱᵛ ⊗ ω)`, natural in finite locally free `ℱ`. This file shows that it comes
from a trace pairing: there is a `k`-linear form `t : H¹(X, ω) → k` such that for every finite
locally free `ℱ` the pairing
```
  H¹(X, ℱ) × Hom(ℱ, ω) → k,   (a, φ) ↦ t(H¹(φ)(a))
```
is perfect. Here `Hom(ℱ, ω) = H⁰(X, Hom(ℱ, ω)) ≅ H⁰(X, ℱᵛ ⊗ ω)` (`ω` is invertible,
`AlgebraicGeometry.Scheme.Modules.dualTensorHomIso`), and the pairing is the cup-product /
evaluation pairing of the blueprint: for `b ∈ H⁰(X, Hom(ℱ, ω))` and `a ∈ H¹(X, ℱ)`, the cup
product `a ∪ b ∈ H¹(X, ℱ ⊗ Hom(ℱ, ω))` followed by evaluation `ℱ ⊗ Hom(ℱ, ω) ⟶ ω` is
`H¹(b)(a)`, since cup product with a global section `b` is `H¹` of the morphism
`ℱ ⟶ ℱ ⊗ Hom(ℱ, ω)`, `s ↦ s ⊗ b`, and evaluation after it is `b` itself.

The proof is the Yoneda lemma: the natural isomorphism `Hom(-, ω) ≅ H¹(X, -)^∨` on finite
locally free modules (`ω` is itself finite locally free) is determined by the image `t` of
`𝟙 ω`, and naturality forces it to be `φ ↦ t ∘ H¹(φ)`
(`AlgebraicGeometry.Scheme.Modules.dualPairing`).

The form `t` is obtained abstractly. For `X` integral, the same duality statements with the
residue trace `H¹(X, ω) → k` of the blueprint (sum of Tate residues over the closed points) in
place of `t` are proved in `WeilConjectures.AlgebraicGeometry.Curve.ResidueTrace`
(`AlgebraicGeometry.Scheme.serreDuality_residueTrace`), deduced from the results here.

## Main statements

- `AlgebraicGeometry.Scheme.exists_trace_bijective_dualPairing`: Serre duality in the form
  `Hom(ℱ, ω) ≅ H¹(X, ℱ)^∨`, `φ ↦ t ∘ H¹(φ)`, for a single trace `t`.
- `AlgebraicGeometry.Scheme.exists_trace_bijective_dualPairingH`: the same statement as a
  `k`-linear bijection `H⁰(X, Hom(ℱ, ω)) ≅ H¹(X, ℱ)^∨`, together with the other side
  `H¹(X, ℱ) ≅ H⁰(X, Hom(ℱ, ω))^∨` of the perfect pairing (the case `q = 0` of duality, applied
  to `ℱᵛ ⊗ ω`).
- `AlgebraicGeometry.Scheme.exists_trace_perfect_cupPairing`: the same perfect pairing in the
  cup-product form `H¹(ℱ) ⊗ H⁰(ℱᵛ ⊗ ω) → H¹(ℱ ⊗ ℱᵛ ⊗ ω) → H¹(ω) → k` of the blueprint.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Yoneda for the duality pairing.** Let `P` be a property of `𝒪_X`-modules with `P ω`, and
let `Ψ` assign to every `ℱ` with `P ℱ` a map `Hom(ℱ, ω) → H¹(X, ℱ)^∨` which is natural in `ℱ`.
Then `Ψ` is the duality pairing `φ ↦ t ∘ H¹(φ)` for `t = Ψ(𝟙 ω)`. -/
lemma Modules.eq_dualPairing_of_natural (P : ObjectProperty X.Modules) {ω : X.Modules}
    (hω : P ω) (Ψ : ∀ ℱ : P.FullSubcategory, (ℱ.obj ⟶ ω) → Module.Dual k (ℱ.obj.H 1))
    (hΨ : ∀ (ℱ 𝒢 : P.FullSubcategory) (f : ℱ ⟶ 𝒢) (φ : 𝒢.obj ⟶ ω),
      Ψ ℱ (f.hom ≫ φ) = Ψ 𝒢 φ ∘ₗ Modules.H.mapLinearMap k f.hom 1)
    (ℱ : P.FullSubcategory) (φ : ℱ.obj ⟶ ω) :
    Ψ ℱ φ = Modules.dualPairing (Ψ ⟨ω, hω⟩ (𝟙 ω)) ℱ.obj φ := by
  ext a
  have h := hΨ ℱ ⟨ω, hω⟩ (ObjectProperty.homMk φ) (𝟙 ω)
  rw [ObjectProperty.homMk_hom, Category.comp_id] at h
  rw [h, Modules.dualPairing_apply]
  rfl

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **Serre duality on a curve as a trace pairing.** Let `X` be a smooth proper curve over `k`
with canonical module `ω = Ω¹_{X/k}`. There is a `k`-linear form `t : H¹(X, ω) → k` such that
for every finite locally free `ℱ` the duality pairing `Hom(ℱ, ω) → H¹(X, ℱ)^∨`,
`φ ↦ t ∘ H¹(φ)`, is bijective. Under `Hom(ℱ, ω) = H⁰(X, Hom(ℱ, ω)) ≅ H⁰(X, ℱᵛ ⊗ ω)` this is the
trace pairing `H¹(X, ℱ) ⊗ H⁰(X, ℱᵛ ⊗ ω) → H¹(X, ω) → k` (cup product, evaluation, trace): for a
global section `b` of `Hom(ℱ, ω)`, cup product with `b` followed by evaluation is `H¹(b)`.

The form `t` is the image of `𝟙 ω` under the natural isomorphism `Hom(-, ω) ≅ H¹(X, -)^∨` of
`nonempty_dual_H_one_iso`. For `X` integral, the statement for the residue trace of the blueprint
is `bijective_dualPairing_residueTrace` (file `Curve/ResidueTrace`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`, case `q = n = 1`) -/
theorem exists_trace_bijective_dualPairing :
    ∃ t : Module.Dual k (Modules.H (X := X) (X ↘ Spec (.of k)).relativeDifferentials 1),
      ∀ (ℱ : X.Modules), SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ →
        Function.Bijective (Modules.dualPairing t ℱ) := by
  set ω : X.Modules := (X ↘ Spec (.of k)).relativeDifferentials
  set P : ObjectProperty X.Modules := SheafOfModules.isFiniteLocallyFree X.ringCatSheaf
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  have := Modules.IsInvertible.of_sheafOfModules ω
  obtain ⟨E⟩ := nonempty_dual_H_one_iso (k := k) (X := X)
  -- `H¹(X, ℱ)^∨ ≅ H⁰(X, Hom(ℱ, ω))`, naturally in `ℱ`
  let E' := E ≪≫ Functor.isoWhiskerLeft P.ι.op
    (Functor.isoWhiskerRight (Modules.dualTensorHomIso ω) (Modules.cohomologyFunctor k 0))
  let Ψ (ℱ : P.FullSubcategory) (φ : ℱ.obj ⟶ ω) : Module.Dual k (ℱ.obj.H 1) :=
    (E'.inv.app (op ℱ)).hom ((Modules.homObjHZeroAddEquiv ℱ.obj ω).symm φ)
  have hΨ (ℱ 𝒢 : P.FullSubcategory) (f : ℱ ⟶ 𝒢) (φ : 𝒢.obj ⟶ ω) :
      Ψ ℱ (f.hom ≫ φ) = Ψ 𝒢 φ ∘ₗ Modules.H.mapLinearMap k f.hom 1 := by
    have h := congr($(E'.inv.naturality f.op).hom
      ((Modules.homObjHZeroAddEquiv 𝒢.obj ω).symm φ))
    have hφ : (Modules.homObjHZeroAddEquiv ℱ.obj ω).symm (f.hom ≫ φ) =
        Modules.H.map (SheafOfModules.homObjMap (R := X.sheaf) f.hom (𝟙 ω)) 0
          ((Modules.homObjHZeroAddEquiv 𝒢.obj ω).symm φ) := by
      rw [AddEquiv.symm_apply_eq, Modules.homObjHZeroAddEquiv_map, AddEquiv.apply_symm_apply]
    simp only [Ψ, hφ]
    exact h
  have hω : P ω := SheafOfModules.IsInvertible.isFiniteLocallyFree ω
  refine ⟨Ψ ⟨ω, hω⟩ (𝟙 ω), fun ℱ hℱ ↦ ?_⟩
  have heq : ⇑(Modules.dualPairing (Ψ ⟨ω, hω⟩ (𝟙 ω)) ℱ) = Ψ ⟨ℱ, hℱ⟩ :=
    funext fun φ ↦ (Modules.eq_dualPairing_of_natural P hω Ψ hΨ ⟨ℱ, hℱ⟩ φ).symm
  rw [heq]
  exact (ConcreteCategory.bijective_of_isIso (E'.inv.app (op ⟨ℱ, hℱ⟩))).comp
    (Modules.homObjHZeroAddEquiv ℱ ω).symm.bijective

/-- **Serre duality on a curve as a perfect trace pairing.** Let `X` be a smooth proper curve
over `k` with canonical module `ω = Ω¹_{X/k}`. There is a `k`-linear form `t : H¹(X, ω) → k`
such that for every finite locally free `ℱ` the `k`-bilinear pairing
```
  H⁰(X, Hom(ℱ, ω)) × H¹(X, ℱ) → k,   (b, a) ↦ t(H¹(b)(a))
```
is perfect: both `H⁰(X, Hom(ℱ, ω)) → H¹(X, ℱ)^∨` (the case `q = 1` of duality) and
`H¹(X, ℱ) → H⁰(X, Hom(ℱ, ω))^∨` (the case `q = 0` of duality for `ℱᵛ ⊗ ω`, as
`Hom(ℱ, ω) ≅ ℱᵛ ⊗ ω`) are bijective. As explained in `exists_trace_bijective_dualPairing`,
this is the cup-product / evaluation / trace pairing of the blueprint. For `X` integral, the
statement for the residue trace is `bijective_dualPairingH_residueTrace`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem exists_trace_bijective_dualPairingH :
    ∃ t : Module.Dual k (Modules.H (X := X) (X ↘ Spec (.of k)).relativeDifferentials 1),
      ∀ (ℱ : X.Modules), SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ →
        Function.Bijective (Modules.dualPairingH t ℱ) ∧
          Function.Bijective (Modules.dualPairingH t ℱ).flip := by
  obtain ⟨t, ht⟩ := exists_trace_bijective_dualPairing (k := k) (X := X)
  refine ⟨t, fun ℱ hℱ ↦ ?_⟩
  have hL := (Modules.bijective_dualPairingH_iff t ℱ).2 (ht ℱ hℱ)
  refine ⟨hL, ?_⟩
  have := hℱ
  have := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation ℱ
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree ℱ
  have := Modules.finiteDimensional_H_of_isProper (k := k) ℱ 1
  let L := LinearEquiv.ofBijective (Modules.dualPairingH t ℱ) hL
  have hflip : (Modules.dualPairingH t ℱ).flip =
      L.dualMap.toLinearMap ∘ₗ (Module.evalEquiv k (ℱ.H 1)).toLinearMap := by
    ext a b
    rfl
  rw [hflip, LinearMap.coe_comp]
  exact L.dualMap.bijective.comp (Module.evalEquiv k (ℱ.H 1)).bijective

open MonoidalCategory in
open scoped AlgebraicGeometry.Scheme.Modules in
/-- **Serre duality on a curve as a perfect cup-product pairing.** Let `X` be a smooth proper
curve over `k` with canonical module `ω = Ω¹_{X/k}`. There is a `k`-linear form
`t : H¹(X, ω) → k` such that for every finite locally free `ℱ` the pairing
```
  H¹(X, ℱ) ⊗ H⁰(X, ℱᵛ ⊗ ω) --∪--> H¹(X, ℱ ⊗ ℱᵛ ⊗ ω) --H¹(ev)--> H¹(X, ω) --t--> k
```
(`Modules.cupPairing`: cup product `Modules.cupH0`, evaluation `Modules.evalTensor`) is perfect:
both `H⁰(X, ℱᵛ ⊗ ω) → H¹(X, ℱ)^∨` and `H¹(X, ℱ) → H⁰(X, ℱᵛ ⊗ ω)^∨` are bijective. This is
`exists_trace_bijective_dualPairingH` transported along `ℱᵛ ⊗ ω ≅ Hom(ℱ, ω)`
(`Modules.cupPairing_eq`). For `X` integral, the statement for the residue trace of the
blueprint is `serreDuality_residueTrace` (file `Curve/ResidueTrace`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem exists_trace_perfect_cupPairing :
    ∃ t : Module.Dual k (Modules.H (X := X) (X ↘ Spec (.of k)).relativeDifferentials 1),
      ∀ (ℱ : X.Modules), SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ →
        Function.Bijective (Modules.cupPairing t ℱ) ∧
          Function.Bijective (Modules.cupPairing t ℱ).flip := by
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  have := Modules.IsInvertible.of_sheafOfModules (X ↘ Spec (.of k)).relativeDifferentials
  obtain ⟨t, ht⟩ := exists_trace_bijective_dualPairingH (k := k) (X := X)
  refine ⟨t, fun ℱ hℱ ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := ht ℱ hℱ
  let L : Modules.H (X := X) (ℱᵛ ⊗ (X ↘ Spec (.of k)).relativeDifferentials) 0 ≃ₗ[k]
      Modules.H (X := X) (Modules.homObj ℱ (X ↘ Spec (.of k)).relativeDifferentials) 0 :=
    LinearEquiv.ofBijective (Modules.H.mapLinearMap k
      (Modules.dualTensorHom ℱ (X ↘ Spec (.of k)).relativeDifferentials) 0)
      (Modules.H.mapLinearEquiv
        (asIso (Modules.dualTensorHom ℱ (X ↘ Spec (.of k)).relativeDifferentials)) 0).bijective
  have hc := Modules.cupPairing_eq t ℱ
  refine ⟨?_, ?_⟩
  · rw [hc, LinearMap.coe_comp]
    exact h₁.comp L.bijective
  · have hflip : (Modules.cupPairing t ℱ).flip =
        L.dualMap.toLinearMap ∘ₗ (Modules.dualPairingH t ℱ).flip := by
      rw [hc]
      rfl
    rw [hflip, LinearMap.coe_comp]
    exact L.dualMap.bijective.comp h₂

end AlgebraicGeometry.Scheme

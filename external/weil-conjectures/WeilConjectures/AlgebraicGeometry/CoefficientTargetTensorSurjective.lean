/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.CoefficientTargetSectionGenerators
import WeilConjectures.AlgebraicGeometry.CoefficientTargetScalarSpan

/-! # Surjective of the coefficient tensor map

Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- A tensor map with the supported pullback-unit formula is surjective.
Only surjectivity is asserted; no equivalence or inverse formula is assumed.
Source: Stacks Project, Tag 02KG (Lemma 30.5.1, affine tensor computation),
Tags 01I9 and 01IA (affine pullback), and Tag 0097 (restriction).
(blueprint: lem-pc-coefficient-target-tensor-surjective).

Proof: Put A = Gamma(U,O), D = Gamma(Z,O), R = Gamma(B,O),
and N = Gamma(Z,F|Y), where Y = f inverse image U. The affine intersection
base-change theorem makes W intersect fprime inverse image B affine and
the restricted cartesian square identifies it with Z times_U B, with ring
R tensor_A D. Restriction preserves quasi-coherence. Apply the affine
pullback section theorem to F|Z and transport tensorPullback to the standard
pullback by uniqueness of adjoints, compatibly with units. Identify
open-immersion pullback with restriction. Target sections are thus
(R tensor_A D) tensor_D N. The structural A-action on N is exactly the
one in the statement: GammaSpecIso cancels the canonical affine chart.
The stated formula identifies c(r tensor n) with (r tensor 1) tensor n,
first for r=1 by unit compatibility, and then for every r by R-linearity.
By tensor induction every target
section is a sum of (r tensor d) tensor n. Balancing over D rewrites each
as (r tensor 1) tensor (d*n), which is c(r tensor (d*n)) by the generator
formula. Tensor additivity and induction in the inner tensor express all
sections in this form, so sums have preimages given by sums of these source
tensors. The zero section has zero preimage, including when Z or B is empty.
This proves surjectivity without flatness or a covering hypothesis. -/
theorem coefficientTarget_tensor_surjective
    {X T : Scheme.{u}} (f : X ⟶ T) [IsSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (hB : IsAffineOpen B) :
    letI : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
      (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let N := (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
          ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
    let M := (pullback g').obj F
    ∀ c : (Γ(T', B) ⊗[Γ(U.toScheme, ⊤)] N) →ₗ[Γ(T', B)]
        Γ((pushforward (W.ι ≫ f')).obj (M.restrict W.ι), B),
      (∀ s : N, c ((1 : Γ(T', B)) ⊗ₜ[Γ(U.toScheme, ⊤)] s) =
        (coefficientSupportIso f' M W B).inv
          (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s))) →
        Function.Surjective c := by
  classical
  dsimp only
  let : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
    (g.appLE ⊤ B (by simp)).hom.toAlgebra
  intro c hc
  let N := (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
        ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
  let M := (pullback g').obj F
  let k : N → Γ((pushforward (W.ι ≫ f')).obj (M.restrict W.ι), B) := fun s ↦
    (coefficientSupportIso f' M W B).inv
      (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
        (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s))
  have hspan : Submodule.span (Γ(T', B)) (Set.range k) ≤ LinearMap.range c := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨s, rfl⟩
    refine ⟨(1 : Γ(T', B)) ⊗ₜ[Γ(U.toScheme, ⊤)] s, ?_⟩
    exact hc s
  intro y
  obtain ⟨n, a, s, he⟩ := coefficientTarget_section_generators
    f F U hU Z hZ g g' f' sq W hW B hB ((coefficientSupportIso f' M W B).hom y)
  have hy : y ∈ LinearMap.range c := by
    have hi : ∀ i : Fin n,
        (coefficientSupportIso f' M W B).inv
          (a i • (M.presheaf.map
            (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW (s i)))) ∈
          LinearMap.range c := fun i ↦ hspan
            (coefficientTarget_scalar_span
              f F U hU Z hZ g g' f' sq W hW B hB (a i) (s i))
    have hs := (LinearMap.range c).sum_mem (fun i (_ : i ∈ Finset.univ) ↦ hi i)
    have he' := congrArg (fun z ↦ (coefficientSupportIso f' M W B).inv z) he
    simp only [map_sum, Iso.hom_inv_id_apply] at he'
    rw [he']
    exact hs
  exact hy

end
end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # The pointwise multiplication morphism of twists

Source: Stacks Project, Constructions, Equation 27.10.1.1 and Tag 01MS.
(blueprint: lem-sc-p1-twist-product-morphism).
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Apply the existing tensor universal property before specializing to `Proj`.
Keeping the scheme abstract here avoids unfolding its structure sheaf during elaboration. -/
private theorem exists_tensorHom (X : Scheme.{u}) (F G H : X.Modules)
    (β : ∀ U : X.Opensᵒᵖ, Γ(F, U.unop) →ₗ[Γ(X, U.unop)]
      Γ(G, U.unop) →ₗ[Γ(X, U.unop)] Γ(H, U.unop))
    (hβ : ∀ {U V : X.Opensᵒᵖ} (f : U ⟶ V) (s : Γ(F, U.unop))
      (t : Γ(G, U.unop)), β V (F.val.map f s) (G.val.map f t) =
        H.val.map f (β U s t)) :
    ∃ φ : F ⊗ G ⟶ H, ∀ (U : X.Opens) (s : Γ(F, U)) (t : Γ(G, U)),
      φ.app U (tmulSection s t) = β (Opposite.op U) s t := by
  obtain ⟨φ, hφ, _⟩ := SheafOfModules.tensor_bilinear_universal X.sheaf F G H β hβ
  exact ⟨φ, fun U s t ↦ hφ (Opposite.op U) s t⟩

/-- Twisting sections multiply pointwise through the sheaf tensor product.

Source: Stacks Project, Constructions, Equation 27.10.1.1 and Tag 01MS;
Step 2 of lem-sc-p1-twist-multiplication.
(blueprint: lem-sc-p1-twist-product-morphism).

Proof: For each open U multiply two twisting sections pointwise in each prime
localization. Their product has degree n+m, by the graded multiplication rule.
Local homogeneous fraction representatives multiply to a homogeneous fraction
representative, so this is a section. This operation is bilinear over the
structure sheaf and commutes with restriction, by the ring laws in each
localization. The tensor universal property gives a morphism from the tensor
product of the two underlying presheaves into the degree n+m twisting presheaf.
Apply the sheafification adjunction and the canonical identification of the
sheaf tensor product with the sheafification of the presheaf tensor product.
The adjunction unit equation says the resulting morphism on tmulSection is
exactly the pointwise product with which we started. This works in every degree,
including zero and negative degrees, without choosing any isomorphism or basis. -/
theorem projectiveLine_twist_product_morphism (k : Type u) [Field k] :
    ∃ μ : ∀ n m : ℤ,
        Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n ⊗
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⟶
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + m),
      (∀ (n m : ℤ) (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens)
        (s : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, U))
        (t : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m, U)) (x : U),
        (((μ n m).app U (tmulSection s t)).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * (t.1 x)) := by
  classical
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k
  let product (n m : ℤ) (U : (Proj 𝒜).Opens)
      (s : Γ(Proj.twist 𝒜 n, U)) (t : Γ(Proj.twist 𝒜 m, U)) :
      Γ(Proj.twist 𝒜 (n + m), U) :=
    ⟨fun x ↦ ⟨s.1 x * t.1 x,
      HomogeneousLocalization.mul_mem_degreePart (s.1 x).2 (t.1 x).2⟩,
      ProjectiveSpectrum.Twist.isLocallyFraction_mul rfl s.2 t.2⟩
  let β (n m : ℤ) (U : (Proj 𝒜).Opensᵒᵖ) :
      Γ(Proj.twist 𝒜 n, U.unop) →ₗ[Γ(Proj 𝒜, U.unop)]
        Γ(Proj.twist 𝒜 m, U.unop) →ₗ[Γ(Proj 𝒜, U.unop)]
          Γ(Proj.twist 𝒜 (n + m), U.unop) :=
    LinearMap.mk₂ Γ(Proj 𝒜, U.unop) (product n m U.unop)
      (by
        intro s s' t
        exact Subtype.ext (funext fun x ↦ Subtype.ext (add_mul _ _ _)))
      (by
        intro r s t
        exact Subtype.ext (funext fun x ↦ Subtype.ext (mul_assoc _ _ _)))
      (by
        intro s t t'
        exact Subtype.ext (funext fun x ↦ Subtype.ext (mul_add _ _ _)))
      (by
        intro r s t
        exact Subtype.ext (funext fun x ↦ Subtype.ext (mul_left_comm _ _ _)))
  have hβ (n m : ℤ) {U V : (Proj 𝒜).Opensᵒᵖ} (f : U ⟶ V)
      (s : Γ(Proj.twist 𝒜 n, U.unop)) (t : Γ(Proj.twist 𝒜 m, U.unop)) :
      β n m V ((Proj.twist 𝒜 n).val.map f s) ((Proj.twist 𝒜 m).val.map f t) =
        (Proj.twist 𝒜 (n + m)).val.map f (β n m U s t) := by
    rfl
  have hex (n m : ℤ) : ∃ φ : Proj.twist 𝒜 n ⊗ Proj.twist 𝒜 m ⟶
      Proj.twist 𝒜 (n + m), ∀ (U : (Proj 𝒜).Opens)
      (s : Γ(Proj.twist 𝒜 n, U)) (t : Γ(Proj.twist 𝒜 m, U)),
      φ.app U (tmulSection s t) = product n m U s t := by
    exact exists_tensorHom (Proj 𝒜) (Proj.twist 𝒜 n) (Proj.twist 𝒜 m)
      (Proj.twist 𝒜 (n + m)) (β n m) (hβ n m)
  refine ⟨fun n m ↦ (hex n m).choose, ?_⟩
  intro n m U s t x
  have h := (hex n m).choose_spec U s t
  exact congrArg (fun z : Γ(Proj.twist 𝒜 (n + m), U) ↦
    (z.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) h

end AlgebraicGeometry

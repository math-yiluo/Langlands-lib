/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MixedRepForward.MixedRepresentationGeneral
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.MixedRepForward.ForwardTransportGeneral
import WeilConjectures.CategoryTheory.FiniteOpenMixedTensorRepresentativeCounit

/-!
# Counit and cochain representative equations for the published mixed open tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tag 07A4 (lemma-pullback-tensor-product)
(blueprint: lem-sf-finite-open-mixed-tensor-representative).
The statement is given for an arbitrary coefficient category; the finite coefficient
case `Mod_A` is obtained by instantiation.
-/

@[expose] public section
set_option autoImplicit false

universe u' u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For a coefficient category `A` and an open immersion `j : U ⟶ X`, with
`F = j^*` on pro-étale `A`-valued sheaves, `κ : LF ≅ DF`, `a : DF ∘ Q_X ≅ Q_U ∘ F_c`, `φ` the
published left-derived tensor comparison, `μ` the native lax tensorators of the cochain
localizations and `c` the signed total of the oplax tensorator of `F`:
(1) the left-derived counit at the homotopy image of `P`, transported along
`Q_X ≅ Q_{h,X} ∘ π_X` and `F_c ∘ π ≅ π ∘ F_h`, is `ε_P = κ_{Q_X P} ≫ a_P`;
(2) `φ ≫ (ε_P ⊗ ε_Q) ≫ μ^U = LF(μ^X) ≫ ε_{T_X(P,Q)} ≫ Q_U(c)`;
(3) `(κ⁻¹ ⊗ 1) ≫ φ⁻¹ ≫ κ ≫ DF(μ^X) ≫ a = (a_P ⊗ ε_Q) ≫ μ^U ≫ Q_U(c)⁻¹`.
No boundedness, flatness or K-flatness is assumed on `P, Q`; no `μ` is inverted.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4 (lemma-pullback-tensor-product).

Proof.
Step 1. `j^*` is exact, so the termwise factor `a^h : DF ∘ Q_{h,X} ≅ Q_{h,U} ∘ F_h` is
invertible on every complex and `(DF, a^h)` is a left-derived presentation of the same
functor as `(LF, ε^h)`. `κ` is the canonical comparison of the two presentations; the
counit-compatible uniqueness of right Kan extensions gives `κ_{Q_h H} ≫ a^h_H = ε^h_H`.
Whiskering by the homotopy quotient and conjugating by the canonical factors gives
`ε_P = κ_{Q_X P} ≫ a_P`, clause (1).
Step 2. `φ` is the universal lift of `LF(μ^h) ≫ ε^h ≫ Q_h(δ^h)` through the tensor counit
`(ε^h ⊗ ε^h) ≫ μ^{h,U}`; its defining equation is
`φ ≫ (ε^h_H ⊗ ε^h_J) ≫ μ^{h,U} = LF(μ^{h,X}) ≫ ε^h_{H ⊗ J} ≫ Q_h(δ^h_{H,J})`.
Step 3. Evaluate at `H = π P`, `J = π Q`. The native cochain lax structure is the
transport `μ = (r⁻¹ ⊗ r⁻¹) ≫ μ^h ≫ Q_h(t) ≫ r` along `quotientCompQhIso`, and `δ^h` at
`π P, π Q` is the image of `c`. Naturality moves the `t` and `r` factors to the ends,
where they cancel; with clause (1) this is clause (2).
Step 4. Naturality of `κ` gives `κ ≫ DF(μ^X) = LF(μ^X) ≫ κ`, so the left side of (3) is
`(κ⁻¹ ⊗ 1) ≫ φ⁻¹ ≫ LF(μ^X) ≫ ε_{T_X(P,Q)}`. Clause (2), composed with `φ⁻¹` before and
`Q_U(c)⁻¹` after, rewrites this as `(κ⁻¹ ⊗ 1) ≫ (ε_P ⊗ ε_Q) ≫ μ^U ≫ Q_U(c)⁻¹`, and
`κ⁻¹ ≫ ε_P = a_P` gives clause (3). Only `κ`, `φ` and `c` are inverted.
(blueprint: lem-sf-finite-open-mixed-tensor-representative)
-/
theorem finiteOpenMixedTensorRepresentative
    (P Q : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ) :
    L((j)^*[A]).map
        ((DerivedCategory.quotientCompQhIso (Sheaf (Scheme.ProEt.topology X) A)).inv.app P) ≫
      (j)^*[A].leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        (((j)^*[A].mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
      (DerivedCategory.quotientCompQhIso (Sheaf (Scheme.ProEt.topology U) A)).hom.app
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj P) =
      (j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P) ≫
        (j)^*[A].mapDerivedCategoryFactors.hom.app P ∧
    ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso
      A j).hom.app
      ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P)).app
      ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q) ≫
      ((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P) ≫
        (j)^*[A].mapDerivedCategoryFactors.hom.app P ⊗ₘ
       (j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q) ≫
        (j)^*[A].mapDerivedCategoryFactors.hom.app Q) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Q
        (C := Sheaf (Scheme.ProEt.topology U) A))
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj P)
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj Q)) =
      L((j)^*[A]).map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)) P Q) ≫
      ((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj
          (HomologicalComplex.mapBifunctor P Q
            (curriedTensor (Sheaf (Scheme.ProEt.topology X) A)) (.up ℤ))) ≫
        (j)^*[A].mapDerivedCategoryFactors.hom.app
          (HomologicalComplex.mapBifunctor P Q
            (curriedTensor (Sheaf (Scheme.ProEt.topology X) A)) (.up ℤ))) ≫
      (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology U) A)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (j)^*[A]).app P).app Q) ∧
    (((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P)) ⊗ₘ 𝟙 _) ≫
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso
        A j).inv.app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P)).app
        ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q) ≫
      (j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (((-⊗ᴸ-(X)[A]).obj
          ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj P)).obj
          ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q)) ≫
      (j)^*[A].mapDerivedCategory.map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)) P Q) ≫
      (j)^*[A].mapDerivedCategoryFactors.hom.app
        (HomologicalComplex.mapBifunctor P Q
          (curriedTensor (Sheaf (Scheme.ProEt.topology X) A)) (.up ℤ)) =
      ((j)^*[A].mapDerivedCategoryFactors.hom.app P ⊗ₘ
        ((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).obj Q) ≫
          (j)^*[A].mapDerivedCategoryFactors.hom.app Q)) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Q
        (C := Sheaf (Scheme.ProEt.topology U) A))
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj P)
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      inv ((DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology U) A)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (j)^*[A]).app P).app Q)) := by
  refine ⟨?_, MixedRepForward.forward_transport_general A j P Q,
    MixedRepForward.mixed_inverse_transport_general A j P Q⟩
  have h := CategoryTheory.Functor.leftDerivedFactors_eq_counit ((j)^*[A]) P
  rw [h]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    CategoryTheory.Functor.mapHomotopyCategoryFactors]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  simp only [cast_eq]

end AlgebraicGeometry.ProEtale

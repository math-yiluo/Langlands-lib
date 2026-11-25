/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule

/-! # Interchanging two ideal-power quotients

Source: Stacks Project, Tag 088A, the quotient by I^n + K^e
(blueprint: lem-weil-pbc-devissage-second-adic-system-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

private local instance quotientProjection_epi {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (F : X.Modules) : Epi (formalModuleQuotientπ I n F) := by
  dsimp [formalModuleQuotientπ]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private def quotientSwapMap {X : Scheme.{u}} (I K : X.IdealSheafData)
    (H : X.Modules) (e n : ℕ) :
    formalModuleQuotient I n (formalModuleQuotient K e H) ⟶
      formalModuleQuotient K e (formalModuleQuotient I n H) := by
  let qI := formalModuleQuotientπ I n H
  let qK := formalModuleQuotientπ K e H
  let pK := formalModuleQuotientπ K e (formalModuleQuotient I n H)
  let bK := Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι e).2 H
  have hK : bK ≫ qI ≫ pK = 0 :=
    (idealModuleProduct_quotient_comp_zero_iff _ qI pK).mp (cokernel.condition _)
  let t := cokernel.desc bK (qI ≫ pK) hK
  let bI := Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2
    (formalModuleQuotient K e H)
  have hI : bI ≫ t = 0 := by
    apply (idealModuleProduct_quotient_comp_zero_iff _ qK t).mpr
    dsimp [qK, t, formalModuleQuotientπ]
    rw [cokernel.π_desc]
    simp [qI, formalModuleQuotientπ]
  exact cokernel.desc bI t hI

@[reassoc (attr := simp)]
private theorem quotientSwapMap_projection {X : Scheme.{u}} (I K : X.IdealSheafData)
    (H : X.Modules) (e n : ℕ) :
    formalModuleQuotientπ K e H ≫
      formalModuleQuotientπ I n (formalModuleQuotient K e H) ≫
      quotientSwapMap I K H e n =
    formalModuleQuotientπ I n H ≫
      formalModuleQuotientπ K e (formalModuleQuotient I n H) := by
  simp [quotientSwapMap, formalModuleQuotientπ]

private def quotientSwapIso {X : Scheme.{u}} (I K : X.IdealSheafData)
    (H : X.Modules) (e n : ℕ) :
    formalModuleQuotient I n (formalModuleQuotient K e H) ≅
      formalModuleQuotient K e (formalModuleQuotient I n H) where
  hom := quotientSwapMap I K H e n
  inv := quotientSwapMap K I H n e
  hom_inv_id := by
    apply (cancel_epi (formalModuleQuotientπ I n (formalModuleQuotient K e H))).1
    apply (cancel_epi (formalModuleQuotientπ K e H)).1
    simp only [quotientSwapMap_projection_assoc,
      quotientSwapMap_projection, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi (formalModuleQuotientπ K e (formalModuleQuotient I n H))).1
    apply (cancel_epi (formalModuleQuotientπ I n H)).1
    simp only [quotientSwapMap_projection_assoc,
      quotientSwapMap_projection, Category.comp_id]

/-- The canonical quotient interchange, natural in both positive indices.
Source: Stacks Project, Tag 088A, the quotient by I^n + K^e
(blueprint: lem-weil-pbc-devissage-second-adic-system-comparison).

Proof: a map out of (H/K^e H)/I^n is precisely a map out of H killing both
K^e H and I^n H, by the two cokernel universal properties. Tensoring by an
ideal module preserves epimorphisms, so vanishing of its product can be checked
after the first quotient projection. The quotient in
the other order has the same property. Factor its composite projection through
the first quotient, and conversely. Both composites are identities: precompose
with the composite quotient projection, which is epi, and use the defining
factorization equations. These equations also give the displayed identity.
For either index transition, precomposing the naturality square with the
projection from H gives the same quotient projection on both paths. Epimorphism
cancellation proves the square, so the component isomorphisms assemble to θ.
-/
theorem grothendieckDevissage_secondAdicSystem_comparison
    {X : Scheme.{u}} (I K : X.IdealSheafData) (H : X.Modules) :
    ∃ (θ : formalCompletionSystem K H ⋙ formalCompletionFunctor I ≅
        (formalCompletionSystem I H ⋙ formalCompletionFunctor K).flip),
      ∀ e n : ℕ,
        formalModuleQuotientπ K (e + 1) H ≫
          formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H) ≫
          (θ.hom.app (op e)).app (op n) =
        formalModuleQuotientπ I (n + 1) H ≫
          formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H) := by
  let c (e n : ℕᵒᵖ) := quotientSwapIso I K H (e.unop + 1) (n.unop + 1)
  let inner (e : ℕᵒᵖ) :
      (formalCompletionSystem K H ⋙ formalCompletionFunctor I).obj e ≅
        (formalCompletionSystem I H ⋙ formalCompletionFunctor K).flip.obj e :=
    NatIso.ofComponents (c e) (by
      intro a b f
      change formalModuleQuotientMap I (𝟙 _) (Nat.succ_le_succ (leOfHom f.unop)) ≫
          (c e b).hom =
        (c e a).hom ≫ formalModuleQuotientMap K
          (formalModuleQuotientMap I (𝟙 H) (Nat.succ_le_succ (leOfHom f.unop)))
          (Nat.le_refl _)
      apply (cancel_epi (formalModuleQuotientπ I (a.unop + 1)
        (formalModuleQuotient K (e.unop + 1) H))).1
      apply (cancel_epi (formalModuleQuotientπ K (e.unop + 1) H)).1
      dsimp only [c, quotientSwapIso]
      simp only [quotientSwapMap, formalModuleQuotientMap, formalModuleQuotientπ,
        Category.assoc, cokernel.π_desc, cokernel.π_desc_assoc, Category.id_comp])
  let θ : formalCompletionSystem K H ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H ⋙ formalCompletionFunctor K).flip :=
    NatIso.ofComponents inner (by
      intro a b f
      apply NatTrans.ext
      funext n
      change formalModuleQuotientMap I
          (formalModuleQuotientMap K (𝟙 H) (Nat.succ_le_succ (leOfHom f.unop)))
          (Nat.le_refl _) ≫
          (c b n).hom = (c a n).hom ≫
          formalModuleQuotientMap K (𝟙 _) (Nat.succ_le_succ (leOfHom f.unop))
      apply (cancel_epi (formalModuleQuotientπ I (n.unop + 1)
        (formalModuleQuotient K (a.unop + 1) H))).1
      apply (cancel_epi (formalModuleQuotientπ K (a.unop + 1) H)).1
      dsimp only [c, quotientSwapIso]
      simp only [quotientSwapMap, formalModuleQuotientMap, formalModuleQuotientπ,
        Category.assoc, cokernel.π_desc, cokernel.π_desc_assoc, Category.id_comp])
  refine ⟨θ, ?_⟩
  intro e n
  exact quotientSwapMap_projection I K H (e + 1) (n + 1)

end

end AlgebraicGeometry

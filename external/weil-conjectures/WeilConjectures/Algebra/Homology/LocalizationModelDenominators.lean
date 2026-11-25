/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizationModelSemilinear
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.LocalizationDerivedFractions

/-! # Denominators for localized derived tensor cohomology

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-first-localization-cohomology-denominators).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A Aq B D : Type u)
  [CommRing R] [CommRing A] [CommRing Aq] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Every localized cohomology class has a denominator and a pre-localization numerator.
Source: Stacks Project, Tags 06Y6 and 0DJ8; exactness of localization.
(blueprint: lem-pc-first-localization-cohomology-denominators).

Proof: resolve B[0] by a K-flat R-complex F and compute with Q tensor_R F.
Exact extension from A to Aq commutes with the total-complex direct sums and
with cycles modulo boundaries. Thus every class of the localized complex is a
fraction of a class of the original complex. Explicitly write a cycle as a
fraction of a term, then multiply its numerator by a further denominator killing
its differential; the resulting numerator is a cycle and the product denominator
still belongs to S. The balanced derived bifunctor's naturality in B identifies
the commuting B-action; naturality in Q and universal-counit comparison transport
the fraction equation to L and K. Under cohomologyIso_smul the denominator acts
by includeLeft (algebraMap A Aq s), and the numerator map is localizationModelMap.
For zero in S the target is zero, and s=0 works; for identity localization the
inverse model comparison supplies the numerator with denominator one. -/
theorem localizationModelMap_denominators
    (S : Submonoid A) [IsLocalization S Aq] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
    (y : K.cohomology i) :
    ∃ (x : L.cohomology i) (s : S),
      (Algebra.TensorProduct.includeLeft (S := R) (algebraMap A Aq (s : A)) :
        Aq ⊗[R] B) • y = localizationModelMap R A Aq B D i Q L K uQ x := by
  let := L.universal
  let := K.universal
  let ζ := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
  let V := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let Z := (restrict R Aq).obj ((extend A Aq).obj Q)
  let e := H.mapIso (ζ.app (V.obj Z)) ≪≫ (K.cohomologyIso i).symm
  obtain ⟨x, s, hs⟩ := derivedLocalization_fractions R A Aq B S
    L.derived L.counit i Q uQ huQ (e.inv y)
  refine ⟨(L.cohomologyIso i).inv x, s, ?_⟩
  let β := (restrict R Aq).map
    ((algebraMap A Aq (s : A)) • 𝟙 ((extend A Aq).obj Q))
  let σ := (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom).map
    ((Algebra.TensorProduct.includeLeft (S := R) (algebraMap A Aq (s : A)) :
      Aq ⊗[R] B) • 𝟙 (K.cohomology i))
  have hact : H.map (L.derived.map (V.map β)) ≫ e.hom = e.hom ≫ σ := by
    apply (cancel_mono (K.cohomologyIso i).hom).1
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [K.cohomologyIso_smul]
    simp only [Iso.inv_hom_id_assoc]
    change H.map (L.derived.map (V.map β)) ≫ H.map (ζ.hom.app _) =
      H.map (ζ.hom.app _) ≫ H.map (K.derived.map (V.map β))
    simpa only [H.map_comp] using congrArg H.map (ζ.hom.naturality (V.map β))
  have heq := congrArg (fun z ↦ e.hom z) hs
  change e.hom (H.map (L.derived.map (V.map β)) (e.inv y)) =
    e.hom (H.map (L.derived.map (V.map uQ)) x) at heq
  have hleft := congrArg (fun f ↦ f (e.inv y)) hact
  change e.hom (H.map (L.derived.map (V.map β)) (e.inv y)) = σ (e.hom (e.inv y))
    at hleft
  rw [hleft] at heq
  rw [Iso.inv_hom_id_apply] at heq
  change (Algebra.TensorProduct.includeLeft (S := R) (algebraMap A Aq (s : A)) :
    Aq ⊗[R] B) • y = e.hom (H.map (L.derived.map (V.map uQ)) x) at heq
  simpa only [localizationModelMap, Functor.map_comp, ModuleCat.comp_apply,
    Iso.inv_hom_id_apply, e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    V, H, Z, ζ, Functor.comp_map, Functor.comp_obj, Iso.app_hom] using heq

end RingTensorCohomology

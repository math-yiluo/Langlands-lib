/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FirstLocalizationMap
/-! # Naturality for characterized localization maps

Source: Stacks Project, Tag 06Y6; Tag 0DJ8.
(blueprint: lem-pc-first-localization-naturality). -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Aq D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Aq] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [tRA : IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem firstLocalizationUnit_naturality
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q') :
    (restrict R A).map f ≫ firstLocalizationUnit R A Aq Q' =
      firstLocalizationUnit R A Aq Q ≫ (restrict R Aq).map ((extend A Aq).map f) := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (1 : Aq) ⊗ₜ[A,algebraMap A Aq] (f.f j x) =
    (ModuleCat.extendScalars (algebraMap A Aq)).map (f.f j)
      ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
  rw [ModuleCat.ExtendScalars.map_tmul]

/-- Naturality for characterized localization maps.
Source: Stacks Project, Tag 06Y6; Tag 0DJ8, affine localization identity.
(blueprint: lem-pc-first-localization-naturality).

Proof: naturality of the extension/restriction unit gives a commuting square
of underlying R-complexes for f and its extension to Aq. Apply the derived
functor and degree-i cohomology. The universal property of each derived functor
identifies delta and epsilon with the unique counit-compatible model comparisons;
its uniqueness also gives the cocycle equation for these comparisons. Substitute
the characterizations of g and h and cancel the cohomology isomorphisms.
This proves equality of the underlying B-linear maps. On a generator 1 tensor x,
the defining formulas he and he' and extension-of-scalars map_tmul identify the
two D-linear composites with this equality. Tensor induction, or hom_ext for
extension of scalars, proves the displayed square. Identity and zero chain maps
obey the same calculation, without flatness assumptions. -/
theorem firstLocalization_naturality (i : ℤ)
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
          (L' : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D)
          (K' : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q') D)
          (δ : L.derived ⟶ L'.derived) (ε : K.derived ⟶ K'.derived)
          (g : L.cohomology i ⟶ L'.cohomology i)
          (h : K.cohomology i ⟶ K'.cohomology i)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj (K.cohomology i))
    (e' : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L'.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj (K'.cohomology i))
    (he : IsFirstLocalizationMap R A Aq B D Q L K i e.hom)
    (he' : IsFirstLocalizationMap R A Aq B D Q' L' K' i e'.hom) :
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
            L'.counit = L.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
              (L'.cohomologyIso i).hom =
          (L.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (L.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (δ.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) →
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) ε ≫
            K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] Aq ⊗[R] B).toRingHom).map h ≫
              (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (K.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R Aq).map ((extend A Aq).map f))))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (ε.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R Aq).obj ((extend A Aq).obj Q'))))) →
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
            e'.hom =
          e.hom ≫
            (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).map h := by
  intro hδ hg hε hh
  let _ := L.universal
  let _ := L'.universal
  let _ := K.universal
  let _ := K'.universal
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)
  let ζ := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit W (Iso.refl _)
  let ζ' := Functor.leftDerivedNatIso L'.derived K'.derived L'.counit K'.counit W
    (Iso.refl _)
  have hζ : Functor.whiskerLeft DerivedCategory.Qh ζ.hom ≫ K.counit = L.counit := by
    simp [ζ]
  have hζ' : Functor.whiskerLeft DerivedCategory.Qh ζ'.hom ≫ K'.counit = L'.counit := by
    simp [ζ']
  have hc : δ ≫ ζ'.hom = ζ.hom ≫ ε := by
    apply Functor.leftDerived_ext K'.derived K'.counit W
    simp only [Functor.whiskerLeft_comp, Category.assoc, hζ', hζ, hδ, hε]
  let V := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
  let a := V.map ((restrict R A).map f)
  let b := V.map ((restrict R Aq).map ((extend A Aq).map f))
  let v := V.map (firstLocalizationUnit R A Aq Q)
  let v' := V.map (firstLocalizationUnit R A Aq Q')
  have hab : a ≫ v' = v ≫ b := by
    dsimp only [a, b, v, v']
    rw [← V.map_comp, ← V.map_comp, firstLocalizationUnit_naturality R A Aq Q Q' f]
  have hd : L.derived.map a ≫ δ.app _ ≫ L'.derived.map v' ≫ ζ'.hom.app _ =
      L.derived.map v ≫ ζ.hom.app _ ≫ K.derived.map b ≫ ε.app _ := by
    rw [← δ.naturality_assoc v']
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hab]
    simp only [Functor.map_comp, Category.assoc]
    rw [← ζ.hom.naturality_assoc b]
    exact congrArg (fun t ↦ L.derived.map v ≫ L.derived.map b ≫ t.app _) hc
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  have hb :
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
          firstLocalizationCohomologyMap R A Aq B D Q' L' K' i =
      firstLocalizationCohomologyMap R A Aq B D Q L K i ≫
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] Aq ⊗[R] B).toRingHom).map h := by
    apply (cancel_mono (K'.cohomologyIso i).hom).1
    dsimp only [firstLocalizationCohomologyMap]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hh]
    simp only [← Category.assoc]
    rw [hg]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (L.cohomologyIso i).hom ≫ H.map (L.derived.map a) ≫ H.map (δ.app _) ≫
      H.map (L'.derived.map v') ≫ H.map (ζ'.hom.app _) =
      (L.cohomologyIso i).hom ≫ H.map (L.derived.map v) ≫ H.map (ζ.hom.app _) ≫
        H.map (K.derived.map b) ≫ H.map (ε.app _)
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ (L.cohomologyIso i).hom ≫ H.map t) hd
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change e'.hom ((ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g
      ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x)) =
    (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).map h
      (e.hom ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x))
  rw [ModuleCat.ExtendScalars.map_tmul, he', he, ModuleCat.ExtendScalars.map_tmul]
  exact congrArg (fun y ↦ (1 : D) ⊗ₜ[Aq ⊗[R] B,algebraMap (Aq ⊗[R] B) D] y)
    (congrArg (fun t ↦ t x) hb)

end RingTensorCohomology

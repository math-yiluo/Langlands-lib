/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivCounit

/-! # Universal derived extension under coefficient equivalences

Source: Stacks Project, Tags 06Y6 and 05RR.
(blueprint: lem-pc-derived-extension-ring-equiv-cohomology). -/

@[expose] public section
set_option autoImplicit false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

private theorem exists_scalarExtension_ringEquiv
    {R₀ B₀ R B : Type u}
    [CommRing R₀] [CommRing B₀] [CommRing R] [CommRing B]
    [Algebra R₀ B₀] [Algebra R B]
    (eR : R₀ ≃+* R) (eB : B₀ ≃+* B)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom) :
    ∃ t : restrictScalars.{u} eR.toRingHom ⋙ extendScalars (algebraMap R₀ B₀) ≅
        extendScalars (algebraMap R B) ⋙ restrictScalars.{u} eB.toRingHom,
      ∀ (M : ModuleCat.{u} R) (b : B₀) (x : M),
        t.hom.app M (b ⊗ₜ[R₀,algebraMap R₀ B₀]
          (show (restrictScalars.{u} eR.toRingHom).obj M from x)) =
            eB b ⊗ₜ[R,algebraMap R B] x := by
  let : Module R₀ B₀ := Module.compHom B₀ (algebraMap R₀ B₀)
  let : Module R B := Module.compHom B (algebraMap R B)
  have : RingHomInvPair eR.toRingHom eR.symm.toRingHom := RingHomInvPair.of_ringEquiv eR
  have : RingHomInvPair eR.symm.toRingHom eR.toRingHom := RingHomInvPair.of_ringEquiv_symm eR
  let c : LinearEquiv eR.toRingHom (σ' := eR.symm.toRingHom) B₀ B :=
    { __ := eB.toAddEquiv
      map_smul' := by
        intro r b
        change eB (algebraMap R₀ B₀ r * b) = algebraMap R B (eR r) * eB b
        rw [map_mul]
        exact congrArg (fun z ↦ z * eB b) (RingHom.congr_fun hRB r) }
  let h (M : ModuleCat.{u} R) : LinearEquiv eR.toRingHom (σ' := eR.symm.toRingHom)
      ((restrictScalars.{u} eR.toRingHom).obj M) M :=
    { __ := AddEquiv.refl M
      map_smul' := fun _ _ ↦ rfl }
  let v (M : ModuleCat.{u} R) := TensorProduct.congr c (h M)
  let l (M : ModuleCat.{u} R) :
      (extendScalars (algebraMap R₀ B₀)).obj ((restrictScalars.{u} eR.toRingHom).obj M) ≃ₗ[B₀]
        (restrictScalars.{u} eB.toRingHom).obj ((extendScalars (algebraMap R B)).obj M) :=
    { __ := (v M).toAddEquiv
      map_smul' := by
        intro b z
        change v M (b • z) = eB b • v M z
        induction z using TensorProduct.inductionOn with
        | tmul b' x =>
          change v M ((b * (show B₀ from b')) ⊗ₜ[R₀,algebraMap R₀ B₀] x) =
            eB b • v M (b' ⊗ₜ[R₀,algebraMap R₀ B₀] x)
          rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul]
          change eB (b * (show B₀ from b')) ⊗ₜ[R,algebraMap R B] (show M from x) = _
          rw [map_mul]
          rfl
        | add z w hz hw =>
          change v M (b • (z + w)) = eB b • v M (z + w)
          rw [smul_add, map_add, map_add, hz, hw, smul_add] }
  let t : restrictScalars.{u} eR.toRingHom ⋙ extendScalars (algebraMap R₀ B₀) ≅
      extendScalars (algebraMap R B) ⋙ restrictScalars.{u} eB.toRingHom :=
    NatIso.ofComponents (fun M ↦ (l M).toModuleIso) (by
      intro M N f
      apply ExtendScalars.hom_ext
      intro x
      change l N ((extendScalars (algebraMap R₀ B₀)).map
        ((restrictScalars.{u} eR.toRingHom).map f)
          ((1 : B₀) ⊗ₜ[R₀,algebraMap R₀ B₀] x)) =
        (extendScalars (algebraMap R B)).map f
          (l M ((1 : B₀) ⊗ₜ[R₀,algebraMap R₀ B₀] x))
      change v N _ = (extendScalars (algebraMap R B)).map f (v M _)
      rw [ExtendScalars.map_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul,
        ExtendScalars.map_tmul]
      rfl)
  exact ⟨t, fun M b x ↦ TensorProduct.congr_tmul c (h M) b x⟩

/-- Universal derived scalar extension, before specifying any extra algebra action,
commutes with coefficient equivalences, together with its counit on cohomology.

Proof: construct the ordinary scalar-extension isomorphism before deriving.
The coefficient equivalence eB is eR-semilinear by hRB, and the identity
additive equivalence from an R-module restricted along eR to itself is also
eR-semilinear. TensorProduct.congr gives an additive equivalence on tensors.
Tensor induction proves B0-linearity, so it gives the module isomorphism.
On b tensor x the formula is eB(b) tensor x. Extension of scalars sends tensors
to tensors with the input map applied, so this formula also proves naturality.
Apply the natural isomorphism termwise to get t on complexes. The theorem
exists_derivedExtension_ringEquiv_counit transports the two universal derived
functors and their counits through the coefficient equivalences, giving d
and its cohomology square. Combine t, d, and their two established properties.
No additional algebra action, model cohomology, or chosen input complex is used.
The construction includes zero rings and complexes and every degree.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1 (independence of choices),
and Tag 05RR, localization of homotopy categories.
(blueprint: lem-pc-derived-extension-ring-equiv-cohomology). -/
theorem exists_derivedExtension_ringEquiv_cohomology
    {R₀ B₀ R B : Type u}
    [CommRing R₀] [CommRing B₀] [CommRing R] [CommRing B]
    [Algebra R₀ B₀] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (L₀ : DerivedCategory (ModuleCat.{u} R₀) ⥤ DerivedCategory (ModuleCat.{u} B₀))
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶
      (extendScalars (algebraMap R₀ B₀)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h₀ : L₀.IsLeftDerivedFunctor ε₀ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (eR : R₀ ≃+* R) (eB : B₀ ≃+* B)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom) (i : ℤ) :
    let π₀ := HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ)
    let π := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
    let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) i
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let P₀ := π₀ ⋙ DerivedCategory.Qh ⋙ L₀ ⋙ H₀
    let P := π ⋙ DerivedCategory.Qh ⋙ L ⋙ H
    let V := (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ)
    let U := restrictScalars.{u} eB.toRingHom
    let T₀ := (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ)
    let T := (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)
    let c₀ := fun K : CochainComplex (ModuleCat.{u} R₀) ℤ ↦
      H₀.map (ε₀.app (π₀.obj K)) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B₀) i).hom.app
          ((HomotopyCategory.quotient _ _).obj (T₀.obj K)) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B₀) (.up ℤ) i).hom.app
          (T₀.obj K)
    let c := fun K : CochainComplex (ModuleCat.{u} R) ℤ ↦
      H.map (ε.app (π.obj K)) ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
          ((HomotopyCategory.quotient _ _).obj (T.obj K)) ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
          (T.obj K)
    ∃ (t : V ⋙ T₀ ≅ T ⋙ U.mapHomologicalComplex (.up ℤ))
      (d : V ⋙ P₀ ≅ P ⋙ U),
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) (b : B₀) (x : K.X j),
        (t.hom.app K).f j (b ⊗ₜ[R₀,algebraMap R₀ B₀] x) =
          eB b ⊗ₜ[R,algebraMap R B] x) ∧
      ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
        d.hom.app K ≫ U.map (c K) =
          c₀ (V.obj K) ≫ HomologicalComplex.homologyMap (t.hom.app K) i ≫
            ((T.obj K).sc i |>.mapHomologyIso U).hom := by
  intro π₀ π H₀ H P₀ P V U T₀ T c₀ c
  obtain ⟨a, ha⟩ := exists_scalarExtension_ringEquiv eR eB hRB
  let t : V ⋙ T₀ ≅ T ⋙ U.mapHomologicalComplex (.up ℤ) :=
    NatIso.mapHomologicalComplex a (.up ℤ)
  have ht (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) (b : B₀) (x : K.X j) :
      (t.hom.app K).f j (b ⊗ₜ[R₀,algebraMap R₀ B₀] x) =
        eB b ⊗ₜ[R,algebraMap R B] x := ha (K.X j) b x
  obtain ⟨d, hd⟩ := exists_derivedExtension_ringEquiv_counit
    L₀ L ε₀ ε h₀ h eR eB hRB i t ht
  exact ⟨t, d, ht, hd⟩

end ModuleCat

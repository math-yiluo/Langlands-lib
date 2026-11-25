/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainRepresentatives
import all WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainClassNaturality

/-! # The augmented Koszul identity class is independent of the exponent

Source: Stacks Project, Tags 08DC, 08DD, 08D1 and 09M1.
(blueprint: lem-sc-koszul-open-augmented-identity-class).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
private theorem homClass_map
    {A : Type u} [CommRing A]
    {L N M : CochainComplex (ModuleCat.{u} A) ℤ}
    (d : CochainComplex.moduleHomComplex L M ⟶ CochainComplex.moduleHomComplex N M)
    (t : L ⟶ M) (s : N ⟶ M)
    (h : d.f 0 (CochainComplex.HomComplex.Cochain.ofHom t) =
      CochainComplex.HomComplex.Cochain.ofHom s) :
    HomologicalComplex.homologyMap d 0 (koszulHomChainClass t) =
      koszulHomChainClass s := by
  let K := CochainComplex.moduleHomComplex L M
  let K' := CochainComplex.moduleHomComplex N M
  let z : K.cycles 0 := (K.sc 0).moduleCatCyclesIso.inv
    ⟨CochainComplex.HomComplex.Cochain.ofHom t,
      CochainComplex.HomComplex.δ_ofHom t⟩
  let z' : K'.cycles 0 := (K'.sc 0).moduleCatCyclesIso.inv
    ⟨CochainComplex.HomComplex.Cochain.ofHom s,
      CochainComplex.HomComplex.δ_ofHom s⟩
  have hz : K.iCycles 0 z = CochainComplex.HomComplex.Cochain.ofHom t := by
    change ((K.sc 0).moduleCatCyclesIso.inv ≫ (K.sc 0).iCycles) _ = _
    rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  have hz' : K'.iCycles 0 z' = CochainComplex.HomComplex.Cochain.ofHom s := by
    change ((K'.sc 0).moduleCatCyclesIso.inv ≫ (K'.sc 0).iCycles) _ = _
    rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  have hc : HomologicalComplex.cyclesMap d 0 z = z' := by
    apply (ModuleCat.mono_iff_injective (K'.iCycles 0)).mp inferInstance
    change (HomologicalComplex.cyclesMap d 0 ≫ K'.iCycles 0) z = _
    rw [HomologicalComplex.cyclesMap_i]
    change d.f 0 (K.iCycles 0 z) = _
    rw [hz, hz', h]
  change (K.homologyπ 0 ≫ HomologicalComplex.homologyMap d 0) z = K'.homologyπ 0 z'
  rw [HomologicalComplex.homologyπ_naturality]
  change K'.homologyπ 0 (HomologicalComplex.cyclesMap d 0 z) = _
  rw [hc]

set_option backward.isDefEq.respectTransparency false in
-- Transposition and homology comparisons have nested complex and functor instances.
private theorem stageClass_transition
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (a b : ℕ) (hab : a ≤ b) (t : koszulOpenSheafComplex A r f a ⟶ F) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let D := koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F)
    let g := HomologicalComplex.extendMap (koszulOpenTransition A r f a b hab)
      ComplexShape.embeddingDownNat
    H.map (DerivedCategory.Q.map (D.map (homOfLE hab)))
      (koszulOpenHomStageClass A r f F a t) =
      koszulOpenHomStageClass A r f F b
        (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map g ≫ t) := by
  let : (tilde.functor (.of A)).Additive :=
    ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
  let : (moduleSpecΓFunctor (R := .of A)).Additive :=
    ⟨fun {_ _} _ _ ↦ rfl⟩
  dsimp only
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
  let D := koszulCechHomDiagram A r f M
  let K (e : ℕ) := CochainComplex.moduleHomComplex
    ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M
  let j (e : ℕ) := koszulCechHomObjIso A r f M e
  let g := HomologicalComplex.extendMap (koszulOpenTransition A r f a b hab)
    ComplexShape.embeddingDownNat
  let d : K a ⟶ K b := (j a).inv ≫ D.map (homOfLE hab) ≫ (j b).hom
  let t' := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map g ≫ t
  have ht : koszulOpenHomTranspose A r f F b t' =
      g ≫ koszulOpenHomTranspose A r f F a t := by
    exact ((tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)).homEquiv_naturality_left
      g t
  have hd : d.f 0
      (CochainComplex.HomComplex.Cochain.ofHom (koszulOpenHomTranspose A r f F a t)) =
      CochainComplex.HomComplex.Cochain.ofHom (koszulOpenHomTranspose A r f F b t') := by
    rw [ht]
    exact ((koszulCechHomDiagram_exists A r f M).choose_spec.2 a b hab 0
      (CochainComplex.HomComplex.Cochain.ofHom (koszulOpenHomTranspose A r f F a t))
      ((koszulCechHomDiagram_exists A r f M).choose_spec.1 a)
      ((koszulCechHomDiagram_exists A r f M).choose_spec.1 b)).trans
        (CochainComplex.HomComplex.Cochain.ofHom_comp _ _).symm
  have hc := homClass_map d (koszulOpenHomTranspose A r f F a t)
    (koszulOpenHomTranspose A r f F b t') hd
  let η := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0
  have hn := η.inv.naturality d
  change HomologicalComplex.homologyMap d 0 ≫ (η.app (K b)).inv =
    (η.app (K a)).inv ≫ H.map (DerivedCategory.Q.map d) at hn
  have heq : (j a).inv ≫ D.map (homOfLE hab) = d ≫ (j b).inv := by
    simp [d, Category.assoc]
  have heq' : H.map (DerivedCategory.Q.map (j a).inv) ≫
      H.map (DerivedCategory.Q.map (D.map (homOfLE hab))) =
      H.map (DerivedCategory.Q.map d) ≫ H.map (DerivedCategory.Q.map (j b).inv) := by
    simp only [← Functor.map_comp, heq]
  dsimp only [koszulOpenHomStageClass]
  change (H.map (DerivedCategory.Q.map (D.map (homOfLE hab))))
    ((H.map (DerivedCategory.Q.map (j a).inv))
      ((η.app (K a)).inv (koszulHomChainClass (koszulOpenHomTranspose A r f F a t)))) = _
  change ((η.app (K a)).inv ≫ H.map (DerivedCategory.Q.map (j a).inv) ≫
    H.map (DerivedCategory.Q.map (D.map (homOfLE hab))))
      (koszulHomChainClass (koszulOpenHomTranspose A r f F a t)) = _
  rw [heq', ← Category.assoc, ← hn]
  change (H.map (DerivedCategory.Q.map (j b).inv))
    ((η.app (K b)).inv
      (HomologicalComplex.homologyMap d 0
        (koszulHomChainClass (koszulOpenHomTranspose A r f F a t)))) = _
  rw [hc]

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_transition
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (a b : ℕ) (hab : a ≤ b) :
    koszulOpenTransition A r f a b hab ≫ koszulOpenAugmentation A r f a =
      koszulOpenAugmentation A r f b := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    simp only [HomologicalComplex.comp_f, koszulOpenAugmentation,
      ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    change koszulOpenTransitionComponent A r f a b 0 ≫
      koszulOpenAugmentationComponent A r f a = koszulOpenAugmentationComponent A r f b
    let g := koszulOpenDiagonal A r f (b - a)
    have hd : (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (a + 1)) 0).comp
        (exteriorPower.map 1 g) =
        (exteriorPower.map 0 g).comp
          (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (b + 1)) 0) := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simp only [LinearMap.comp_apply, koszulOpen_exterior_coe_map,
        ExteriorAlgebra.koszulBoundary, LinearMap.codRestrict_apply,
        Submodule.subtype_apply]
      exact koszulOpen_contract_natural A r g _ _
        (koszulOpen_forms_comp A r f a b hab) x
    apply ModuleCat.hom_ext
    change (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
      ((ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (a + 1)) 0).comp
        (exteriorPower.map 1 g)) = _
    rw [hd, ← LinearMap.comp_assoc, exteriorPower.zeroEquiv_naturality]
    rfl
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (ModuleCat.of A A) (n + 1) (by omega)).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
/-- Augmentation sends every explicit identity class to the same structure section.
Source: Stacks Project, Tag 08D1 (Koszul-to-Cech cocone); Tag 08DC, equation 36.9.4.1.
(blueprint: lem-sc-koszul-open-augmented-identity-class).

Proof: Use postcomposition naturality of the explicit stage-to-derived-sections
class to rewrite augmentation of the identity class as the class of the augmentation
chain map into the structure complex. The Koszul power transition from index zero to e
commutes with augmentation: contraction is natural under the diagonal scaling map,
the exponent identity e-0+1=e+1 identifies the linear forms, and the degree-zero
exterior-power equivalence is natural. In positive tail degrees the target is zero.
Transposition takes precomposition by the sheaf transition to precomposition by the
module transition. The defining formula of koszulCechHomDiagram identifies its
transition on cochains with this precomposition. Naturality of the cycles inclusion
and homology projection proves the equality of Hom-chain classes; naturality of
homologyFunctorFactors transports it to the specified derived stage class. The colimit
cocone identity D.map(0 to e) followed by iota_e = iota_0 makes their colimit images
equal. Applying the Cech-to-derived-sections map gives the displayed equality.
No inverse augmentation or choice of evaluation equivalence is needed. The argument
works at e=0, for r=0, for zero f_j, and for the zero ring: it uses only functor laws
and the same Koszul contraction identity, without nonvanishing assumptions. -/
theorem koszulOpen_augmented_identity_class
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)] :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
    let c := fun e : ℕ ↦ H.map (koszulCechDerivedComparison A r f (koszulOpenSheafComplex A r f e))
        (H.map (DerivedCategory.Q.map (colimit.ι
          (koszulCechHomDiagram A r f
            (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj
              (koszulOpenSheafComplex A r f e))) e))
          (koszulOpenHomStageClass A r f (koszulOpenSheafComplex A r f e) e (𝟙 _)))
    ∀ e : ℕ, H.map (G.map (koszulOpenUnit A r f e)) (c e) =
      H.map (G.map (koszulOpenUnit A r f 0)) (c 0)  := by
  dsimp only
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
  let T := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ))
  let O := T.obj
    (((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)).extend
      ComplexShape.embeddingDownNat)
  let t (e : ℕ) := T.map
    (HomologicalComplex.extendMap (koszulOpenAugmentation A r f e)
      ComplexShape.embeddingDownNat)
  let D := koszulCechHomDiagram A r f
    (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj O)
  intro e
  have hn (a : ℕ) := koszulOpenHom_chain_class_naturality A r f
    (koszulOpenSheafComplex A r f a) O a (𝟙 _) (t a)
  simp only [Category.id_comp] at hn
  have he := hn e
  have h0 := hn 0
  dsimp only [koszulOpenUnit, koszulOpenObject, koszulOpenStructure]
  change H.map (G.map (DerivedCategory.Q.map (t e))) _ =
    H.map (G.map (DerivedCategory.Q.map (t 0))) _
  calc
    _ = H.map (koszulCechDerivedComparison A r f O)
        (H.map (DerivedCategory.Q.map (colimit.ι D e))
          (koszulOpenHomStageClass A r f O e (t e))) := by
      exact he
    _ = H.map (koszulCechDerivedComparison A r f O)
        (H.map (DerivedCategory.Q.map (colimit.ι D 0))
          (koszulOpenHomStageClass A r f O 0 (t 0))) := by
      apply congrArg (H.map (koszulCechDerivedComparison A r f O))
      have ht : (T.map
          (HomologicalComplex.extendMap (koszulOpenTransition A r f 0 e (Nat.zero_le e))
            ComplexShape.embeddingDownNat)) ≫ t 0 = t e := by
        dsimp only [t]
        rw [← Functor.map_comp, ← HomologicalComplex.extendMap_comp,
          augmentation_transition]
      have hc := stageClass_transition A r f O 0 e (Nat.zero_le e) (t 0)
      dsimp only at hc
      rw [ht] at hc
      rw [← hc]
      change (H.map (DerivedCategory.Q.map (D.map (homOfLE (Nat.zero_le e)))) ≫
        H.map (DerivedCategory.Q.map (colimit.ι D e)))
          (koszulOpenHomStageClass A r f O 0 (t 0)) = _
      rw [← Functor.map_comp, ← Functor.map_comp, colimit.w]
    _ = _ := by exact h0.symm

end AlgebraicGeometry

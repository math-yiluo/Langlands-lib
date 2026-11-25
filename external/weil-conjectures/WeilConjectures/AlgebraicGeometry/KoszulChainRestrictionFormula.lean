/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem

/-! # The restriction formula for a Koszul chain representative

Source: Stacks Project, Tags 06Z0, 08DC and 08DD.
(blueprint: lem-sc-koszul-chain-restriction-formula).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem naturalEquiv_add
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] {A : Type*} [CommRing A]
    (R : C ⥤ D) [R.Additive] (S : C ⥤ ModuleCat A) [S.Additive] (P : D)
    (b : ∀ E : C, (P ⟶ R.obj E) ≃ S.obj E)
    (hb : ∀ (E E' : C) (g : E ⟶ E') (ψ : P ⟶ R.obj E),
      b E' (ψ ≫ R.map g) = S.map g (b E ψ))
    (E : C) (ψ ψ' : P ⟶ R.obj E) : b E (ψ + ψ') = b E ψ + b E ψ' := by
  let p : P ⟶ R.obj (E ⊞ E) := ψ ≫ R.map biprod.inl + ψ' ≫ R.map biprod.inr
  have hp₁ : p ≫ R.map biprod.fst = ψ := by simp [p, ← R.map_comp]
  have hp₂ : p ≫ R.map biprod.snd = ψ' := by simp [p, ← R.map_comp]
  have hp : p ≫ R.map (biprod.fst + biprod.snd) = ψ + ψ' := by
    rw [R.map_add, Preadditive.comp_add, hp₁, hp₂]
  rw [← hp, hb, S.map_add]
  change S.map biprod.fst (b (E ⊞ E) p) +
    S.map biprod.snd (b (E ⊞ E) p) = _
  rw [← hb, ← hb, hp₁, hp₂]

private theorem koszulHomChainClass_eq_homologyπ {A : Type u} [CommRing A]
    {L M : CochainComplex (ModuleCat.{u} A) ℤ} (g : L ⟶ M)
    (z : (CochainComplex.moduleHomComplex L M).cycles 0)
    (hz : (CochainComplex.moduleHomComplex L M).iCycles 0 z =
      CochainComplex.HomComplex.Cochain.ofHom g) :
    koszulHomChainClass g = (CochainComplex.moduleHomComplex L M).homologyπ 0 z := by
  let K := CochainComplex.moduleHomComplex L M
  let S := K.sc 0
  have hc : S.moduleCatCyclesIso.inv
      ⟨CochainComplex.HomComplex.Cochain.ofHom g,
        CochainComplex.HomComplex.δ_ofHom g⟩ = z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 0)).1 inferInstance
    change ((S.moduleCatCyclesIso.inv ≫ S.iCycles) _) = _
    rw [S.moduleCatCyclesIso_inv_iCycles]
    exact hz.symm
  change S.homologyπ (S.moduleCatCyclesIso.inv _) = _
  exact congrArg S.homologyπ hc

private theorem moduleHomologyFactors_inv_naturality_apply
    {A : Type u} [CommRing A] [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ L) (n : ℤ)
    (x : K.homology n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map (DerivedCategory.Q.map g)
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app K).inv x) =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app L).inv
        (HomologicalComplex.homologyMap g n x) :=
  (ConcreteCategory.congr_hom
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).inv.naturality g) x).symm

private theorem koszulOpenHomTranspose_tilde_counit
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (s : ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
      (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F) ≅ F)
    (hs : ∀ n : ℤ, s.hom.f n = Scheme.Modules.fromTildeΓ (R := .of A) (F.X n))
    (e : ℕ) (g : (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat ⟶
      ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F) :
    koszulOpenHomTranspose A r f F e
      (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map g ≫ s.hom) = g := by
  let : (tilde.functor (.of A)).Additive :=
    ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
  let : (moduleSpecΓFunctor (R := .of A)).Additive :=
    ⟨fun {_ _} _ _ ↦ rfl⟩
  let adj := (tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)
  have hc : adj.counit.app F = s.hom := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (hs n).symm
  change adj.homEquiv _ _ (_ ≫ s.hom) = g
  rw [← hc, ← Adjunction.homEquiv_counit]
  exact (adj.homEquiv _ _).apply_symm_apply g

private theorem naturalEquiv_transport_chain
    {C D : Type*} [Category C] [Category D] {A : Type*} [CommRing A]
    (R : C ⥤ D) (S : C ⥤ ModuleCat A) (P : C)
    (b : ∀ E : C, (R.obj P ⟶ R.obj E) ≃ S.obj E)
    (hb : ∀ (E E' : C) (g : E ⟶ E') (ψ : R.obj P ⟶ R.obj E),
      b E' (ψ ≫ R.map g) = S.map g (b E ψ))
    {X Y Z : C} (u : X ⟶ P) (t : X ⟶ Y) (e : Y ≅ Z) (x : S.obj Y)
    (hx : ∀ ψ₀ : R.obj P ⟶ R.obj Y, R.map u ≫ ψ₀ = R.map t → b Y ψ₀ = x)
    (ψ : R.obj P ⟶ R.obj Z) (hψ : R.map u ≫ ψ = R.map (t ≫ e.hom)) :
    b Z ψ = S.map e.hom x := by
  let ψ₀ := ψ ≫ R.map e.inv
  have hψ₀ : R.map u ≫ ψ₀ = R.map t := by
    dsimp only [ψ₀]
    rw [← Category.assoc, hψ, ← R.map_comp, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hψ' : ψ₀ ≫ R.map e.hom = ψ := by
    dsimp only [ψ₀]
    rw [Category.assoc, ← R.map_comp, Iso.inv_hom_id, R.map_id, Category.comp_id]
  rw [← hψ', hb, hx ψ₀ hψ₀]

private theorem koszulOpenHomStageClass_colimit_of_cycle
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (e : ℕ) (t : koszulOpenSheafComplex A r f e ⟶ F) :
    let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
    let L := (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat
    let K := CochainComplex.moduleHomComplex L M
    let D := koszulCechHomDiagram A r f M
    let C := koszulCechHomColimit A r f M
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let η := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0
    ∀ (g : L ⟶ M), koszulOpenHomTranspose A r f F e t = g →
      ∀ (z : K.cycles 0), K.iCycles 0 z = CochainComplex.HomComplex.Cochain.ofHom g →
      H.map (DerivedCategory.Q.map (colimit.ι D e))
          (koszulOpenHomStageClass A r f F e t) =
        (η.app C).inv (HomologicalComplex.homologyMap (colimit.ι D e) 0
          (HomologicalComplex.homologyMap (koszulCechHomObjIso A r f M e).inv 0
            (K.homologyπ 0 z))) := by
  intro M L K D C H η g ht z hz
  dsimp only [koszulOpenHomStageClass]
  rw [ht, koszulHomChainClass_eq_homologyπ g z hz]
  rw [moduleHomologyFactors_inv_naturality_apply,
    moduleHomologyFactors_inv_naturality_apply]
  rfl

/-- The canonical comparison on an actual chain representative is restriction followed
by inverse augmentation and evaluation at one.
Source: Stacks Project, Equation 36.9.4.1, Tag 08DC; Tags 08D1 and 08DD.
(blueprint: lem-sc-koszul-chain-restriction-formula)

Proof: On the principal intersection indexed by J, apply the canonical affine counit
s to the module chain map g. The Koszul-to-Cech cocone evaluates g on the ordered wedge
and divides by the product of the f_j to exponent e+1. Contracting the localized full
Koszul complex with a generator whose f_j is invertible shows that the same fraction
represents restriction composed with the inverse augmentation. The totalization sign
in the cocone is precisely the sign converting the negative tail differential into
the alternating Cech differential. Pass this equality to degree-zero homology; hz
identifies the cycle represented by g. The Cech-to-derived-sections map carries it to
the corresponding derived section. Evaluation at one identifies sections with Hom
from the restricted structure object, additively, and postcomposition by eF transports
the target. This supplies b and the equality for every psi satisfying the displayed
augmentation equation; invertibility is given by
affine_perfect_koszul_principal_unit_iso at exponent e+1. Empty cover and zero ring yield
zero groups; no exactness of
filtered colimits, regularity, boundedness of F or injectivity is used. -/
theorem koszulChain_restriction_formula
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (eF : DerivedCategory.Q.obj F ≅ E.obj)
    (s : ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
      (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F) ≅ F)
    (hs : ∀ n : ℤ, s.hom.f n = Scheme.Modules.fromTildeΓ (R := .of A) (F.X n)) :
    let R := ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{u}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
    let D := koszulCechHomDiagram A r f M
    let C := koszulCechHomColimit A r f M
    let β := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app C).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (koszulCechDerivedComparison A r f F ≫
          (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map eF.hom)
    ∃ b : (R.obj (koszulOpenStructure A) ⟶ R.obj E.obj) ≃+
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.obj E.obj),
      ∀ (e : ℕ)
        (g : (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat ⟶ M)
        (z : (CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).cycles 0),
        (CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).iCycles 0 z =
            CochainComplex.HomComplex.Cochain.ofHom g →
        ∀ ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E.obj,
          R.map (koszulOpenUnit A r f e) ≫ ψ =
            R.map (DerivedCategory.Q.map
              (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map g) ≫
                DerivedCategory.Q.map s.hom ≫ eF.hom) →
          b ψ = β (HomologicalComplex.homologyMap (colimit.ι D e) 0
            (HomologicalComplex.homologyMap (koszulCechHomObjIso A r f M e).inv 0
              ((CochainComplex.moduleHomComplex
                ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).homologyπ
                  0 z))) := by
  classical
  intro R M D C β
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
  let T := (koszulOpenTilde A).mapHomologicalComplex (.up ℤ)
  obtain ⟨b, hb, hchain⟩ := koszulOpenHom_chain_evaluation A r f
  let b' : (R.obj (koszulOpenStructure A) ⟶ R.obj E.obj) ≃+ H.obj (G.obj E.obj) :=
    { b E.obj with map_add' := naturalEquiv_add R (G ⋙ H) _ b hb E.obj }
  refine ⟨b', ?_⟩
  intro e g z hz ψ hψ
  let t : koszulOpenSheafComplex A r f e ⟶ F := T.map g ≫ s.hom
  have ht : koszulOpenHomTranspose A r f F e t = g :=
    koszulOpenHomTranspose_tilde_counit A r f F s hs e g
  have hψt : R.map (koszulOpenUnit A r f e) ≫ ψ =
      R.map (DerivedCategory.Q.map t ≫ eF.hom) := by
    rw [hψ]
    exact congrArg R.map (by simp only [t, T, Functor.map_comp, Category.assoc])
  have htransport := naturalEquiv_transport_chain R (G ⋙ H) (koszulOpenStructure A)
    b hb (koszulOpenUnit A r f e) (DerivedCategory.Q.map t) eF _
      (hchain F hF e t) ψ hψt
  change b E.obj ψ = _
  refine htransport.trans ?_
  have hstage := koszulOpenHomStageClass_colimit_of_cycle A r f F e t g ht z hz
  have hresult := congrArg
    (fun x ↦ H.map (G.map eF.hom) (H.map (koszulCechDerivedComparison A r f F) x)) hstage
  refine hresult.trans ?_
  simp only [β, Functor.map_comp, ModuleCat.comp_apply]
  rfl

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianCounitCocycleDefinitions
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import WeilConjectures.AlgebraicGeometry.AbelianInjectiveCounitCocycle

/-! # The cocycle calculation for an arbitrary abelian injective target

Source: Stacks Project, Tags 01F7 and 06XR.
(blueprint: new-abelian-counit-cocycle-calculation)
-/

@[expose] public section
universe u v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
attribute [local instance] AlgebraicGeometry.Scheme.Modules.instAddCommGroupH
attribute [local instance] cocycle_pushforward_additive
attribute [local irreducible] abelianResolutionIso
attribute [local irreducible] Functor.rightDerivedObjIsoOfResolution
attribute [local irreducible] siteSectionsObjIso

private theorem homotopy_of_comp_quasiIso_nat
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L J : CochainComplex C ℕ} [∀ n, Injective (J.X n)]
    (α : K ⟶ L) [QuasiIso α] (β₁ β₂ : L ⟶ J)
    (w : α ≫ β₁ = α ≫ β₂) : Nonempty (Homotopy β₁ β₂) := by
  let e := ComplexShape.embeddingUpNat
  have : QuasiIso (HomologicalComplex.extendMap α e) :=
    (HomologicalComplex.quasiIso_extendMap_iff α e).2 inferInstance
  have : ∀ n, Injective ((J.extend e).X n) := fun n ↦ inferInstance
  have hw : HomologicalComplex.extendMap α e ≫ HomologicalComplex.extendMap β₁ e =
      HomologicalComplex.extendMap α e ≫ HomologicalComplex.extendMap β₂ e := by
    simp only [← HomologicalComplex.extendMap_comp, w]
  obtain ⟨ht⟩ := CochainComplex.homotopy_of_comp_quasiIso_of_injective
    (I := J.extend e)
    ⟨0, fun n hn ↦ (CochainComplex.isStrictlyGE_iff (J.extend e) 0).1
      inferInstance n hn⟩
    (HomologicalComplex.extendMap α e)
    (HomologicalComplex.extendMap β₁ e) (HomologicalComplex.extendMap β₂ e)
    ⟨Homotopy.ofEq hw⟩
  exact ⟨ht.ofExtend⟩


/-- The inverse-image/coefficient cocycle computation for abelian sheaves.
It asserts no comparison with a target module resolution.

Source: Stacks Project, Tag 01F7, Lemma 01F8 and equation 01F9; Tag 06XR.
(blueprint: new-abelian-counit-cocycle-calculation)

Proof: Replace the forgotten source module resolution by an abelian injective
resolution using its quasi-isomorphic augmentation. The proved comparison
evaluation identifies the prescribed source normalization after this change.
Lift the coefficient map from the inverse image of the abelian resolution to
the given injective target. The original lift and this composite lift have the
same augmented composite, so they are homotopic, by exactness of inverse image
and injectivity of the target terms. Their section maps have equal homology.
For two abelian injective resolutions, the fixed Ext-to-sections normalization
sends each closed Hom cocycle to its section-homology class. The exact-functor
cocycle theorem computes inverse image and coefficients, and the constant-sheaf
adjunction identifies its integer-generator evaluation with the section map.
Naturality of the adjunction unit factors the replacement section map through
the source comparison. Combining these homology equalities proves the result.
The argument includes degree zero, zero sheaves and empty schemes. -/
theorem abelian_counit_cocycle_calculation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Y.Modules) (F : X.Modules) (J : InjectiveResolution A)
    (c : (invImage f).obj
      ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A) ⟶
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F))
    (R : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F))
    (L : ((invImage f).mapHomologicalComplex (.up ℕ)).obj
      (((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex) ⟶ R.cocomplex)
    (hL : (HomologicalComplex.singleMapHomologicalComplex (invImage f) (.up ℕ) 0).inv.app
      ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A) ≫
      ((invImage f).mapHomologicalComplex (.up ℕ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)) (.up ℕ) 0).inv.app A ≫
          ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).mapHomologicalComplex
            (.up ℕ)).map J.ι) ≫ L = (CochainComplex.single₀ _).map c ≫ R.ι)
    (s : abelianPushforward f ⋙ abelianSections Y ≅ abelianSections X)
    (hs : ∀ G, s.hom.app G = G.obj.map
      (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ op (⊤ : X.Opens)))
    (p : ℕ) (x : H A p) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map
      (((abelianSections Y).mapHomologicalComplex (.up ℕ)).map
        ((NatTrans.mapHomologicalComplex (abelianAdjunction f).unit (.up ℕ)).app
          (((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).mapHomologicalComplex
            (.up ℕ)).obj J.cocomplex) ≫
          ((abelianPushforward f).mapHomologicalComplex (.up ℕ)).map L) ≫
        (NatTrans.mapHomologicalComplex s.hom (.up ℕ)).app R.cocomplex))
      ((abelianResolutionIso Y J p).hom x) =
    (abelianInjectiveResolutionIso X F R p).hom
      (Sheaf.H.map c p (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
        ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A) p x)) := by
  let T := SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app A ≫
    (T.mapHomologicalComplex (.up ℕ)).map J.ι
  have : QuasiIso ι := by
    dsimp only [ι]
    exact quasiIso_comp _ _
  let I := injectiveResolution (T.obj A)
  let φ := InjectiveResolution.descOfQuasiIso (𝟙 (T.obj A)) I ι
  have hφ : ι ≫ φ = I.ι := by simp [φ]
  let α := (HomologicalComplex.singleMapHomologicalComplex (invImage f) (.up ℕ) 0).inv.app
      (T.obj A) ≫ ((invImage f).mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso α := by
    dsimp only [α]
    exact quasiIso_comp _ _
  let β := InjectiveResolution.descOfQuasiIso c R α
  have hβ : α ≫ β = (CochainComplex.single₀ _).map c ≫ R.ι := by
    exact InjectiveResolution.descOfQuasiIso_commutes _ _ _
  have hβ0 : (invImage f).map (I.ι.f 0) ≫ β.f 0 = c ≫ R.ι.f 0 := by
    simpa [α] using congrArg (fun g ↦ g.f 0) hβ
  have hev :
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map
        (((abelianSections Y).mapHomologicalComplex (.up ℕ)).map φ))
        ((abelianResolutionIso Y J p).hom x) =
      (abelianInjectiveResolutionIso Y A I p).hom x := by
    have h := abelian_resolution_comparison_evaluation Y A J I φ
      (by simpa [ι] using hφ) p x
    exact h
  have hc := abelian_injective_counit_cocycle_calculation f A F I c R β hβ0
    s hs p x
  let K := (T.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let Q := (invImage f).mapHomologicalComplex (.up ℕ)
  let P := (abelianPushforward f).mapHomologicalComplex (.up ℕ)
  let G := (abelianSections Y).mapHomologicalComplex (.up ℕ)
  let η := NatTrans.mapHomologicalComplex (abelianAdjunction f).unit (.up ℕ)
  let σ := NatTrans.mapHomologicalComplex s.hom (.up ℕ)
  let L' := Q.map φ ≫ β
  let γ := (HomologicalComplex.singleMapHomologicalComplex (invImage f) (.up ℕ) 0).inv.app
      (T.obj A) ≫ Q.map ι
  have : QuasiIso γ := by
    dsimp only [γ, Q]
    exact quasiIso_comp _ _
  have hL' : γ ≫ L' = (CochainComplex.single₀ _).map c ≫ R.ι := by
    change (_ ≫ Q.map ι) ≫ (Q.map φ ≫ β) = _
    rw [Category.assoc, ← Category.assoc (Q.map ι), ← Q.map_comp, hφ]
    simpa only [α, Q, Category.assoc] using hβ
  have hw : γ ≫ L = γ ≫ L' := by
    rw [hL']
    exact hL
  obtain ⟨ht⟩ := homotopy_of_comp_quasiIso_nat γ L L' hw
  let t := G.map (η.app K ≫ P.map L) ≫ σ.app R.cocomplex
  let t' := G.map (η.app K ≫ P.map L') ≫ σ.app R.cocomplex
  let tβ := G.map (η.app I.cocomplex ≫ P.map β) ≫ σ.app R.cocomplex
  have heq : HomologicalComplex.homologyMap t p =
      HomologicalComplex.homologyMap t' p := by
    exact (((abelianSections Y).mapHomotopy
      (((abelianPushforward f).mapHomotopy ht).compLeft (η.app K))).compRight
        (σ.app R.cocomplex)).homologyMap_eq p
  have hn : φ ≫ η.app I.cocomplex = η.app K ≫ P.map (Q.map φ) := by
    exact η.naturality φ
  have hnG : G.map φ ≫ G.map (η.app I.cocomplex) =
      G.map (η.app K) ≫ G.map (P.map (Q.map φ)) := by
    simpa only [Functor.map_comp] using congrArg G.map hn
  have ht' : t' = G.map φ ≫ tβ := by
    dsimp only [t', tβ, L']
    simp only [Functor.map_comp, Category.assoc]
    simpa only [Category.assoc] using congrArg
      (fun m ↦ m ≫ G.map (P.map β) ≫ σ.app R.cocomplex) hnG.symm
  dsimp only [HomologicalComplex.homologyFunctor] at hev hc
  have hev' : (HomologicalComplex.homologyMap (G.map φ) p)
      ((abelianResolutionIso Y J p).hom x) =
      (abelianInjectiveResolutionIso Y A I p).hom x := by
    simpa only [G, HomologicalComplex.homologyFunctor_map] using hev
  have hc' : (HomologicalComplex.homologyMap tβ p)
      ((abelianInjectiveResolutionIso Y A I p).hom x) =
      (abelianInjectiveResolutionIso X F R p).hom
        (Sheaf.H.map c p (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
          (T.obj A) p x)) := by
    simpa only [tβ, G, P, η, σ, HomologicalComplex.homologyFunctor_map] using hc
  change (HomologicalComplex.homologyMap t p) ((abelianResolutionIso Y J p).hom x) = _
  rw [heq, ht', HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply]
  exact (congrArg (HomologicalComplex.homologyMap tβ p) hev').trans hc'


end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

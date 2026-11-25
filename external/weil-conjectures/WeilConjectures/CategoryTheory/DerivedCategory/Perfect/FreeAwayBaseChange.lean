/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Embedding.RestrictionExtend
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.FiniteFree

/-!
# Finite free local models which are stable under base change

Let `K` be a perfect complex of flat `A`-modules in degrees `[0, b]`, and `ι : K ⟶ C` a morphism
to a complex `C` indexed by `ℕ` (extended by zero to `ℤ`) which is a quasi-isomorphism after
every base change. For every prime `p` of `A` there are `s ∉ p`, a complex `P` of finite free
`A_s`-modules in degrees `[0, b]` and a morphism `P ⟶ A_s ⊗[A] C` which stays a
quasi-isomorphism after every base change `A_s ⟶ B`
(`CochainComplex.exists_free_away_quasiIso_baseChange`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace ModuleCat

variable (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A' B]
  [Algebra A B] [IsScalarTower A A' B]

/-- Base change in two steps `A ⟶ A' ⟶ B` is base change along `A ⟶ B`. -/
noncomputable def baseChangeCompIso : baseChange A A' ⋙ baseChange A' B ≅ baseChange A B :=
  NatIso.ofComponents (fun M ↦ (AlgebraTensorModule.cancelBaseChange A A' B B M).toModuleIso)
    (by
      intro M N f
      ext : 1
      refine LinearMap.ext fun x ↦ ?_
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | tmul b y =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' =>
          simp only [tmul_add, map_add] at hy hy' ⊢
          rw [hy, hy']
        | tmul a x => rfl)

lemma baseChangeCompIso_hom_app_tmul (M : ModuleCat.{u} A) (b : B) (a : A') (m : M) :
    ((baseChangeCompIso A A' B).hom.app M).hom (b ⊗ₜ (a ⊗ₜ m)) = (a • b) ⊗ₜ m :=
  rfl

/-- Base change in two steps `A ⟶ A' ⟶ B` of a complex of modules is its base change along
`A ⟶ B`. -/
noncomputable def mapHomologicalComplexBaseChangeCompIso {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} A) c) :
    ((baseChange A' B).mapHomologicalComplex c).obj
        (((baseChange A A').mapHomologicalComplex c).obj K) ≅
      ((baseChange A B).mapHomologicalComplex c).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ (baseChangeCompIso A A' B).app (K.X i))
    (fun i j _ ↦ ((baseChangeCompIso A A' B).hom.naturality (K.d i j)).symm)

lemma mapHomologicalComplexBaseChangeCompIso_hom_f_apply {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} A) c) (i : ι) (x : B ⊗[A'] (A' ⊗[A] K.X i)) :
    ((mapHomologicalComplexBaseChangeCompIso A A' B K).hom.f i).hom x =
      AlgebraTensorModule.cancelBaseChange A A' B B (K.X i) x :=
  rfl

end ModuleCat

namespace CochainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

instance isStrictlySupported_embeddingUpNat (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] :
    K.IsStrictlySupported ComplexShape.embeddingUpNat :=
  ⟨fun i' hi' ↦ K.isZero_of_isStrictlyGE 0 i' (by
    by_contra h
    exact hi' i'.toNat (by simp [Int.toNat_of_nonneg (not_lt.1 h)]))⟩

variable {A : Type u} [CommRing A]

/-- Base change along `A ⟶ A' ⟶ B` of a morphism of complexes is a quasi-isomorphism if base
change along `A ⟶ B` is. -/
lemma quasiIso_map_baseChange_comp {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} A) c} (φ : K ⟶ L) (A' B : Type u) [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    [QuasiIso (((ModuleCat.baseChange A B).mapHomologicalComplex _).map φ)] :
    QuasiIso (((ModuleCat.baseChange A' B).mapHomologicalComplex _).map
      (((ModuleCat.baseChange A A').mapHomologicalComplex _).map φ)) := by
  let η := ModuleCat.baseChangeCompIso A A' B
  let e (M : HomologicalComplex (ModuleCat.{u} A) c) :
      ((ModuleCat.baseChange A' B).mapHomologicalComplex _).obj
        (((ModuleCat.baseChange A A').mapHomologicalComplex _).obj M) ≅
        ((ModuleCat.baseChange A B).mapHomologicalComplex _).obj M :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ η.app (M.X i))
      (fun i j _ ↦ (η.hom.naturality (M.d i j)).symm)
  have hsq : ((ModuleCat.baseChange A' B).mapHomologicalComplex _).map
      (((ModuleCat.baseChange A A').mapHomologicalComplex _).map φ) ≫ (e L).hom =
      (e K).hom ≫ ((ModuleCat.baseChange A B).mapHomologicalComplex _).map φ := by
    ext i : 1
    exact η.hom.naturality (φ.f i)
  rw [← quasiIso_iff_comp_right _ (e L).hom, hsq]
  infer_instance

variable [HasDerivedCategory.{u} (ModuleCat.{u} A)]

/-- **Finite free local models stable under base change.** Let `K` be a complex of flat
`A`-modules in degrees `[0, b]` which is perfect in `D(A)`, `C` a complex of `A`-modules indexed
by `ℕ` and `ι : K ⟶ C` (with `C` extended by zero to `ℤ`) a morphism which is a
quasi-isomorphism after every base change `A ⟶ B`. For every prime `p` of `A` there are `s ∉ p`,
a complex `P` of free `A_s`-modules of finite rank in degrees `[0, b]` and a morphism
`Φ : P ⟶ A_s ⊗[A] C` (in degrees `≥ 0`) which is a quasi-isomorphism after every base change
`A_s ⟶ B`. -/
theorem exists_free_away_quasiIso_baseChange (C : CochainComplex (ModuleCat.{u} A) ℕ)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [K.IsStrictlyGE 0] [K.IsStrictlyLE b]
    (hK : ∀ n, Module.Flat A (K.X n)) (hKP : (DerivedCategory.Q.obj K).IsPerfect)
    (ι : K ⟶ C.extend ComplexShape.embeddingUpNat)
    (hι : ∀ (B : Type u) [CommRing B] [Algebra A B],
      QuasiIso (((ModuleCat.baseChange A B).mapHomologicalComplex _).map ι))
    (p : Ideal A) [p.IsPrime] :
    ∃ s ∉ p, ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away s)) ℤ)
      (_ : P.IsStrictlyGE 0) (_ : P.IsStrictlyLE b),
      (∀ n, Module.Free (Localization.Away s) (P.X n) ∧
        Module.Finite (Localization.Away s) (P.X n)) ∧
      ∃ Φ : P.restriction ComplexShape.embeddingUpNat ⟶
          ((ModuleCat.baseChange A (Localization.Away s)).mapHomologicalComplex _).obj C,
        ∀ (B : Type u) [CommRing B] [Algebra (Localization.Away s) B],
          QuasiIso (((ModuleCat.baseChange (Localization.Away s) B).mapHomologicalComplex
            _).map Φ) := by
  obtain ⟨s, hs, P, _, _, hP, φ, _⟩ :=
    DerivedCategory.exists_quasiIso_free_away_of_isPerfect K 0 b hK hKP p
  let e := ComplexShape.embeddingUpNat
  let F := ModuleCat.baseChange A (Localization.Away s)
  refine ⟨s, hs, P, inferInstance, inferInstance, hP,
    e.homRestrict (φ ≫ (F.mapHomologicalComplex _).map ι ≫ (C.mapExtendIso e F).hom),
    fun B _ _ ↦ ?_⟩
  let G := ModuleCat.baseChange (Localization.Away s) B
  let : Algebra A B := ((algebraMap (Localization.Away s) B).comp
    (algebraMap A (Localization.Away s))).toAlgebra
  have : IsScalarTower A (Localization.Away s) B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : CochainComplex.IsStrictlyGE ((G.mapHomologicalComplex _).obj P) 0 :=
    (CochainComplex.isStrictlyGE_iff ((G.mapHomologicalComplex _).obj P) 0).2 fun i hi ↦
      G.map_isZero (P.isZero_of_isStrictlyGE 0 i hi)
  rw [← HomologicalComplex.homRestrict_map_comp_mapExtendIso_hom,
    ← HomologicalComplex.quasiIso_iff_quasiIso_homRestrict]
  -- base change of `φ`
  have hPflat (i : ℤ) : Module.Flat (Localization.Away s) (P.X i) := by
    have := (hP i).1
    infer_instance
  have hFK (i : ℤ) :
      Module.Flat (Localization.Away s) (((F.mapHomologicalComplex _).obj K).X i) := by
    have := hK i
    change Module.Flat (Localization.Away s) (Localization.Away s ⊗[A] K.X i)
    infer_instance
  have hcone (k : ℤ) (hk : b + 1 ≤ k) : Module.Flat (Localization.Away s)
      (LinearMap.ker ((CochainComplex.mappingCone φ).d k (k + 1)).hom) := by
    have hz : IsZero ((CochainComplex.mappingCone φ).X k) :=
      (CochainComplex.mappingCone.isZero_X_iff φ k).2
        ⟨P.isZero_of_isStrictlyLE b (k + 1) (by lia),
          F.map_isZero (K.isZero_of_isStrictlyLE b k (by lia))⟩
    have : Subsingleton ((CochainComplex.mappingCone φ).X k) :=
      ModuleCat.subsingleton_of_isZero hz
    infer_instance
  have := CochainComplex.quasiIso_map_baseChange B φ hPflat hFK hcone
  -- base change of `ι`
  have := quasiIso_map_baseChange_comp ι (Localization.Away s) B
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  infer_instance

end CochainComplex

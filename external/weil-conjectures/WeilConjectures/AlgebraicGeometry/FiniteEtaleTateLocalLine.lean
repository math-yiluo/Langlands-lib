/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf

/-! # Local triviality of the finite coefficient line
Source: Stacks Project, Tag 03PK. (auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Extending scalars from a `ZMod N`-module agrees with extending its underlying
abelian group: all additive maps between `ZMod N`-modules are automatically linear. -/
private noncomputable def zmodScalarExtensionIso
    (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp A := by
  let f := finiteEtaleTwistScalar N A hA
  let adj := ModuleCat.extendScalarsAddCommGrpAdj A
  let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} A) :
      ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).obj P) ≃
        (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
    { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
        (AddMonoidHom.toZModLinearMap N (M := M)
          (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
      invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
      left_inv := fun g ↦ rfl
      right_inv := fun g ↦ by ext; rfl }
  let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
      ModuleCat.extendScalarsAddCommGrp A) ⊣ ModuleCat.restrictScalars f :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
        homEquiv_naturality_left_symm := by
          intro M' M P g k
          change (adj.homEquiv _ _).symm
            ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map g ≫
              (e M P).symm k) = _
          exact adj.homEquiv_naturality_left_symm _ _
        homEquiv_naturality_right := by
          intro M P P' g k
          change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
          rw [adj.homEquiv_naturality_right]
          rfl }
  exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'

/-- The published finite twist line is the existing abelian-sheaf scalar extension. -/
private noncomputable def finiteEtaleLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (finiteEtaleMuModulePresheaf T N)
      (zmodScalarExtensionIso N A hA))

/-- Pull back the universal primitive-root cover of the global section ring. Its
root trivializes the roots-of-unity sheaf and hence its scalar extension. -/
theorem finiteEtaleTateLine_surjectiveTrivialization
    (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hInvertible : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ∃ (V : Scheme.{u}) (q : V ⟶ T), Etale q ∧ Function.Surjective q.base ∧
      Nonempty ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) q).obj
        (finiteEtaleTateLine T N A hA) ≅
          MonoidalCategoryStruct.tensorUnit
            (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))) := by
  classical
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hNg : IsUnit (N : Γ(T, ⊤)) :=
    T.toRingedSpace.isUnit_of_isUnit_germ ⊤ (N : Γ(T, ⊤))
      (fun t _ ↦ by simpa only [map_natCast] using hInvertible t)
  let B := Γ(T, ⊤)
  have : Etale (primitiveRootsCover B N) := etale_primitiveRootsCover B N (NeZero.ne N) hNg
  let V := pullback T.toSpecΓ (primitiveRootsCover B N)
  let q : V ⟶ T := pullback.fst _ _
  have hq : Function.Surjective q.base := by
    intro t
    obtain ⟨v, hv⟩ := surjective_primitiveRootsCover B N hNg (T.toSpecΓ t)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback t v hv.symm
    exact ⟨z, hz⟩
  let φ : CommRingCat.of (PrimitiveRootsAlgebra B N) ⟶ Γ(V, ⊤) :=
    (ΓSpecIso (.of (PrimitiveRootsAlgebra B N))).inv ≫
      (pullback.snd T.toSpecΓ (primitiveRootsCover B N)).appTop
  let ζ : Γ(V, ⊤)ˣ := ((PrimitiveRootsAlgebra.isUnit_zeta B N hN).map φ.hom).unit
  have hζ : ζ ^ N = 1 := by
    ext
    simp only [ζ, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one, ← map_pow,
      PrimitiveRootsAlgebra.zeta_pow, map_one]
  have hζ' : ∀ i < N, ∀ j < N, i ≠ j →
      IsUnit ((ζ : Γ(V, ⊤)) ^ i - (ζ : Γ(V, ⊤)) ^ j) := by
    intro i hi j hj hij
    simpa only [ζ, IsUnit.unit_spec, ← map_pow, ← map_sub] using
      (PrimitiveRootsAlgebra.isUnit_zeta_pow_sub_zeta_pow B N hi hj hij).map φ.hom
  have := V.isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub N ζ hζ hζ'
  have := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf N q
  let e : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) q).obj
      (finiteEtaleTateLine T N A hA) ≅
        MonoidalCategoryStruct.tensorUnit (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) q).mapIso
        (finiteEtaleLineAbIso T N A hA) ≪≫
      (AlgebraicGeometry.Etale.upperStarExtendScalarsIso A q).app _ ≪≫
      (AlgebraicGeometry.Etale.extendScalars A V).mapIso
        (asIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf N q)) ≪≫
      (AlgebraicGeometry.Etale.extendScalars A V).mapIso
        (asIso (V.constantZModToRootsOfUnitySheaf N ζ hζ)).symm ≪≫
      AlgebraicGeometry.Etale.extendScalarsConstantZModIso V hA
  exact ⟨V, q, inferInstance, hq, ⟨e⟩⟩

/-- The primitive-root cover trivializes the coefficient line. -/
theorem finiteEtaleTateLine_localTrivial
    (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hInvertible : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ∃ cover : Cover.{u} etalePrecoverage T, ∀ i : cover.I₀,
      Nonempty
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) (cover.f i)).obj
          (finiteEtaleTateLine T N A hA) ≅
            MonoidalCategoryStruct.tensorUnit
              (Sheaf (cover.X i).smallEtaleTopology (ModuleCat.{u + 1} A))) := by
  classical
  obtain ⟨V, q, hqE, hq, ⟨e⟩⟩ :=
    finiteEtaleTateLine_surjectiveTrivialization T N hN hInvertible A hA
  have : Etale q := hqE
  let cover : Cover.{u} etalePrecoverage T :=
    Cover.mkOfCovers PUnit (fun _ ↦ V) (fun _ ↦ q)
      (fun t ↦ ⟨⟨⟩, hq t⟩) (fun _ ↦ inferInstance)
  exact ⟨cover, fun _ ↦ ⟨e⟩⟩

end AlgebraicGeometry.Scheme

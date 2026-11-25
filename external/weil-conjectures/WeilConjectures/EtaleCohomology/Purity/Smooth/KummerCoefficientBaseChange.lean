/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.Mathlib.Algebra.Group.Equiv.Defs

/-!
# Base change of the Kummer coefficients

For a finite coefficient ring `Λ` of characteristic `n` which is free as a `ℤ/n`-module, the
natural map `Λ ⊗ Hᵠ(X, μₙ) ⟶ Hᵠ(X, μₙ ⊗ Λ)` is an isomorphism, compatibly with the Kummer
boundary maps (blueprint `lem-pur-kummer-coefficient-base-change`).

Over an algebraically closed field `μₙ ≅ ℤ/n`, and the comparison reduces to the additivity of
cohomology: `μₙ ⊗ Λ` is the constant sheaf on `Λ ⊗ ℤ/n ≅ (ℤ/n)ʳ`, through the unit
`ℤ/n ⟶ Λ ⊗ ℤ/n` (`AlgebraicGeometry.Etale.unit_comp_constantSheafCompExtendScalarsIso`).
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Opposite TensorProduct




namespace CategoryTheory.Functor

variable (F : AddCommGrpCat.{v} ⥤ AddCommGrpCat.{w}) [F.Additive] {L : Type*} [AddCommGroup L]
  {Z V : AddCommGrpCat.{v}} (ψ : L →+ (Z ⟶ V))

/-- The map `L ⊗ F(Z) ⟶ F(V)`, `c ⊗ z ↦ F(ψ c) z`. -/
noncomputable def tensorMapOf : L ⊗[ℤ] F.obj Z →+ F.obj V :=
  TensorProduct.liftAddHom
    { toFun c := (F.map (ψ c)).hom
      map_zero' := by simp
      map_add' c c' := by simp }
    (fun m c z ↦ by
      change (F.map (ψ (m • c))).hom z = (F.map (ψ c)).hom (m • z)
      rw [_root_.map_zsmul, F.map_zsmul, _root_.map_zsmul]
      rfl)

@[simp]
lemma tensorMapOf_tmul (c : L) (z : F.obj Z) : F.tensorMapOf ψ (c ⊗ₜ z) = F.map (ψ c) z :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- If `ψ : L ≅ Hom(Z, V)` and `V` is a finite direct sum of copies of `Z`, whose endomorphisms
are integers, then `L ⊗ F(Z) ≅ F(V)` for every additive functor `F`. -/
theorem bijective_tensorMapOf (hψ : Function.Bijective ψ) {r : ℕ}
    (κ : V ≅ ⨁ fun _ : Fin r ↦ Z) (hZ : ∀ g : Z ⟶ Z, ∃ m : ℤ, g = m • 𝟙 Z) :
    Function.Bijective (F.tensorMapOf ψ) := by
  let π (i : Fin r) : V ⟶ Z := κ.hom ≫ biproduct.π (fun _ : Fin r ↦ Z) i
  let ι (i : Fin r) : Z ⟶ V := biproduct.ι (fun _ : Fin r ↦ Z) i ≫ κ.inv
  have hsum : ∑ i, π i ≫ ι i = 𝟙 V := by
    calc ∑ i, π i ≫ ι i = κ.hom ≫ (∑ i, biproduct.π (fun _ : Fin r ↦ Z) i ≫
          biproduct.ι (fun _ : Fin r ↦ Z) i) ≫ κ.inv := by
          rw [Preadditive.sum_comp, Preadditive.comp_sum]
          simp only [π, ι, Category.assoc]
      _ = 𝟙 V := by rw [biproduct.total, Category.id_comp, κ.hom_inv_id]
  obtain ⟨β, hβ⟩ : ∃ β : Fin r → L, ∀ i, ψ (β i) = ι i := ⟨fun i ↦ (hψ.2 (ι i)).choose,
    fun i ↦ (hψ.2 (ι i)).choose_spec⟩
  let G : F.obj V →+ L ⊗[ℤ] F.obj Z :=
    { toFun y := ∑ i, β i ⊗ₜ (F.map (π i) y)
      map_zero' := by simp
      map_add' a b := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib] }
  have hGΞ : ∀ x, G (F.tensorMapOf ψ x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]
    | tmul c z =>
      rw [tensorMapOf_tmul]
      have hm (i : Fin r) : ∃ m : ℤ, ψ c ≫ π i = m • 𝟙 Z := hZ _
      choose m hm using hm
      have hc : c = ∑ i, m i • β i := by
        apply hψ.1
        rw [_root_.map_sum]
        simp only [_root_.map_zsmul, hβ]
        calc ψ c = ψ c ≫ ∑ i, π i ≫ ι i := by rw [hsum, Category.comp_id]
          _ = ∑ i, (ψ c ≫ π i) ≫ ι i := by
            rw [Preadditive.comp_sum]
            simp only [Category.assoc]
          _ = ∑ i, m i • ι i := by
            simp only [hm, Preadditive.zsmul_comp, Category.id_comp]
      change ∑ i, β i ⊗ₜ (F.map (π i) (F.map (ψ c) z)) = _
      conv_rhs => rw [hc, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hm, F.map_zsmul, F.map_id,
        TensorProduct.smul_tmul]
      rfl
  have hsumF : ∀ y : F.obj V, ∑ i, F.map (ι i) (F.map (π i) y) = y := by
    intro y
    have h := congrArg (fun φ : F.obj V ⟶ F.obj V ↦ φ y) (congrArg F.map hsum)
    simp only [F.map_sum, F.map_id] at h
    refine Eq.trans ?_ h
    classical
    simp only [← ConcreteCategory.comp_apply, ← F.map_comp]
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
        AddCommGrpCat.hom_add_apply]
  refine ⟨Function.LeftInverse.injective hGΞ, fun y ↦ ⟨G y, ?_⟩⟩
  change F.tensorMapOf ψ (∑ i, β i ⊗ₜ (F.map (π i) y)) = y
  rw [_root_.map_sum]
  simp only [tensorMapOf_tmul, hβ]
  exact hsumF y

end CategoryTheory.Functor



namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

set_option linter.flexible false in
/-- The unit of `constantSheaf ⊣ Γ(⊤, -)` on modules, made abelian, is the unit on abelian
groups, under `forget₂ ∘ constantSheaf ≅ constantSheaf ∘ forget₂`. -/
lemma forget₂_map_constantSheafAdj_unit_app (N : ModuleCat.{u + 1} Λ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal).unit.app
          N) ≫
      ((constantSheafSheafComposeForget₂Iso Λ).hom.app N).hom.app (op (⊤_ X.Etale)) =
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj N) := by
  simp [constantSheafAdj, constantPresheafAdj, constantSheafSheafComposeForget₂Iso]
  have : X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction _ (ModuleCat.forget₂CoinduceAdj Λ)
  have h : Functor.whiskerRight (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N))
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≫
        (sheafifyComposeIso X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
          ((Functor.const X.Etaleᵒᵖ).obj N)).inv =
      toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
    rw [← sheafComposeIso_hom_fac, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h2 := congrArg (fun φ ↦ φ.app (op (⊤_ X.Etale))) h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h2
  erw [Category.id_comp]
  exact h2

/-- **The unit of extension of scalars on constant sheaves.** Under
`Λ ⊗ M_X ≅ (Λ ⊗ M)_X` and `forget₂ ∘ constantSheaf ≅ constantSheaf ∘ forget₂`, the unit
`M_X ⟶ Λ ⊗ M_X` is the constant sheaf on the unit `M ⟶ Λ ⊗ M`. -/
lemma unit_comp_constantSheafCompExtendScalarsIso (M : AddCommGrpCat.{u + 1}) :
    (extendScalarsAdjunction Λ X).unit.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) ≫
      (forget₂Sheaf Λ X).map ((constantSheafCompExtendScalarsIso Λ X).hom.app M) ≫
        (constantSheafSheafComposeForget₂Iso Λ).hom.app
          ((ModuleCat.extendScalarsAddCommGrp Λ).obj M) =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((ModuleCat.extendScalarsAddCommGrpAdj Λ).unit.app M) := by
  let adjA := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  apply (adjA.homEquiv _ _).injective
  have hR : adjA.homEquiv M ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((ModuleCat.extendScalarsAddCommGrp Λ).obj M)))
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((ModuleCat.extendScalarsAddCommGrpAdj Λ).unit.app M)) =
        (ModuleCat.extendScalarsAddCommGrpAdj Λ).unit.app M ≫ adjA.unit.app _ := by
    rw [Adjunction.homEquiv_unit]
    exact (adjA.unit.naturality _).symm
  have hU := Adjunction.unit_leftAdjointUniq_hom_app
    (adjA.comp (extendScalarsAdjunction Λ X))
    (((ModuleCat.extendScalarsAddCommGrpAdj Λ).comp (constantSheafAdj X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) terminalIsTerminal)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))) M
  erw [hR]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← Category.assoc]
  erw [hU]
  simp only [Adjunction.ofNatIsoRight, NatTrans.comp_app, Adjunction.comp_unit_app,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.assoc]
  congr 1
  exact forget₂_map_constantSheafAdj_unit_app Λ X _


/-- A module isomorphic to `Λ` has endomorphism ring `Λ`. -/
lemma bijective_smul_id_of_iso {W : ModuleCat.{u + 1} Λ} (ι : W ≅ ModuleCat.of Λ Λ) :
    Function.Bijective (fun c : Λ ↦ c • 𝟙 W) := by
  refine ⟨fun c d h ↦ ?_, fun g ↦ ⟨(ι.inv ≫ g ≫ ι.hom) (1 : Λ), ?_⟩⟩
  · have := congrArg (fun φ : W ⟶ W ↦ (ι.inv ≫ φ ≫ ι.hom) (1 : Λ)) h
    simpa using this
  · rw [← cancel_epi ι.inv, ← cancel_mono ι.hom]
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    simp

/-- Every endomorphism of `ℤ/n` is multiplication by an integer. -/
lemma exists_eq_zsmul_id_zmod (n : ℕ)
    (g : AddCommGrpCat.of (ULift.{u + 1} (ZMod n)) ⟶ AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) :
    ∃ m : ℤ, g = m • 𝟙 _ := by
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (g.hom (ULift.up 1)).down
  refine ⟨m, ?_⟩
  ext ⟨a⟩
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective a
  have ha : (ULift.up (b : ZMod n) : ULift.{u + 1} (ZMod n)) = b • ULift.up 1 := by
    apply ULift.ext
    simp
  rw [ha, map_zsmul]
  change (b • g.hom (ULift.up 1)).down =
    (m • (b • (ULift.up (1 : ZMod n) : ULift.{u + 1} (ZMod n)))).down
  simp [← hm, mul_comm]

section Instances

/-! The `HasExt` instances of the étale sheaf categories, as lemmas applied to variables, used as
local instances below. Instance synthesis otherwise produces `IsGrothendieckAbelian.hasExt` applied
to the (non-atomic) sheaf category; inside definitions this proof is abstracted into an auxiliary
lemma stating the unfolded `HasExt`, which the kernel can only compare with the original by
unfolding the derived category constructions. -/

/-- `HasExt` for étale sheaves of `Λ`-modules, as a lemma to be used as a local instance. -/
lemma hasExt_sheaf_moduleCat (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  inferInstance

/-- `HasExt` for abelian étale sheaves, as a lemma to be used as a local instance. -/
lemma hasExt_sheaf_addCommGrpCat (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

end Instances

attribute [local instance high] hasExt_sheaf_moduleCat hasExt_sheaf_addCommGrpCat

section Generic

/-! Generic constructions on tensor products, instantiated below at `Ext`-groups. -/

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The map `R ⊗ A ⟶ B`, `c ⊗ x ↦ c • g x`, for an `R`-module `B`. -/
noncomputable def _root_.TensorProduct.liftSMulAddHom (R : Type*) [CommRing R] [Module R B]
    (g : A →+ B) : R ⊗[ℤ] A →+ B :=
  TensorProduct.liftAddHom
    { toFun c := (DistribSMul.toAddMonoidHom _ c).comp g
      map_zero' := by ext; simp
      map_add' c d := by ext; simp [add_smul] }
    (fun m c x ↦ by
      simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
        DistribSMul.toAddMonoidHom_apply, map_zsmul, zsmul_eq_mul]
      rw [mul_smul, Int.cast_smul_eq_zsmul, smul_comm])

lemma _root_.TensorProduct.liftSMulAddHom_tmul (R : Type*) [CommRing R] [Module R B]
    (g : A →+ B) (c : R) (x : A) :
    TensorProduct.liftSMulAddHom R g (c ⊗ₜ x) = c • g x :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- Two additive maps out of `L ⊗ M` agreeing on pure tensors agree. -/
private lemma tensorAddHom_apply_eq_of_tmul {L M P : Type*} [AddCommGroup L] [AddCommGroup M]
    [AddCommGroup P] (f g : L ⊗[ℤ] M →+ P) (h : ∀ c x, f (c ⊗ₜ x) = g (c ⊗ₜ x))
    (y : L ⊗[ℤ] M) : f y = g y := by
  induction y using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul c x => exact h c x

end Generic

section BaseChange

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (q : ℕ)

/-- The comparison `Extᵠ(Λ ⊗ ℤ_X, N) ⟶ Hᵠ(X, N)` is bijective. -/
lemma bijective_extToSheafHOf_unitIntToExtendScalars
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (extToSheafHOf Λ (unitIntToExtendScalars Λ X) N q) :=
  bijective_extToSheafHOf Λ _ (bijective_unitIntToExtendScalars_comp Λ X) q N

/-- The maps comparing `Hᵠ(X, μₙ)` with `Extᵠ(Λ_X, μₙ ⊗ Λ)`, bundled so that they are constructed
in a single definition (see `extExtendScalarsIntAddEquiv`, `kummerCoefficientMap` and
`kummerCoefficientTensorMap`). -/
structure KummerCoefficientMaps where
  /-- `Extᵠ(Λ ⊗ ℤ_X, N) ≅ Hᵠ(X, N)`. -/
  addEquiv (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Abelian.Ext.{u + 1} ((extendScalars Λ X).obj X.constantSheafInt) N q ≃+
      Sheaf.H ((forget₂Sheaf Λ X).obj N) q
  /-- `Hᵠ(X, μₙ) ⟶ Extᵠ(Λ_X, μₙ ⊗ Λ)`. -/
  map : Sheaf.H (X.rootsOfUnitySheaf (ringChar Λ)) q →+
      Abelian.Ext.{u + 1} ((extendScalars Λ X).obj X.constantSheafInt)
        ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))) q
  /-- `Λ ⊗ Hᵠ(X, μₙ) ⟶ Extᵠ(Λ_X, μₙ ⊗ Λ)`. -/
  tensorMap : Λ ⊗[ℤ] Sheaf.H (X.rootsOfUnitySheaf (ringChar Λ)) q →+
      Abelian.Ext.{u + 1} ((extendScalars Λ X).obj X.constantSheafInt)
        ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))) q

/-- The comparison maps of `KummerCoefficientMaps`. -/
noncomputable def kummerCoefficientMaps : KummerCoefficientMaps Λ X q :=
  let e (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      Abelian.Ext.{u + 1} ((extendScalars Λ X).obj X.constantSheafInt) N q ≃+
        Sheaf.H ((forget₂Sheaf Λ X).obj N) q :=
    AddEquiv.ofBijectiveAddMonoidHom _ (bijective_extToSheafHOf_unitIntToExtendScalars Λ X q N)
  let m : Sheaf.H (X.rootsOfUnitySheaf (ringChar Λ)) q →+
      Abelian.Ext.{u + 1} ((extendScalars Λ X).obj X.constantSheafInt)
        ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))) q :=
    (e _).symmComp (Sheaf.H.map (F := X.rootsOfUnitySheaf (ringChar Λ))
      ((extendScalarsAdjunction Λ X).unit.app (X.rootsOfUnitySheaf (ringChar Λ))) q)
  { addEquiv := e
    map := m
    tensorMap := TensorProduct.liftSMulAddHom Λ m }

/-- `Extᵠ(Λ ⊗ ℤ_X, N) ≅ Hᵠ(X, N)` on a quasi-compact quasi-separated scheme. -/
noncomputable def extExtendScalarsIntAddEquiv
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Abelian.Ext.{u + 1} ((extendScalars Λ X).obj X.constantSheafInt) N q ≃+
      Sheaf.H ((forget₂Sheaf Λ X).obj N) q :=
  (kummerCoefficientMaps Λ X q).addEquiv N

/-- The coefficient extension `Hᵠ(X, μₙ) ⟶ Hᵠ(X, μₙ ⊗ Λ) = Extᵠ(Λ_X, μₙ ⊗ Λ)` induced by
`μₙ ⟶ μₙ ⊗ Λ`, `n` the characteristic of `Λ`. -/
noncomputable def kummerCoefficientMap :
    Sheaf.H (X.rootsOfUnitySheaf (ringChar Λ)) q →+
      Abelian.Ext.{u + 1} ((extendScalars Λ X).obj X.constantSheafInt)
        ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))) q :=
  (kummerCoefficientMaps Λ X q).map

private lemma kummerCoefficientMap_eq : kummerCoefficientMap Λ X q =
    (extExtendScalarsIntAddEquiv Λ X q _).symmComp
      (Sheaf.H.map (F := X.rootsOfUnitySheaf (ringChar Λ))
      ((extendScalarsAdjunction Λ X).unit.app (X.rootsOfUnitySheaf (ringChar Λ))) q) :=
  rfl

/-- The natural map `Λ ⊗ Hᵠ(X, μₙ) ⟶ Hᵠ(X, μₙ ⊗ Λ)`, `c ⊗ x ↦ c • x`. -/
noncomputable def kummerCoefficientTensorMap :
    Λ ⊗[ℤ] Sheaf.H (X.rootsOfUnitySheaf (ringChar Λ)) q →+
      Abelian.Ext.{u + 1} ((extendScalars Λ X).obj X.constantSheafInt)
        ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))) q :=
  (kummerCoefficientMaps Λ X q).tensorMap

private lemma kummerCoefficientTensorMap_eq :
    kummerCoefficientTensorMap Λ X q =
      TensorProduct.liftSMulAddHom Λ (kummerCoefficientMap Λ X q) :=
  rfl

@[simp]
lemma kummerCoefficientTensorMap_tmul (c : Λ) (x : Sheaf.H (X.rootsOfUnitySheaf (ringChar Λ)) q) :
    kummerCoefficientTensorMap Λ X q (c ⊗ₜ x) = c • kummerCoefficientMap Λ X q x := by
  rw [kummerCoefficientTensorMap_eq]
  exact TensorProduct.liftSMulAddHom_tmul Λ _ c x

lemma extExtendScalarsIntAddEquiv_smul (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (c : Λ)
    (y : Abelian.Ext.{u + 1} ((extendScalars Λ X).obj X.constantSheafInt) N q) :
    extExtendScalarsIntAddEquiv Λ X q N (c • y) =
      Sheaf.H.map ((forget₂Sheaf Λ X).map (c • 𝟙 N)) q (extExtendScalarsIntAddEquiv Λ X q N y) := by
  rw [Abelian.Ext.smul_eq_comp_mk₀]
  exact extToSheafHOf_comp_mk₀ Λ _ _ q y

lemma extExtendScalarsIntAddEquiv_kummerCoefficientMap
    (x : Sheaf.H (X.rootsOfUnitySheaf (ringChar Λ)) q) :
    extExtendScalarsIntAddEquiv Λ X q _ (kummerCoefficientMap Λ X q x) =
      Sheaf.H.map ((extendScalarsAdjunction Λ X).unit.app _) q x := by
  rw [kummerCoefficientMap_eq]
  exact AddEquiv.apply_symmComp _ _ x

end BaseChange

section Constant

variable {X : Scheme.{u}} (n : ℕ) (ζ : X.constantZMod n ≅ X.rootsOfUnitySheaf n)

/-- The underlying abelian sheaf of `μₙ ⊗ Λ`, trivialized by `ζ : ℤ/n ≅ μₙ`, is the constant
sheaf on `Λ ⊗ ℤ/n`. -/
noncomputable def forget₂ExtendScalarsRootsOfUnityIso :
    (forget₂Sheaf Λ X).obj ((extendScalars Λ X).obj (X.rootsOfUnitySheaf n)) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
          ((ModuleCat.extendScalarsAddCommGrp Λ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))) :=
  (forget₂Sheaf Λ X).mapIso ((extendScalars Λ X).mapIso ζ.symm ≪≫
    (constantSheafCompExtendScalarsIso Λ X).app _) ≪≫
    (constantSheafSheafComposeForget₂Iso Λ).app _

lemma unit_comp_smul_comp_forget₂ExtendScalarsRootsOfUnityIso (c : Λ) :
    (extendScalarsAdjunction Λ X).unit.app (X.rootsOfUnitySheaf n) ≫
      (forget₂Sheaf Λ X).map (c • 𝟙 _) ≫ (forget₂ExtendScalarsRootsOfUnityIso Λ n ζ).hom =
    ζ.inv ≫ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((ModuleCat.extendScalarsAddCommGrpAdj Λ).unit.app _ ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map (c • 𝟙 _)) := by
  have h1 {A B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : A ⟶ B) :
      (forget₂Sheaf Λ X).map (c • 𝟙 A) ≫ (forget₂Sheaf Λ X).map g =
        (forget₂Sheaf Λ X).map g ≫ (forget₂Sheaf Λ X).map (c • 𝟙 B) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]
  let W := (ModuleCat.extendScalarsAddCommGrp Λ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))
  have h4 : (forget₂Sheaf Λ X).map (c • 𝟙 ((constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj W)) ≫ (constantSheafSheafComposeForget₂Iso Λ).hom.app W =
        (constantSheafSheafComposeForget₂Iso Λ).hom.app W ≫
          (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
            ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map (c • 𝟙 W)) := by
    rw [show c • 𝟙 ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj W) =
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map (c • 𝟙 W) by
        rw [Functor.map_smul, CategoryTheory.Functor.map_id]]
    exact (constantSheafSheafComposeForget₂Iso Λ).hom.naturality (c • 𝟙 W)
  have hK := unit_comp_constantSheafCompExtendScalarsIso Λ X
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))
  have h2 := (extendScalarsAdjunction Λ X).unit.naturality ζ.inv
  simp only [forget₂ExtendScalarsRootsOfUnityIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc, Iso.symm_hom]
  rw [reassoc_of% (h1 ((extendScalars Λ X).map ζ.inv)),
    reassoc_of% (h1 ((constantSheafCompExtendScalarsIso Λ X).hom.app _)), h4]
  erw [← reassoc_of% h2]
  rw [reassoc_of% hK]

end Constant

section Main

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (q : ℕ)
  {k : Type u} [Field k] [IsAlgClosed k]

/-- **Base change of the Kummer coefficients.** If `Λ` is free over `ℤ/n`, `n` its characteristic
invertible in the algebraically closed field `k`, then `Λ ⊗ Hᵠ(X, μₙ) ⟶ Hᵠ(X, μₙ ⊗ Λ)` is
bijective for every quasi-compact quasi-separated `k`-scheme `X`. -/
theorem bijective_kummerCoefficientTensorMap (f : X ⟶ Spec (.of k))
    [HasInvertibleExponent Λ (Spec (.of k))] {r : ℕ} (e : Λ ≃+ (Fin r → ZMod (ringChar Λ))) :
    Function.Bijective (kummerCoefficientTensorMap Λ X q) := by
  have hN : ((ringChar Λ : ℕ) : k) ≠ 0 := by
    have h := (isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ) (Spec (.of k))).map
      (Scheme.ΓSpecIso (.of k)).hom.hom
    rw [map_natCast] at h
    exact h.ne_zero
  let ζ := (AffineSpace.nonempty_constantZModIsoRootsOfUnitySheaf f hN).some
  let Z := AddCommGrpCat.of (ULift.{u + 1} (ZMod (ringChar Λ)))
  let W := (ModuleCat.extendScalarsAddCommGrp Λ).obj Z
  let ιW : W ≅ ModuleCat.of Λ Λ :=
    ModuleCat.extendScalarsAddCommGrpZModIso ringChar.Nat.cast_ringChar
  let ψ : Λ →+ (Z ⟶ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj W) :=
    { toFun c := (ModuleCat.extendScalarsAddCommGrpAdj Λ).unit.app Z ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map (c • 𝟙 W)
      map_zero' := by rw [zero_smul, Functor.map_zero, Limits.comp_zero]
      map_add' c d := by rw [add_smul, Functor.map_add, Preadditive.comp_add] }
  have hψ : Function.Bijective ψ := by
    have : (ψ : Λ → _) = ((ModuleCat.extendScalarsAddCommGrpAdj Λ).homEquiv Z W) ∘
        (fun c ↦ c • 𝟙 W) := by
      funext c
      rw [Function.comp_apply, Adjunction.homEquiv_unit]
      rfl
    rw [this]
    exact (Equiv.bijective _).comp (bijective_smul_id_of_iso Λ ιW)
  let κ : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj W ≅
      ⨁ fun _ : Fin r ↦ Z :=
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso ιW ≪≫
      (e.trans (AddEquiv.piCongrRight fun _ ↦ AddEquiv.ulift.symm)).toAddCommGrpIso ≪≫
        (AddCommGrpCat.biproductIsoPi _).symm
  let F := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    Sheaf.functorH X.smallEtaleTopology q
  have hT := F.bijective_tensorMapOf ψ hψ κ (exists_eq_zsmul_id_zmod (ringChar Λ))
  let τ := forget₂ExtendScalarsRootsOfUnityIso Λ (ringChar Λ) ζ
  let Hζ : Sheaf.H (X.rootsOfUnitySheaf (ringChar Λ)) q ≃+ F.obj Z :=
    ((Sheaf.functorH _ q).mapIso ζ.symm).addCommGroupIsoToAddEquiv
  let Hτ := ((Sheaf.functorH _ q).mapIso τ).addCommGroupIsoToAddEquiv
  let C : Λ ⊗[ℤ] Sheaf.H (X.rootsOfUnitySheaf (ringChar Λ)) q ≃ₗ[ℤ] Λ ⊗[ℤ] F.obj Z :=
    TensorProduct.congr (LinearEquiv.refl ℤ Λ) Hζ.toIntLinearEquiv
  have hcomp : ∀ y, Hτ (extExtendScalarsIntAddEquiv Λ X q _ (kummerCoefficientTensorMap Λ X q y)) =
      F.tensorMapOf ψ (C y) :=
    tensorAddHom_apply_eq_of_tmul
      (Hτ.toAddMonoidHom.comp ((extExtendScalarsIntAddEquiv Λ X q _).toAddMonoidHom.comp
        (kummerCoefficientTensorMap Λ X q)))
      ((F.tensorMapOf ψ).comp C.toLinearMap.toAddMonoidHom) fun c x ↦ by
      change Hτ (extExtendScalarsIntAddEquiv Λ X q _ (kummerCoefficientTensorMap Λ X q (c ⊗ₜ x))) =
        F.tensorMapOf ψ (C (c ⊗ₜ x))
      rw [kummerCoefficientTensorMap_tmul, extExtendScalarsIntAddEquiv_smul,
        extExtendScalarsIntAddEquiv_kummerCoefficientMap]
      change Sheaf.H.map τ.hom q (Sheaf.H.map _ q (Sheaf.H.map _ q x)) =
        F.tensorMapOf ψ (c ⊗ₜ Sheaf.H.map ζ.inv q x)
      rw [Functor.tensorMapOf_tmul, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
      erw [unit_comp_smul_comp_forget₂ExtendScalarsRootsOfUnityIso]
      rw [Sheaf.H.map_comp_apply]
      rfl
  have : (kummerCoefficientTensorMap Λ X q : _ → _) =
      (extExtendScalarsIntAddEquiv Λ X q _).symm ∘ Hτ.symm ∘ F.tensorMapOf ψ ∘ C := by
    funext y
    simp only [Function.comp_apply, ← hcomp, AddEquiv.symm_apply_apply]
  rw [this]
  exact (AddEquiv.bijective _).comp ((AddEquiv.bijective _).comp (hT.comp C.bijective))

/-- Blueprint `lem-pur-kummer-coefficient-base-change`: Base change of the Kummer coefficients.

Let `k` be an algebraically closed field, `Λ` a finite coefficient ring of characteristic `n`
invertible in `k` which is free over `ℤ/n` (the blueprint's `A`, free over `ℤ/ℓᴺ`), and `X` a
quasi-compact quasi-separated `k`-scheme, for instance a smooth separated curve. Then for every
`q` the natural map

`Λ ⊗ Hᵠ(X, μₙ) ⟶ Hᵠ(X, μₙ ⊗ Λ) = Extᵠ(Λ_X, μₙ ⊗ Λ)`

(`AlgebraicGeometry.Etale.kummerCoefficientTensorMap`) is bijective, and it is compatible with
the Kummer boundary maps: the Kummer class `κ(u) : Λ_X ⟶ Λ_X(1)[1]` with coefficients in `Λ`
(`AlgebraicGeometry.Etale.kummerClassOf`) is the image of `1 ⊗ δ(u)`, `δ(u) ∈ H¹(X, μₙ)` the
boundary of `u` in the Kummer sequence. -/
theorem kummer_coefficient_base_change (f : X ⟶ Spec (.of k))
    [HasInvertibleExponent Λ (Spec (.of k))] [HasInvertibleExponent Λ X] [NeZero (ringChar Λ)]
    {r : ℕ} (e : Λ ≃+ (Fin r → ZMod (ringChar Λ))) :
    (∀ q : ℕ, Function.Bijective (kummerCoefficientTensorMap Λ X q)) ∧
      ∀ u : Γ(X, ⊤)ˣ, kummerClassOf X Λ u =
        (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
          Abelian.Ext.homAddEquiv (kummerCoefficientTensorMap Λ X 1
            (1 ⊗ₜ X.kummerδ₀ (ringChar Λ) (isUnit_ringChar_of_hasInvertibleExponent X)
              (Additive.ofMul u))) ≫
          (tateTwistObjectOneIso X Λ).inv⟦(1 : ℤ)⟧' := by
  refine ⟨fun q ↦ bijective_kummerCoefficientTensorMap Λ X q f e, fun u ↦ ?_⟩
  rw [kummerCoefficientTensorMap_tmul, one_smul]
  exact kummerClassOf_eq_extToSheafHOf_symm Λ X u

end Main

end AlgebraicGeometry.Etale

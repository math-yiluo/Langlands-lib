/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Functor
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme
private noncomputable def kernelPower {C : Type w} [Category.{v} C] [Abelian C]
    (G : C) (m k : ℕ) : kernel ((m * k) • 𝟙 G) ⟶ kernel (m • 𝟙 G) :=
  kernel.lift _ (k • kernel.ι ((m * k) • 𝟙 G)) (by
    rw [Preadditive.nsmul_comp, ← Preadditive.comp_nsmul, smul_smul]
    simpa only [mul_comm] using kernel.condition ((m * k) • 𝟙 G))

private lemma kernelPower_ι {C : Type w} [Category.{v} C] [Abelian C]
    (G : C) (m k : ℕ) :
    kernelPower G m k ≫ kernel.ι (m • 𝟙 G) =
      k • kernel.ι ((m * k) • 𝟙 G) := by
  exact kernel.lift_ι _ _ _

private lemma kernelPower_epi {C : Type w} [Category.{v} C] [Abelian C]
    (G : C) (m k : ℕ) [Epi (k • 𝟙 G)] : Epi (kernelPower G m k) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro Y y
  obtain ⟨Y', π, hπ, x, hx⟩ :=
    surjective_up_to_refinements_of_epi (k • 𝟙 G) (y ≫ kernel.ι (m • 𝟙 G))
  have hx' : x ≫ ((m * k) • 𝟙 G) = 0 := by
    calc
      x ≫ ((m * k) • 𝟙 G) = (x ≫ (k • 𝟙 G)) ≫ (m • 𝟙 G) := by
        simp only [Preadditive.comp_nsmul, Category.comp_id, smul_smul]
      _ = (π ≫ y ≫ kernel.ι (m • 𝟙 G)) ≫ (m • 𝟙 G) := by rw [hx]
      _ = 0 := by simp only [Category.assoc, kernel.condition, comp_zero]
  refine ⟨Y', π, hπ, kernel.lift _ x hx', ?_⟩
  apply (cancel_mono (kernel.ι (m • 𝟙 G))).mp
  rw [Category.assoc (kernel.lift _ x hx') (kernelPower G m k),
    kernelPower_ι, Preadditive.comp_nsmul, kernel.lift_ι]
  simpa only [Preadditive.comp_nsmul, Category.comp_id, Category.assoc] using hx

private lemma kernelPower_cokernel {C : Type w} [Category.{v} C] [Abelian C]
    (G : C) (m k : ℕ) [Epi (m • 𝟙 G)] [Epi (k • 𝟙 G)] :
    ∃ h : (m • 𝟙 (kernel ((m * k) • 𝟙 G))) ≫ kernelPower G m k = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (kernelPower G m k) h)) := by
  have h : (m • 𝟙 (kernel ((m * k) • 𝟙 G))) ≫ kernelPower G m k = 0 := by
    apply (cancel_mono (kernel.ι (m • 𝟙 G))).mp
    rw [Category.assoc, kernelPower_ι, Preadditive.nsmul_comp, Category.id_comp,
      smul_smul, zero_comp]
    simpa only [Preadditive.comp_nsmul, Category.comp_id] using
      kernel.condition ((m * k) • 𝟙 G)
  let S := ShortComplex.mk (m • 𝟙 (kernel ((m * k) • 𝟙 G))) (kernelPower G m k) h
  have he : S.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro Y x hx
    obtain ⟨Y', π, hπ, z, hz⟩ :=
      surjective_up_to_refinements_of_epi (m • 𝟙 G)
        (x ≫ kernel.ι ((m * k) • 𝟙 G))
    have hz' : z ≫ ((m * k) • 𝟙 G) = 0 := by
      calc
        z ≫ ((m * k) • 𝟙 G) = (z ≫ (m • 𝟙 G)) ≫ (k • 𝟙 G) := by
          simp only [Preadditive.comp_nsmul, Category.comp_id,
          smul_smul, mul_comm]
        _ = (π ≫ x ≫ kernel.ι ((m * k) • 𝟙 G)) ≫ (k • 𝟙 G) := by rw [hz]
        _ = π ≫ (x ≫ kernelPower G m k) ≫ kernel.ι (m • 𝟙 G) := by
          rw [Category.assoc, Category.assoc, Preadditive.comp_nsmul,
            Category.comp_id, ← kernelPower_ι]
          simp only [Category.assoc]
        _ = 0 := by change π ≫ (x ≫ S.g) ≫ _ = 0; rw [hx, zero_comp, comp_zero]
    refine ⟨Y', π, hπ, kernel.lift _ z hz', ?_⟩
    apply (cancel_mono (kernel.ι ((m * k) • 𝟙 G))).mp
    change (π ≫ x) ≫ kernel.ι ((m * k) • 𝟙 G) =
      (kernel.lift _ z hz' ≫ (m • 𝟙 _)) ≫ kernel.ι ((m * k) • 𝟙 G)
    simpa only [Preadditive.comp_nsmul, Category.comp_id,
      Preadditive.nsmul_comp, kernel.lift_ι, Category.assoc] using hz
  have : Epi S.g := kernelPower_epi G m k
  exact ⟨h, ⟨he.gIsCokernel⟩⟩

private lemma finiteEtaleGenerator_smul (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) (W : T.Etaleᵒᵖ)
    (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    finiteEtaleTateOneGenerator A N T hA W a z =
      a • finiteEtaleTateOneGenerator A N T hA W 1 z := by
  unfold finiteEtaleTateOneGenerator
  let f := (toSheafify T.smallEtaleTopology
    (finiteEtaleMuModulePresheaf T N ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA))).app W
  exact (congrArg f (by
    simpa only [mul_one] using
      (ModuleCat.ExtendScalars.smul_tmul (finiteEtaleTwistScalar N A hA)
        (M := finiteEtaleMuModuleObj T N W) a 1 z).symm)).trans
    (f.hom.map_smul a _)

private noncomputable def muHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleMuModulePresheaf T N ⟶
      P.obj ⋙ ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) where
  toFun f := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom (f.app U).hom.toAddMonoidHom
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.naturality g) x }⟩
  invFun f := {
    app := fun U ↦ ModuleCat.ofHom
      (X := finiteEtaleMuModuleObj T N U)
      (Y := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
      (AddMonoidHom.toZModLinearMap N
        (M := finiteEtaleMuModuleObj T N U)
        (M₁ := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
        (f.hom.app U).hom)
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

private noncomputable def lineHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleTateLine T N A hA ⟶ P) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) :=
  ((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ P).trans
    ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).whiskerRight
      T.Etaleᵒᵖ).homEquiv _ P.obj).trans (muHomEquiv T N A hA P))

private lemma lineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : finiteEtaleTateLine T N A hA ⟶ P) (U : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf N).obj.obj U) :
    (lineHomEquiv T N A hA P f).hom.app U z =
      f.hom.app U (finiteEtaleTateOneGenerator A N T hA U 1 z) := by
  dsimp [lineHomEquiv, muHomEquiv]
  change ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).homEquiv _ _
        ((toSheafify T.smallEtaleTopology _ ≫ f.hom).app U)) z = _
  rfl

private lemma lineHomEquiv_comp (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    {P Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : finiteEtaleTateLine T N A hA ⟶ P) (g : P ⟶ Q) :
    lineHomEquiv T N A hA Q (f ≫ g) =
      lineHomEquiv T N A hA P f ≫
        (sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map g := by
  ext U z
  change g.hom.app U (f.hom.app U
    (finiteEtaleTateOneGenerator A N T hA U 1 z)) =
    g.hom.app U ((lineHomEquiv T N A hA P f).hom.app U z)
  rw [lineHomEquiv_generator]
private lemma lineMap_isIso (T : Scheme.{u}) (m m' : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (hA' : (m' : A) = 0)
    (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
    (hq : (m • 𝟙 (T.rootsOfUnitySheaf m')) ≫ q = 0)
    (hc : IsColimit (CokernelCofork.ofπ q hq)) :
    let η := lineHomEquiv T m A hA (finiteEtaleTateLine T m A hA) (𝟙 _)
    IsIso ((lineHomEquiv T m' A hA' (finiteEtaleTateLine T m A hA)).symm (q ≫ η)) := by
  intro η
  let f := (lineHomEquiv T m' A hA' (finiteEtaleTateLine T m A hA)).symm (q ≫ η)
  have : Epi q := epi_of_isColimit_cofork hc
  have hf {P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
      (g : finiteEtaleTateLine T m A hA ⟶ P) :
      lineHomEquiv T m' A hA' P (f ≫ g) = q ≫ lineHomEquiv T m A hA P g := by
    rw [lineHomEquiv_comp]
    dsimp only [f]
    rw [Equiv.apply_symm_apply, Category.assoc]
    exact congrArg (fun z ↦ q ≫ z) (by
      simpa only [Category.id_comp] using
        (lineHomEquiv_comp T m A hA (𝟙 _) g).symm)
  apply isIso_of_coyoneda_map_bijective
  intro P
  constructor
  · intro g g' h
    apply (lineHomEquiv T m A hA P).injective
    apply (cancel_epi q).mp
    rw [← hf, ← hf]
    exact congrArg (lineHomEquiv T m' A hA' P) h
  · intro g
    let z := lineHomEquiv T m' A hA' P g
    have hz : (m • 𝟙 (T.rootsOfUnitySheaf m')) ≫ z = 0 := by
      ext U x
      change z.hom.app U (m • x) = 0
      rw [_root_.map_nsmul]
      change m • (show P.obj.obj U from z.hom.app U x) = 0
      rw [← Nat.cast_smul_eq_nsmul A, hA, zero_smul]
    let z' := hc.desc (CokernelCofork.ofπ z hz)
    refine ⟨(lineHomEquiv T m A hA P).symm z', ?_⟩
    apply (lineHomEquiv T m' A hA' P).injective
    rw [hf, Equiv.apply_symm_apply]
    exact hc.fac (CokernelCofork.ofπ z hz) WalkingParallelPair.one

private noncomputable def positiveIso (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m m' : ℕ) (hA : (m : A) = 0) (hA' : (m' : A) = 0)
    (e : finiteEtaleTateLine T m' A hA' ≅ finiteEtaleTateLine T m A hA) :
    ∀ n : ℕ, finiteEtaleTateTwist T m' A hA' n ≅ finiteEtaleTateTwist T m A hA n
  | 0 => Iso.refl _
  | 1 => e
  | n + 2 => tensorIso (positiveIso T A m m' hA hA' e (n + 1)) e

private noncomputable def signedIso (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m m' : ℕ) (hA : (m : A) = 0) (hA' : (m' : A) = 0)
    (e : finiteEtaleTateLine T m' A hA' ≅ finiteEtaleTateLine T m A hA) :
    ∀ a : ℤ, finiteEtaleTateSheaf A m' T hA' a ≅ finiteEtaleTateSheaf A m T hA a
  | .ofNat n => positiveIso T A m m' hA hA' e n
  | .negSucc n =>
    asIso ((MonoidalClosed.pre (positiveIso T A m m' hA hA' e (n + 1)).inv).app
      (finiteEtaleTateTwist T m A hA 0))

private lemma signedIso_eval (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (m m' : ℕ) (hA : (m : A) = 0) (hA' : (m' : A) = 0)
    (e : finiteEtaleTateLine T m' A hA' ≅ finiteEtaleTateLine T m A hA) (n : ℕ) :
    tensorHom (signedIso T A m m' hA hA' e (.ofNat (n + 1))).hom
        (signedIso T A m m' hA hA' e (.negSucc n)).hom ≫
      (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
        (finiteEtaleTateSheaf A m T hA 0) =
      (ihom.ev (finiteEtaleTateSheaf A m' T hA' (.ofNat (n + 1)))).app
        (finiteEtaleTateSheaf A m' T hA' 0) := by
  change tensorHom (positiveIso T A m m' hA hA' e (n + 1)).hom
      ((MonoidalClosed.pre (positiveIso T A m m' hA hA' e (n + 1)).inv).app
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A))) ≫
      (ihom.ev (finiteEtaleTateTwist T m A hA (n + 1))).app
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)) =
      (ihom.ev (finiteEtaleTateTwist T m' A hA' (n + 1))).app
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A))
  rw [MonoidalCategory.tensorHom_def, Category.assoc, MonoidalClosed.id_tensor_pre_app_comp_ev]
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

/-! Remaining coherence package for finite Tate pullback.
(auxiliary; not a blueprint node). -/
/-- Derived tensor/shift comparison and change of annihilating exponent for finite Tate
sheaves. Source: Stacks Project, Tags 03PK, 07A4 and 0G7E.

Proof: compose the existing derived monoidal comparison with the degree-zero pullback
comparison and commute pullback past the shift. For exponent change write `m' = m * k`.
Kummer exactness makes multiplication by both `m` and `k` on the multiplicative-group
sheaf epimorphic. The induced map `ker(m*k) → ker(m)` is the cokernel of multiplication
by `m` on `ker(m*k)`, as one checks by lifting along those epimorphisms. Maps from the
coefficient root line to an `A`-module sheaf are exactly additive maps from roots of unity
to the underlying abelian sheaf. Since `mA = 0`, every such map factors uniquely through
that cokernel. Thus the exponent map induces an isomorphism on coefficient lines. Its
formula on pure generators follows from the scalar-extension adjunction. Tensor powers
extend it to positive degrees; precomposition with its inverse extends it to duals.
Naturality of evaluation gives the final equation.
(auxiliary; not a blueprint node). -/
theorem etaleFiniteTwistPullback_rest (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0)
    (r : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) →
        ((Etale.upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf m) ≅
          T'.rootsOfUnitySheaf m))
    (c : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) → IsUnit (m : Γ(T', ⊤)) → ∀ a : ℤ,
        (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateSheaf A m T hA a) ≅
          finiteEtaleTateSheaf A m T' hA a)
    (p : ∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) → ∀ a b : ℤ,
        finiteEtaleTateSheaf A m T hA a ⊗ finiteEtaleTateSheaf A m T hA b ≅
          finiteEtaleTateSheaf A m T hA (a + b)) :
        (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      ∃ d : ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) T
          ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ⋙
          shiftFunctor _ b) ⋙ (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ≅
        (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ⋙
          Etale.derivedTensorRight (ModuleCat.{u + 1} A) T'
            ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T' hA a)) ⋙
              shiftFunctor _ b),
        ∀ K : Etale.DerivedCategoryModule A T,
          d.app K =
            ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.commShiftIso b).app
              (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a))) ≪≫
            (shiftFunctor _ b).mapIso
              (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v K
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ≪≫
              ((Etale.derivedTensor (ModuleCat.{u + 1} A) T').obj
                ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K)).mapIso
                ((Etale.singleFunctorCompLeftDerivedUpperStarIso
                  (ModuleCat.{u + 1} A) v).app (finiteEtaleTateSheaf A m T hA a) ≪≫
                (DerivedCategory.singleFunctor _ 0).mapIso (c v hT hT' a)))) ∧
    (∀ (m' : ℕ), 0 < m' → ∀ (hdiv : m ∣ m')
        (T : Scheme.{u}),
      IsUnit (m' : Γ(T, ⊤)) →
      ∃ (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
        (t : ∀ a : ℤ, finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) a ≅
          finiteEtaleTateSheaf A m T hA a),
      q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf) ∧
      (∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m').obj.obj W),
        (t 1).hom.hom.app W (finiteEtaleTateOneGenerator A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) W a z) =
          finiteEtaleTateOneGenerator A m T hA W a (q.hom.app W z)) ∧
      t 0 = Iso.refl _ ∧
      (∀ n : ℕ, t (.ofNat (n + 2)) =
        tensorIso (t (.ofNat (n + 1))) (t 1)) ∧
      (∀ n : ℕ,
        tensorHom (t (.ofNat (n + 1))).hom (t (.negSucc n)).hom ≫
            (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
              (finiteEtaleTateSheaf A m T hA 0) =
          (ihom.ev (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv))
            (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) 0))) := by
  classical
  have _ := @r
  have _ := p
  clear r p
  constructor
  · intro T T' v hT hT' a b
    let F := (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor
    let M := (DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)
    let e : F.obj M ≅ (DerivedCategory.singleFunctor _ 0).obj
        (finiteEtaleTateSheaf A m T' hA a) :=
      (Etale.singleFunctorCompLeftDerivedUpperStarIso
      (ModuleCat.{u + 1} A) v).app (finiteEtaleTateSheaf A m T hA a) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (c v hT hT' a)
    let e₂ : Etale.derivedTensorRight (ModuleCat.{u + 1} A) T' (F.obj M) ≅
        Etale.derivedTensorRight (ModuleCat.{u + 1} A) T'
          ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T' hA a)) :=
      (Etale.derivedTensorRightFunctor (ModuleCat.{u + 1} A) T').mapIso e
    let d := Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (Etale.derivedTensorRight (ModuleCat.{u + 1} A) T M)
        (F.commShiftIso b) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight
        (Etale.derivedTensorRightCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v M)
        (shiftFunctor _ b) ≪≫
      isoWhiskerRight
        (isoWhiskerLeft F e₂)
        (shiftFunctor _ b) ≪≫
      Functor.associator _ _ _
    refine ⟨d, fun K ↦ ?_⟩
    apply Iso.ext
    dsimp only [d]
    simp only [Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Category.id_comp,
      Category.comp_id, Functor.mapIso_hom, Functor.map_comp]
    erw [Category.id_comp]
    change (F.commShiftIso b).hom.app (((Etale.derivedTensor
      (ModuleCat.{u + 1} A) T).obj K).obj M) ≫
      (shiftFunctor _ b).map (Etale.leftDerivedUpperStarTensorIso
        (ModuleCat.{u + 1} A) v K M).hom ≫
      (shiftFunctor _ b).map (((Etale.derivedTensor (ModuleCat.{u + 1} A) T').obj
        (F.obj K)).map e.hom) = _
    simp only [e, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
    rfl
  · intro m' hm' hdiv T hT
    obtain ⟨k, rfl⟩ := hdiv
    have hmk : IsUnit ((m : Γ(T, ⊤)) * (k : Γ(T, ⊤))) := by
      simpa only [Nat.cast_mul] using hT
    have : Epi (m • 𝟙 T.gmSheaf) :=
      (T.kummerSequence_shortExact m (isUnit_of_mul_isUnit_left hmk)).epi_g
    have : Epi (k • 𝟙 T.gmSheaf) :=
      (T.kummerSequence_shortExact k (isUnit_of_mul_isUnit_right hmk)).epi_g
    obtain ⟨hq, ⟨hc⟩⟩ := kernelPower_cokernel T.gmSheaf m k
    let q : T.rootsOfUnitySheaf (m * k) ⟶ T.rootsOfUnitySheaf m :=
      kernelPower T.gmSheaf m k
    let hA' : ((m * k : ℕ) : A) = 0 := by simp only [Nat.cast_mul, hA, zero_mul]
    let η := lineHomEquiv T m A hA (finiteEtaleTateLine T m A hA) (𝟙 _)
    let f := (lineHomEquiv T (m * k) A hA'
      (finiteEtaleTateLine T m A hA)).symm (q ≫ η)
    have : IsIso f := lineMap_isIso T m (m * k) A hA hA' q hq hc
    let e := asIso f
    refine ⟨q, signedIso T A m (m * k) hA hA' e, ?_, ?_, rfl, ?_, ?_⟩
    · simpa only [Nat.mul_div_right _ hm] using kernelPower_ι T.gmSheaf m k
    · intro W a z
      have he : f.hom.app W (finiteEtaleTateOneGenerator A (m * k) T hA' W 1 z) =
          finiteEtaleTateOneGenerator A m T hA W 1 (q.hom.app W z) := by
        have h := congrArg (fun g ↦ g.hom.app W z)
          ((lineHomEquiv T (m * k) A hA' _).apply_symm_apply (q ≫ η))
        rw [lineHomEquiv_generator] at h
        exact h.trans (lineHomEquiv_generator T m A hA _ (𝟙 _) W (q.hom.app W z))
      change f.hom.app W (finiteEtaleTateOneGenerator A (m * k) T hA' W a z) = _
      rw [finiteEtaleGenerator_smul, _root_.map_smul, he]
      exact (finiteEtaleGenerator_smul T m A hA W a (q.hom.app W z)).symm
    · intro n
      rfl
    · intro n
      exact signedIso_eval T A m (m * k) hA hA' e n

end AlgebraicGeometry.Scheme

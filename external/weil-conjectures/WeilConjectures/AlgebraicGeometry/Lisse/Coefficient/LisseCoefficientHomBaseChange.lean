/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.LinearAlgebra.Span.Basic
import WeilConjectures.NumberTheory.Padics.LocalFieldCoefficientStages
import WeilConjectures.AlgebraicGeometry.Lisse.LisseRationalScalarFiberMaps
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Quotient

/-! Finite coefficient descent of lisse rational sheaves.

## References

* Deligne, Weil II (1.1.1) d), pp. 146-147, the displayed Hom base-change formula
-/

@[expose] public section
set_option autoImplicit false
universe d
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

noncomputable section

private theorem restrictionLeftAdjoint
    {A B : Type (d + 1)} [Ring A] [Ring B] (f : A →+* B) :
    (ModuleCat.restrictScalars.{d + 1} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{d + 1, d + 1, d + 1} f).isLeftAdjoint

attribute [local instance] restrictionLeftAdjoint

private theorem integerExtension_free
    (E L : Type (d + 1)) [Field E] [Field L]
    [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :
    letI := (lisseIntegerInclusion l E L ι).toAlgebra
    Module.Free (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) ∧
    Module.Finite (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L) := by
  let := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] E L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ι.commutes r).symm
  have hc (x : E) : Padic.coefficientExtensionAbsoluteValue l L (algebraMap E L x) =
      Padic.coefficientExtensionAbsoluteValue l E x := by
    change spectralNorm ℚ_[l] L (ι x) = spectralNorm ℚ_[l] E x
    unfold spectralNorm
    rw [minpoly.algHom_eq ι ι.injective]
  obtain ⟨f, hf, hfree, hfinite, _⟩ := Padic.local_field_coefficient_stages l E L hc
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l L)
    (lisseCoherence_uniformizerIdeal_eq l E) (lisseCoherence_uniformizerIdeal_eq l L)
  have heq : f = lisseIntegerInclusion l E L ι := by
    ext x
    exact (hf x).trans ((lisseIntegerInclusion_exists l E L ι).choose_spec x).symm
  subst f
  exact ⟨hfree, hfinite⟩

section QuotientCoordinates

variable {R S : Type (d + 1)} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type}

private def quotientBasis (b : Module.Basis ι R S) (I : Ideal R) :
    Module.Basis ι (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  (b.baseChange (R ⧸ I)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv

private theorem quotientBasis_repr (b : Module.Basis ι R S) (I : Ideal R)
    (s : S) (i : ι) :
    (quotientBasis b I).repr (Ideal.Quotient.mk (I.map (algebraMap R S)) s) i =
      Ideal.Quotient.mk I (b.repr s i) := by
  change (b.baseChange (R ⧸ I)).repr
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I)
      (Ideal.Quotient.mk (I.map (algebraMap R S)) s)) i = _
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
    Module.Basis.baseChange_repr_tmul]
  change (b.repr s i) • (1 : R ⧸ I) = _
  rw [Algebra.smul_def, mul_one]
  rfl

private def quotientTensorCoordinate (b : Module.Basis ι R S) (I : Ideal R)
    (M : ModuleCat.{d + 1} R) (hM : Module.IsTorsionBySet R M I) (i : ι) :
    TensorProduct R (S ⧸ I.map (algebraMap R S)) M →ₗ[R] M := by
  letI := hM.module
  let Q := S ⧸ I.map (algebraMap R S)
  let c : Q →ₗ[R] (R ⧸ I) := ((quotientBasis b I).coord i).restrictScalars R
  exact TensorProduct.lift
    { toFun := fun a ↦
        { toFun := fun m ↦ c a • m
          map_add' := fun _ _ ↦ smul_add _ _ _
          map_smul' := fun r m ↦ smul_comm _ _ _ }
      map_add' := by intros; ext m; simp [add_smul]
      map_smul' := by
        intro r a
        ext m
        change c (r • a) • m = r • c a • m
        rw [c.map_smul, smul_assoc] }

private theorem quotientTensorCoordinate_tmul (b : Module.Basis ι R S) (I : Ideal R)
    (M : ModuleCat.{d + 1} R) (hM : Module.IsTorsionBySet R M I) (i : ι)
    (a : S ⧸ I.map (algebraMap R S)) (m : M) :
    letI := hM.module
    quotientTensorCoordinate b I M hM i (TensorProduct.tmul R a m) =
      (quotientBasis b I).repr a i • m := by
  rfl

private theorem quotientTensorCoordinate_natural (b : Module.Basis ι R S) (I : Ideal R)
    (M N : ModuleCat.{d + 1} R)
    (hM : Module.IsTorsionBySet R M I) (hN : Module.IsTorsionBySet R N I)
    (i : ι) (f : M ⟶ N)
    (z : TensorProduct R (S ⧸ I.map (algebraMap R S)) M) :
    quotientTensorCoordinate b I N hN i
        (LinearMap.baseChange (S ⧸ I.map (algebraMap R S)) f.hom z) =
      f (quotientTensorCoordinate b I M hM i z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a m =>
    change @SMul.smul _ _ hN.hasSMul ((quotientBasis b I).repr a i) (f m) =
      f (@SMul.smul _ _ hM.hasSMul ((quotientBasis b I).repr a i) m)
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective ((quotientBasis b I).repr a i)
    rw [← hr]
    exact (f.hom.map_smul r m).symm

private theorem quotientBasis_apply (b : Module.Basis ι R S) (I : Ideal R) (i : ι) :
    quotientBasis b I i = Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) := by
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).injective
  simp [quotientBasis]

private theorem quotientTensor_reconstruct [Fintype ι] (b : Module.Basis ι R S) (I : Ideal R)
    (M : ModuleCat.{d + 1} R) (hM : Module.IsTorsionBySet R M I)
    (z : TensorProduct R (S ⧸ I.map (algebraMap R S)) M) :
    (∑ i, Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) •
      TensorProduct.tmul R (1 : S ⧸ I.map (algebraMap R S))
        (quotientTensorCoordinate b I M hM i z)) = z := by
  classical
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    simp only [map_add, TensorProduct.tmul_add, smul_add, Finset.sum_add_distrib, hz, hw]
  | tmul a m =>
    let := hM.module
    have h : ∀ i, (quotientBasis b I).repr a i • quotientBasis b I i ⊗ₜ[R] m =
        Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) •
          TensorProduct.tmul R (1 : S ⧸ I.map (algebraMap R S))
            (quotientTensorCoordinate b I M hM i (TensorProduct.tmul R a m)) := by
      intro i
      rw [quotientTensorCoordinate_tmul, quotientBasis_apply]
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective ((quotientBasis b I).repr a i)
      rw [← hr]
      change (r • Ideal.Quotient.mk (I.map (algebraMap R S)) (b i)) ⊗ₜ[R] m = _
      rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      simp only [smul_eq_mul, mul_one]
      rfl
    calc
      _ = ∑ i, ((quotientBasis b I).repr a i • quotientBasis b I i) ⊗ₜ[R] m :=
        Finset.sum_congr rfl (fun i _ ↦ (h i).symm)
      _ = (∑ i, (quotientBasis b I).repr a i • quotientBasis b I i) ⊗ₜ[R] m :=
        by rw [TensorProduct.sum_tmul]
      _ = a ⊗ₜ[R] m := by rw [Module.Basis.sum_repr]

private theorem ringExtension_comparison_tmul
    {A B : Type (d + 1)} [CommRing A] [CommRing B] (f : A →+* B)
    (M : ModuleCat.{d + 1} A) (a : B) (m : M) :
    (((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} f).leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} f)).hom.app M)
        (ModuleCat.ringExtensionTmul.{d + 1, d + 1} f M a m) = TensorProduct.tmul A
          (show (ModuleCat.restrictScalars.{d + 1} f).obj (ModuleCat.of B B) from a) m := by
  have hu := congrArg (fun v ↦ v m)
    ((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} f).unit_leftAdjointUniq_hom_app
      (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} f) M)
  change _ = TensorProduct.tmul A
    (show (ModuleCat.restrictScalars.{d + 1} f).obj (ModuleCat.of B B) from (1 : B)) m at hu
  change (((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} f).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} f)).hom.app M)
      (a • (show (ModuleCat.ringExtendScalars.{d + 1, d + 1} f).obj M from
        (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} f).unit.app M m)) = _
  change (((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} f).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} f)).hom.app M)
      (show (ModuleCat.ringExtendScalars.{d + 1, d + 1} f).obj M from
        (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} f).unit.app M m) = _ at hu
  erw [map_smul, hu, ModuleCat.ExtendScalars.smul_tmul, mul_one]

private abbrev tensorModuleFunctor {A B : Type (d + 1)}
    [CommRing A] [CommRing B] [Algebra A B] :
    ModuleCat.{d + 1} A ⥤ ModuleCat.{d + 1} B where
  obj M := ModuleCat.of B (B ⊗[A] M)
  map v := ModuleCat.ofHom (LinearMap.baseChange B v.hom)
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

private def ringTensorIso {A B : Type (d + 1)} [CommRing A] [CommRing B]
    [Algebra A B] :
    ModuleCat.ringExtendScalars.{d + 1, d + 1} (algebraMap A B) ≅
      tensorModuleFunctor (A := A) (B := B) :=
  (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} (algebraMap A B)).leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} (algebraMap A B)) ≪≫
    tensorAlgebraNatIso

private theorem ringTensorIso_tmul {A B : Type (d + 1)} [CommRing A] [CommRing B]
    [Algebra A B] (M : ModuleCat.{d + 1} A) (a : B) (m : M) :
    ((ringTensorIso (A := A) (B := B)).hom.app M)
      (ModuleCat.ringExtensionTmul.{d + 1, d + 1} (algebraMap A B) M a m) =
        TensorProduct.tmul A a m := by
  change (tensorAlgebraIso M).hom
    ((((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} (algebraMap A B)).leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} (algebraMap A B))).hom.app M)
        (ModuleCat.ringExtensionTmul.{d + 1, d + 1} (algebraMap A B) M a m)) = _
  rw [ringExtension_comparison_tmul]
  rfl

private def ringQuotientCoordinate (b : Module.Basis ι R S) (I : Ideal R)
    (M : ModuleCat.{d + 1} R) (hM : Module.IsTorsionBySet R M I) (i : ι) :
    (ModuleCat.restrictScalars.{d + 1}
      (algebraMap R (S ⧸ I.map (algebraMap R S)))).obj
        ((ModuleCat.ringExtendScalars.{d + 1, d + 1}
          (algebraMap R (S ⧸ I.map (algebraMap R S)))).obj M) ⟶
      M :=
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars.{d + 1}
      (algebraMap R (S ⧸ I.map (algebraMap R S)))).obj
        ((ModuleCat.ringExtendScalars.{d + 1, d + 1}
          (algebraMap R (S ⧸ I.map (algebraMap R S)))).obj M))
    (Y := M)
    { toFun := fun z ↦ quotientTensorCoordinate b I M hM i
        (((ringTensorIso (A := R) (B := S ⧸ I.map (algebraMap R S))).hom.app M) z)
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro r z
        change quotientTensorCoordinate b I M hM i
          (((ringTensorIso (A := R) (B := S ⧸ I.map (algebraMap R S))).hom.app M)
            ((algebraMap R (S ⧸ I.map (algebraMap R S)) r) • z)) = _
        rw [map_smul, algebraMap_smul]
        exact (quotientTensorCoordinate b I M hM i).map_smul r _ }

private theorem ringQuotientCoordinate_tmul (b : Module.Basis ι R S) (I : Ideal R)
    (M : ModuleCat.{d + 1} R) (hM : Module.IsTorsionBySet R M I) (i : ι)
    (s : S) (m : M) :
    ringQuotientCoordinate b I M hM i
      (ModuleCat.ringExtensionTmul.{d + 1, d + 1}
        (algebraMap R (S ⧸ I.map (algebraMap R S))) M
          (Ideal.Quotient.mk (I.map (algebraMap R S)) s) m) = b.repr s i • m := by
  change quotientTensorCoordinate b I M hM i
    (((ringTensorIso (A := R) (B := S ⧸ I.map (algebraMap R S))).hom.app M) _) = _
  rw [ringTensorIso_tmul, quotientTensorCoordinate_tmul, quotientBasis_repr]
  rfl

private theorem ringQuotient_reconstruct [Fintype ι] (b : Module.Basis ι R S)
    (I : Ideal R) (M : ModuleCat.{d + 1} R)
    (hM : Module.IsTorsionBySet R M I)
    (z : (ModuleCat.ringExtendScalars.{d + 1, d + 1}
      (algebraMap R (S ⧸ I.map (algebraMap R S)))).obj M) :
    (∑ i, Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) •
      ModuleCat.ringExtensionTmul.{d + 1, d + 1}
        (algebraMap R (S ⧸ I.map (algebraMap R S))) M 1
          (ringQuotientCoordinate b I M hM i z)) = z := by
  classical
  let e := (ringTensorIso (A := R) (B := S ⧸ I.map (algebraMap R S))).hom.app M
  apply (ConcreteCategory.bijective_of_isIso e).injective
  dsimp only [e]
  simp only [map_sum, map_smul]
  calc
    _ = ∑ i, Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) •
        TensorProduct.tmul R (1 : S ⧸ I.map (algebraMap R S))
          (quotientTensorCoordinate b I M hM i (e z)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) • ·)
        (ringTensorIso_tmul M (1 : S ⧸ I.map (algebraMap R S))
          (ringQuotientCoordinate b I M hM i z))
    _ = _ := quotientTensor_reconstruct b I M hM (e z)

private def quotientCoordinatePresheaf (b : Module.Basis ι R S) (I : Ideal R)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥) (i : ι) :
    M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1}
      (algebraMap R (S ⧸ I.map (algebraMap R S))) ⋙
        ModuleCat.restrictScalars.{d + 1}
          (algebraMap R (S ⧸ I.map (algebraMap R S))) ⟶ M.obj where
  app U := ringQuotientCoordinate b I (M.obj.obj U)
    (lisseCoherence_quotientSectionTorsion Y I M hM U.unop) i
  naturality U V v := by
    apply ModuleCat.hom_ext
    ext z
    change quotientTensorCoordinate b I _ _ i
      (((ringTensorIso (A := R) (B := S ⧸ I.map (algebraMap R S))).hom.app _)
        ((ModuleCat.ringExtendScalars.{d + 1, d + 1} _).map (M.obj.map v) z)) = _
    have h := congrArg (fun f ↦ f z)
      ((ringTensorIso (A := R) (B := S ⧸ I.map (algebraMap R S))).hom.naturality
        (M.obj.map v))
    change ((ringTensorIso (A := R) (B := S ⧸ I.map (algebraMap R S))).hom.app _)
        ((ModuleCat.ringExtendScalars.{d + 1, d + 1} _).map (M.obj.map v) z) =
      LinearMap.baseChange (S ⧸ I.map (algebraMap R S)) (M.obj.map v).hom
        (((ringTensorIso (A := R) (B := S ⧸ I.map (algebraMap R S))).hom.app _) z) at h
    rw [h]
    exact quotientTensorCoordinate_natural b I _ _ _ _ i (M.obj.map v) _

private def quotientCoordinateSheaf (b : Module.Basis ι R S) (I : Ideal R)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥) (i : ι) :
    (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1}
      (algebraMap R (S ⧸ I.map (algebraMap R S))))).obj
      ((Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology
        (algebraMap R (S ⧸ I.map (algebraMap R S)))).obj M) ⟶
      M :=
  ⟨(sheafifyComposeIso Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} _)
      (M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1} _)).inv ≫
    sheafifyLift Y.smallEtaleTopology (quotientCoordinatePresheaf Y b I M hM i) M.property⟩

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientCoordinateSheaf_tmul (b : Module.Basis ι R S) (I : Ideal R)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥) (i : ι)
    (U : Y.Etale) (s : S) (m : M.obj.obj (op U)) :
    (quotientCoordinateSheaf Y b I M hM i).hom.app (op U)
      (lisseCoherence_quotientScalarGenerator Y (algebraMap R S)
        (I.map (algebraMap R S)) M U (Ideal.Quotient.mk _ s) m) = b.repr s i • m := by
  have h := congrArg (fun v ↦ v.app (op U)
      (ModuleCat.ringExtensionTmul.{d + 1, d + 1}
        (algebraMap R (S ⧸ I.map (algebraMap R S)))
          (M.obj.obj (op U)) (Ideal.Quotient.mk _ s) m))
    (show Functor.whiskerRight (toSheafify Y.smallEtaleTopology
        (M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1} _))
          (ModuleCat.restrictScalars.{d + 1} _) ≫ (quotientCoordinateSheaf Y b I M hM i).hom =
        quotientCoordinatePresheaf Y b I M hM i by
      dsimp only [quotientCoordinateSheaf]
      rw [← Category.assoc, sheafComposeIso_inv_fac, toSheafify_sheafifyLift])
  exact h.trans (ringQuotientCoordinate_tmul b I _ _ i s m)

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientCoordinateSheaf_tmul_explicit (b : Module.Basis ι R S) (I : Ideal R)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥) (i : ι)
    (U : Y.Etale) (s : S) (m : M.obj.obj (op U)) :
    (quotientCoordinateSheaf Y b I M hM i).hom.app (op U)
      (((toSheafification Y.smallEtaleTopology
        (ModuleCat.{d + 1} (S ⧸ I.map (algebraMap R S)))).app
          (M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1}
            (algebraMap R (S ⧸ I.map (algebraMap R S))))).app (op U)
        (ModuleCat.ringExtensionTmul.{d + 1, d + 1}
          (algebraMap R (S ⧸ I.map (algebraMap R S))) _ (Ideal.Quotient.mk _ s) m)) =
      b.repr s i • m := by
  have h := congrArg (fun v ↦ v.app (op U)
      (ModuleCat.ringExtensionTmul.{d + 1, d + 1}
        (algebraMap R (S ⧸ I.map (algebraMap R S)))
          (M.obj.obj (op U)) (Ideal.Quotient.mk _ s) m))
    (show Functor.whiskerRight (toSheafify Y.smallEtaleTopology
        (M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1} _))
          (ModuleCat.restrictScalars.{d + 1} _) ≫ (quotientCoordinateSheaf Y b I M hM i).hom =
        quotientCoordinatePresheaf Y b I M hM i by
      dsimp only [quotientCoordinateSheaf]
      rw [← Category.assoc, sheafComposeIso_inv_fac, toSheafify_sheafifyLift])
  exact h.trans (ringQuotientCoordinate_tmul b I _ _ i s m)

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem sheaf_sum_apply {A : Type (d + 1)} [Ring A]
    {M N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} A)}
    {α : Type*} (t : Finset α) (f : α → (M ⟶ N)) (U : Y.Etale)
    (x : M.obj.obj (op U)) :
    (∑ i ∈ t, f i).hom.app (op U) x = ∑ i ∈ t, (f i).hom.app (op U) x := by
  let ev : (M ⟶ N) →+ N.obj.obj (op U) :=
    { toFun := fun v ↦ v.hom.app (op U) x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact map_sum ev f t

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem sheaf_comp_app_apply {A : Type (d + 1)} [Ring A]
    {M N P : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} A)}
    (f : M ⟶ N) (g : N ⟶ P) (U : Y.Etale) (x : M.obj.obj (op U)) :
    (f ≫ g).hom.app (op U) x = g.hom.app (op U) (f.hom.app (op U) x) := by
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply]

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem sheaf_iso_hom_inv_app_apply {A : Type (d + 1)} [Ring A]
    {M N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} A)} (e : M ≅ N)
    (U : Y.Etale) (x : N.obj.obj (op U)) :
    e.hom.hom.app (op U) (e.inv.hom.app (op U) x) = x := by
  rw [← ModuleCat.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.id_apply]

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem restrictedScalarSheaf_ext
    {A B : Type (d + 1)} [CommRing A] [CommRing B] (f : A →+* B)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} A))
    (v w : (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f)).obj
      ((Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology f).obj M) ⟶ N)
    (h : ∀ (U : Y.Etale) (a : B) (m : M.obj.obj (op U)),
      v.hom.app (op U)
          (((toSheafification Y.smallEtaleTopology (ModuleCat.{d + 1} B)).app
            (M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1} f)).app (op U)
              (ModuleCat.ringExtensionTmul.{d + 1, d + 1} f _ a m)) =
      w.hom.app (op U)
          (((toSheafification Y.smallEtaleTopology (ModuleCat.{d + 1} B)).app
            (M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1} f)).app (op U)
              (ModuleCat.ringExtensionTmul.{d + 1, d + 1} f _ a m))) : v = w := by
  let P := M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1} f
  let e := sheafifyComposeIso Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1} f) P
  apply Sheaf.hom_ext
  apply (cancel_epi e.hom).mp
  apply sheafify_hom_ext Y.smallEtaleTopology _ _ N.property
  dsimp only [e]
  simp only [← Category.assoc, sheafComposeIso_hom_fac]
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let c := ((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} f).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} f)).app (M.obj.obj U)
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso c.inv).surjective z
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
  | tmul a m =>
    have ht : c.inv (TensorProduct.tmul A a m) =
        ModuleCat.ringExtensionTmul.{d + 1, d + 1} f _ a m := by
      apply (ConcreteCategory.bijective_of_isIso c.hom).injective
      rw [← ModuleCat.comp_apply, c.inv_hom_id, ModuleCat.id_apply]
      exact (ringExtension_comparison_tmul f _ a m).symm
    rw [ht]
    exact h U.unop a m

private def quotientReconstructMap (b : Module.Basis ι R S) (I : Ideal R)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R)) (i : ι) :
    M ⟶ (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1}
      (algebraMap R (S ⧸ I.map (algebraMap R S))))).obj
        ((Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology
          (algebraMap R (S ⧸ I.map (algebraMap R S)))).obj M) :=
  lisseCoherence_scalarSheafUnit Y (algebraMap R (S ⧸ I.map (algebraMap R S))) M ≫
    (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{d + 1}
      (algebraMap R (S ⧸ I.map (algebraMap R S))))).map
      (Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) •
        𝟙 ((Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology
          (algebraMap R (S ⧸ I.map (algebraMap R S)))).obj M))

omit [IsNoetherian Y] [Y.IsSeparated]

private theorem quotientSheaf_reconstruct [Fintype ι] (b : Module.Basis ι R S)
    (I : Ideal R) (M : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥) :
    (∑ i, quotientCoordinateSheaf Y b I M hM i ≫ quotientReconstructMap Y b I M i) =
      𝟙 _ := by
  classical
  apply restrictedScalarSheaf_ext Y _ M _
  intro U a x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hh := congrArg
    (((toSheafification Y.smallEtaleTopology
      (ModuleCat.{d + 1} (S ⧸ I.map (algebraMap R S)))).app
        (M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1} _)).app (op U))
    (ringQuotient_reconstruct b I (M.obj.obj (op U))
      (lisseCoherence_quotientSectionTorsion Y I M hM U)
      (ModuleCat.ringExtensionTmul.{d + 1, d + 1} _ _ (Ideal.Quotient.mk _ s) x))
  simp only [map_sum, map_smul, ringQuotientCoordinate_tmul] at hh
  rw [sheaf_sum_apply]
  calc
    _ = ∑ i, (quotientReconstructMap Y b I M i).hom.app (op U)
        ((quotientCoordinateSheaf Y b I M hM i).hom.app (op U)
          (((toSheafification Y.smallEtaleTopology
            (ModuleCat.{d + 1} (S ⧸ I.map (algebraMap R S)))).app
              (M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1}
                (algebraMap R (S ⧸ I.map (algebraMap R S))))).app (op U)
            (ModuleCat.ringExtensionTmul.{d + 1, d + 1}
              (algebraMap R (S ⧸ I.map (algebraMap R S))) _
              (Ideal.Quotient.mk _ s) x))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [sheaf_comp_app_apply]
    _ = ∑ i, Ideal.Quotient.mk (I.map (algebraMap R S)) (b i) •
        ((toSheafification Y.smallEtaleTopology
          (ModuleCat.{d + 1} (S ⧸ I.map (algebraMap R S)))).app
            (M.obj ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1}
              (algebraMap R (S ⧸ I.map (algebraMap R S))))).app (op U)
          (ModuleCat.ringExtensionTmul.{d + 1, d + 1}
            (algebraMap R (S ⧸ I.map (algebraMap R S))) _ 1 (b.repr s i • x)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [quotientCoordinateSheaf_tmul_explicit]
      dsimp only [quotientReconstructMap, ObjectProperty.FullSubcategory.comp_hom,
        NatTrans.comp_app]
      erw [ModuleCat.comp_apply, lisseCoherence_scalarSheafUnit_apply]
      rfl
    _ = _ := hh

private theorem quotientSheaf_reconstruct_apply [Fintype ι] (b : Module.Basis ι R S)
    (I : Ideal R) (M : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥)
    (U : Y.Etale)
    (z : (lisseCoherence_quotientScalarLevel Y (algebraMap R S)
      (I.map (algebraMap R S)) M).obj.obj (op U)) :
    (∑ i, b i • (show (lisseCoherence_quotientScalarLevel Y (algebraMap R S)
        (I.map (algebraMap R S)) M).obj.obj (op U) from
      (lisseCoherence_scalarSheafUnit Y (algebraMap R (S ⧸ I.map (algebraMap R S))) M).hom.app
        (op U) ((quotientCoordinateSheaf Y b I M hM i).hom.app (op U) z))) = z := by
  have h := congrArg (fun v ↦ v.hom.app (op U) z)
    (quotientSheaf_reconstruct Y b I M hM)
  rw [sheaf_sum_apply] at h
  exact h

end QuotientCoordinates

section CofinalLevels

variable (E L : Type (d + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private def coefficientCofinalIndex (n : ℕ) : ℕ :=
  lisseRamificationIndex l E L ι * (n + 1) - 1

private theorem coefficientCofinal_source (n : ℕ) :
    lisseScalarSourceIndex l E L ι (coefficientCofinalIndex l E L ι n) = n := by
  rw [lisseCoherence_scalarIndex_eq]
  have he : 0 < lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.1
  dsimp only [coefficientCofinalIndex]
  apply Nat.div_eq_of_lt_le <;>
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul, Nat.mul_comm n] <;>
    omega

private theorem coefficientCofinal_ideal (n : ℕ) :
    Padic.coefficientExtensionIdeal l L (coefficientCofinalIndex l E L ι n + 1) =
      Ideal.map (lisseIntegerInclusion l E L ι)
        (Padic.coefficientExtensionIdeal l E (n + 1)) := by
  have he : 0 < lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.1
  have hp := Nat.mul_pos he (Nat.succ_pos n)
  have hr : Ideal.map (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionMaximalIdeal l E) =
        Padic.coefficientExtensionMaximalIdeal l L ^ lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.2
  dsimp only [Padic.coefficientExtensionIdeal, coefficientCofinalIndex]
  rw [Ideal.map_pow, lisseCoherence_uniformizerIdeal_eq l E, hr,
    ← lisseCoherence_uniformizerIdeal_eq l L, ← pow_mul]
  congr 1
  exact Nat.sub_add_cancel hp

private theorem coefficientCofinal_mono {m n : ℕ} (h : m ≤ n) :
    coefficientCofinalIndex l E L ι m ≤ coefficientCofinalIndex l E L ι n := by
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (by omega : m + 1 ≤ n + 1)) 1

private theorem coefficientCofinal_ge (n : ℕ) :
    n ≤ coefficientCofinalIndex l E L ι n := by
  have he : 0 < lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.1
  have h : n + 1 ≤ lisseRamificationIndex l E L ι * (n + 1) := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (n + 1) (show 1 ≤ lisseRamificationIndex l E L ι by omega)
  dsimp only [coefficientCofinalIndex]
  omega

private def coefficientCofinalLevelIso (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    ((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj
        (op (coefficientCofinalIndex l E L ι n)) ≅
      lisseCoherence_quotientScalarLevel Y (lisseIntegerInclusion l E L ι)
        (Ideal.map (lisseIntegerInclusion l E L ι)
          (Padic.coefficientExtensionIdeal l E (n + 1))) (F.obj.obj (op n)) := by
  exact lisseScalarLevelIso l E Y L ι F _ ≪≫
    eqToIso (congrArg₂ (lisseCoherence_quotientScalarLevel Y (lisseIntegerInclusion l E L ι))
      (coefficientCofinal_ideal l E L ι n)
      (congrArg (fun k ↦ F.obj.obj (op k)) (coefficientCofinal_source l E L ι n)))

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientLevel_transport_generator
    {R S : Type (d + 1)} [CommRing R] [CommRing S] (f : R →+* S)
    (I J : Ideal S) (hI : I = J)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R)) (hM : M = N)
    (U : Y.Etale) (s : S) (x : M.obj.obj (op U)) :
    ((eqToIso (congrArg₂ (lisseCoherence_quotientScalarLevel Y f) hI hM)).hom).hom.app
        (op U) (lisseCoherence_quotientScalarGenerator Y f I M U
          (Ideal.Quotient.mk I s) x) =
      lisseCoherence_quotientScalarGenerator Y f J N U (Ideal.Quotient.mk J s)
        ((eqToHom hM).hom.app (op U) x) := by
  subst J N
  rfl

private def coefficientCofinalSourceIso (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    F.obj.obj (op (lisseScalarSourceIndex l E L ι
      (coefficientCofinalIndex l E L ι n))) ≅ F.obj.obj (op n) :=
  eqToIso (congrArg (fun k ↦ F.obj.obj (op k)) (coefficientCofinal_source l E L ι n))

private theorem coefficientCofinalLevelIso_generator
    (F : LisseIntegralSheaf l E Y) (n : ℕ) (U : Y.Etale)
    (s : Padic.coefficientExtensionIntegers l L)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι
      (coefficientCofinalIndex l E L ι n)))).obj.obj (op U)) :
    (coefficientCofinalLevelIso l Y E L ι F n).hom.hom.app (op U)
        (lisseScalarGenerator l E Y L ι F (coefficientCofinalIndex l E L ι n) U
          (Ideal.Quotient.mk _ s) x) =
      lisseCoherence_quotientScalarGenerator Y (lisseIntegerInclusion l E L ι)
        (Ideal.map (lisseIntegerInclusion l E L ι)
          (Padic.coefficientExtensionIdeal l E (n + 1))) (F.obj.obj (op n)) U
        (Ideal.Quotient.mk _ s)
        ((coefficientCofinalSourceIso l Y E L ι F n).hom.hom.app (op U) x) := by
  dsimp only [coefficientCofinalLevelIso, lisseScalarGenerator, Iso.trans_hom]
  erw [← ModuleCat.comp_apply]
  simp only [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.inv_hom_id_assoc]
  exact quotientLevel_transport_generator Y (lisseIntegerInclusion l E L ι) _ _
    (coefficientCofinal_ideal l E L ι n) _ _
    (congrArg (fun k ↦ F.obj.obj (op k)) (coefficientCofinal_source l E L ι n)) U s x

private def coefficientCofinalUnit (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    F.obj.obj (op n) ⟶
      (sheafCompose Y.smallEtaleTopology
        (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).obj
          (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj
            (op (coefficientCofinalIndex l E L ι n))) :=
  lisseCoherence_scalarSheafUnit Y
      ((Ideal.Quotient.mk (Ideal.map (lisseIntegerInclusion l E L ι)
        (Padic.coefficientExtensionIdeal l E (n + 1)))).comp
          (lisseIntegerInclusion l E L ι)) (F.obj.obj (op n)) ≫
    (sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).map
        (coefficientCofinalLevelIso l Y E L ι F n).inv

private theorem coefficientCofinalUnit_apply (F : LisseIntegralSheaf l E Y)
    (n : ℕ) (U : Y.Etale) (x : (F.obj.obj (op n)).obj.obj (op U)) :
    (coefficientCofinalUnit l Y E L ι F n).hom.app (op U) x =
      lisseScalarGenerator l E Y L ι F (coefficientCofinalIndex l E L ι n) U 1
        ((coefficientCofinalSourceIso l Y E L ι F n).inv.hom.app (op U) x) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((coefficientCofinalLevelIso l Y E L ι F n).hom.hom.app (op U))).injective
  have hone : (1 : Padic.coefficientExtensionRing l L
      (coefficientCofinalIndex l E L ι n + 1)) = Ideal.Quotient.mk _
        (1 : Padic.coefficientExtensionIntegers l L) := (map_one _).symm
  rw [hone, coefficientCofinalLevelIso_generator]
  simp only [← ModuleCat.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.inv_hom_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.id_apply]
  change _ = lisseCoherence_quotientScalarGenerator Y _ _ _ U 1 x
  change (coefficientCofinalLevelIso l Y E L ι F n).hom.hom.app (op U)
    ((coefficientCofinalLevelIso l Y E L ι F n).inv.hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y _ (F.obj.obj (op n))).hom.app (op U) x)) = _
  erw [← ModuleCat.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.id_apply]
  exact lisseCoherence_scalarSheafUnit_apply Y _ _ U x

variable {r : ℕ}
  (b : letI := (lisseIntegerInclusion l E L ι).toAlgebra
    Module.Basis (Fin r) (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L))

private def coefficientCofinalCoordinate (F : LisseIntegralSheaf l E Y) (n : ℕ)
    (i : Fin r) :
    (sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).obj
        (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj
          (op (coefficientCofinalIndex l E L ι n))) ⟶ F.obj.obj (op n) := by
  letI := (lisseIntegerInclusion l E L ι).toAlgebra
  exact (sheafCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).map
      (coefficientCofinalLevelIso l Y E L ι F n).hom ≫
    quotientCoordinateSheaf Y b (Padic.coefficientExtensionIdeal l E (n + 1))
      (F.obj.obj (op n)) (lisseCoherence_integralLevel_annihilated l E Y F n) i

private theorem coefficientCofinalCoordinate_generator
    (F : LisseIntegralSheaf l E Y) (n : ℕ) (i : Fin r) (U : Y.Etale)
    (s : Padic.coefficientExtensionIntegers l L)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι
      (coefficientCofinalIndex l E L ι n)))).obj.obj (op U)) :
    letI := (lisseIntegerInclusion l E L ι).toAlgebra
    (coefficientCofinalCoordinate l Y E L ι b F n i).hom.app (op U)
        (lisseScalarGenerator l E Y L ι F (coefficientCofinalIndex l E L ι n) U
          (Ideal.Quotient.mk _ s) x) =
      b.repr s i • ((coefficientCofinalSourceIso l Y E L ι F n).hom.hom.app (op U) x) := by
  let := (lisseIntegerInclusion l E L ι).toAlgebra
  change (quotientCoordinateSheaf Y b _ _ _ i).hom.app (op U)
    ((coefficientCofinalLevelIso l Y E L ι F n).hom.hom.app (op U) _) = _
  erw [coefficientCofinalLevelIso_generator, quotientCoordinateSheaf_tmul]

private theorem restrictedChosenScalar_ext (F : LisseIntegralSheaf l E Y) (m : ℕ)
    (N : Sheaf Y.smallEtaleTopology
      (ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l E)))
    (v w : (sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).obj
        (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj (op m)) ⟶ N)
    (h : ∀ (U : Y.Etale) (s : Padic.coefficientExtensionIntegers l L)
      (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)),
      v.hom.app (op U) (lisseScalarGenerator l E Y L ι F m U
        (Ideal.Quotient.mk _ s) x) =
      w.hom.app (op U) (lisseScalarGenerator l E Y L ι F m U
        (Ideal.Quotient.mk _ s) x)) : v = w := by
  apply (cancel_epi ((sheafCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).map
      (lisseScalarLevelIso l E Y L ι F m).inv)).mp
  refine restrictedScalarSheaf_ext Y (lisseScalarCoefficientMap l E L ι m)
    (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))) N _ _ ?_
  intro U a x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact h U s x

private theorem scalarGenerator_integer_smul (F : LisseIntegralSheaf l E Y)
    (m : ℕ) (U : Y.Etale) (s : Padic.coefficientExtensionIntegers l L)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    lisseScalarGenerator l E Y L ι F m U (Ideal.Quotient.mk _ s) x =
      s • lisseScalarGenerator l E Y L ι F m U 1 x := by
  dsimp only [lisseScalarGenerator, lisseIntegralScalarGenerator,
    lisseCoherence_quotientScalarGenerator, ModuleCat.ringExtensionTmul]
  simp only [one_smul, map_smul]
  change (lisseScalarLevelIso l E Y L ι F m).inv.hom.app (op U) (s • _) = _
  exact ((lisseScalarLevelIso l E Y L ι F m).inv.hom.app (op U)).hom.map_smul s _

private theorem scalarGenerator_integer_transition (F : LisseIntegralSheaf l E Y)
    (m n : ℕ) (h : m ≤ n) (U : Y.Etale)
    (s : Padic.coefficientExtensionIntegers l L)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι n))).obj.obj (op U)) :
    ((((lisseIntegralScalarExtension l E Y L ι).obj F).obj.map
      (homOfLE h).op).hom.app (op U))
        (lisseScalarGenerator l E Y L ι F n U (Ideal.Quotient.mk _ s) x) =
      lisseScalarGenerator l E Y L ι F m U (Ideal.Quotient.mk _ s)
        ((F.obj.map (homOfLE (lisseCoherence_scalarIndex_mono l E L ι h)).op).hom.app
          (op U) x) := by
  rw [scalarGenerator_integer_smul, map_smul,
    lisseCoherence_extendedGenerator_transition_le, scalarGenerator_integer_smul]

private theorem inverse_naturality {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ A') (f : B ≅ B') (v : A ⟶ B) (w : A' ⟶ B')
    (h : v ≫ f.hom = e.hom ≫ w) : e.inv ≫ v = w ≫ f.inv := by
  apply (cancel_mono f.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using congrArg (e.inv ≫ ·) h

private theorem coefficientCofinalSource_naturality (F : LisseIntegralSheaf l E Y)
    {m n : ℕ} (h : m ≤ n) :
    F.obj.map (homOfLE (lisseCoherence_scalarIndex_mono l E L ι
        (coefficientCofinal_mono l E L ι h))).op ≫
      (coefficientCofinalSourceIso l Y E L ι F m).hom =
    (coefficientCofinalSourceIso l Y E L ι F n).hom ≫ F.obj.map (homOfLE h).op :=
  lisseCoherence_sequenceCast_naturality F.obj
    (coefficientCofinal_source l E L ι m) (coefficientCofinal_source l E L ι n) _ h

private theorem coefficientCofinalUnit_naturality (F : LisseIntegralSheaf l E Y)
    {m n : ℕ} (h : m ≤ n) :
    coefficientCofinalUnit l Y E L ι F n ≫
      (sheafCompose Y.smallEtaleTopology
        (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).map
          (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.map
            (homOfLE (coefficientCofinal_mono l E L ι h)).op) =
      F.obj.map (homOfLE h).op ≫ coefficientCofinalUnit l Y E L ι F m := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  ext x
  change (((((lisseIntegralScalarExtension l E Y L ι).obj F).obj.map
    (homOfLE (coefficientCofinal_mono l E L ι h)).op).hom.app U))
      ((coefficientCofinalUnit l Y E L ι F n).hom.app U x) = _
  rw [coefficientCofinalUnit_apply, lisseCoherence_extendedGenerator_transition_le]
  change _ = (coefficientCofinalUnit l Y E L ι F m).hom.app U
    ((F.obj.map (homOfLE h).op).hom.app U x)
  rw [coefficientCofinalUnit_apply]
  congr 1
  have hs := coefficientCofinalSource_naturality l Y E L ι F h
  have he : (coefficientCofinalSourceIso l Y E L ι F n).inv ≫
      F.obj.map (homOfLE (lisseCoherence_scalarIndex_mono l E L ι
        (coefficientCofinal_mono l E L ι h))).op =
      F.obj.map (homOfLE h).op ≫ (coefficientCofinalSourceIso l Y E L ι F m).inv := by
    exact inverse_naturality _ _ _ _ hs
  exact congrArg (fun v ↦ v.hom.app U x) he

private theorem coefficientCofinalCoordinate_naturality
    (F : LisseIntegralSheaf l E Y) {m n : ℕ} (h : m ≤ n) (i : Fin r) :
    (sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))).map
        (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.map
          (homOfLE (coefficientCofinal_mono l E L ι h)).op) ≫
      coefficientCofinalCoordinate l Y E L ι b F m i =
    coefficientCofinalCoordinate l Y E L ι b F n i ≫ F.obj.map (homOfLE h).op := by
  apply restrictedChosenScalar_ext l Y E L ι F _ _
  intro U s x
  change (coefficientCofinalCoordinate l Y E L ι b F m i).hom.app (op U)
    (((((lisseIntegralScalarExtension l E Y L ι).obj F).obj.map
      (homOfLE (coefficientCofinal_mono l E L ι h)).op).hom.app (op U)) _) = _
  rw [scalarGenerator_integer_transition, coefficientCofinalCoordinate_generator]
  change _ = (F.obj.map (homOfLE h).op).hom.app (op U)
    ((coefficientCofinalCoordinate l Y E L ι b F n i).hom.app (op U) _)
  rw [coefficientCofinalCoordinate_generator, map_smul]
  congr 1
  exact congrArg (fun v ↦ v.hom.app (op U) x)
    (coefficientCofinalSource_naturality l Y E L ι F h)

attribute [local instance] lisseCoefficientIntegersCommRing lisseCoefficientIntegersAlgebra
  lisseCoefficientIntegersModule lisseCoefficientQuotientCommRing lisseCoefficientQuotientAlgebra
attribute [local irreducible] lisseIntegerInclusion lisseRamificationIndex lisseScalarSourceIndex
  coefficientCofinalLevelIso lisseScalarLevelIso lisseIntegralScalarGenerator
  lisseCoherence_scalarSheafAdj lisseCoherence_scalarSheafUnit Sheaf.ringExtendScalars
  Padic.coefficientExtensionAbsoluteValue Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionMaximalIdeal

private theorem coefficientCofinal_reconstruct
    (F : LisseIntegralSheaf l E Y) (n : ℕ) (U : Y.Etale)
    (z : ((((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj
      (op (coefficientCofinalIndex l E L ι n))).obj.obj (op U))) :
    (∑ i, b i • (show ((((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj
      (op (coefficientCofinalIndex l E L ι n))).obj.obj (op U)) from
        (coefficientCofinalUnit l Y E L ι F n).hom.app (op U)
          ((coefficientCofinalCoordinate l Y E L ι b F n i).hom.app (op U) z))) = z := by
  classical
  let := (lisseIntegerInclusion l E L ι).toAlgebra
  let e := coefficientCofinalLevelIso l Y E L ι F n
  apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op U))).injective
  rw [map_sum]
  refine Eq.trans ?_ (quotientSheaf_reconstruct_apply Y b
    (Padic.coefficientExtensionIdeal l E (n + 1)) (F.obj.obj (op n))
      (lisseCoherence_integralLevel_annihilated l E Y F n) U (e.hom.hom.app (op U) z))
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change b i • e.hom.hom.app (op U)
    (e.inv.hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y _ (F.obj.obj (op n))).hom.app (op U)
        ((quotientCoordinateSheaf Y b _ _ _ i).hom.app (op U)
          (e.hom.hom.app (op U) z)))) = _
  congr 1
  exact sheaf_iso_hom_inv_app_apply Y e U _

private def coefficientHomCoordinate
    (b : letI := (lisseIntegerInclusion l E L ι).toAlgebra
      Module.Basis (Fin r) (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionIntegers l L)) (F G : LisseIntegralSheaf l E Y)
    (u : (lisseIntegralScalarExtension l E Y L ι).obj F ⟶
      (lisseIntegralScalarExtension l E Y L ι).obj G) (i : Fin r) : F ⟶ G := by
  let Rf := sheafCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{d + 1} (lisseIntegerInclusion l E L ι))
  refine ⟨{
    app := fun m ↦
      coefficientCofinalUnit l Y E L ι F m.unop ≫
        Rf.map (u.hom.app (op (coefficientCofinalIndex l E L ι m.unop))) ≫
          coefficientCofinalCoordinate l Y E L ι b G m.unop i
    naturality := ?_ }⟩
  intro m n v
  have h : n.unop ≤ m.unop := leOfHom v.unop
  have hunit := coefficientCofinalUnit_naturality l Y E L ι F h
  have hcoord := coefficientCofinalCoordinate_naturality l Y E L ι b G h i
  have hu := congrArg Rf.map
    (u.hom.naturality (homOfLE (coefficientCofinal_mono l E L ι h)).op)
  simp only [Functor.map_comp] at hu
  change F.obj.map (homOfLE h).op ≫
      (coefficientCofinalUnit l Y E L ι F n.unop ≫ _ ≫ _) = _
  rw [← Category.assoc, ← hunit]
  simp only [Category.assoc]
  rw [← Category.assoc (Rf.map _) (Rf.map _), hu]
  simp only [Category.assoc]
  erw [hcoord]
  have hv : (homOfLE h).op = v := Subsingleton.elim _ _
  erw [hv]

private theorem integral_transition_epi (F : LisseIntegralSheaf l E Y)
    {m n : ℕ} (h : m ≤ n) : Epi (F.obj.map (homOfLE h).op) := by
  have hs (k : ℕ) : Epi (F.obj.map (homOfLE (Nat.le_succ k)).op) := by
    have : ∀ i : (ObjectProperty.ofObj Y.uliftPointSmallEtale).FullSubcategory,
        Epi (i.obj.sheafFiber.map (F.obj.map (homOfLE (Nat.le_succ k)).op)) := by
      rintro ⟨-, ⟨x⟩⟩
      apply (ModuleCat.epi_iff_surjective _).mpr
      exact (F.property.2.2 _ (Y.algClosurePoint x) k).1
    have H := (jointlyReflectIsomorphisms_ulift_pointSmallEtale Y
      (ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l E))).jointlyFaithful
    exact H.jointlyReflectEpimorphisms.epi _
  induction n, h using Nat.le_induction with
  | base =>
    have heq : F.obj.map (homOfLE (le_refl m)).op = 𝟙 _ := by
      have hi : (homOfLE (le_refl m)).op = 𝟙 (op m) := Subsingleton.elim _ _
      exact (congrArg F.obj.map hi).trans (F.obj.map_id _)
    rw [heq]
    infer_instance
  | succ n h ih =>
    have : Epi (F.obj.map (homOfLE (Nat.le_succ n)).op) := hs n
    have heq : F.obj.map (homOfLE (h.trans (Nat.le_succ n))).op =
        F.obj.map (homOfLE (Nat.le_succ n)).op ≫ F.obj.map (homOfLE h).op := by
      rw [← F.obj.map_comp]
      congr 1
    rw [heq]
    infer_instance

private theorem integralHom_ext_cofinal (F G : LisseIntegralSheaf l L Y)
    (v w : F ⟶ G)
    (h : ∀ n, v.hom.app (op (coefficientCofinalIndex l E L ι n)) =
      w.hom.app (op (coefficientCofinalIndex l E L ι n))) : v = w := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  have hm := coefficientCofinal_ge l E L ι m.unop
  have := integral_transition_epi l Y L F hm
  apply (cancel_epi (F.obj.map (homOfLE hm).op)).mp
  exact (v.hom.naturality (homOfLE hm).op).trans
    ((congrArg (· ≫ G.obj.map (homOfLE hm).op) (h m.unop)).trans
      (w.hom.naturality (homOfLE hm).op).symm)

private theorem integral_sum_apply {F G : LisseIntegralSheaf l L Y}
    {α : Type*} (t : Finset α) (f : α → (F ⟶ G)) (m : ℕ) (U : Y.Etale)
    (x : (F.obj.obj (op m)).obj.obj (op U)) :
    ((∑ i ∈ t, f i).hom.app (op m)).hom.app (op U) x =
      ∑ i ∈ t, ((f i).hom.app (op m)).hom.app (op U) x := by
  let ev : (F ⟶ G) →+ (G.obj.obj (op m)).obj.obj (op U) :=
    { toFun := fun v ↦ (v.hom.app (op m)).hom.app (op U) x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact map_sum ev f t

private theorem coefficientCofinal_extendedMap_unit
    (F G : LisseIntegralSheaf l E Y) (v : F ⟶ G)
    (n : ℕ) (U : Y.Etale) (x : (F.obj.obj (op n)).obj.obj (op U)) :
    (((lisseIntegralScalarExtension l E Y L ι).map v).hom.app
      (op (coefficientCofinalIndex l E L ι n))).hom.app (op U)
        ((coefficientCofinalUnit l Y E L ι F n).hom.app (op U) x) =
      (coefficientCofinalUnit l Y E L ι G n).hom.app (op U)
        ((v.hom.app (op n)).hom.app (op U) x) := by
  rw [coefficientCofinalUnit_apply, lisseScalarGenerator_map,
    coefficientCofinalUnit_apply]
  congr 1
  have hv := lisseCoherence_natTrans_index_cast v.hom
    (coefficientCofinal_source l E L ι n)
  have he : (coefficientCofinalSourceIso l Y E L ι F n).inv ≫
      v.hom.app (op (lisseScalarSourceIndex l E L ι
        (coefficientCofinalIndex l E L ι n))) =
    v.hom.app (op n) ≫ (coefficientCofinalSourceIso l Y E L ι G n).inv := by
    exact inverse_naturality _ _ _ _ hv
  exact congrArg (fun w ↦ w.hom.app (op U) x) he

private theorem integral_span (F G : LisseIntegralSheaf l E Y)
    (u : (lisseIntegralScalarExtension l E Y L ι).obj F ⟶
      (lisseIntegralScalarExtension l E Y L ι).obj G) :
    u ∈ Submodule.span (Padic.coefficientExtensionIntegers l L)
      (Set.range (fun g : F ⟶ G ↦ (lisseIntegralScalarExtension l E Y L ι).map g)) := by
  classical
  let := (lisseIntegerInclusion l E L ι).toAlgebra
  have hf := integerExtension_free l E L ι
  let := hf.1
  let := hf.2
  let b := Module.finBasis (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionIntegers l L)
  let g := coefficientHomCoordinate l Y E L ι b F G u
  have heq : u = ∑ i, b i • (lisseIntegralScalarExtension l E Y L ι).map (g i) := by
    apply integralHom_ext_cofinal l Y E L ι
    intro n
    apply lisseCoherence_chosenScalarLevel_ext l E Y L ι F _ _
      (lisseCoherence_integralLevel_annihilated l L Y _ _)
    intro U x
    let y := (coefficientCofinalSourceIso l Y E L ι F n).hom.hom.app (op U) x
    have hy : (coefficientCofinalUnit l Y E L ι F n).hom.app (op U) y =
        lisseScalarGenerator l E Y L ι F (coefficientCofinalIndex l E L ι n) U 1 x := by
      rw [coefficientCofinalUnit_apply]
      dsimp only [y]
      rw [← ModuleCat.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
        Iso.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.id_apply]
    rw [← hy, integral_sum_apply]
    have hr := coefficientCofinal_reconstruct l Y E L ι b G n U
      ((u.hom.app (op (coefficientCofinalIndex l E L ι n))).hom.app (op U)
        ((coefficientCofinalUnit l Y E L ι F n).hom.app (op U) y))
    rw [← hr]
    apply Finset.sum_congr rfl
    intro i _
    change _ = b i • (((lisseIntegralScalarExtension l E Y L ι).map (g i)).hom.app
      (op (coefficientCofinalIndex l E L ι n))).hom.app (op U)
        ((coefficientCofinalUnit l Y E L ι F n).hom.app (op U) y)
    rw [coefficientCofinal_extendedMap_unit]
    rfl
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (g i)))

private abbrev rationalHomModule (F G : LisseRationalSheaf l E Y) :
    Module E (F ⟶ G) := lisseRationalHomScalarModule l E Y F G

attribute [local instance] rationalHomModule

private theorem rational_span_of_integral_span
    (hi : ∀ (F G : LisseIntegralSheaf l E Y)
      (u : (lisseIntegralScalarExtension l E Y L ι).obj F ⟶
        (lisseIntegralScalarExtension l E Y L ι).obj G),
      u ∈ Submodule.span (Padic.coefficientExtensionIntegers l L)
        (Set.range (fun g : F ⟶ G ↦ (lisseIntegralScalarExtension l E Y L ι).map g)))
    (F G : LisseRationalSheaf l E Y)
    (f : (lisseRationalScalarExtension l E Y L ι).obj F ⟶
      (lisseRationalScalarExtension l E Y L ι).obj G) :
    f ∈ Submodule.span L
      (Set.range (fun g : F ⟶ G ↦ (lisseRationalScalarExtension l E Y L ι).map g)) := by
  let W := Submodule.span L
    (Set.range (fun g : F ⟶ G ↦ (lisseRationalScalarExtension l E Y L ι).map g))
  change f ∈ W
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => exact W.add_mem hf hg
  | tmul a u =>
    have hu := hi F.integral G.integral u
    have hunit : ∀ v, v ∈ Submodule.span (Padic.coefficientExtensionIntegers l L)
        (Set.range (fun g : F.integral ⟶ G.integral ↦
          (lisseIntegralScalarExtension l E Y L ι).map g)) →
        TensorProduct.tmul (Padic.coefficientExtensionIntegers l L) (1 : L) v ∈ W := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨g, rfl⟩ := hv
        have hg := Submodule.subset_span (R := L)
          (s := Set.range (fun g : F ⟶ G ↦
            (lisseRationalScalarExtension l E Y L ι).map g))
          (Set.mem_range_self (TensorProduct.tmul (Padic.coefficientExtensionIntegers l E)
            (1 : E) g))
        rw [lisseCoherence_rationalScalar_map_tmul, map_one] at hg
        exact hg
      | zero => simpa only [TensorProduct.tmul_zero] using W.zero_mem
      | add v w hv hw ihv ihw =>
        simpa only [TensorProduct.tmul_add] using W.add_mem ihv ihw
      | smul c v hv ih =>
        rw [TensorProduct.tmul_smul]
        change (c : L) • TensorProduct.tmul (Padic.coefficientExtensionIntegers l L)
          (1 : L) v ∈ W
        exact W.smul_mem (c : L) ih
    have hh := W.smul_mem a (hunit u hu)
    change a • ((1 : L) ⊗ₜ[Padic.coefficientExtensionIntegers l L] u) ∈ W at hh
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hh

end CofinalLevels

-- Preserve the existing target signature, including its algebraic-closure hypothesis.
set_option linter.unusedSectionVars false in
/-- Finite coefficient extension spans the rational morphisms between extended sheaves. -/
theorem lisseCoefficientHomBaseChange_span
    (E₀ : Padic.FiniteCoefficientFields l K) :
    let P := (lisseCoefficientDiagramData l Y K).diagram
    let T := (P.map (homOfLE
      (show Padic.finiteCoefficientBase l K ≤ E₀ from
        show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor
    let Q := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor
    ∀ (A B : P.obj ⟨Padic.finiteCoefficientBase l K⟩) (f : T.obj A ⟶ T.obj B),
      (Q.map f : lisseRationalHom l E₀.val Y (Q.obj (T.obj A)) (Q.obj (T.obj B))) ∈
        Submodule.span
          (M := lisseRationalHom l E₀.val Y (Q.obj (T.obj A)) (Q.obj (T.obj B)))
          E₀.val (Set.range (fun g : A ⟶ B ↦
          (Q.map (T.map g) :
            lisseRationalHom l E₀.val Y (Q.obj (T.obj A)) (Q.obj (T.obj B))))) := by
  dsimp only
  unfold lisseCoefficientDiagramData
  dsimp only
  intro A B f
  exact rational_span_of_integral_span l Y (Padic.finiteCoefficientBase l K).val E₀.val
    (IntermediateField.inclusion bot_le)
    (integral_span l Y (Padic.finiteCoefficientBase l K).val E₀.val
      (IntermediateField.inclusion bot_le)) A B f

end

end AlgebraicGeometry.Scheme

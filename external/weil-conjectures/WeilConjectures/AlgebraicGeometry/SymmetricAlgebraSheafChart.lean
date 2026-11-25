/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Charts of `Spec_X (Sym^• ℰ)` over opens on which `ℰ` is free

If `U` is an affine open of `X` on which the sections `Γ(ℰ, U)` of the quasi-coherent sheaf `ℰ`
have a basis indexed by `Fin c`, then `Spec_X (Sym^• ℰ) ×_X U ≅ 𝔸^c_U` over `U`
(`AlgebraicGeometry.Scheme.Modules.symSpecChart`): the restriction of `Spec_X (Sym^• ℰ)` to `U` is
`Spec (Sym_{Γ(X, U)} Γ(ℰ, U)) = Spec Γ(X, U)[T₁, …, T_c]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The affine space `𝔸^n` is functorial in isomorphisms of the base. -/
noncomputable def affineSpaceMapIso (n : Type u) {S T : Scheme.{u}} (e : S ≅ T) :
    𝔸(n; S) ≅ 𝔸(n; T) where
  hom := AffineSpace.map n e.hom
  inv := AffineSpace.map n e.inv
  hom_inv_id := by rw [← AffineSpace.map_comp, e.hom_inv_id, AffineSpace.map_id]
  inv_hom_id := by rw [← AffineSpace.map_comp, e.inv_hom_id, AffineSpace.map_id]

/-- The ring map `Γ(X, U)[T₁, …, T_c] ⟶ Sym_{Γ(X, U)} Γ(ℰ, U)` sending `Tₖ` to the `k`-th basis
vector. -/
noncomputable def symChartRingHom {c : ℕ} (U : X.AffineZariskiSite)
    (b : Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)) :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin c)) Γ(X, U.1)) ⟶
      CommRingCat.of (SymmetricAlgebra Γ(X, U.1) Γ(F, U.1)) :=
  CommRingCat.ofHom ((SymmetricAlgebra.equivMvPolynomial
    (b.reindex Equiv.ulift.symm)).symm.toAlgHom.toRingHom)

lemma C_comp_symChartRingHom {c : ℕ} (U : X.AffineZariskiSite)
    (b : Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)) :
    CommRingCat.ofHom MvPolynomial.C ≫ F.symChartRingHom U b =
      CommRingCat.ofHom (algebraMap Γ(X, U.1) (SymmetricAlgebra Γ(X, U.1) Γ(F, U.1))) := by
  ext r
  exact (SymmetricAlgebra.equivMvPolynomial (b.reindex Equiv.ulift.symm)).symm.commutes r

instance {c : ℕ} (U : X.AffineZariskiSite) (b : Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)) :
    IsIso (F.symChartRingHom U b) := by
  unfold symChartRingHom
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (AlgEquiv.bijective _)

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

The chart `Spec_X (Sym^• ℰ) ×_X U ≅ 𝔸^c_U` over an affine open `U` on which `Γ(ℰ, U)` is free of
rank `c`, induced by `Sym_{Γ(X, U)} Γ(ℰ, U) ≅ Γ(X, U)[T₁, …, T_c]`. -/
noncomputable def symSpecChart [F.IsQuasicoherent] {c : ℕ} (U : X.AffineZariskiSite)
    (b : Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)) :
    Limits.pullback F.symSpecProj U.1.ι ≅ 𝔸(ULift.{u} (Fin c); U.1) :=
  ((AffineZariskiSite.relativeGluingData
      F.coequifibered_toSymPresheaf).isPullback_natTrans_ι_toBase U).flip.isoPullback.symm ≪≫
    asIso (Spec.map (F.symChartRingHom U b)) ≪≫
    (AffineSpace.SpecIso (ULift.{u} (Fin c)) Γ(X, U.1)).symm ≪≫
    (affineSpaceMapIso (ULift.{u} (Fin c)) U.2.isoSpec).symm

lemma symSpecChart_hom_over [F.IsQuasicoherent] {c : ℕ} (U : X.AffineZariskiSite)
    (b : Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)) :
    (F.symSpecChart U b).hom ≫ 𝔸(ULift.{u} (Fin c); U.1) ↘ U.1 =
      Limits.pullback.snd F.symSpecProj U.1.ι := by
  simp only [symSpecChart, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  change _ ≫ _ ≫ _ ≫ AffineSpace.map _ U.2.isoSpec.inv ≫ _ = _
  rw [AffineSpace.map_over, AffineSpace.SpecIso_inv_over_assoc, ← Spec.map_comp_assoc,
    C_comp_symChartRingHom, Iso.inv_comp_eq]
  refine Eq.trans ?_ (IsPullback.isoPullback_hom_snd _).symm
  rfl

/-- Over an affine base, the zero section of `𝔸^n_{Spec R}` is `Spec` of evaluation at `0`. -/
lemma zeroSection_Spec_eq (n : Type u) (R : CommRingCat.{u}) :
    AffineSpace.zeroSection n (Spec R) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff (R := R) (σ := n))) ≫
        (AffineSpace.SpecIso n R).inv := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [AffineSpace.zeroSection_over, Category.assoc, AffineSpace.SpecIso_inv_over,
      ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    simp
  · rw [AffineSpace.zeroSection_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp

lemma symChartRingHom_comp_algebraMapInv {c : ℕ} (U : X.AffineZariskiSite)
    (b : Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)) :
    F.symChartRingHom U b ≫ CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv (R := Γ(X, U.1))
      (M := Γ(F, U.1))).toRingHom =
      CommRingCat.ofHom (MvPolynomial.constantCoeff (R := Γ(X, U.1))) := by
  ext1
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · change SymmetricAlgebra.algebraMapInv
      ((SymmetricAlgebra.equivMvPolynomial (b.reindex Equiv.ulift.symm)).symm
        (MvPolynomial.C r)) = _
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, AlgHom.commutes]
    simp
  · change SymmetricAlgebra.algebraMapInv
      ((SymmetricAlgebra.equivMvPolynomial (b.reindex Equiv.ulift.symm)).symm
        (MvPolynomial.X i)) = _
    rw [SymmetricAlgebra.equivMvPolynomial_symm_X, SymmetricAlgebra.algebraMapInv_ι]
    simp

lemma ι_inv_toBase_id (U : X.AffineZariskiSite) :
    U.1.ι ≫ inv (AffineZariskiSite.relativeGluingData
      (coequifibered_id_restrict (X := X))).toBase =
      U.2.isoSpec.hom ≫ colimit.ι (AffineZariskiSite.relativeGluingData
        (coequifibered_id_restrict (X := X))).functor U := by
  rw [IsIso.comp_inv_eq, Category.assoc, Scheme.Cover.RelativeGluingData.ι_toBase]
  simp [AffineZariskiSite.relativeGluingData, AffineZariskiSite.restrictIsoSpec]

/-- In the chart `symSpecChart`, the zero section of `Spec_X (Sym^• ℰ)` is the zero section of
`𝔸^c_U`. -/
lemma exists_symSpecChart_zeroSection [F.IsQuasicoherent] {c : ℕ} (U : X.AffineZariskiSite)
    (b : Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)) :
    ∃ σ : U.1.toScheme ⟶ Limits.pullback F.symSpecProj U.1.ι,
      σ ≫ Limits.pullback.fst F.symSpecProj U.1.ι = U.1.ι ≫ F.symSpecZeroSection ∧
      σ ≫ Limits.pullback.snd F.symSpecProj U.1.ι = 𝟙 _ ∧
      σ ≫ (F.symSpecChart U b).hom = AffineSpace.zeroSection (ULift.{u} (Fin c)) U.1 := by
  refine ⟨AffineSpace.zeroSection _ _ ≫ (F.symSpecChart U b).inv, ?_, ?_, by simp⟩
  · simp only [symSpecChart, Iso.trans_inv, Iso.symm_inv, asIso_inv, Category.assoc]
    erw [IsPullback.isoPullback_hom_fst]
    change AffineSpace.zeroSection _ _ ≫ AffineSpace.map _ U.2.isoSpec.hom ≫ _ = _
    rw [← Category.assoc (AffineSpace.zeroSection _ _), AffineSpace.zeroSection_comp_map,
      Category.assoc, zeroSection_Spec_eq, Category.assoc, Iso.inv_hom_id_assoc,
      symSpecZeroSection, ← Category.assoc U.1.ι, ι_inv_toBase_id, Category.assoc,
      AffineZariskiSite.ι_relativeGluingMap]
    congr 1
    rw [← symChartRingHom_comp_algebraMapInv F U b, Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
    rfl
  · rw [Category.assoc, ← symSpecChart_hom_over F U b, Iso.inv_hom_id_assoc,
      AffineSpace.zeroSection_over]

end AlgebraicGeometry.Scheme.Modules

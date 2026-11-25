/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension

import Mathlib.RingTheory.Localization.BaseChange

/-! # Normalized finite-stage and embedding scalar extension

## Main definitions

- `pbcFiniteRawScalarComparison`: the integral-normalized comparison between the
  StageSystem transition and raw scalar tensor on the same small coefficient fields.

## References

* Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
* Stacks 03EK and 0D6D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rawScalar_naturality
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) {D : Type*} [Category D]
    (F G : ScalarLocalization R C p ⥤ D)
    (a : ∀ K : C, F.obj ⟨K⟩ ⟶ G.obj ⟨K⟩)
    (ha : ∀ {K L : C} (f : K ⟶ L),
      F.map ((ScalarLocalization.localization R C p).map f) ≫ a L =
        a K ≫ G.map ((ScalarLocalization.localization R C p).map f))
    (K L : C) (f : ScalarLocalization.mk (R := R) (p := p) K ⟶ ⟨L⟩) :
    F.map f ≫ a L = a K ≫ G.map f := by
  let Q := ScalarLocalization.localization R C p
  obtain ⟨⟨u, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers p)
    (TensorProduct.mk R (Localization.Away p) (K ⟶ L) 1) f
  have hs' : (s : R) • f = Q.map u := hs
  obtain ⟨v, hv⟩ := IsLocalization.map_units (Localization.Away p) s
  let z : Q.obj K ≅ Q.obj K :=
    { hom := (v : Localization.Away p) • 𝟙 _
      inv := (↑(v⁻¹) : Localization.Away p) • 𝟙 _
      hom_inv_id := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
          Units.inv_mul, one_smul]
      inv_hom_id := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
          Units.mul_inv, one_smul] }
  have hz : Q.map ((s : R) • 𝟙 K) = z.hom := by
    change (1 : Localization.Away p) ⊗ₜ[R] ((s : R) • 𝟙 K) =
      (v : Localization.Away p) • ((1 : Localization.Away p) ⊗ₜ[R] (𝟙 K))
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [TensorProduct.tmul_smul, hv]
    change (s : R) • ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) = _
    rw [TensorProduct.smul_tmul' (s : R), Algebra.smul_def, mul_one]
  let : IsIso (Q.map ((s : R) • 𝟙 K)) := by
    rw [hz]
    exact z.isIso_hom
  have hf : Q.map ((s : R) • 𝟙 K) ≫ f = Q.map u := by
    simpa only [Q.map_smul, Q.map_id, Linear.smul_comp, Category.id_comp] using hs'
  apply (cancel_epi (F.map (Q.map ((s : R) • 𝟙 K)))).1
  rw [← F.map_comp_assoc, hf, ha u, ← hf, G.map_comp, ← Category.assoc,
    ← ha ((s : R) • 𝟙 K), Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rawScalar_comparison
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) {D : Type*} [Category D]
    (F G : ScalarLocalization R C p ⥤ D) (J : C ⥤ D)
    (e : ScalarLocalization.localization R C p ⋙ F ≅ J)
    (hJ : J = ScalarLocalization.localization R C p ⋙ G) :
    ∃! c : F ≅ G, ∀ K : C, HEq (c.hom.app ⟨K⟩) (e.hom.app K) := by
  subst J
  let c : F ≅ G := NatIso.ofComponents (fun K ↦ e.app K.obj)
    (fun {K L} f ↦ rawScalar_naturality p F G (fun K ↦ e.hom.app K)
      (fun f ↦ e.hom.naturality f) K.obj L.obj f)
  refine ⟨c, fun _ ↦ HEq.rfl, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq (hc' K.obj)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rawScalar_levelConstant_hom (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison T d n).hom =
      AdicCoefficients.constantComparison T (A ⧸ d.ideal ^ (n + 1)) := by
  let := d.quotientFinite
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T d).obj (Opposite.op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec U b

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian T] dT iT in
private theorem rawScalar_coefficientMap :
    pbcCompletedScalarMap l Ω T h =
      pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T := by
  have hq (n : ℕ) : pbcQuotientInclusion.{u} l Ω h n =
      pbcScalarQuotientMap l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) n := by
    rfl
  have hf (n : ℕ) : pbcFiniteScalarMap l Ω T h n =
      AdicCoefficients.coefficientMap T
        (pbcScalarQuotientMap l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) n) := by
    dsimp only [pbcFiniteScalarMap]
    rw [hq]
    apply (Iso.inv_comp_eq (pbcLevelConstantComparison T (pbcStageDatum l Ω E) n)).mpr
    rw [rawScalar_levelConstant_hom, rawScalar_levelConstant_hom]
    change (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _ =
      (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  apply (pbcCompletedScalarMap_exists l Ω T h).unique
  · exact (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec
  · intro n
    rw [hf]
    exact (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T).exists.choose_spec n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rawScalar_integralTensor :
    pbcIntegralScalarExtension l Ω T dT.out iT.out h =
      pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T dT.out iT.out := by
  unfold pbcIntegralScalarExtension pbcEmbeddingIntegralTensor
    pbcAmbientScalarExtension pbcEmbeddingAmbientTensor
  congr 2
  exact congrArg (fun φ ↦ pbcDerivedExtend φ) (rawScalar_coefficientMap l Ω T h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two finite-field scalar constructions have a unique integral-normalized
comparison. HEq retains the canonical equality of the quotient-normalized
coefficient maps and hence of their actual derived tensor objects. -/
theorem pbcFiniteRawScalarComparison_existsUnique :
    ∃! c : (pbcScalarSystem l Ω T dT.out iT.out).T h ≅
        pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h)
          T dT.out iT.out,
      ∀ K : pbcIntegralStage l Ω T E,
        HEq (c.hom.app ((pbcStageLocalization l Ω T E).obj K))
          ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app K) := by
  have hJ : pbcIntegralScalarExtension l Ω T dT.out iT.out h ⋙
      pbcStageLocalization l Ω T F =
      pbcStageLocalization l Ω T E ⋙
        pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T dT.out iT.out := by
    rw [rawScalar_integralTensor l Ω T h]
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro K L f
    simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
      pbcScalarLocalization_naturality l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T f
  exact rawScalar_comparison (pbcStageUniformizer.{u} l Ω E)
    ((pbcScalarSystem l Ω T dT.out iT.out).T h)
    (pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T dT.out iT.out)
    _ (pbcScalarIntegralComparison l Ω T dT.out iT.out h) hJ

/-- The unique comparison fixed on every integral representative; its identity-field
case is the recorded tensor-multiplication unit, rather than an arbitrary automorphism. -/
def pbcFiniteRawScalarComparison :=
  (pbcFiniteRawScalarComparison_existsUnique l Ω T h).exists.choose

end AlgebraicGeometry.Scheme

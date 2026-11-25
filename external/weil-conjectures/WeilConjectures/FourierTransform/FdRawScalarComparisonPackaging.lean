/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarData

/-! # Packaging raw scalar comparisons on the specified stage systems

Source: trace-definition coefficient-category comparison, localization step 7
(blueprint: lem-fd-raw-scalar-comparison-packaging).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures

-- Keep the cached scalar-localization category abstract, as in its stage-system owner.
attribute [local irreducible] ScalarLocalization.category

-- Bundling the coefficient instances permits equality induction without unfolding their
-- transported field operations inside derived-category constructions.

private structure CoefficientModel (l : ℕ) [Fact l.Prime] (K : Type u) where
  field : Field K
  algebra : letI := field; Algebra ℚ_[l] K
  finite : letI := field; letI := algebra; FiniteDimensional ℚ_[l] K

private theorem CoefficientModel.ext' (l : ℕ) [Fact l.Prime] (K : Type u)
    (a b : CoefficientModel l K) (hf : a.field = b.field)
    (ha : HEq a.algebra b.algebra) : a = b := by
  cases a
  cases b
  cases hf
  cases eq_of_heq ha
  rfl

private abbrev modelCategory (l : ℕ) [Fact l.Prime] (K : Type u)
    (T : Scheme.{u}) (a : CoefficientModel l K) :=
  letI := a.field
  letI := a.algebra
  letI := a.finite
  sfRationalConstructibleCategory l K T

private instance modelCat (l : ℕ) [Fact l.Prime] (K : Type u)
    (T : Scheme.{u}) (a : CoefficientModel l K) : Category (modelCategory l K T a) :=
  letI := a.field
  letI := a.algebra
  letI := a.finite
  inferInstanceAs (Category (sfRationalConstructibleCategory l K T))

private theorem model_obj (l : ℕ) [Fact l.Prime] (K : Type u)
    (T : Scheme.{u}) (a b : CoefficientModel l K) (hab : a = b)
    (c : Category.{u + 2} (modelCategory l K T a))
    (d : Category.{u + 2} (modelCategory l K T b))
    (hcd : HEq c d) {D : Type*} [catD : Category* D]
    (F : @CategoryTheory.Functor (modelCategory l K T a) c D catD)
    (G : @CategoryTheory.Functor (modelCategory l K T b) d D catD)
    (hFG : HEq F G) (X : modelCategory l K T a) (Y : modelCategory l K T b)
    (hXY : HEq X Y) : F.obj X = G.obj Y := by
  subst b
  cases eq_of_heq hcd
  cases eq_of_heq hFG
  cases eq_of_heq hXY
  rfl

private abbrev modelIntegral (l : ℕ) [Fact l.Prime] (K : Type u)
    (T : Scheme.{u}) (a : CoefficientModel l K) :=
  letI := a.field
  letI := a.algebra
  letI := a.finite
  sfIntegralConstructibleCategory l K T

private abbrev modelHom (l : ℕ) [Fact l.Prime] (K L : Type u)
    (a : CoefficientModel l K) (b : CoefficientModel l L) :=
  letI := a.field
  letI := a.algebra
  letI := b.field
  letI := b.algebra
  K →ₐ[ℚ_[l]] L

private abbrev modelLocalization (l : ℕ) [Fact l.Prime] (K : Type u)
    (T : Scheme.{u}) (a : CoefficientModel l K) :=
  letI := a.field
  letI := a.algebra
  letI := a.finite
  sfRationalConstructibleLocalization l K T

private abbrev modelScalar (l : ℕ) [Fact l.Prime] (K L : Type u)
    (T : Scheme.{u}) (a : CoefficientModel l K) (b : CoefficientModel l L)
    (i : modelHom l K L a b) :=
  letI := a.field
  letI := a.algebra
  letI := a.finite
  letI := b.field
  letI := b.algebra
  letI := b.finite
  sfRationalScalarExtension l K T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i

private abbrev modelIntegralScalar (l : ℕ) [Fact l.Prime] (K L : Type u)
    (T : Scheme.{u}) (a : CoefficientModel l K) (b : CoefficientModel l L)
    (i : modelHom l K L a b) :=
  letI := a.field
  letI := a.algebra
  letI := a.finite
  letI := b.field
  letI := b.algebra
  letI := b.finite
  sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) K L i T

private theorem model_scalar_obj (l : ℕ) [Fact l.Prime] (K L : Type u)
    (T : Scheme.{u}) (a a' : CoefficientModel l K) (b b' : CoefficientModel l L)
    (ha : a = a') (hb : b = b')
    (i : modelHom l K L a b) (i' : modelHom l K L a' b') (hi : HEq i i')
    (X : modelCategory l K T a) (Y : modelIntegral l K T a')
    (hX : HEq X ((modelLocalization l K T a').obj Y)) :
    HEq ((modelScalar l K L T a b i).obj X)
      ((modelLocalization l L T b').obj ((modelIntegralScalar l K L T a' b' i').obj Y)) := by
  subst a'
  subst b'
  cases eq_of_heq hi
  cases eq_of_heq hX
  let := a.field
  let := a.algebra
  let := a.finite
  let := b.field
  let := b.algebra
  let := b.finite
  exact heq_of_eq (sfRationalScalarExtension_obj l K T 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i
      ((sfRationalConstructibleLocalization l K T).obj Y))

private def canonicalModel (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E : Padic.FiniteCoefficientFields l Ω) : CoefficientModel l (Shrink.{u} E.val) :=
  ⟨Shrink.instField, Shrink.instAlgebra,
    AlgebraicallyClosedCoefficients.coefficientFinite l Ω E⟩

private def pbcModel (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E : Padic.FiniteCoefficientFields l Ω) : CoefficientModel l (Shrink.{u} E.val) :=
  ⟨pbcFiniteFieldField l Ω E, pbcFiniteFieldAlgebra l Ω E, pbcFiniteFieldFinite l Ω E⟩

private theorem canonicalModel_eq (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E : Padic.FiniteCoefficientFields l Ω) :
    canonicalModel.{u} l Ω E = pbcModel.{u} l Ω E := by
  apply CoefficientModel.ext'
  · rfl
  · exact HEq.rfl

private theorem coefficient_inclusion_heq (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    HEq (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω E L h)
      (pbcFiniteFieldInclusion.{u} l Ω h) := by
  rfl

private theorem canonical_category_heq (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω T E)
      (modelCat l (Shrink.{u} E.val) T (canonicalModel l Ω E)) := by
  dsimp only [GeneralAlgebraicallyClosedCoefficients.stageCategory,
    modelCat, canonicalModel, modelCategory,
    AlgebraicallyClosedCoefficients.Coefficient]
  rfl

private theorem pbc_category_heq (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω T E)
      (modelCat l (Shrink.{u} E.val) T (pbcModel l Ω E)) := by
  apply (canonical_category_heq l Ω T E).trans
  have h := canonicalModel_eq.{u} l Ω E
  generalize canonicalModel.{u} l Ω E = a at h ⊢
  cases h
  rfl

private theorem inverse_heq
    {C : Type*} [Category* C] {X Y X' Y' : C}
    (e : X ≅ Y) (f : X' ≅ Y') (hX : X = X') (hY : Y = Y')
    (h : HEq e.hom f.hom) : HEq e.inv f.inv := by
  subst X'
  subst Y'
  exact heq_of_eq ((Iso.inv_eq_inv e f).mpr (eq_of_heq h))

private theorem transportedComparison_shift
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (F G : C ⥤ D) (h : F = G) (c : G.CommShift ℤ)
    (J : D ⥤ B) [J.CommShift ℤ] (H : C ⥤ B) [H.CommShift ℤ]
    (j : G ⋙ J ≅ H)
    (hj : letI := c; NatTrans.CommShift j.hom ℤ ∧ NatTrans.CommShift j.inv ℤ) :
    letI := cast (congrArg (fun K : C ⥤ D ↦ K.CommShift ℤ) h.symm) c
    NatTrans.CommShift ((Functor.isoWhiskerRight (eqToIso h) J ≪≫ j).symm.hom) ℤ ∧
      NatTrans.CommShift ((Functor.isoWhiskerRight (eqToIso h) J ≪≫ j).symm.inv) ℤ := by
  subst G
  simpa only [eqToIso_refl, Functor.isoWhiskerRight_refl, Iso.refl_trans] using
    (show NatTrans.CommShift j.symm.hom ℤ ∧ NatTrans.CommShift j.symm.inv ℤ from
      ⟨hj.2, hj.1⟩)

private def packageInverseComparison
    {A : Type*} [Preorder A]
    {C D : A → Type*} [∀ i, Category (C i)] [∀ i, Category (D i)]
    (S : StageSystem C) (R : StageSystem D)
    (t : ∀ {i j : A}, i ≤ j → C i ⥤ C j)
    (a : ∀ {i j k : A} (h : i ≤ j) (k : j ≤ k), t h ⋙ t k ≅ t (h.trans k))
    (ht : ∀ i j h, S.T h = t (i := i) (j := j) h)
    (ha : ∀ i j k h k', HEq (S.assoc h k') (a (i := i) (j := j) (k := k) h k'))
    (Φ : ∀ i, C i ⥤ D i)
    (j : ∀ {i k : A} (h : i ≤ k), t h ⋙ Φ k ≅ Φ i ⋙ R.T h)
    (hc : ∀ {i k m : A} (h : i ≤ k) (k' : k ≤ m) (X : C i),
      (j k').hom.app ((t h).obj X) ≫
        (R.T k').map ((j h).hom.app X) ≫ (R.assoc h k').hom.app ((Φ i).obj X) =
      (Φ m).map ((a h k').hom.app X) ≫ (j (h.trans k')).hom.app X) :
    StageSystem.Morphism S R where
  Φ := Φ
  β {i k} h := (Functor.isoWhiskerRight (eqToIso (ht i k h)) (Φ k) ≪≫ j h).symm
  coh := by
    rcases S with ⟨sT, sA, sC⟩
    have hT : @sT = @t := by funext i k h; exact ht i k h
    cases hT
    have hA : @sA = @a := by funext i k m h k'; exact eq_of_heq (ha i k m h k')
    cases hA
    intro i k m h k' X
    simp only [eqToIso_refl, Functor.isoWhiskerRight_refl, Iso.refl_trans,
      Iso.symm_hom]
    rw [← cancel_epi ((R.T k').map ((j h).hom.app X)),
      ← cancel_epi ((j k').hom.app ((t h).obj X))]
    have hh := hc h k' X
    rw [← cancel_mono ((j (h.trans k')).hom.app X)]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Iso.inv_hom_id_app]
    rw [(R.T k').map_id]
    simpa only [Functor.comp_obj, Category.id_comp, Category.comp_id,
      Iso.hom_inv_id_app_assoc] using hh.symm

/-- Convert an already coherent raw inverse comparison into a morphism of the specified
stage systems. This is only presentation transport and inversion of the integral-lift square;
existence of the integral comparison and existence of the raw comparison are inputs.
Source: trace-definition final coefficient-category sentence, localization step 7
(blueprint: lem-fd-raw-scalar-comparison-packaging).

Proof: The specification of GeneralAlgebraicallyClosedCoefficients.stageSystem identifies
its transition functors and associators with scalar and assoc. Transport j inverse along
these equalities. This defines beta with the arrow direction required by StageSystem.Morphism;
its finite functors are family.functor. Precompose the raw inverse cocycle with the two beta
components and cancel j against beta to obtain Morphism.coh. Transport family.shift using
its shift_identity; the stage transition shift is the canonical equality transport of the
specified scalar shift, so both beta shift squares follow from the given j shift squares.
The finite functors and their shifts agree with the supplied stage equivalences, hence are
exact. Transport the raw unit equation to beta inverse. Finally invert the supplied
integral-lift equation: localization preserves inverses and composition, so the inverse of
Q(b inverse) followed by the inverse scalar-integral comparison is the scalar-integral
comparison followed by Q(b). The supplied rational object normalizations identify the
endpoints; only their canonical equality casts occur. This gives the required forward lift.
No pentagon or four-field assertion is assumed or concluded here.
-/
theorem fdRawScalarComparisonPackaging
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (family : RationalFamily l Ω T stage)
    (j : RawComparison l Ω T stage family)
    (hshift : (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
        NatTrans.CommShift (j h).hom ℤ ∧ NatTrans.CommShift (j h).inv ℤ ∧
        (scalar l Ω T h ⋙ J l Ω T stage family L).IsTriangulated ∧
        (J l Ω T stage family E ⋙ (P l Ω T).T h).IsTriangulated))
    (hlift : (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((j h).hom.app K')
          ((pbcStageLocalization l Ω T L).map ((b h).inv.app K) ≫
            (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
              ((I l Ω T stage E).obj K))))
    (hunit : (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq ((j (le_refl E)).hom.app K)
          ((J l Ω T stage family E).map
            ((unit l Ω T E).hom.app K))))
    (hcocycle : (∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j k).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T k).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h k).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family M).map ((assoc l Ω T h k).hom.app K) ≫
          (j (h.trans k)).hom.app K))
    : ∃ (F : StageSystem.Morphism
      (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
      (D := pbcStageCategory l Ω T)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (pbcScalarSystem l Ω T dT.out iT.out))
      (s : ∀ E, (F.Φ E).CommShift ℤ),
      let _ : ∀ E, (F.Φ E).CommShift ℤ := s
      (∀ E, HEq (F.Φ E) (stage E).rational.functor) ∧
      (∀ E (n : ℤ),
    HEq ((F.Φ E).commShiftIso n) ((stage E).rational.functor.commShiftIso n)) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (F.β h).hom ℤ ∧ NatTrans.CommShift (F.β h).inv ℤ) ∧
      (∀ E, (F.Φ E).IsTriangulated) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((F.β (le_refl E)).inv.app K)
      ((F.Φ E).map
        ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E).hom.app K))) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
    (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
    HEq ((F.β h).hom.app K')
      ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app
          ((stage E).integral.functor.obj K) ≫
        (pbcStageLocalization l Ω T L).map ((b h).hom.app K))) := by
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T
  have ht := (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l Ω T).exists.choose_spec.1
  have ha := (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l Ω T).exists.choose_spec.2
  let F := packageInverseComparison S (P l Ω T)
    (fun {_ _} h ↦ scalar l Ω T h) (fun {_ _ _} h k ↦ assoc l Ω T h k)
    ht ha family.functor j hcocycle
  refine ⟨F, family.shift, family.identity, family.shift_identity, ?_, ?_, ?_, ?_⟩
  · intro E L h
    exact transportedComparison_shift _ _ (ht E L h)
      (scalarCommShift l Ω T h) (family.functor L)
      (family.functor E ⋙ (P l Ω T).T h) (j h) ⟨(hshift h).1, (hshift h).2.1⟩
  · intro E
    let A := scalar l Ω T (le_refl E)
    have : A.IsEquivalence := Functor.isEquivalence_of_iso (unit l Ω T E).symm
    have : (A ⋙ family.functor E).IsTriangulated := (hshift (le_refl E)).2.2.1
    exact Functor.isTriangulated_of_precomp A (family.functor E)
  · intro E K
    dsimp only [F, packageInverseComparison]
    simpa only [Iso.symm_inv, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, eqToHom_map,
      eqToHom_comp_heq_iff] using hunit E K
  · intro E L h K K' hK
    have he := hlift h K K' hK
    let q := (pbcStageLocalization l Ω T L).mapIso ((b h).symm.app K) ≪≫
      (pbcScalarIntegralComparison l Ω T dT.out iT.out h).symm.app
        ((I l Ω T stage E).obj K)
    have hscalar := model_scalar_obj l (Shrink.{u} E.val) (Shrink.{u} L.val) T
      (canonicalModel l Ω E) (pbcModel l Ω E)
      (canonicalModel l Ω L) (pbcModel l Ω L)
      (canonicalModel_eq l Ω E) (canonicalModel_eq l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
      (pbcFiniteFieldInclusion l Ω h) (coefficient_inclusion_heq l Ω h) K' K hK
    have hx : ((scalar l Ω T h ⋙ family.functor L).obj K') =
        (pbcStageLocalization l Ω T L).obj
        ((I l Ω T stage L).obj ((U l Ω T h).obj K)) := by
      have hx' := model_obj l (Shrink.{u} L.val) T
        (canonicalModel l Ω L) (pbcModel l Ω L) (canonicalModel_eq l Ω L)
        (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω T L)
        (modelCat l (Shrink.{u} L.val) T (pbcModel l Ω L))
        (pbc_category_heq l Ω T L)
        (family.functor L) (stage L).rational.functor (family.identity L)
        ((scalar l Ω T h).obj K')
        ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω L) T).obj
          ((U l Ω T h).obj K)) hscalar
      exact hx'.trans ((stage L).objects _)
    have hy : ((family.functor E ⋙ (P l Ω T).T h).obj K') =
        (pbcScalarExtension l Ω T dT.out iT.out h).obj
          ((pbcStageLocalization l Ω T E).obj ((I l Ω T stage E).obj K)) := by
      have hy' := model_obj l (Shrink.{u} E.val) T
        (canonicalModel l Ω E) (pbcModel l Ω E) (canonicalModel_eq l Ω E)
        (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω T E)
        (modelCat l (Shrink.{u} E.val) T (pbcModel l Ω E))
        (pbc_category_heq l Ω T E)
        (family.functor E) (stage E).rational.functor (family.identity E) K'
        ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) hK
      change ((P l Ω T).T h).obj ((family.functor E).obj K') = _
      rw [hy', (stage E).objects]
      rfl
    have hi := inverse_heq ((j h).app K') q hx hy he
    dsimp only [F, packageInverseComparison]
    simpa only [Iso.symm_hom, Iso.trans_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, eqToIso.inv, eqToHom_app, eqToHom_map,
      comp_eqToHom_heq_iff, q, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv] using hi

end WeilConjectures

import Langlands.Shimura.Unitary.DiagonalPointNaturality
import Langlands.GroupScheme.InnerAutomorphism

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module Matrix
open scoped CategoryTheory.MonObj Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual diagonal homomorphism from multiplicative-group points to Harris points. -/
def diagonalCocharacterPoints (T : Over (Spec (CommRingCat.of ℂ)))
    (p : (E →+* ℝ) → Fin n → Prop) :
    (T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) →*
      (T ⟶ D.complexRationalGroupScheme.X) :=
  (D.diagonalWeightPointHom C T p).comp (GroupScheme.Gm.pointsEquiv _ T).toMonoidHom

set_option backward.isDefEq.respectTransparency false in
/-- Diagonal cocharacter point homomorphisms are natural on all test schemes. -/
theorem diagonalCocharacterPoints_naturality
    (p : (E →+* ℝ) → Fin n → Prop)
    {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T)
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    D.diagonalCocharacterPoints C T' p (a ≫ x) =
      a ≫ D.diagonalCocharacterPoints C T p x := by
  change D.diagonalWeightPointFamily C T' p (GroupScheme.Gm.pointsEquiv _ T' (a ≫ x)) =
    a ≫ D.diagonalWeightPointFamily C T p (GroupScheme.Gm.pointsEquiv _ T x)
  rw [GroupScheme.Gm.pointsEquiv_naturality, D.diagonalWeightPointFamily_naturality]

/-- The scheme cocharacter with prescribed inverse-weight supports and inverse multiplier. -/
def diagonalCocharacter (p : (E →+* ℝ) → Fin n → Prop) :
    (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme :=
  GroupScheme.homOfPoints (fun T => D.diagonalCocharacterPoints C T p)
    (fun a x => D.diagonalCocharacterPoints_naturality C p a x)

/-- Evaluation of the constructed cocharacter gives the original actual point family. -/
theorem diagonalCocharacter_points (p : (E →+* ℝ) → Fin n → Prop)
    (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    x ≫ (D.diagonalCocharacter C p).hom.hom =
      D.diagonalWeightPointFamily C T p (GroupScheme.Gm.pointsEquiv _ T x) :=
  GroupScheme.comp_homOfPoints _ _ T x

set_option backward.isDefEq.respectTransparency false in
/-- The standard diagonal scheme cocharacter is exactly the first-factor Kottwitz cocharacter. -/
theorem diagonalCocharacter_kottwitz :
    D.diagonalCocharacter C (fun τ j => j.val < if τ = C.distinguished then n - 1 else n) =
      D.kottwitzCocharacter C true := by
  apply GroupScheme.hom_ext_points
  intro T x
  rw [D.diagonalCocharacter_points, D.diagonalWeightPointFamily_kottwitz,
    MulEquiv.symm_apply_apply]

/-- The chosen diagonal conjugator is the pullback of its actual complex point. -/
theorem diagonalWeightPointConjugator_constant
    (p q : (E →+* ℝ) → Fin n → Prop)
    (h : ∀ τ, (Finset.univ.filter (p τ)).card = (Finset.univ.filter (q τ)).card)
    (T : Over (Spec (CommRingCat.of ℂ))) :
    GroupScheme.constantPoint D.complexRationalGroupScheme
      (D.diagonalWeightPointConjugator C (Over.mk (𝟙 _)) p q h) T =
        D.diagonalWeightPointConjugator C T p q h :=
  D.diagonalWeightPointConjugator_naturality C
    (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 _)) p q h

/-- Equal support sizes give conjugacy of actual scheme cocharacters by a complex point. -/
theorem diagonalCocharacter_conjugate_of_card_eq
    (p q : (E →+* ℝ) → Fin n → Prop)
    (h : ∀ τ, (Finset.univ.filter (p τ)).card = (Finset.univ.filter (q τ)).card) :
    D.diagonalCocharacter C p ≫
      (GroupScheme.innerIso D.complexRationalGroupScheme
        (D.diagonalWeightPointConjugator C (Over.mk (𝟙 _)) p q h)).hom =
      D.diagonalCocharacter C q := by
  apply GroupScheme.hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, GroupScheme.comp_innerIso_hom,
    D.diagonalCocharacter_points, D.diagonalCocharacter_points,
    D.diagonalWeightPointConjugator_constant]
  exact D.diagonalWeightPointConjugator_spec C T p q h _

/-- Conjugacy of actual diagonal scheme cocharacters by an actual complex group point. -/
def DiagonalCocharacterConjugate (p q : (E →+* ℝ) → Fin n → Prop) : Prop :=
  ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ D.complexRationalGroupScheme.X,
    D.diagonalCocharacter C p ≫ (GroupScheme.innerIso D.complexRationalGroupScheme g).hom =
      D.diagonalCocharacter C q

set_option backward.isDefEq.respectTransparency false in
/-- Support cardinalities exactly classify these scheme cocharacters up to inner conjugacy. -/
theorem diagonalCocharacterConjugate_iff_card_eq
    (p q : (E →+* ℝ) → Fin n → Prop) :
    D.DiagonalCocharacterConjugate C p q ↔
      ∀ τ, (Finset.univ.filter (p τ)).card = (Finset.univ.filter (q τ)).card := by
  constructor
  · rintro ⟨g, hg⟩
    let T : Over (Spec (CommRingCat.of ℂ)) := Over.mk (𝟙 _)
    let : Nontrivial Γ(T.left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    apply (D.diagonalWeightPointConjugate_iff_card_eq C T p q).mp
    refine ⟨GroupScheme.constantPoint D.complexRationalGroupScheme g T, ?_⟩
    intro u
    have he := congrArg
      (fun f : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
        D.complexRationalGroupScheme => (GroupScheme.Gm.pointsEquiv _ T).symm u ≫ f.hom.hom) hg
    rw [Grp.comp_hom_hom, ← Category.assoc, GroupScheme.comp_innerIso_hom,
      D.diagonalCocharacter_points, D.diagonalCocharacter_points,
      MulEquiv.apply_symm_apply] at he
    exact he
  · intro h
    exact ⟨D.diagonalWeightPointConjugator C (Over.mk (𝟙 _)) p q h,
      D.diagonalCocharacter_conjugate_of_card_eq C p q h⟩

set_option backward.isDefEq.respectTransparency false in
/-- Conjugacy to the actual Kottwitz scheme cocharacter is exactly the signature count condition. -/
theorem diagonalCocharacterConjugate_kottwitz_iff
    (q : (E →+* ℝ) → Fin n → Prop) :
    (∃ g : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ D.complexRationalGroupScheme.X,
      D.kottwitzCocharacter C true ≫ (GroupScheme.innerIso D.complexRationalGroupScheme g).hom =
        D.diagonalCocharacter C q) ↔
      ∀ τ, (Finset.univ.filter (q τ)).card =
        if τ = C.distinguished then n - 1 else n := by
  rw [← D.diagonalCocharacter_kottwitz C]
  change D.DiagonalCocharacterConjugate C
    (fun τ j => j.val < if τ = C.distinguished then n - 1 else n) q ↔ _
  rw [D.diagonalCocharacterConjugate_iff_card_eq]
  apply forall_congr'
  intro τ
  rw [Finset.filter_congr_decidable, Fin.card_filter_val_lt, min_eq_right (by split_ifs <;> omega)]
  exact eq_comm

end Langlands.Shimura.CentralSimpleUnitaryData

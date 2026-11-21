import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelParameterGeometry
import Langlands.AlgebraicGeometry.FlatEquivalenceRelation.Classifier

/-! # The closed locus where sections are the labels of an ordered full level -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {A : AbelianScheme S} {g n : ℕ}

/-- The point with coefficients `r` of a full level on a test scheme, viewed as a
morphism into the original abelian scheme over the base. -/
def FullLevel.label {T : Over S} (v : FullLevel ((baseChange T.hom).obj A) g n)
    (r : Fin (2 * g) → ZMod n) : T ⟶ A.X :=
  Additive.toMul (toSection A.toGrp T n
    (Fintype.linearCombination (ZMod n) (sectionTupleBaseChangeEquiv A g n T.hom v.sections) r))

/-- The label map is the torsion section composed with the projection from the base change. -/
theorem FullLevel.label_left {T : Over S} (v : FullLevel ((baseChange T.hom).obj A) g n)
    (r : Fin (2 * g) → ZMod n) : (v.label r).left =
      (Additive.toMul (enumerateTuple v.sections r)).val.left ≫ pullback.fst A.X.hom T.hom := by
  let e : Level ((baseChange T.hom).obj A).toGrp (Over.mk (𝟙 T.left)) n ≃ₗ[ZMod n]
      Level A.toGrp T n := fibreTorsionLinearEquiv A.toGrp T.hom n
  have he (i : Fin (2 * g)) : sectionTupleBaseChangeEquiv A g n T.hom v.sections i =
      e (v.sections i) := rfl
  have h : Fintype.linearCombination (ZMod n)
        (sectionTupleBaseChangeEquiv A g n T.hom v.sections) r =
      e (enumerateTuple v.sections r) := by
    simp only [enumerateTuple, Fintype.linearCombination_apply, he]
    change (∑ i, r i • e (v.sections i)) = e.toLinearMap (∑ i, r i • v.sections i)
    rw [map_sum e.toLinearMap]
    exact Finset.sum_congr rfl (fun i _ => (e.map_smul (r i) (v.sections i)).symm)
  unfold FullLevel.label
  rw [h]
  change (𝟙 _ ≫ (Additive.toMul (enumerateTuple v.sections r)).val.left) ≫ _ = _
  rw [Category.id_comp]
  rfl

private theorem FullLevel.eq_of_labels {T : Over S}
    {v w : FullLevel ((baseChange T.hom).obj A) g n}
    (h : ∀ r, v.label r = w.label r) : v = w := by
  have hsections : v.sections = w.sections := by
    funext i
    apply (fibreTorsionLinearEquiv A.toGrp T.hom n).injective
    apply toSection_injective A.toGrp T n
    apply Additive.toMul.injective
    simpa [FullLevel.label, Fintype.linearCombination_apply, sectionTupleBaseChangeEquiv] using
      h (Pi.single i 1)
  cases v
  cases w
  cases hsections
  rfl

variable (A g n)
variable (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤)))

local notation "F" => fullLevelParameterScheme A g n hn hu
local notation "decoded" => fullLevelParameterHomEquiv A g n hn hu

private theorem decoded_label_comp {T T' : Over S} (f : T' ⟶ T) (q : T ⟶ F)
    (r : Fin (2 * g) → ZMod n) :
    (decoded T' (f ≫ q)).label r = f ≫ (decoded T q).label r := by
  have h : Fintype.linearCombination (ZMod n)
        (sectionTupleBaseChangeEquiv A g n T'.hom (decoded T' (f ≫ q)).sections) r =
      levelRestrict A.toGrp f n (Fintype.linearCombination (ZMod n)
        (sectionTupleBaseChangeEquiv A g n T.hom (decoded T q).sections) r) := by
    simp only [Fintype.linearCombination_apply, map_sum, ZMod.map_smul,
      fullLevelParameterHomEquiv_comp]
  unfold FullLevel.label
  rw [h, toSection_levelRestrict]

private theorem equalizer_ker_le_iff {Y Q B : Over S} [IsSeparated Y.hom]
    (p q : B ⟶ Y) (f : Q ⟶ B) :
    (equalizer.ι p q).left.ker ≤ f.left.ker ↔ f ≫ p = f ≫ q := by
  rw [FlatEquivalenceRelation.ker_le_ker_iff_exists]
  constructor
  · rintro ⟨l, hl⟩
    have hbase : l ≫ (equalizer p q).hom = Q.hom := by
      rw [← (equalizer.ι p q).w, ← Category.assoc, hl, f.w]
    have hf : Over.homMk l hbase ≫ equalizer.ι p q = f := by
      apply Over.OverMorphism.ext
      exact hl
    rw [← hf, Category.assoc, Category.assoc, equalizer.condition]
  · intro h
    exact ⟨(equalizer.lift f h).left, congrArg Over.Hom.left (equalizer.lift_ι f h)⟩

variable (α : (Fin (2 * g) → ZMod n) → (Over.mk (𝟙 S) ⟶ A.X))

private def parameterMark (r : Fin (2 * g) → ZMod n) : F ⟶ A.X :=
  (Over.homMk (F).hom (by simp) : F ⟶ Over.mk (𝟙 S)) ≫ α r

/-- Inside the scheme of full levels, cut out the equality of every labelled section with
its given mark. The ideal uses relative equalizers over the base. -/
def markedFullLevelIdeal : (F).left.IdealSheafData :=
  ⨆ r, (equalizer.ι ((decoded F (𝟙 F)).label r) (parameterMark A g n hn hu α r)).left.ker

private theorem markedFullLevelIdeal_le_ker_iff {T : Scheme.{u}} (t : T ⟶ S) (f : Over.mk t ⟶ F) :
    markedFullLevelIdeal A g n hn hu α ≤ f.left.ker ↔
      ∀ r, ((decoded (Over.mk t) f).label r).left = t ≫ (α r).left := by
  rw [markedFullLevelIdeal, iSup_le_iff]
  refine forall_congr' fun r => (equalizer_ker_le_iff _ _ f).trans ?_
  rw [← decoded_label_comp A g n hn hu f (𝟙 F) r, Category.comp_id]
  constructor
  · intro h
    have h' := congrArg Over.Hom.left h
    simpa only [Over.comp_left, parameterMark, Over.homMk_left, ← Category.assoc, f.w,
      Over.mk_hom] using h'
  · intro h
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, parameterMark, Over.homMk_left, ← Category.assoc, f.w,
      Over.mk_hom] using h

include hn hu in
/-- Over a base with invertible level, the condition that all the specified marks are
induced by a full level is represented by a closed immersion. -/
theorem exists_closed_markedFullLevelLocus :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsClosedImmersion j ∧
      ∀ (T : Scheme.{u}) (t : T ⟶ S), (∃ l : T ⟶ Z, l ≫ j = t) ↔
        ∃ v : FullLevel ((baseChange t).obj A) g n,
          ∀ r, (Additive.toMul (enumerateTuple v.sections r)).val.left ≫
            pullback.fst A.X.hom t = t ≫ (α r).left := by
  let J := markedFullLevelIdeal A g n hn hu α
  let j := J.subschemeι ≫ (F).hom
  have hmem {T : Scheme.{u}} (t : T ⟶ S) (l : T ⟶ J.subscheme) (hl : l ≫ j = t) :
      ∀ r, ((decoded (Over.mk t) (Over.homMk (l ≫ J.subschemeι)
        ((Category.assoc _ _ _).trans hl))).label r).left = t ≫ (α r).left :=
    (markedFullLevelIdeal_le_ker_iff A g n hn hu α t _).mp
      (J.ker_subschemeι.ge.trans (l.le_ker_comp _))
  have hjmono : Mono j := by
    constructor
    intro T l₁ l₂ h
    apply (cancel_mono J.subschemeι).mp
    let t := l₁ ≫ j
    let f₁ : Over.mk t ⟶ F := Over.homMk (l₁ ≫ J.subschemeι) (Category.assoc _ _ _)
    let f₂ : Over.mk t ⟶ F := Over.homMk (l₂ ≫ J.subschemeι) ((Category.assoc _ _ _).trans h.symm)
    have hf : f₁ = f₂ := by
      apply (decoded (Over.mk t)).injective
      apply FullLevel.eq_of_labels
      intro r
      apply Over.OverMorphism.ext
      exact (hmem t l₁ rfl r).trans (hmem t l₂ h.symm r).symm
    exact congrArg Over.Hom.left hf
  have : IsFinite (F).hom := (fullLevelParameterScheme_finiteEtale A g n hn hu).1
  have hclosed : IsClosedImmersion j := (IsClosedImmersion.iff_isFinite_and_mono j).mpr
    ⟨inferInstanceAs (IsFinite (J.subschemeι ≫ (F).hom)), hjmono⟩
  refine ⟨J.subscheme, j, hclosed, fun T t => ?_⟩
  constructor
  · rintro ⟨l, hl⟩
    let f : Over.mk t ⟶ F := Over.homMk (l ≫ J.subschemeι) ((Category.assoc _ _ _).trans hl)
    refine ⟨decoded (Over.mk t) f, fun r => ?_⟩
    exact (FullLevel.label_left (T := Over.mk t) (decoded (Over.mk t) f) r).symm.trans
      (hmem t l hl r)
  · rintro ⟨v, hv⟩
    let f := (decoded (Over.mk t)).symm v
    have hker : J ≤ f.left.ker := (markedFullLevelIdeal_le_ker_iff A g n hn hu α t f).mpr (by
      dsimp only [f]
      rw [Equiv.apply_symm_apply]
      intro r
      exact (FullLevel.label_left (T := Over.mk t) v r).trans (hv r))
    obtain ⟨l, hl⟩ := (FlatEquivalenceRelation.ker_le_ker_iff_exists J.subschemeι f.left).mp
      (J.ker_subschemeι.le.trans hker)
    refine ⟨l, ?_⟩
    change l ≫ J.subschemeι ≫ (F).hom = t
    rw [← Category.assoc, hl]
    exact f.w

end Langlands.AbelianScheme.PolarizedFiniteLevel

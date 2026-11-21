import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.ClosedEqualizerFamily
import Langlands.AlgebraicGeometry.PointTopology.DenseRationalFibres
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.GroupScheme.TranslationLaws

/-! # The finite subgroup of translation periods of a finite map -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

private def translationPeriods {S : Scheme.{u}} {G : GroupScheme S} {W : Over S}
    (F : G.X ⟶ W) : GroupScheme.SubgroupFunctor G where
  carrier T :=
    { carrier := {g | ∀ (T' : Over S) (b : T' ⟶ T) (a : T' ⟶ G.X),
        ((b ≫ g) * a) ≫ F = a ≫ F}
      one_mem' := fun T' b a ↦ by rw [MonObj.comp_one, one_mul]
      mul_mem' := by
        intro g h hg hh T' b a
        change ((b ≫ (g * h)) * a) ≫ F = a ≫ F
        rw [MonObj.comp_mul, mul_assoc, hg T' b _, hh T' b a]
      inv_mem' := by
        intro g hg T' b a
        have he := hg T' b ((b ≫ g)⁻¹ * a)
        rw [← mul_assoc, mul_inv_cancel, one_mul] at he
        rw [GrpObj.comp_inv]
        exact he.symm }
  comp_mem {T T'} b {g} hg := fun T'' c a ↦ by
    simpa only [Category.assoc] using hg T'' (c ≫ b) a

private lemma mul_const_eq_comp_translation {S : Scheme.{u}} (A : AbelianScheme S)
    {T : Over S} (x : T ⟶ A.X) (p : Over.mk (𝟙 S) ⟶ A.X) :
    x * (toUnit T ≫ p) = x ≫ GroupScheme.translation A.toGrp p := by
  have h : Over.mkIdTerminal.from T = toUnit T := Over.mkIdTerminal.hom_ext _ _
  rw [GroupScheme.points_translation, h]
  exact mul_comm x (toUnit T ≫ p)

/-- A finite map from an abelian variety to a separated scheme has a finite
closed subgroup of translation periods. Translations are detected by any
Zariski-dense family of rational points, including on nonreduced tests. -/
abbrev FiniteTranslationPeriodsStatement : Prop :=
  ∀ {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))) [IsReduced A.X.left]
    {W : Over (Spec (CommRingCat.of K))} [IsSeparated W.hom] (F : A.X ⟶ W) [IsFinite F.left]
    {J : Type v} (p : J → RationalPoint K A.X), HasDenseRationalPointFamily p →
    ∃ (H : GroupScheme (Spec (CommRingCat.of K))) (i : H ⟶ A.toGrp),
      IsClosedImmersion i.hom.hom.left ∧ IsFinite H.X.hom ∧
      (∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X) (a : T ⟶ A.X),
        ((h ≫ i.hom.hom) * a) ≫ F = a ≫ F) ∧
      ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ A.X),
        (∀ k, x ≫ GroupScheme.translation A.toGrp (p k) ≫ F = toUnit T ≫ p k ≫ F) ↔
          ∃ h : T ⟶ H.X, h ≫ i.hom.hom = x

set_option backward.isDefEq.respectTransparency.types false in
/-- Take the closed simultaneous equalizer of translated and constant maps.
It lies in a finite fibre. On its product with the abelian variety, the dense
rational fibres show invariance under the universal period. -/
theorem exists_finiteTranslationPeriods : FiniteTranslationPeriodsStatement.{u, v} := by
  intro K _ A _ W _ F _ J p hp
  let S := Spec (CommRingCat.of K)
  let f (k : J) : A.X ⟶ W := GroupScheme.translation A.toGrp (p k) ≫ F
  let g (k : J) : A.X ⟶ W := toUnit A.X ≫ p k ≫ F
  let D := simultaneousEqualizer f g
  let e := simultaneousEqualizerι f g
  have : IsClosedImmersion e.left := inferInstanceAs (IsClosedImmersion (simultaneousEqualizerι f g).left)
  have : Mono e := Over.mono_of_mono_left e
  have he (k : J) : e ≫ f k = e ≫ g k := simultaneousEqualizer_condition f g k
  have hfin : IsFinite D.hom := by
    have hd : Dense (⋃ k : J, Set.range (p k).left) := hp
    let a := (1 : RationalPoint K A.X).left (IsLocalRing.closedPoint K)
    obtain ⟨_, -, hz⟩ := hd.inter_open_nonempty _ isOpen_univ ⟨a, Set.mem_univ _⟩
    obtain ⟨k, -, -⟩ := Set.mem_iUnion.mp hz
    have : IsIso (GroupScheme.translation A.toGrp (p k)).left :=
      inferInstanceAs (IsIso ((Over.forget S).map (GroupScheme.CommonAffine.translationIso A.toGrp (p k)).hom))
    have : IsFinite (f k).left :=
      inferInstanceAs (IsFinite ((GroupScheme.translation A.toGrp (p k)).left ≫ F.left))
    let b := (p k ≫ F).left
    have : IsClosedImmersion b := isClosedImmersion_of_comp_eq_id W.hom b (Over.w (p k ≫ F))
    have hfac : e.left ≫ (f k).left = D.hom ≫ b := by
      have hc := congrArg (fun q ↦ q.left) (he k)
      change e.left ≫ (f k).left = e.left ≫ A.X.hom ≫ b at hc
      calc
        _ = e.left ≫ A.X.hom ≫ b := hc
        _ = (e.left ≫ A.X.hom) ≫ b := (Category.assoc _ _ _).symm
        _ = _ := congrArg (fun m ↦ m ≫ b) (Over.w e)
    let v := pullback.lift e.left D.hom hfac
    have hv : v ≫ pullback.fst (f k).left b = e.left := pullback.lift_fst _ _ _
    have : IsClosedImmersion (v ≫ pullback.fst (f k).left b) := hv ▸ inferInstanceAs (IsClosedImmersion e.left)
    have : IsClosedImmersion v := IsClosedImmersion.of_comp_isClosedImmersion v (pullback.fst (f k).left b)
    rw [← pullback.lift_snd e.left D.hom hfac]
    infer_instance
  have : IsAffine D.left := isAffine_of_isAffineHom D.hom
  let a : D ⊗ A.X ⟶ W := ((fst D A.X ≫ e) * snd D A.X) ≫ F
  let b : D ⊗ A.X ⟶ W := snd D A.X ≫ F
  have hperiod : a = b := by
    apply hom_ext_of_denseRationalFibres p hp
    intro k
    let r : D ⟶ D ⊗ A.X := lift (𝟙 D) (toUnit D ≫ p k)
    calc
      r ≫ a = (e * (toUnit D ≫ p k)) ≫ F := by
        simp only [a, r, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp]
      _ = e ≫ f k := by
        rw [mul_const_eq_comp_translation A]
        exact Category.assoc _ _ _
      _ = e ≫ g k := he k
      _ = r ≫ b := by
        change e ≫ toUnit A.X ≫ p k ≫ F = r ≫ snd D A.X ≫ F
        rw [comp_toUnit_assoc, lift_snd_assoc]
        rfl
  have htest (T : Over S) (c : T ⟶ D) (d : T ⟶ A.X) : ((c ≫ e) * d) ≫ F = d ≫ F := by
    calc
      _ = lift c d ≫ a := by
        simp only [a, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd]
      _ = lift c d ≫ b := by rw [hperiod]
      _ = _ := lift_snd_assoc _ _ _
  let P := translationPeriods F
  have hrep (T : Over S) (x : T ⟶ A.X) : x ∈ P.carrier T ↔ ∃ y : T ⟶ D, y ≫ e = x := by
    constructor
    · intro hx
      refine ⟨simultaneousEqualizerLift f g x ?_, simultaneousEqualizerLift_ι f g _ _⟩
      intro k
      change ∀ (T' : Over S) (c : T' ⟶ T) (d : T' ⟶ A.X),
        ((c ≫ x) * d) ≫ F = d ≫ F at hx
      have hk := hx T (𝟙 T) (toUnit T ≫ p k)
      rw [Category.id_comp, mul_const_eq_comp_translation A, Category.assoc] at hk
      simpa only [f, g, Category.assoc, comp_toUnit_assoc] using hk
    · rintro ⟨y, rfl⟩
      intro T' c d
      simpa only [Category.assoc] using htest T' (c ≫ y) d
  let H := P.representingGroupScheme e hrep
  let i := P.representingHom e hrep
  have hi : i.hom.hom = e := P.representingHom_hom e hrep
  refine ⟨H, i, ?_, hfin, ?_, ?_⟩
  · rw [hi]
    infer_instance
  · intro T h d
    rw [hi]
    exact htest T h d
  · intro T x
    rw [hi]
    constructor
    · intro hx
      refine ⟨simultaneousEqualizerLift f g x ?_, simultaneousEqualizerLift_ι f g _ _⟩
      intro k
      simpa only [f, g, Category.assoc, comp_toUnit_assoc] using hx k
    · rintro ⟨y, rfl⟩ k
      calc
        _ = y ≫ e ≫ f k := Category.assoc _ _ _
        _ = y ≫ e ≫ g k := congrArg (fun m ↦ y ≫ m) (he k)
        _ = _ := by
          change y ≫ e ≫ toUnit A.X ≫ p k ≫ F = _
          rw [comp_toUnit_assoc e, comp_toUnit_assoc y]

end Langlands.AbelianScheme

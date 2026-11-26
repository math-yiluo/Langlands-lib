import Langlands.AbelianScheme.PolarizedFiniteLevel.AlgebraicallyClosedFieldPolarizationDivisionStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleMumfordProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.KernelTensorPowerDescent
import Langlands.GroupScheme.SimplyConnected.SplitPicardTrivialCoverReduction
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricCardinality
import Langlands.AlgebraicGeometry.Picard.MumfordMapPicardClass
import Langlands.AlgebraicGeometry.Picard.MumfordSchemeMapHomomorphismProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingProof
import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleReflection
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualMultiplication
import Langlands.AbelianScheme.MultiplicationIsogenyProof
import Langlands.AbelianScheme.IsogenyActionDescent
import Langlands.GroupScheme.TranslationLaws

/-! # Positive-multiple descent of ample Mumford presentations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (isoClass pullbackHom)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev overHom {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B) : A.X ⟶ B.X :=
  (groupHom f).hom.hom

private abbrev bundlePower {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) : LineBundle X :=
  ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩

private structure Normalization (P : Prerequisites.{u}) {S : Scheme.{u}} (A : AbelianScheme S)
    (L : LineBundle A.X.left) where
  baseInverse : LineBundle S
  baseEvaluation : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj)
    baseInverse.obj ≅ structureSheaf S
  inverse : LineBundle A.X.left
  evaluation : tensorObj (LineBundle.normalize P.preservation A.X.hom (unitSection A)
    (unitSection_comp A) L baseInverse baseEvaluation).obj.carrier inverse.obj ≅
      structureSheaf A.X.left

private def Normalization.ofBundle {P : Prerequisites.{u}} {S : Scheme.{u}} {A : AbelianScheme S}
    (L : LineBundle A.X.left) : Normalization P A L :=
  let B := (LineBundle.pullback (unitSection A)).obj L
  let N := (RigidifiedLineBundle.forget _).obj
    (LineBundle.normalize P.preservation A.X.hom (unitSection A) (unitSection_comp A) L
      B.inverse B.tensorInverseIso)
  ⟨B.inverse, B.tensorInverseIso, N.inverse, N.tensorInverseIso⟩

variable {P : Prerequisites.{u}} {K : Type u} [Field K]
  {A : AbelianScheme (Spec (CommRingCat.of K))} (W : DualWitness A)
  {L M : LineBundle A.X.left}

private abbrev Normalization.map (d : Normalization P A L) : A.X ⟶ (W.dual P).X :=
  mumfordSchemeMapOfLineBundle P.preservation A L d.baseInverse d.baseEvaluation d.inverse
    d.evaluation P.square W.hasDual

private def Normalization.hom (d : Normalization P A L) : A ⟶ W.dual P :=
  mumfordHomOfLineBundle P.preservation A L d.baseInverse d.baseEvaluation d.inverse
    d.evaluation P.square W.hasDual P.composition P.unitCoherence P.associativity P.comparison
    P.symmetry P.stability
    (relativeMumfordSchemeMapHomomorphism P.preservation P.stability P.square _ A _ _
      d.evaluation W.hasDual) W.inverseBundle W.evaluation W.geometry

private lemma Normalization.overHom_hom (d : Normalization P A L) :
    overHom (d.hom W) = d.map W := rfl

private lemma Normalization.map_pow (d : Normalization P A L) (e : Normalization P A M) (n : ℕ)
    (h : isoClass P.preservation M = isoClass P.preservation L ^ n) :
    e.map W = d.map W ^ n :=
  mumfordSchemeMapOfLineBundle_eq_pow_of_isoClass P A W L d.baseInverse d.baseEvaluation
    d.inverse d.evaluation M e.baseInverse e.baseEvaluation e.inverse e.evaluation n h

private lemma Normalization.map_pullback (d : Normalization P A L) (q : A ⟶ A)
    (d' : Normalization P A ((LineBundle.pullback (AbelianScheme.hom q)).obj L)) :
    d'.map W = overHom q ≫ d.map W ≫ overHom (W.map P W q) := by
  let p : Rosati.Prerequisites.{u} :=
    ⟨P.preservation, P.composition, P.unitCoherence, P.associativity, P.comparison,
      P.symmetry, P.stability, P.square, P.universality⟩
  let w : Rosati.DualData A := ⟨W.hasDual, W.geometry, W.inverseBundle, W.evaluation⟩
  apply MumfordPicardClass.pointClass_injective p A w A.X
  calc
    _ = _ := (MumfordPicardClass.pointClass_mumfordSchemeMapOfLineBundle p A w _
      d'.baseInverse d'.baseEvaluation d'.inverse d'.evaluation).trans
        (MumfordPicardClass.classOf_mumfordFamily p K A _ d'.baseInverse
          d'.baseEvaluation d'.inverse d'.evaluation)
    _ = _ := (MumfordPicardClass.pointClass_comp_mumford_comp_dual p K A q L d.baseInverse
      d.baseEvaluation d.inverse d.evaluation w).symm

private lemma multiplication_isIsogeny (A : AbelianScheme (Spec (CommRingCat.of K)))
    {n : ℕ} (hn : 0 < n) : IsIsogeny (multiplication A (n : ℤ)) :=
  isIsogeny_multiplication_of_statement GroupScheme.multiplicationIsogeny A _ (by exact_mod_cast hn.ne')

private lemma multiplication_comp_eq_nsmul {S : Scheme.{u}} {A B : AbelianScheme S}
    (f : A ⟶ B) (n : ℕ) : multiplication A (n : ℤ) ≫ f = n • f := by
  rw [multiplication, natCast_zsmul, Preadditive.nsmul_comp, Category.id_comp]

private lemma dual_multiplication (n : ℕ) :
    W.map P W (multiplication A (n : ℤ)) = multiplication (W.dual P) (n : ℤ) :=
  relativeDualAbelianSchemeMap_multiplication P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability W.hasDual
    W.inverseBundle W.evaluation W.geometry (n : ℤ)

private lemma Normalization.sameMumford_ample [IsAlgClosed K]
    (d : Normalization P A L) (e : Normalization P A M) (h : d.map W = e.map W)
    (hL : L.IsAmple) : M.IsAmple := by
  let D := LineBundle.tensor P.preservation M L.inverse
  have hInv : isoClass P.preservation L.inverse = (isoClass P.preservation L)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← LineBundle.isoClass_tensor]
    exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ L.tensorInverseIso)
  have hD : GroupScheme.IsTranslationInvariant A.toGrp D := by
    intro x
    let z : A.X ⟶ A.X := Over.mkIdTerminal.from A.X ≫ x
    have htr : z * 𝟙 A.X = GroupScheme.translation A.toGrp x := rfl
    have h0 (F : LineBundle A.X.left) :
        pullbackHom P.preservation z.left (isoClass P.preservation F) = 1 :=
      LineBundle.pullbackHom_eq_one_of_factor P.preservation A.X.hom x.left (by simp [z]) _
    have h1 := familyPointClass_mumfordSchemeMap_of_unique P A W L d.baseInverse
      d.baseEvaluation d.inverse d.evaluation z (𝟙 A.X)
    have h2 := familyPointClass_mumfordSchemeMap_of_unique P A W M e.baseInverse
      e.baseEvaluation e.inverse e.evaluation z (𝟙 A.X)
    change familyPointClass P.preservation A (poincareFamily A W.hasDual) (z ≫ d.map W)
      (𝟙 A.X) = _ at h1
    change familyPointClass P.preservation A (poincareFamily A W.hasDual) (z ≫ e.map W)
      (𝟙 A.X) = _ at h2
    rw [h, h2] at h1
    simp only [htr, h0, Over.id_left, LineBundle.pullbackHom_id, inv_one, mul_one] at h1
    apply (LineBundle.isoClass_eq_iff (preservation := P.preservation)).mp
    rw [← LineBundle.pullbackHom_isoClass]
    simp only [D, LineBundle.isoClass_tensor, hInv, map_mul, map_inv]
    apply mul_inv_eq_mul_inv_iff_mul_eq_mul.mpr
    rw [mul_comm (isoClass P.preservation M)]
    exact mul_inv_eq_mul_inv_iff_mul_eq_mul.mp h1
  obtain ⟨x, ⟨i⟩⟩ := algClosedFieldTranslationDifferenceLifting P.preservation K A L
    L.inverse L.tensorInverseIso D hL hD
  have hi := LineBundle.isoClass_eq_of_iso (preservation := P.preservation) i
  rw [LineBundle.isoClass_tensor, LineBundle.isoClass_tensor, mul_left_inj] at hi
  obtain ⟨e'⟩ := LineBundle.isoClass_eq_iff.mp hi
  let t := (GroupScheme.translation A.toGrp x).left
  let : IsIso t := (Over.forget _).map_isIso (GroupScheme.CommonAffine.translationIso A.toGrp x).hom
  exact (closedImmersionPullbackAmple _ _ t L inferInstance hL).of_iso
    ((LineBundle.forget _).mapIso e')

private theorem divide_of_descended [IsAlgClosed K] (mu : A ⟶ W.dual P) {n : ℕ}
    (hn : 0 < n) (d : Normalization P A L) (hm : overHom (n • mu) = d.map W)
    (hL : L.IsAmple) (M : LineBundle A.X.left)
    (I : (LineBundle.pullback (hom (multiplication A (n : ℤ)))).obj M ≅ bundlePower L n) :
    HasAmpleMumfordPresentation P.preservation P.square A W.hasDual (overHom mu) := by
  let q := multiplication A (n : ℤ)
  have hq : IsIsogeny q := multiplication_isIsogeny A hn
  let e : Normalization P A M := Normalization.ofBundle M
  let d' : Normalization P A ((LineBundle.pullback (hom q)).obj M) := Normalization.ofBundle _
  have hpow : d'.map W = d.map W ^ n := d.map_pow W d' n
    ((LineBundle.isoClass_eq_of_iso I).trans (isoClass_tensorPow P.preservation L n))
  have hh : q ≫ e.hom W ≫ W.map P W q = n • (n • mu) := by
    apply Additive.toMul.injective
    apply Grp.hom_ext
    change overHom q ≫ e.map W ≫ overHom (W.map P W q) = overHom (n • (n • mu))
    rw [← e.map_pullback W q d', hpow, ← hm]
    exact (groupHom_nsmul_hom (W.dual P) (n • mu) n).symm
  have hφ : e.hom W = mu := by
    have hmove (g : A ⟶ W.dual P) :
        q ≫ g ≫ W.map P W q = q ≫ q ≫ g := by
      change q ≫ g ≫ W.map P W (multiplication A (n : ℤ)) = _
      rw [dual_multiplication W]
      congr 1
      rw [multiplication_comp_eq_nsmul, multiplication, natCast_zsmul,
        Preadditive.comp_nsmul, Category.comp_id]
    have hμ : q ≫ q ≫ mu = n • (n • mu) := by
      change multiplication A (n : ℤ) ≫ multiplication A (n : ℤ) ≫ mu = _
      rw [multiplication_comp_eq_nsmul mu, multiplication_comp_eq_nsmul]
    apply IsogenyActionDescent.hom_ext hq
    apply IsogenyActionDescent.hom_ext hq
    exact (hmove _).symm.trans (hh.trans hμ.symm)
  let e' : Normalization P A (bundlePower M n) := Normalization.ofBundle _
  have hmap : e'.map W = d.map W := by
    rw [e.map_pow W e' n (isoClass_tensorPow P.preservation M n), ← e.overHom_hom W,
      hφ, ← groupHom_nsmul_hom]
    exact hm
  have hmAmp := d.sameMumford_ample W e' hmap.symm hL
  exact ⟨M, e.baseInverse, e.baseEvaluation, e.inverse, e.evaluation,
    hmAmp.of_positive_tensorPower_iso hn (Iso.refl _),
    (congrArg overHom hφ.symm).trans (e.overHom_hom W)⟩

private theorem finite_field_line_trivial {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
    [IsFinite p] (L : LineBundle X) : Nonempty (L ≅ LineBundle.trivial X) := by
  let := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra p
  have : IsAffine X := isAffine_of_isAffineHom p
  have : Module.Finite K Γ(X, ⊤) :=
    RingHom.Finite.comp p.finite_appTop (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower K inferInstance
  exact GroupScheme.lineBundle_nonempty_iso_trivial_of_isAffine L

private theorem exists_kernel_lift (q : A ⟶ A) (hq : IsIsogeny q)
    (d : Normalization P A L) (hi : KernelTranslation.inclusion q ≫ d.map W = 1) :
    Nonempty (KernelTranslation.Lift q L) := by
  let H := (KernelTranslation.kernel q).X
  let i := KernelTranslation.inclusion q
  let u := relativeFst A H ≫ i
  let v := relativeSnd A H
  have hfin : IsFinite H.hom :=
    MorphismProperty.of_isPullback (GroupScheme.kernel_isPullback_scheme (groupHom q)) hq.1
  obtain ⟨t⟩ := finite_field_line_trivial H.hom ((LineBundle.pullback i.left).obj L)
  have ht : pullbackHom P.preservation i.left (isoClass P.preservation L) = 1 :=
    LineBundle.isoClass_eq_of_iso t
  have hu : pullbackHom P.preservation u.left (isoClass P.preservation L) = 1 := by
    change pullbackHom P.preservation ((relativeFst A H).left ≫ i.left)
      (isoClass P.preservation L) = 1
    rw [← LineBundle.pullbackHom_comp, ht, map_one]
  have hφ : u ≫ d.map W = (1 : relativeOver A H ⟶ (W.dual P).X) := by
    change (relativeFst A H ≫ i) ≫ d.map W = _
    rw [Category.assoc, hi, MonObj.comp_one]
  have hid := familyPointClass_poincareFamily_pow_left P A W
    (1 : relativeOver A H ⟶ (W.dual P).X) v 0
  simp only [pow_zero] at hid
  have h := familyPointClass_mumfordSchemeMap_of_unique P A W L d.baseInverse
    d.baseEvaluation d.inverse d.evaluation u v
  change familyPointClass P.preservation A (poincareFamily A W.hasDual) (u ≫ d.map W) v = _ at h
  rw [hφ, hid, hu, inv_one, mul_one] at h
  have he := mul_inv_eq_one.mp h.symm
  change Nonempty ((Scheme.Modules.pullback v.left).obj L.obj ≅
    (Scheme.Modules.pullback (v * u).left).obj L.obj)
  rw [mul_comm v u]
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp he.symm
  exact ⟨(LineBundle.forget _).mapIso e⟩

/-- A positive multiple with an ample Mumford presentation over an algebraically closed field
has an ample Mumford presentation before multiplication, in every characteristic. -/
theorem algebraicallyClosedFieldPolarizationDivision :
    AlgebraicallyClosedFieldPolarizationDivisionStatement.{u} := by
  intro P K _ _ A W mu n hn h
  obtain ⟨L, B, evB, N, evN, hL, hm⟩ := h
  let d : Normalization P A L := ⟨B, evB, N, evN⟩
  let q := multiplication A (n : ℤ)
  have hq : IsIsogeny q := multiplication_isIsogeny A hn
  have hkill {T : Over (Spec (CommRingCat.of K))} (k : T ⟶ (KernelTranslation.kernel q).X) :
      (k ≫ KernelTranslation.inclusion q) ≫ overHom q = 1 :=
    ((GroupScheme.kernelPointsEquiv (groupHom q) T) k).property
  have hk : ∀ {T : Over (Spec (CommRingCat.of K))} (k : T ⟶ (KernelTranslation.kernel q).X),
      k ^ n = 1 := by
    intro T k
    apply (cancel_mono (KernelTranslation.inclusion q)).mp
    rw [MonObj.pow_comp, MonObj.one_comp]
    have he := hkill k
    change (k ≫ KernelTranslation.inclusion q) ≫ (groupHom (multiplication A (n : ℤ))).hom.hom = 1 at he
    rwa [points_multiplication, zpow_natCast] at he
  have hι : KernelTranslation.inclusion q ≫ d.map W = 1 := by
    rw [← show overHom (n • mu) = d.map W from hm, ← multiplication_comp_eq_nsmul mu]
    change KernelTranslation.inclusion q ≫ (overHom q ≫ overHom mu) = 1
    have he : KernelTranslation.inclusion q ≫ overHom q = 1 := by
      simpa only [Category.id_comp] using hkill (𝟙 (KernelTranslation.kernel q).X)
    rw [← Category.assoc, he, MonObj.one_comp]
  obtain ⟨α⟩ := exists_kernel_lift W q hq d hι
  obtain ⟨M, ⟨I⟩⟩ := KernelTranslation.exists_descended_power q hq α n hk
  exact divide_of_descended W mu hn d hm hL M I

end Langlands.AbelianScheme.PolarizedFiniteLevel

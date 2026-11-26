import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationRayPositivityStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicBundleAmpleProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleSymmetry
import Langlands.AlgebraicGeometry.Picard.ProperAmpleTrivialFiniteProof
import Langlands.AlgebraicGeometry.RelativeDimensionLoci
import Langlands.AlgebraicGeometry.SmoothPureDimensionProof

/-! # Positivity of proportional polarizations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (IsoClasses isoClass pullbackHom)
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable (P : Prerequisites.{u}) {S : Scheme.{u}} {A : AbelianScheme S} (W : DualWitness A)

local notation "diag" f:max => poincareDiagonalBundle A W.hasDual (groupHom f).hom.hom
local notation "pc" => familyPointClass P.preservation A (poincareFamily A W.hasDual)

private theorem diagonalClass_eq_pointClass (f : A ⟶ W.dual P) :
    isoClass P.preservation (diag f) = pc (groupHom f).hom.hom (𝟙 A.X) := by
  have h := isoClass_pullback_poincareDiagonalBundle P.preservation A W.hasDual
    (groupHom f).hom.hom (𝟙 A.X)
  simpa only [Over.id_left, ← LineBundle.pullbackHom_isoClass, LineBundle.pullbackHom_id,
    MonoidHom.id_apply, Category.id_comp] using h

/-- The class of the diagonal Poincaré bundle is multiplicative in the
homomorphism to the dual, written with its additive group law. -/
def DualWitness.poincareDiagonalClassHom :
    Multiplicative (A ⟶ W.dual P) →* IsoClasses P.preservation A.X.left where
  toFun f := isoClass P.preservation (diag f.toAdd)
  map_one' := by
    rw [diagonalClass_eq_pointClass]
    exact familyPointClass_poincareFamily_one_left P.preservation A W.hasDual W.geometry
      W.inverseBundle W.evaluation P.stability P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry (𝟙 A.X)
  map_mul' f g := by
    simp only [diagonalClass_eq_pointClass]
    exact familyPointClass_poincareFamily_mul_left P.preservation A W.hasDual W.geometry
      W.inverseBundle W.evaluation P.stability P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry (groupHom f.toAdd).hom.hom
      (groupHom g.toAdd).hom.hom (𝟙 A.X)

private theorem diagonal_pullback_isAmple (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (lam : A ⟶ W.dual P) (hlam : W.IsPolarization P lam) :
    ((LineBundle.pullback (pullback.fst A.X.hom s)).obj (diag lam)).IsAmple := by
  have h := poincareDiagonal_isAmple_of_fieldPresentation P K ((baseChange s).obj A)
    (W.pullback P s) (dualBaseChangeMap A W.hasDual P.universality s (groupHom lam).hom.hom)
    (hlam.2 K s)
  exact h.of_iso ((LineBundle.forget _).mapIso
    (poincareDiagonalBaseChangeIso P.universality s A W.hasDual (groupHom lam).hom.hom))

private theorem false_of_finite_positive_relativeDimension (K : Type u) [Field K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ) (hg : 0 < g)
    (hdim : B.HasRelativeDimension g) (hfin : IsFinite B.X.hom) : False := by
  let : IsFinite B.X.hom := hfin
  let e : B.X.left := unitSection B (Classical.choice inferInstance)
  have h0 : HasPureDimensionFibers 0 B.X.hom :=
    (hasPureDimensionFibers_zero_iff_locallyQuasiFinite B.X.hom).mpr inferInstance
  have hp := Langlands.AlgebraicGeometry.smoothPureDimension.2 B.X.left
    (Spec (CommRingCat.of K)) B.X.hom g hdim
  have hdimg := (hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq B.X.hom g).mp hp e
  have hdim0 := (hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq B.X.hom 0).mp h0 e
  have heq := hdimg.symm.trans hdim0
  exact hg.ne' (by exact_mod_cast heq)

private theorem not_zero_sum_polarizations (hS : Nonempty S) (g : ℕ) (hg : 0 < g)
    (hdim : A.HasRelativeDimension g) (lam lam' : A ⟶ W.dual P)
    (hlam : W.IsPolarization P lam) (hlam' : W.IsPolarization P lam')
    (k l : ℕ) (hk : 0 < k) (heq : k • lam' + l • lam = 0) : False := by
  let x := Classical.choice hS
  let K := AlgebraicClosure (S.residueField x)
  let s : Spec (CommRingCat.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) K)) ≫ S.fromSpecResidueField x
  let B := (baseChange s).obj A
  let p : B.X.left ⟶ A.X.left := pullback.fst A.X.hom s
  let L := (LineBundle.pullback p).obj (diag lam')
  let M := (LineBundle.pullback p).obj (diag lam)
  let Lk : LineBundle B.X.left := ⟨tensorPow L.obj k, tensorPow_isLocallyFreeRankOne _ L k⟩
  let Ml : LineBundle B.X.left := ⟨tensorPow M.obj l, tensorPow_isLocallyFreeRankOne _ M l⟩
  let LM := LineBundle.tensor P.preservation Lk Ml
  have hL := diagonal_pullback_isAmple P W K s lam' hlam'
  have hM := diagonal_pullback_isAmple P W K s lam hlam
  have hLk := positiveTensorPowerAmple _ L Lk k hk hL ⟨Iso.refl _⟩
  have hclass : isoClass P.preservation LM = 1 := by
    let f := (pullbackHom P.preservation p).comp (W.poincareDiagonalClassHom P)
    have he := congrArg f (congrArg Multiplicative.ofAdd heq)
    change f ((Multiplicative.ofAdd lam') ^ k * (Multiplicative.ofAdd lam) ^ l) = f 1 at he
    rw [map_mul, map_pow, map_pow, map_one] at he
    rw [LineBundle.isoClass_tensor, isoClass_tensorPow, isoClass_tensorPow]
    exact he
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp
    (hclass.trans (LineBundle.isoClass_trivial P.preservation (X := B.X.left)).symm)
  have hLM : LM.IsAmple := by
    cases l with
    | zero =>
      -- The zeroth power is the unit for the actual tensor product.
      exact hLk.of_iso (tensorRightUnitor Lk.obj).symm
    | succ l =>
      have hMl := positiveTensorPowerAmple _ M Ml (l + 1) (Nat.succ_pos l) hM ⟨Iso.refl _⟩
      exact ampleTensor _ Lk Ml LM ⟨Iso.refl _⟩ hLk hMl
  have hfin : IsFinite B.X.hom := properAmpleTrivialFinite K _ B.X.hom LM inferInstance hLM
    ⟨(LineBundle.forget _).mapIso e⟩
  exact false_of_finite_positive_relativeDimension K B g hg
    (hasRelativeDimension_baseChange A g hdim s) hfin

/-- Two proportional actual polarizations in positive relative dimension
have a positive ratio. -/
theorem polarizationRayPositivity : PolarizationRayPositivityStatement.{u} := by
  intro P S hS A g hg hdim W lam lam' hlam hlam' a b ha heq
  by_contra! hnonpos
  rcases (mul_nonpos_iff.mp hnonpos) with ⟨ha₀, hb₀⟩ | ⟨ha₀, hb₀⟩
  · let k := a.toNat
    let l := (-b).toNat
    have hka : (k : ℤ) = a := Int.toNat_of_nonneg ha₀
    have hlb : (l : ℤ) = -b := Int.toNat_of_nonneg (neg_nonneg.mpr hb₀)
    have hk : 0 < k := by omega
    apply not_zero_sum_polarizations P W hS g hg hdim lam lam' hlam hlam' k l hk
    rw [← Nat.cast_smul_eq_nsmul ℤ k, ← Nat.cast_smul_eq_nsmul ℤ l,
      hka, hlb, neg_smul, heq, add_neg_cancel]
  · let k := (-a).toNat
    let l := b.toNat
    have hka : (k : ℤ) = -a := Int.toNat_of_nonneg (neg_nonneg.mpr ha₀)
    have hlb : (l : ℤ) = b := Int.toNat_of_nonneg hb₀
    have hk : 0 < k := by omega
    apply not_zero_sum_polarizations P W hS g hg hdim lam lam' hlam hlam' k l hk
    rw [← Nat.cast_smul_eq_nsmul ℤ k, ← Nat.cast_smul_eq_nsmul ℤ l,
      hka, hlb, neg_smul, heq, neg_add_cancel]

end Langlands.AbelianScheme.PolarizedFiniteLevel

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationStabilizer
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitConjugation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylFibers
import Mathlib.Data.Sigma.Basic

/-! # The double averaging index and association multiplicity -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.Association

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})

/-- The pairs `(s,P')` in the VI.3 average for the source Levi `M`. -/
abbrev WeylParabolicPair (M : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) : Type (u + 1) :=
  Σ s : relativeWeylGroup i,
    SemistandardSpectralParabolicFiber i (weylConjugateLevi hG hi hD M hM s)

/-- Reindex each parabolic fiber by the fiber over the original Levi. -/
def weylParabolicPairEquivProd (M : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) :
    WeylParabolicPair hG hi hD M hM ≃
      relativeWeylGroup i × SemistandardSpectralParabolicFiber i M :=
  Equiv.sigmaEquivProdOfEquiv fun s => (weylParabolicFiberEquiv hG hi hD M hM s).symm

theorem card_weylParabolicPair (M : SemistandardSpectralLevi i)
    (hM : torusCentralizer i ≤ M.val) :
    Nat.card (WeylParabolicPair hG hi hD M hM) =
      Nat.card (relativeWeylGroup i) * Nat.card (SemistandardSpectralParabolicFiber i M) :=
  (Nat.card_congr (weylParabolicPairEquivProd hG hi hD M hM)).trans (Nat.card_prod _ _)

theorem finite_weylParabolicPair (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
    (M : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val) :
    Finite (WeylParabolicPair hG hi hD M hM) := by
  let := hG.finite_relativeWeylGroup i hi
  let := (hfin F G hG S i hi M).1
  exact Finite.of_equiv _ (weylParabolicPairEquivProd hG hi hD M hM).symm

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

set_option hygiene false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu

section DoubleSum

variable [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (t : Θ) (hM : torusCentralizer i ≤ t.1.levi)
  (x : WeylParabolicPair hG hi hD t.1.toLevi hM)

/-- The actual index `(sO,P')` at the parabolic in one pair of the VI.3 sum. -/
def weylParabolicTarget : Θ :=
  (existsUnique_weylTransports_of_levi_eq a ha mu t x.2.val hM x.1 x.2.property.symm).exists.choose

private theorem weylParabolicTarget_spec :
    (weylParabolicTarget hG hi hD a ha mu t hM x).1 = x.2.val ∧
      WeylTransports a ha mu x.1 t (weylParabolicTarget hG hi hD a ha mu t hM x) :=
  (existsUnique_weylTransports_of_levi_eq a ha mu t x.2.val hM x.1
    x.2.property.symm).exists.choose_spec

@[simp] theorem weylParabolicTarget_parabolic :
    (weylParabolicTarget hG hi hD a ha mu t hM x).1 = x.2.val :=
  (weylParabolicTarget_spec hG hi hD a ha mu t hM x).1

theorem weylParabolicTarget_transports :
    WeylTransports a ha mu x.1 t (weylParabolicTarget hG hi hD a ha mu t hM x) :=
  (weylParabolicTarget_spec hG hi hD a ha mu t hM x).2

/-- In the VI.3 index, the fiber over a given associated target is exactly
the Weyl elements carrying the source to that target. -/
def weylParabolicPairEquivTransporters :
    WeylParabolicPair hG hi hD t.1.toLevi hM ≃
      Σ q : associatedIndices a ha mu t, {s // WeylTransports a ha mu s t q.val} where
  toFun x :=
    let h := weylParabolicTarget_transports hG hi hD a ha mu t hM x
    ⟨⟨weylParabolicTarget hG hi hD a ha mu t hM x, ⟨x.1, h⟩⟩, ⟨x.1, h⟩⟩
  invFun y := ⟨y.2.val, ⟨y.1.val.1, (y.2.property.levi_eq hM).symm⟩⟩
  left_inv x := Sigma.subtype_ext rfl (weylParabolicTarget_parabolic hG hi hD a ha mu t hM x)
  right_inv y := by
    let x : WeylParabolicPair hG hi hD t.1.toLevi hM :=
      ⟨y.2.val, ⟨y.1.val.1, (y.2.property.levi_eq hM).symm⟩⟩
    apply Sigma.subtype_ext
    · exact Subtype.ext ((weylParabolicTarget_transports hG hi hD a ha mu t hM x).eq_of_same_parabolic
        y.2.property hM (weylParabolicTarget_parabolic hG hi hD a ha mu t hM x))
    · rfl

end DoubleSum

/-- For a fixed transporter `r`, every transporter to `q` has the form `r*h`,
where `h` stabilizes the full source index. -/
def weylTransporterEquivStabilizer {t q : Θ} {r : relativeWeylGroup i}
    (hr : WeylTransports a ha mu r t q) :
    weylOrbitStabilizerSubgroup a ha mu t ≃ {s // WeylTransports a ha mu s t q} where
  toFun h := ⟨r * h.val, WeylTransports.mul h.property hr⟩
  invFun s := ⟨r⁻¹ * s.val, s.property.mul hr.inv⟩
  left_inv h := Subtype.ext (inv_mul_cancel_left r h.val)
  right_inv s := Subtype.ext (mul_inv_cancel_left r s.val)

variable [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (t : Θ) (hM : torusCentralizer i ≤ t.1.levi)

/-- Regroup the double averaging index by associated targets. -/
theorem card_weylParabolicPair_eq_association_mul_stabilizer :
    Nat.card (WeylParabolicPair hG hi hD t.1.toLevi hM) =
      Nat.card (associatedIndices a ha mu t) *
        Nat.card (weylOrbitStabilizerSubgroup a ha mu t) := by
  let e := Equiv.sigmaEquivProdOfEquiv fun q : associatedIndices a ha mu t =>
    (weylTransporterEquivStabilizer a ha mu q.property.choose_spec).symm
  exact (Nat.card_congr ((weylParabolicPairEquivTransporters hG hi hD a ha mu t hM).trans e)).trans
    (Nat.card_prod _ _)

include hG hi hD in
/-- The literal multiplicity in Remark VII.2.4. -/
theorem card_association_mul_stabilizer_mul_leviWeyl :
    Nat.card (associatedIndices a ha mu t) * Nat.card (WeylOrbitStabilizer a ha mu t hM) *
        Nat.card (semistandardLeviRelativeWeylSubgroup i t.1.toLevi) =
      Nat.card (relativeWeylGroup i) * Nat.card (SemistandardSpectralParabolicFiber i t.1.toLevi) := by
  rw [mul_assoc, ← card_weylOrbitStabilizerSubgroup a ha mu t hM,
    ← card_weylParabolicPair_eq_association_mul_stabilizer hG hi hD a ha mu t hM]
  exact card_weylParabolicPair hG hi hD t.1.toLevi hM

variable (r : CocharacterPresentation hG t.1)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

/-- The source coefficient for one representative of an association class. -/
def associationWeight : ℝ :=
  ((SourceConstants.cReal r K hK) ^ 2)⁻¹ * (SourceConstants.gammaReal r K hK)⁻¹ /
    (Nat.card (WeylOrbitStabilizer a ha mu t hM) : ℝ)

include hi hD in
theorem card_association_mul_unquotientedWeight
    (hfin : SemistandardSpectralFiberFinitenessStatement.{u}) :
    (Nat.card (associatedIndices a ha mu t) : ℝ) * SourceConstants.unquotientedWeight r K hK =
      associationWeight hG a ha mu t hM r K hK := by
  let := hG.finite_relativeWeylGroup i hi
  let := (hfin F G hG S i hi t.1.toLevi).1
  let := (hfin F G hG S i hi t.1.toLevi).2
  have hW : (Nat.card (relativeWeylGroup i) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hP : (Nat.card (SemistandardSpectralParabolicFiber i t.1.toLevi) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hS : (Nat.card (WeylOrbitStabilizer a ha mu t hM) : ℝ) ≠ 0 := by
    exact_mod_cast (card_weylOrbitStabilizer_pos a ha mu hG hi t hM).ne'
  have hm :
      (Nat.card (associatedIndices a ha mu t) : ℝ) *
          ((Nat.card (semistandardLeviRelativeWeylSubgroup i t.1.toLevi) : ℝ) /
            ((Nat.card (relativeWeylGroup i) : ℝ) *
              (Nat.card (SemistandardSpectralParabolicFiber i t.1.toLevi) : ℝ))) =
        1 / (Nat.card (WeylOrbitStabilizer a ha mu t hM) : ℝ) := by
    rw [← mul_div_assoc, div_eq_div_iff (mul_ne_zero hW hP) hS, one_mul, mul_right_comm]
    exact_mod_cast card_association_mul_stabilizer_mul_leviWeyl hG hi hD a ha mu t hM
  rw [SourceConstants.unquotientedWeight, mul_left_comm, hm, mul_one_div, associationWeight]

end Langlands.HarishChandraSchwartz.RationalSemistandard.Association

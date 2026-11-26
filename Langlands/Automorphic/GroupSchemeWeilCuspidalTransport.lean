import Langlands.Analysis.Local.ScaledMeasureL2Equiv
import Langlands.Automorphic.GroupSchemeWeilParabolicTransport
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated

/-! # Cuspidal `L²` under the adelic Weil comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Analysis

variable {A B X Y : Type*} [Monoid A] [Monoid B]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  {ρX : B →* (X →L[ℂ] X)} {ρY : A →* (Y →L[ℂ] Y)}

/-- The nonzero, closed and minimal invariant submodule condition for a bounded action. -/
abbrev IsIrreducibleClosedSummand (ρ : B →* (X →L[ℂ] X)) (P : Submodule ℂ X) : Prop :=
  P ≠ ⊥ ∧ IsClosed (P : Set X) ∧ (∀ g, ∀ x ∈ P, ρ g x ∈ P) ∧
    ∀ Q : Submodule ℂ X, Q ≤ P → IsClosed (Q : Set X) →
      (∀ g, ∀ x ∈ Q, ρ g x ∈ Q) → Q = ⊥ ∨ Q = P

/-- The image of a closed irreducible subrepresentation under an intertwining
continuous linear equivalence is a closed irreducible subrepresentation. -/
theorem IsIrreducibleClosedSummand.comap_symm_of_intertwining
    {P : Submodule ℂ X} (hP : IsIrreducibleClosedSummand ρX P)
    (E : X ≃L[ℂ] Y) (a : A → B) (ha : Function.Surjective a)
    (hE : ∀ g x, E (ρX (a g) x) = ρY g (E x)) :
    IsIrreducibleClosedSummand ρY (P.comap E.symm.toLinearMap) := by
  rcases hP with ⟨hnz, hcl, hinv, hmin⟩
  let P' := P.comap E.symm.toLinearMap
  refine ⟨?_, hcl.preimage E.symm.continuous, ?_, ?_⟩
  · intro hzero
    apply hnz
    rw [← Submodule.map_comap_eq_of_surjective E.symm.surjective P]
    change P'.map E.symm.toLinearMap = ⊥
    change P' = ⊥ at hzero
    rw [hzero, Submodule.map_bot]
  · intro g y hy
    change E.symm (ρY g y) ∈ P
    have heq : E.symm (ρY g y) = ρX (a g) (E.symm y) := by
      apply E.injective
      simpa only [E.apply_symm_apply] using (hE g (E.symm y)).symm
    rw [heq]
    exact hinv _ _ hy
  · intro Q hQP hclQ hQ
    let Q' := Q.comap E.toLinearMap
    have hQ'P : Q' ≤ P := by
      intro x hx
      have hx' := hQP hx
      change E.symm (E x) ∈ P at hx'
      simpa only [E.symm_apply_apply] using hx'
    have hinvQ' : ∀ g : B, ∀ x ∈ Q', ρX g x ∈ Q' := by
      intro g x hx
      obtain ⟨g, rfl⟩ := ha g
      change E (ρX (a g) x) ∈ Q
      rw [hE]
      exact hQ g (E x) hx
    rcases hmin Q' hQ'P (hclQ.preimage E.continuous) hinvQ' with hzero | heq
    · left
      apply (Submodule.eq_bot_iff _).mpr
      intro y hy
      have hy' : E.symm y ∈ Q' := by
        change E (E.symm y) ∈ Q
        simpa only [E.apply_symm_apply] using hy
      rw [hzero, Submodule.mem_bot] at hy'
      exact E.symm.injective (hy'.trans (map_zero E.symm).symm)
    · right
      apply le_antisymm hQP
      intro y hy
      have hy' : E.symm y ∈ Q' := by
        rw [heq]
        exact hy
      change E (E.symm y) ∈ Q at hy'
      simpa only [E.apply_symm_apply] using hy'

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

/-- Taking the closure of a linear range commutes with a continuous linear equivalence. -/
theorem topologicalClosure_range_comp_equiv (E : X ≃L[ℂ] Y) (f : V →ₗ[ℂ] X) :
    (LinearMap.range (E.toLinearMap.comp f)).topologicalClosure =
      (LinearMap.range f).topologicalClosure.comap E.symm.toLinearMap := by
  have hrange : LinearMap.range (E.toLinearMap.comp f) =
      (LinearMap.range f).comap E.symm.toLinearMap := by
    ext y
    change (∃ v, E (f v) = y) ↔ ∃ v, f v = E.symm y
    exact exists_congr fun v => E.eq_symm_apply.symm
  rw [hrange]
  apply SetLike.coe_injective
  change closure (E.symm ⁻¹' (LinearMap.range f : Set X)) =
    E.symm ⁻¹' closure (LinearMap.range f : Set X)
  exact (E.symm.toHomeomorph.preimage_closure _).symm

end Langlands.Analysis

namespace Langlands.Automorphic.GroupSchemeFunctions.WeilCuspidalTransport

open Langlands.Global AdelicGroupPoints AdelicWeilRestriction PositiveRealTorus
open Langlands.GroupScheme

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of L))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {W : GroupScheme (Spec (CommRingCat.of K))} [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom]
  (w : W ≅ AffineWeil.groupScheme K L G)
  {T : CommGroupScheme (Spec (CommRingCat.of K))} {i : T.toGrp ⟶ W}
  {T' : CommGroupScheme (Spec (CommRingCat.of L))} {j : T'.toGrp ⟶ G}
  (hpos : (imageSubgroup K T W i).map (ambientEquiv K L w).toMonoidHom =
    imageSubgroup L T' G j)

local notation "QK" => PositiveRationalQuotient K W T i
local notation "QL" => PositiveRationalQuotient L G T' j
local notation "mK" => positiveRationalQuotientHaarMeasure K W T i
local notation "mL" => positiveRationalQuotientHaarMeasure L G T' j
local notation "q" => positiveQuotientEquiv K L w hpos

section Periods

variable (hPD : ParabolicDynamicStatement.{u}) (hW : IsConnectedReductive W) (hG : IsConnectedReductive G)

private theorem integrand_comp (Q : ProperRationalParabolic W) (P : ProperRationalParabolic G)
    (m : WeilSubgroupsMatch K L w (properRationalParabolicRadicals hPD hW Q)
      (properRationalParabolicRadicals hPD hG P)) (f : QL → ℂ) (g : normOneSubgroup K W) :
    properParabolicPositivePeriodIntegrand K W hPD hW T i Q (f ∘ q) g =
      properParabolicPositivePeriodIntegrand L G hPD hG T' j P f (normOneEquiv K L w g) ∘
        weilRadicalQuotientEquiv K L w hPD hW hG Q P m := by
  funext x
  induction x using Quotient.inductionOn with
  | _ n =>
      change properParabolicPositivePeriodIntegrand K W hPD hW T i Q (f ∘ q) g
          (LeftCosetSpace.mk _ n) =
        properParabolicPositivePeriodIntegrand L G hPD hG T' j P f (normOneEquiv K L w g)
          (weilRadicalQuotientEquiv K L w hPD hW hG Q P m (LeftCosetSpace.mk _ n))
      simp only [Function.comp_apply, weilRadicalQuotientEquiv_mk,
        properParabolicPositivePeriodIntegrand_mk, positiveQuotientEquiv_mk, map_mul,
        normOneEquiv_val, weilRadicalAdelicEquiv_val]

private theorem period_converges_iff (Q : ProperRationalParabolic W) (P : ProperRationalParabolic G)
    (m : WeilSubgroupsMatch K L w (properRationalParabolicRadicals hPD hW Q)
      (properRationalParabolicRadicals hPD hG P)) (f : QL → ℂ) (g : normOneSubgroup K W) :
    HasConvergentProperParabolicPositivePeriod K W hPD hW T i Q (f ∘ q) g ↔
      HasConvergentProperParabolicPositivePeriod L G hPD hG T' j P f (normOneEquiv K L w g) := by
  unfold HasConvergentProperParabolicPositivePeriod
  rw [integrand_comp K L w hpos hPD hW hG Q P m]
  exact (measurePreserving_weilRadicalQuotient K L w hPD hW hG Q P m).integrable_comp_emb
    (weilRadicalQuotientEquiv K L w hPD hW hG Q P m).measurableEmbedding

private theorem period_comp (Q : ProperRationalParabolic W) (P : ProperRationalParabolic G)
    (m : WeilSubgroupsMatch K L w (properRationalParabolicRadicals hPD hW Q)
      (properRationalParabolicRadicals hPD hG P)) (f : QL → ℂ) (g : normOneSubgroup K W) :
    properParabolicPositivePeriod K W hPD hW T i Q (f ∘ q) g =
      properParabolicPositivePeriod L G hPD hG T' j P f (normOneEquiv K L w g) := by
  unfold properParabolicPositivePeriod
  rw [integrand_comp K L w hpos hPD hW hG Q P m]
  exact (measurePreserving_weilRadicalQuotient K L w hPD hW hG Q P m).integral_comp
    (weilRadicalQuotientEquiv K L w hPD hW hG Q P m).measurableEmbedding _

private theorem ae_normOne_iff {p : normOneSubgroup L G → Prop} :
    (∀ᵐ x ∂(Measure.haar : Measure (normOneSubgroup K W)), p (normOneEquiv K L w x)) ↔
      ∀ᵐ y ∂(Measure.haar : Measure (normOneSubgroup L G)), p y :=
  MeasureTransport.ae_pullback_iff (normOneEquiv K L w).toHomeomorph.toMeasurableEquiv
    (map_normOneHaar K L w) (ENNReal.coe_ne_zero.mpr (normOneHaarFactor_pos K L w).ne')

include hpos in
/-- A function pulled back along the quotient comparison is almost-everywhere cuspidal
exactly when the original function is. Convergence and vanishing both transport. -/
theorem pullback_mem_aeCuspidal_iff (f : QL → ℂ) :
    f ∘ q ∈ aeParabolicCuspidalFunctionSubmodule K W hPD hW T i ↔
      f ∈ aeParabolicCuspidalFunctionSubmodule L G hPD hG T' j := by
  have hmatch (Q : ProperRationalParabolic W) (P : ProperRationalParabolic G)
      (m : WeilSubgroupsMatch K L w (properRationalParabolicRadicals hPD hW Q)
        (properRationalParabolicRadicals hPD hG P)) :
      ((∀ᵐ g ∂(Measure.haar : Measure (normOneSubgroup K W)),
          HasConvergentProperParabolicPositivePeriod K W hPD hW T i Q (f ∘ q) g) ∧
        properParabolicPositivePeriod K W hPD hW T i Q (f ∘ q) =ᵐ[
          (Measure.haar : Measure (normOneSubgroup K W))] 0) ↔
      ((∀ᵐ g ∂(Measure.haar : Measure (normOneSubgroup L G)),
          HasConvergentProperParabolicPositivePeriod L G hPD hG T' j P f g) ∧
        properParabolicPositivePeriod L G hPD hG T' j P f =ᵐ[
          (Measure.haar : Measure (normOneSubgroup L G))] 0) := by
    change (_ ∧ (∀ᵐ g ∂(Measure.haar : Measure (normOneSubgroup K W)),
        properParabolicPositivePeriod K W hPD hW T i Q (f ∘ q) g = 0)) ↔
      (_ ∧ (∀ᵐ g ∂(Measure.haar : Measure (normOneSubgroup L G)),
        properParabolicPositivePeriod L G hPD hG T' j P f g = 0))
    simp only [period_converges_iff K L w hpos hPD hW hG Q P m,
      period_comp K L w hpos hPD hW hG Q P m]
    exact and_congr (ae_normOne_iff K L w (p :=
      HasConvergentProperParabolicPositivePeriod L G hPD hG T' j P f))
      (ae_normOne_iff K L w (p := fun g =>
        properParabolicPositivePeriod L G hPD hG T' j P f g = 0))
  constructor
  · intro hf P
    obtain ⟨Q, m⟩ := exists_lower_parabolicRadical K L w hPD hW hG P
    exact (hmatch Q P m).mp (hf Q)
  · intro hf Q
    obtain ⟨P, m⟩ := exists_upper_parabolicRadical K L w hPD hW hG Q
    exact (hmatch Q P m).mpr (hf P)

end Periods

variable (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i) (hj : Function.Injective (characterRestrict j))
  [(characterRestrict j).range.FiniteIndex]
  (J : Type u) [Fintype J] (e' : T'.toGrp ≅ splitTorus (Spec (CommRingCat.of L)) J)
  (hc' : IsCentral j)

include hpos hi I e hc hj J e' hc'

/-- The positive quotient comparison is measurable in both directions for the actual
quotient measurable spaces. -/
def quotientMeasurableEquiv : QK ≃ᵐ QL := by
  let := positiveRationalQuotient_borelSpace K W T i hi I e hc
  let := positiveRationalQuotient_borelSpace L G T' j hj J e' hc'
  exact (q).toMeasurableEquiv

local notation "qM" => quotientMeasurableEquiv K L w hpos hi I e hc hj J e' hc'

@[simp]
theorem quotientMeasurableEquiv_apply (x : QK) : qM x = q x := rfl

theorem ae_quotient_iff {p : QL → Prop} :
    (∀ᵐ x ∂mK, p (q x)) ↔ ∀ᵐ y ∂mL, p y :=
  MeasureTransport.ae_pullback_iff qM
    (map_positiveQuotientHaar K L w hi e hj e' hpos hc hc')
    (ENNReal.coe_ne_zero.mpr (normOneHaarFactor_pos K L w).ne')

/-- Pullback identifies actual `L²` classes of the two positive rational quotients. -/
def quotientL2Equiv : Lp ℂ 2 mL ≃L[ℂ] Lp ℂ 2 mK :=
  MeasureTransport.l2Equiv qM (map_positiveQuotientHaar K L w hi e hj e' hpos hc hc')
    (ENNReal.coe_ne_zero.mpr (normOneHaarFactor_pos K L w).ne') ENNReal.coe_ne_top

local notation "U" => quotientL2Equiv K L w hpos hi I e hc hj J e' hc'

theorem coeFn_quotientL2Equiv (f : Lp ℂ 2 mL) : U f =ᵐ[mK] f ∘ q :=
  MeasureTransport.coeFn_l2Equiv qM _ _ _ f

theorem coeFn_quotientL2Equiv_symm (f : Lp ℂ 2 mK) : (U).symm f =ᵐ[mL] f ∘ (q).symm :=
  MeasureTransport.coeFn_l2Equiv_symm qM _ _ _ f

section Cuspidal

variable (hPD : ParabolicDynamicStatement.{u}) (hW : IsConnectedReductive W) (hG : IsConnectedReductive G)

local notation "SK" => fullAEL2CuspidalSubmodule K W hPD hW T i hi I e hc
local notation "SL" => fullAEL2CuspidalSubmodule L G hPD hG T' j hj J e' hc'

theorem quotientL2Equiv_mem_cuspidal_iff (f : Lp ℂ 2 mL) : U f ∈ SK ↔ f ∈ SL := by
  change (U f : QK → ℂ) ∈ aeParabolicCuspidalFunctionSubmodule K W hPD hW T i ↔
    (f : QL → ℂ) ∈ aeParabolicCuspidalFunctionSubmodule L G hPD hG T' j
  exact (mem_aeParabolicCuspidalFunctionSubmodule_congr K W hPD hW T i hi I e hc _ _
    (Lp.stronglyMeasurable _) ((Lp.stronglyMeasurable f).comp_measurable (qM).measurable)
    (coeFn_quotientL2Equiv K L w hpos hi I e hc hj J e' hc' f)).trans
    (pullback_mem_aeCuspidal_iff K L w hpos hPD hW hG f)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Pullback restricts to a continuous linear equivalence of the full cuspidal subspaces. -/
def cuspidalEquiv : SL ≃L[ℂ] SK where
  toFun f := ⟨U f.val, (quotientL2Equiv_mem_cuspidal_iff K L w hpos hi I e hc hj J e' hc'
    hPD hW hG f.val).mpr f.property⟩
  invFun f := ⟨(U).symm f.val, (quotientL2Equiv_mem_cuspidal_iff K L w hpos hi I e hc hj J e' hc'
    hPD hW hG ((U).symm f.val)).mp (by rw [(U).apply_symm_apply]; exact f.property)⟩
  left_inv f := Subtype.ext ((U).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((U).apply_symm_apply f.val)
  map_add' f g := Subtype.ext (map_add U f.val g.val)
  map_smul' z f := Subtype.ext (map_smul U z f.val)
  continuous_toFun := ((U).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((U).symm.continuous.comp continuous_subtype_val).subtype_mk _

local notation "Uc" => cuspidalEquiv K L w hpos hi I e hc hj J e' hc' hPD hW hG

theorem cuspidalEquiv_val (f : SL) : (Uc f).val = U f.val := rfl

theorem coeFn_cuspidalEquiv (f : SL) : (Uc f).val =ᵐ[mK] f.val ∘ q :=
  coeFn_quotientL2Equiv K L w hpos hi I e hc hj J e' hc' f.val

theorem coeFn_cuspidalEquiv_symm (f : SK) : ((Uc).symm f).val =ᵐ[mL] f.val ∘ (q).symm :=
  coeFn_quotientL2Equiv_symm K L w hpos hi I e hc hj J e' hc' f.val

variable [hHaarK : (Measure.haar : Measure (normOneSubgroup K W)).IsMulRightInvariant]
  [hHaarL : (Measure.haar : Measure (normOneSubgroup L G)).IsMulRightInvariant]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
/-- The comparison intertwines the actual bounded right actions on the full cuspidal subspaces. -/
theorem cuspidalEquiv_rightAction (a : AdelicGroupPoints K W) (f : SL) :
    Uc (fullAEL2CuspidalBoundedRightAction L G hPD hG T' j hj J e' hc'
      (ambientEquiv K L w a) f) =
      fullAEL2CuspidalBoundedRightAction K W hPD hW T i hi I e hc a (Uc f) := by
  let hK := haarQuotientMeasureRightInvariant K W T i hi I e hc
  let hL := haarQuotientMeasureRightInvariant L G T' j hj J e' hc'
  let a' := ambientEquiv K L w a
  let y := quotientL2RightTranslate L G T' j mL hL a' f.val
  apply Subtype.ext
  change U y = quotientL2RightTranslate K W T i mK hK a (U f.val)
  apply Lp.ext
  filter_upwards [coeFn_quotientL2Equiv K L w hpos hi I e hc hj J e' hc' y,
    (ae_quotient_iff K L w hpos hi I e hc hj J e' hc').mpr
      (coeFn_quotientL2RightTranslate L G T' j mL hL a' f.val),
    coeFn_quotientL2RightTranslate K W T i mK hK a (U f.val),
    (hK a).quasiMeasurePreserving.ae
      (coeFn_quotientL2Equiv K L w hpos hi I e hc hj J e' hc' f.val)] with x hy hL' hK' hf
  simp only [Function.comp_apply] at hy hf
  rw [hy, hL', hK', hf, positiveQuotientEquiv_rightTranslate]

open Langlands.Analysis in
/-- A closed irreducible summand corresponds to a closed irreducible summand under the
equivalence of the actual cuspidal representations. -/
theorem cuspidalEquiv_irreducibleSummand (P : Submodule ℂ SL)
    (hP : IsIrreducibleClosedSummand
      (fullAEL2CuspidalBoundedRightAction L G hPD hG T' j hj J e' hc') P) :
    IsIrreducibleClosedSummand
      (fullAEL2CuspidalBoundedRightAction K W hPD hW T i hi I e hc)
      (P.comap (Uc).symm.toLinearMap) :=
  hP.comap_symm_of_intertwining Uc (ambientEquiv K L w) (ambientEquiv K L w).surjective
    (cuspidalEquiv_rightAction K L w hpos hi I e hc hj J e' hc' hPD hW hG)

end Cuspidal

end Langlands.Automorphic.GroupSchemeFunctions.WeilCuspidalTransport

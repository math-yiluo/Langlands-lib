import Langlands.Shimura.PEL.HarrisTaylorCMIntegralPowerModel
import Langlands.Shimura.PEL.PolarizedWeilIntegralPowerModel
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedUnpointedPresheaf
import Mathlib.CategoryTheory.Conj

/-! # A polarized integral model for an even power of a CM self-isogeny -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.AbelianScheme

/-- A finite-order integral model of a positive rational power gives finite
order of the original rational automorphism. -/
theorem finiteOrder_of_integral_conjugate_power {S : Scheme} {A B : AbelianScheme S}
    (r : Rationalization.of B ≅ Rationalization.of A)
    (a : Aut (Rationalization.of A)) (k : ℕ) (hk : 0 < k)
    (g : Aut B)
    (hg : Rationalization.ofHom g.hom = r.hom ≫ (a ^ k).hom ≫ r.inv)
    (hfin : IsOfFinOrder g) :
    let f : End0 A := a.hom
    IsOfFinOrder f := by
  let f : End0 A := a.hom
  change IsOfFinOrder f
  let φ : Aut B →* End0 B :=
    ((rationalization S).mapEnd B).comp (Aut.toEnd B)
  have hfinR : IsOfFinOrder (φ g) := by
    obtain ⟨d, hd, hgd⟩ := hfin.exists_pow_eq_one
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨d, hd, ?_⟩
    rw [← map_pow, hgd, map_one]
  have hpow : (a ^ k).hom = f ^ k :=
    map_pow (Aut.toEnd _) a k
  have hc : φ g = r.symm.conj (f ^ k) := by
    change Rationalization.ofHom g.hom = r.hom ≫ _ ≫ r.inv
    rw [← hpow]
    exact hg
  have hfinPow : IsOfFinOrder (f ^ k) := by
    apply (Function.Injective.isOfFinOrder_iff
      (f := r.symm.conj.toMonoidHom) r.symm.conj.injective).mp
    change IsOfFinOrder (r.symm.conj (f ^ k))
    rw [← hc]
    exact hfinR
  exact hfinPow.of_pow (Nat.ne_of_gt hk)

end Langlands.AbelianScheme

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AbelianScheme.Tate
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (P : Prerequisites.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

variable
  (hs : ∀ Y : Cover (Spec (CommRingCat.of Ω)), Finite (Fiber (𝟙 (Spec (CommRingCat.of Ω))) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ((Spec (CommRingCat.of Ω)), ⊤)))
  (X : PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality (S := (Spec (CommRingCat.of Ω))))

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Frame" => WeilAdelicFrame P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability X.hasDual X.geometry X.inversePoincare
  X.evaluation compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) (𝟙 (Spec (CommRingCat.of Ω)))
local notation "Rat" => Rational X.actionObj.abelianScheme (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True)
local notation "lattice" => harrisIntegralFrameLattice D C P compatibility h (𝟙 (Spec (CommRingCat.of Ω))) X

/-- The exact integral power model also carries an actual polarization
preserved by its actual integral automorphism. -/
def PolarizedIntegralPowerModelWitness :
    letI := auxiliaryStarRing D C
    ∀ (_q : ℚˣ) (_e : X.actionObj ≅ X.actionObj), Prop := by
  let := auxiliaryStarRing D C
  intro q e
  let u : Aut (Rationalization.of X.actionObj.abelianScheme) :=
    RationalAlgebraAction.underlyingIso e
  exact ∃ (eta : Frame) (m : ℕ), 0 < m ∧ q ^ (2 * m) = 1 ∧
    ∃ (B : AbelianScheme (Spec (CommRingCat.of Ω)))
      (r : Rationalization.of B ≅ Rationalization.of X.actionObj.abelianScheme)
      (g : Aut B) (W : DualWitness B) (lam : B ⟶ W.dual P),
      W.IsPolarization P lam ∧
      g.hom ≫ lam ≫ W.map P W g.hom = lam ∧
      (∀ w : Rat, w ∈ lattice eta ↔
        ∃ x : GroupScheme.Tate.Full B.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))),
          rationalHomMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) r.hom
            (GroupScheme.Tate.toRational B.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) x) = w) ∧
      Rationalization.ofHom g.hom = r.hom ≫ (u ^ (2 * m)).hom ≫ r.inv ∧
      Rationalization.ofHom g.inv = r.hom ≫ (u ^ (2 * m)).inv ≫ r.inv

variable
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom]
  (additivity : PositivePairAdditivity D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality (S := (Spec (CommRingCat.of Ω))))
  (dualExists : ∀ B : AbelianScheme (Spec (CommRingCat.of Ω)),
    Nonempty (DualEvaluationData P.preservation P.stability B))

local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "orbitTower" => PolarizedWeilLevel.levelTower P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) (𝟙 (Spec (CommRingCat.of Ω))) hs htor hu
local notation "transport" => PolarizedWeilLevel.levelIso P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) (𝟙 (Spec (CommRingCat.of Ω))) hs htor hu additivity
local notation "Mult" => PolarizedWeilLevel.Multiple P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  additivity

include dualExists in
omit [IsScalarTower ℚ F A] in
/-- The admission's actual dual-existence field suffices to polarize the same
integral even-power model obtained from the original fixed Harris orbit. -/
theorem polarizedIntegralPowerModelWitness_of_levelIso_fixed (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    ∀ (a : (orbitTower X).obj ((indexFunctor).obj U)) (q : ℚˣ)
      (e : X.actionObj ≅ X.actionObj) (he : Mult X X q e),
      transport X X ((indexFunctor).obj U) q e he a = a →
        PolarizedIntegralPowerModelWitness D C P compatibility h Ω X q e := by
  let := auxiliaryStarRing D C
  intro a q e he hfixed
  obtain ⟨eta, m, hm, hq, B, r, g, hr, hg, hgi⟩ :=
    integralPowerModelWitness_of_levelIso_fixed
      D C P compatibility h Ω hs htor hu X additivity U a q e he hfixed
  let WB := Classical.choice (dualExists B)
  let W : DualWitness B :=
    ⟨WB.hasDual, WB.geometry, WB.inversePoincare, WB.evaluation⟩
  let Y := PolarizedWeilLevel.PolarizedAction.isogenyModel
    (P := P) (X := X) (B := B) (e := r) (W := W)
    (p := 𝟙 (Spec (CommRingCat.of Ω)))
  have hpres := PolarizedWeilLevel.integralPolarizedPowerModel
    P additivity hu X B r W (𝟙 (Spec (CommRingCat.of Ω)))
    q e he (2 * m) hq g hg
  refine ⟨eta, m, hm, hq, B, r, g, W, Y.polarization, hpres.1, ?_, hr, hg, hgi⟩
  exact hpres.2

omit [IsScalarTower ℚ F A] [IsAlgClosed Ω] [CharZero Ω] hμfin hμet in
/-- Finiteness is left solely with the integral polarized automorphism theorem:
its finite-order consequence transfers to the original rational self-isogeny. -/
theorem finiteOrder_of_polarizedIntegralPowerModelWitness
    (hfinite : ∀ (B : AbelianScheme (Spec (CommRingCat.of Ω)))
      (W : DualWitness B) (lam : B ⟶ W.dual P), W.IsPolarization P lam →
        ∀ g : Aut B, g.hom ≫ lam ≫ W.map P W g.hom = lam → IsOfFinOrder g) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : X.actionObj ≅ X.actionObj),
      PolarizedIntegralPowerModelWitness D C P compatibility h Ω X q e →
        (let f : End0 X.actionObj.abelianScheme := RationalAlgebraAction.hom0 e.hom
         IsOfFinOrder f) := by
  let := auxiliaryStarRing D C
  intro q e hw
  obtain ⟨eta, m, hm, hq, B, r, g, W, lam, hpol, hpres, hr, hg, hgi⟩ := hw
  exact finiteOrder_of_integral_conjugate_power r
    (RationalAlgebraAction.underlyingIso e) (2 * m) (Nat.mul_pos (by decide) hm)
    g hg (hfinite B W lam hpol g hpres)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

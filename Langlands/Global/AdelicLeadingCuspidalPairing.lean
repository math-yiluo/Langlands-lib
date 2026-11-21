import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDirectSum

/-! # Levi cusp-test pairings and the split-component action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "Y" => (AdelicGroupPoints F G → ℂ)
local notation "M" => fam.M J
local notation "P" => fam.P J
local notation "μJ" => normOneRationalQuotientHaarMeasure F M

/-- The adelic image of the positive split component commutes with the adelic image
of its Levi. -/
theorem commute_positiveSplitComponent_levi (a : fam.positiveSplitComponent J)
    (m : AdelicGroupPoints F M) :
    Commute (map F P G (fam.p J) a.val) (map F M G (fam.l J ≫ fam.p J) m) := by
  obtain ⟨b, _, hb⟩ := a.2
  have hc : Commute (map F (fam.A J).toGrp M (fam.a J) b) m :=
    commute_of_mem_center ((fam.isCompatible J).splitComponent.isCentralSplitTorus.isCentral _ b) m
  have hmap := hc.map (map F M G (fam.l J ≫ fam.p J)).toMonoidHom
  change Commute (map F M G (fam.l J ≫ fam.p J) (map F (fam.A J).toGrp M (fam.a J) b))
    (map F M G (fam.l J ≫ fam.p J) m) at hmap
  rw [← hb]
  exact hmap

/-- The unnormalized shift of a function on the pairing integrand can be
evaluated by shifting its external argument. -/
theorem leviPairingIntegrand_splitComponent (test : AdelicGroupPoints F (fam.M J) → ℂ)
    (a : fam.positiveSplitComponent J) (f : Y)
    (g : AdelicGroupPoints F G) :
    fam.leviPairingIntegrand J (fam.splitComponentRepresentation J a f) g test =
      fam.leviPairingIntegrand J f (map F P G (fam.p J) a.val * g) test := by
  funext q
  let m : AdelicGroupPoints F M := (Quotient.out q : normOneSubgroup F M).val
  let gM := map F M G (fam.l J ≫ fam.p J) m
  let gA := map F P G (fam.p J) a.val
  change f (gA * (gM * g)) * starRingEnd ℂ (test m) =
    f (gM * (gA * g)) * starRingEnd ℂ (test m)
  exact congrArg (fun x => f x * starRingEnd ℂ (test m))
    (by rw [← mul_assoc, (fam.commute_positiveSplitComponent_levi J a m).eq, mul_assoc])

/-- The space of functions whose pairings against a fixed Levi test
are absolutely convergent at every external argument. -/
def leviPairingDomain (test : AdelicGroupPoints F (fam.M J) → ℂ) : Submodule ℂ Y where
  carrier := {f | ∀ g, Integrable (fam.leviPairingIntegrand J f g test) μJ}
  zero_mem' := by
    intro g
    have hz : fam.leviPairingIntegrand J 0 g test = 0 := by
      funext q
      simp only [leviPairingIntegrand, Pi.zero_apply, zero_mul]
    rw [hz]
    exact integrable_zero _ _ _
  add_mem' := by
    intro f h hf hh g
    convert (hf g).add (hh g) using 1
    funext q
    simp only [leviPairingIntegrand, Pi.add_apply, add_mul]
  smul_mem' := by
    intro c f hf g
    convert (hf g).const_mul c using 1
    funext q
    simp only [leviPairingIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem splitComponent_mem_leviPairingDomain (test : AdelicGroupPoints F (fam.M J) → ℂ)
    (a : fam.positiveSplitComponent J)
    {f : Y} (hf : f ∈ fam.leviPairingDomain J test) :
    fam.splitComponentRepresentation J a f ∈ fam.leviPairingDomain J test := by
  intro g
  rw [fam.leviPairingIntegrand_splitComponent J test]
  exact hf _

/-- Pairing is linear on its domain of absolute integrability. -/
def leviPairingLinear (test : AdelicGroupPoints F (fam.M J) → ℂ) :
    fam.leviPairingDomain J test →ₗ[ℂ] Y where
  toFun f g := fam.leviPairing J f.val g test
  map_add' f h := by
    funext g
    change (∫ q, fam.leviPairingIntegrand J (f.val + h.val) g test q ∂μJ) =
      fam.leviPairing J f.val g test + fam.leviPairing J h.val g test
    have hadd : fam.leviPairingIntegrand J (f.val + h.val) g test =
        fam.leviPairingIntegrand J f.val g test + fam.leviPairingIntegrand J h.val g test := by
      funext q
      simp only [leviPairingIntegrand, Pi.add_apply, add_mul]
    rw [hadd]
    exact integral_add (f.2 g) (h.2 g)
  map_smul' c f := by
    funext g
    change (∫ q, fam.leviPairingIntegrand J (c • f.val) g test q ∂μJ) =
      c • fam.leviPairing J f.val g test
    unfold leviPairing
    rw [← integral_smul]
    congr 1
    funext q
    simp only [leviPairingIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]

local instance positiveSplitComponentCommGroup : CommGroup (fam.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (fam.positiveSplitComponent_mul_comm J a.2 b.2)

/-- Scalar cusp-test evaluations preserve joint generalized eigenspaces
for the unnormalized positive split-component action. -/
theorem leviPairingLinear_mem_jointGenEigenspace (test : AdelicGroupPoints F (fam.M J) → ℂ)
    {χ : fam.positiveSplitComponent J → ℂ} (f : fam.leviPairingDomain J test)
    (hf : f.val ∈ jointGenEigenspace (fam.splitComponentRepresentation J) χ) :
    (fam.leviPairingLinear J test) f ∈ jointGenEigenspace (fam.splitComponentRepresentation J) χ := by
  let T := fam.splitComponentRepresentation J
  let S := fam.leviPairingDomain J test
  let L := fam.leviPairingLinear J test
  apply mem_jointGenEigenspace.mpr
  intro a
  obtain ⟨k, hk⟩ := mem_jointGenEigenspace.mp hf a
  let D : Module.End ℂ Y := T a - χ a • 1
  have hD (x : Y) (hx : x ∈ S) : D x ∈ S :=
    S.sub_mem (fam.splitComponent_mem_leviPairingDomain J test a hx) (S.smul_mem _ hx)
  let d := D.restrict hD
  have hcomm (x : S) : L (d x) = D (L x) := by
    let Tx : S := ⟨T a x.val, fam.splitComponent_mem_leviPairingDomain J test a x.2⟩
    have hTx : L Tx = T a (L x) := by
      funext g
      change fam.leviPairing J (T a x.val) g test =
        fam.leviPairing J x.val (map F P G (fam.p J) a.val * g) test
      unfold leviPairing
      rw [fam.leviPairingIntegrand_splitComponent J test]
    change L (Tx - χ a • x) = T a (L x) - χ a • L x
    rw [map_sub, map_smul, hTx]
  have hpow (n : ℕ) : L ((d ^ n) f) = (D ^ n) (L f) := by
    induction n with
    | zero => simp only [pow_zero, Module.End.one_apply]
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hcomm, ih]
  have hzero : (d ^ k) f = 0 := by
    apply Subtype.ext
    rw [Module.End.pow_restrict]
    exact hk
  refine ⟨k, ?_⟩
  change (D ^ k) (L f) = 0
  rw [← hpow, hzero, map_zero]

end Langlands.Global.StandardParabolicFamily

import Langlands.Geometry.FormalGroup.FormalIdempotentTransport
import Langlands.Geometry.FormalGroup.HarrisComponentQuotient
import Langlands.Geometry.FormalGroup.HarrisWeilFramingHeight
import Langlands.Geometry.FormalGroup.PolarizedPrimalFraming

/-! # Relative Frobenius on the primal rigidifier of Harris's split Weil datum -/

noncomputable section

universe u

namespace Langlands.FormalGroup.Harris

open CategoryTheory ValuativeRel LocalDivision ModuleLaw
open PolarizedFramedAffinePoint
open scoped WithZero

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {prime : ℕ} [Fact prime.Prime]
variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable [Algebra ℤ_[prime] 𝒪[K]]
variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable [IsScalarTower ℤ_[prime] 𝒪[K] W] {ϖ : 𝒪[K]}
variable (frame : SplitPolarizedFrame prime K D W ϖ) (σ : W ≃ₐ[𝒪[K]] W)

local instance harrisWeilPrimalFramingPadicIntegerRingAlgebra : Algebra ℤ_[prime] (IntegerRing K D) :=
  Algebra.compHom (IntegerRing K D) (algebraMap ℤ_[prime] 𝒪[K])

variable [ExpChar (ResidueRing W (algebraMap 𝒪[K] W ϖ)) prime] (m : ℕ)
variable (hσ :
  (Nilp.twistResidueEquiv (σ.restrictScalars ℤ_[prime]) (σ.commutes ϖ)).toRingHom =
    iterateFrobenius (ResidueRing W (algebraMap 𝒪[K] W ϖ)) prime m)
variable (hF : (frame.order.frobeniusHom prime m
    (Nilp.twistResidueEquiv (σ.restrictScalars ℤ_[prime]) (σ.commutes ϖ)).toAlgHom hσ).val.IsIsogeny)
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)} {ι τ : Type} [Finite ι] [Finite τ]
variable {M : ModuleLaw ℤ_[prime] (ResidueRing W (algebraMap 𝒪[K] W ϖ)) ι}
variable {N : ModuleLaw ℤ_[prime] ((Nilp.reductionFunctor W (algebraMap 𝒪[K] W ϖ)).obj T).obj τ}

local notation "πW" => algebraMap 𝒪[K] W ϖ
local notation "σₚ" => AlgEquiv.restrictScalars ℤ_[prime] σ
local notation "hπ" => AlgEquiv.commutes σ ϖ
local notation "σ₀" => AlgEquiv.toAlgHom (Nilp.twistResidueEquiv σₚ hπ)
local notation "Frob" => frame.frobeniusRationalSimilitude m σ₀ hσ hF
local notation "Tσ" => Nilp.twistObj σₚ hπ T
local notation "r" => frameCoefficientMap prime πW T
local notation "twistSquare" => CoefficientChange.twist σₚ hπ frame T

/-- Relative Frobenius of the frame restricts to an invertible section on the primal images. -/
def primalFrobeniusSectionIso (A : frame.order.DivisionImage M) :
    RationalSectionIso ℚ_[prime] (M.map r) ((M.map σ₀).map r) (reducedTop T) :=
  (A.map r).restrictSectionIso ((A.map σ₀).map r) ((Frob).sectionIso.baseChange r)
    (((Frob).orderLinear.baseChange r) (0, 1))

theorem primalFrobeniusSectionIso_hom (A : frame.order.DivisionImage M) :
    (primalFrobeniusSectionIso frame σ m hσ hF (T := T) A).hom =
      RationalSection.ofHom ((M.frobeniusHom prime m σ₀ hσ).map r) ⊤ := by
  change (A.map r).restrictSection ((A.map σ₀).map r)
    (RationalSection.baseChange r ⊤ (Frob).sectionIso.hom) = _
  rw [← A.baseChange_restrictSection, frame.frobeniusRationalSimilitude_hom,
    A.restrictSection_ofHom]
  change RationalSection.baseChange r ⊤
    (RationalSection.ofHom (A.restrictHom (A.map σ₀) (frame.law.frobeniusHom prime m σ₀ hσ)) ⊤) = _
  rw [A.restrictHom_frobeniusHom, RationalSection.baseChange_ofHom]
  rfl

/-- The twisted source carries the transported image of the coefficient-Frobenius primal frame. -/
def splitSpecialWeilPrimalSource (A : frame.order.DivisionImage M) :
    (source (frame := frame) (T := Tσ)).order.DivisionImage
      (((M.map σ₀).map r).map (twistSquare).reduced) :=
  (((A.map σ₀).map r).map (twistSquare).reduced).transport
    (twistSquare).sourceIso.orderIso.toModuleIso
    ((twistSquare).sourceIso.orderIso.hom.commutes (0, 1))

/-- The twisted target carries the transported image of the old reduced target. -/
def splitSpecialWeilPrimalTarget (X : PolarizedFramedAffinePoint prime πW frame T)
    (B : X.reducedTarget.order.DivisionImage N) :
    (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).reducedTarget.order.DivisionImage
      (N.map (twistSquare).reduced) :=
  (B.map (twistSquare).reduced).transport
    ((twistSquare).targetIso (X.changeFrame Frob)).orderIso.toModuleIso
    (((twistSquare).targetIso (X.changeFrame Frob)).orderIso.hom.commutes (0, 1))

/-- The actual primal rigidifier of the (A.4) representative is pulled back after
inverse precomposition by relative Frobenius on the primal frame. -/
theorem splitSpecialWeilFrobeniusPoint_primalFraming_hom
    (X : PolarizedFramedAffinePoint prime πW frame T)
    (A : frame.order.DivisionImage M) (B : X.reducedTarget.order.DivisionImage N) :
    ((splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).primalFraming
      (splitSpecialWeilPrimalSource frame σ (T := T) A)
      (splitSpecialWeilPrimalTarget frame σ m hσ hF X B)).hom =
      RationalSection.baseChange (twistSquare).reduced ⊤
        (RationalSection.comp (X.primalFraming (A.map r) B).hom
          (primalFrobeniusSectionIso frame σ m hσ hF (T := T) A).inv) := by
  rw [primalFraming_hom, splitSpecialWeilFrobeniusPoint_rho, primalFraming_hom]
  let φ := (twistSquare).reduced
  let a := (twistSquare).sourceIso.orderIso
  let b := ((twistSquare).targetIso (X.changeFrame Frob)).orderIso
  let e := (Frob).sectionIso.baseChange r
  let A' := (A.map σ₀).map r
  let f := RationalSection.comp X.rho e.inv
  have ht := Hom.IdempotentImage.restrictSection_transportIso (A'.map φ) (B.map φ)
    a.toModuleIso b.toModuleIso (a.hom.commutes (0, 1)) (b.hom.commutes (0, 1))
    (RationalSection.baseChange φ ⊤ f)
  have hp := (A'.baseChange_restrictSection B φ f).symm
  have h := ((Frob).orderLinear.baseChange r).inverse e
  have hc := A'.restrictSection_comp (A.map r) B X.rho e.inv (h (0, 1))
  exact ht.trans (hp.trans (congrArg (RationalSection.baseChange φ ⊤) hc))

/-- The raw p-height of the primal rigidifier changes by minus the exponent
times the dimension of the primal frame. -/
theorem splitSpecialWeilFrobeniusPoint_hasPrimalFramingHeight
    (X : PolarizedFramedAffinePoint prime πW frame T)
    (A : frame.order.DivisionImage M) (B : X.reducedTarget.order.DivisionImage N)
    {H : ℕ} (hH : 0 < H) (hM : M.HasPiHeight (prime : ℤ_[prime]) prime H)
    (hRank : RelativeFrobeniusIsogenyStatement M prime m)
    {h : reducedTop T → ℤ} (hh : X.HasPrimalFramingHeight (A.map r) B h) :
    (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).HasPrimalFramingHeight
      (splitSpecialWeilPrimalSource frame σ (T := T) A)
      (splitSpecialWeilPrimalTarget frame σ m hσ hF X B)
      (fun x => h (coefficientOpenPoint (twistSquare).reduced ⊤ x) -
        (m * Nat.card ι : ℕ)) := by
  let e := primalFrobeniusSectionIso frame σ m hσ hF (T := T) A
  have hi := e.hasHeightFunction_inv_ofHom ((M.frobeniusHom prime m σ₀ hσ).map r)
    (primalFrobeniusSectionIso_hom frame σ m hσ hF (T := T) A) ((hRank σ₀ hσ).map r)
    X.localFraming.scalar_ne_zero (Fact.out : prime.Prime).pos hH (hM.map r) ((hM.map σ₀).map r)
  have hc := RationalSection.HasHeightFunction.comp (Fact.out : prime.Prime).two_le
    ((hM.map σ₀).map r) (hM.map r) hh hi
  unfold HasPrimalFramingHeight
  rw [splitSpecialWeilFrobeniusPoint_primalFraming_hom]
  have hfun : (fun x => h (coefficientOpenPoint (twistSquare).reduced ⊤ x) -
        (m * Nat.card ι : ℕ)) =
      (fun x => -((m * Nat.card ι : ℕ) : ℤ) + h x) ∘
        coefficientOpenPoint (twistSquare).reduced ⊤ := by
    funext x
    rw [Function.comp_apply, sub_eq_add_neg, add_comm]
  exact hfun.symm ▸ hc.baseChange (twistSquare).reduced

/-- The coordinate given by negative normalized primal height increases by one. -/
theorem splitSpecialWeilFrobeniusPoint_hasPrimalComponentHeight
    (X : PolarizedFramedAffinePoint prime πW frame T)
    (A : frame.order.DivisionImage M) (B : X.reducedTarget.order.DivisionImage N)
    {H : ℕ} (hH : 0 < H) (hM : M.HasPiHeight (prime : ℤ_[prime]) prime H)
    (hRank : RelativeFrobeniusIsogenyStatement M prime m)
    {j : reducedTop T → ℤ}
    (hj : X.HasPrimalFramingHeight (A.map r) B (fun x => -((m * Nat.card ι : ℕ) : ℤ) * j x)) :
    (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).HasPrimalFramingHeight
      (splitSpecialWeilPrimalSource frame σ (T := T) A)
      (splitSpecialWeilPrimalTarget frame σ m hσ hF X B)
      (fun x => -((m * Nat.card ι : ℕ) : ℤ) *
        (j (coefficientOpenPoint (twistSquare).reduced ⊤ x) + 1)) := by
  have hfun : (fun x => -((m * Nat.card ι : ℕ) : ℤ) *
        (j (coefficientOpenPoint (twistSquare).reduced ⊤ x) + 1)) =
      (fun x => -((m * Nat.card ι : ℕ) : ℤ) *
        j (coefficientOpenPoint (twistSquare).reduced ⊤ x) - (m * Nat.card ι : ℕ)) := by
    funext x
    ring
  exact hfun.symm ▸
    splitSpecialWeilFrobeniusPoint_hasPrimalFramingHeight frame σ m hσ hF X A B hH hM hRank hj

/-- If the first valuation coordinate gives the negative normalized primal
height before the Weil operation, the right translation in (A.3) gives it afterwards. -/
theorem splitSpecialWeilFrobeniusPoint_hasPrimalHeight_weilComponent_fst
    [Algebra ℚ_[prime] D] (νD : Valuation D ℤᵐ⁰) (νp : Valuation ℚ_[prime] ℤᵐ⁰)
    (g : (splitInvolution ℚ_[prime] D).similitudes) (uniformizer : (Dᵐᵒᵖ)ˣ)
    (hUniformizer : oppositeUnitOrder νD uniformizer = Multiplicative.ofAdd (1 : ℤ))
    (X : PolarizedFramedAffinePoint prime πW frame T)
    (A : frame.order.DivisionImage M) (B : X.reducedTarget.order.DivisionImage N)
    {H : ℕ} (hH : 0 < H) (hM : M.HasPiHeight (prime : ℤ_[prime]) prime H)
    (hRank : RelativeFrobeniusIsogenyStatement M prime m)
    (hg : X.HasPrimalFramingHeight (A.map r) B (fun _ =>
      -((m * Nat.card ι : ℕ) : ℤ) *
        (splitValuationCoordinates ℚ_[prime] D νD νp g).1.toAdd)) :
    (splitSpecialWeilFrobeniusPoint frame σ m hσ hF X).HasPrimalFramingHeight
      (splitSpecialWeilPrimalSource frame σ (T := T) A)
      (splitSpecialWeilPrimalTarget frame σ m hσ hF X B)
      (fun _ => -((m * Nat.card ι : ℕ) : ℤ) *
        (splitValuationCoordinates ℚ_[prime] D νD νp
          (g * weilComponentElement ℚ_[prime] D uniformizer
            (PolarizedOrderModule.frobeniusMultiplier prime 1) m)).1.toAdd) := by
  have he :
      (splitValuationCoordinates ℚ_[prime] D νD νp
        (g * weilComponentElement ℚ_[prime] D uniformizer
          (PolarizedOrderModule.frobeniusMultiplier prime 1) m)).1.toAdd =
        (splitValuationCoordinates ℚ_[prime] D νD νp g).1.toAdd + 1 := by
    rw [map_mul, weilComponentElement, splitValuationCoordinates_element, hUniformizer]
    rfl
  have hfun := congrArg (fun n : ℤ => fun _ : reducedTop Tσ =>
    -((m * Nat.card ι : ℕ) : ℤ) * n) he
  exact hfun.symm ▸
    splitSpecialWeilFrobeniusPoint_hasPrimalComponentHeight frame σ m hσ hF X A B hH hM hRank hg

end Langlands.FormalGroup.Harris

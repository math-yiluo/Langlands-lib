import Langlands.Geometry.FormalGroup.HarrisSplitFrameActionLaws

/-! # Frame action on the actual split polarized isomorphism classes -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v s

open CategoryTheory ValuativeRel

namespace Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint

open LocalDivision GroupScheme.Cartier PDivisibleGroup
open SpecialModule.HeightSquaredModule

attribute [local instance] Langlands.FormalGroup.Harris.splitPointTestAlgebra

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {W : Type v} [CommRing W] [Algebra 𝒪[K] W] {π : 𝒪[K]}
variable {p e : ℕ} [Fact p.Prime] {b : 𝒪[K]ˣ}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) («ι» := ι)
  (R := ResidueRing W (algebraMap 𝒪[K] W π)) π}
variable {hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e} {he : 0 < e}
variable {T : Nilp.{v, v} W (algebraMap 𝒪[K] W π)}

local notation "red" => specialFibre (π := π) T
local notation "α" => pDivisibleAction Φ hp he
local notation "Point" => SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T
local notation "Similitudes" => SplitFrameSimilitudes α

/-- The full special-fibre rigidifier obeys the inverse-precomposition formula. -/
theorem actFrame_rigidifier (g : SplitFrameSimilitudes (Φ.pDivisibleAction hp he))
    (X : SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T) (hExact : FiniteCartierDualExactnessStatement.{v}) :
    ((actFrame g X).rigidifier hExact).val =
      (inverseFrameOnSpecialFibre T hExact g).val.trans (X.rigidifier hExact).val := by
  have h := splitOrderRigidifierOnBaseChange_trans (S := red)
    (G₁ := Φ.pDivisibleGroup hp he) (G₂ := Φ.pDivisibleGroup hp he)
    (G₃ := pDivisibleGroup (R := T.obj) X.target hp he)
    (a := α) (b := α) (d := pDivisibleAction (R := T.obj) X.target hp he)
    hExact (OrderQuasiIsogeny.ofAut (orderAutBaseChange (S := red) α g.1)).symm
    X.primalRigidifier g.2⁻¹ X.multiplier
  dsimp only [rigidifier, actFrame, inverseFrameOnSpecialFibre, targetTower,
    splitPDivisibleGroup, orderAction, splitPDivisibleAction]
  with_reducible exact h

private def orderAutOfRigidifier {R : CommRingCat.{v}} {A : Type u} [Ring A]
    {G : PDivisibleGroup R p} {a : A →+* End G} (q : OrderQuasiIsogeny a a) : orderAut a :=
  ⟨q.val, q.commutes⟩

private def frameAutOnSpecialFibre (g : Similitudes) (hExact : FiniteCartierDualExactnessStatement.{v}) :=
  orderAutOfRigidifier (inverseFrameOnSpecialFibre T hExact g).symm

private def withRigidifier {R S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {A : Type u} [Ring A] {G : PDivisibleGroup (CommRingCat.of S) p} {a : A →+* End G}
    (X : PolarizedFramedTower (R := R) a)
    (q : OrderQuasiIsogeny a ((baseChangeEnd (S := S) X.target).comp X.order)) :
    PolarizedFramedTower (R := R) a :=
  { X with rigidifier := q }

private theorem act_orderAutOfRigidifier {R S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {A : Type u} [Ring A] {G : PDivisibleGroup (CommRingCat.of S) p} {a : A →+* End G}
    (X : PolarizedFramedTower (R := R) a) (q : OrderQuasiIsogeny a a) :
    PolarizedFramedTower.act (orderAutOfRigidifier q.symm) X =
      withRigidifier X (q.trans X.rigidifier) := rfl

private theorem framedTower_actFrame (g : Similitudes) (X : Point)
    (hExact : FiniteCartierDualExactnessStatement.{v}) :
    (actFrame g X).framedTower hExact =
      PolarizedFramedTower.act (frameAutOnSpecialFibre (T := T) g hExact) (X.framedTower hExact) := by
  have he := actFrame_rigidifier g X hExact
  have hr : (actFrame g X).rigidifier hExact =
      (inverseFrameOnSpecialFibre T hExact g).trans (X.rigidifier hExact) :=
    OrderQuasiIsogeny.ext_val he
  have h := congrArg (withRigidifier (S := red) (X.framedTower hExact)) hr
  have hg := act_orderAutOfRigidifier (X.framedTower hExact) (inverseFrameOnSpecialFibre T hExact g)
  change (actFrame g X).framedTower hExact =
    PolarizedFramedTower.act (orderAutOfRigidifier (inverseFrameOnSpecialFibre T hExact g).symm)
      (X.framedTower hExact)
  refine Eq.trans ?_ hg.symm
  dsimp only [withRigidifier, framedTower, actFrame, targetTower, orderAction, polarization,
    splitPDivisibleGroup, splitPDivisibleAction, splitPDivisiblePolarization] at h ⊢
  exact h

private def isoAfterFrameAction {R S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {A : Type u} [Ring A] {G : PDivisibleGroup (CommRingCat.of S) p} {a : A →+* End G}
    {X Y X' Y' : PolarizedFramedTower (R := R) a}
    (g : orderAut a) (i : PolarizedFramedTower.Iso X Y)
    (hx : X' = PolarizedFramedTower.act g X) (hy : Y' = PolarizedFramedTower.act g Y) :
    PolarizedFramedTower.Iso X' Y' :=
  hx.symm ▸ hy.symm ▸ i.act g

/-- The same actual target isometry identifies the framed points after inverse precomposition. -/
def actFrameIso (g : Similitudes) {X Y : Point} {hExact : FiniteCartierDualExactnessStatement.{v}}
    (i : PolarizedFramedTower.Iso (X.framedTower hExact) (Y.framedTower hExact)) :
    PolarizedFramedTower.Iso ((actFrame g X).framedTower hExact) ((actFrame g Y).framedTower hExact) := by
  have h := isoAfterFrameAction (S := red) (R := T.obj) (frameAutOnSpecialFibre (T := T) g hExact)
    i (framedTower_actFrame g X hExact) (framedTower_actFrame g Y hExact)
  exact h

/-- The actual frame similitudes act on the strict polarized isomorphism classes. -/
@[instance_reducible]
def frameAction (hExact : FiniteCartierDualExactnessStatement.{v}) :
    MulAction Similitudes (IsomorphismClass (W := W) (π := π) Φ hp he T hExact) where
  smul g := Quotient.map (actFrame g) (fun _ _ ⟨i⟩ => ⟨actFrameIso g i⟩)
  one_smul x := Quotient.inductionOn x fun X => congrArg Quotient.mk'' (actFrame_one X)
  mul_smul g h x := Quotient.inductionOn x fun X => congrArg Quotient.mk'' (actFrame_mul g h X)

end Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint

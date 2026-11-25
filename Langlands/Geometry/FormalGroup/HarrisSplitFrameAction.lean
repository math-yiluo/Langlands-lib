import Langlands.Geometry.FormalGroup.PDivisibleFrameSimilitudes
import Langlands.Geometry.FormalGroup.PDivisibleSplitRigidifierTransport

/-! # The frame action on actual split polarized affine points -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v s

open CategoryTheory ValuativeRel

namespace Langlands.PDivisibleGroup

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime] {A : Type v} [Ring A]
variable {G : PDivisibleGroup (CommRingCat.of R) p}

/-- Pull back the actual rational order automorphisms of the frame. -/
def orderAutBaseChange (a : A →+* End G) :
    orderAut a →* orderAut ((baseChangeEnd (S := S) G).comp a) := by
  let F := rationalBaseChangeFunctor R S p
  let f := F.mapAut (RationalCategory.of G)
  exact {
    toFun := fun g => ⟨f g.val, ((OrderQuasiIsogeny.ofAut g).baseChange (S := S)).commutes⟩
    map_one' := Subtype.ext f.map_one
    map_mul' g h := Subtype.ext (f.map_mul g.val h.val) }

end Langlands.PDivisibleGroup

namespace Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint

open LocalDivision ModuleLaw GroupScheme.Cartier PDivisibleGroup
open SpecialModule.HeightSquaredModule

attribute [local instance] Langlands.FormalGroup.Harris.splitPointTestAlgebra

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {W : Type v} [CommRing W] [Algebra 𝒪[K] W] {π : 𝒪[K]}
variable {p e : ℕ} [Fact p.Prime] {b : 𝒪[K]ˣ}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := ResidueRing W (algebraMap 𝒪[K] W π)) π}
variable {hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e} {he : 0 < e}
variable {T : Nilp.{v, v} W (algebraMap 𝒪[K] W π)}

local notation "red" => specialFibre (π := π) T
local notation "α" => pDivisibleAction Φ hp he

/-- Precompose the primal rigidifier by the inverse of the pulled-back frame automorphism. -/
def actFrame (g : SplitFrameSimilitudes (Φ.pDivisibleAction hp he))
    (X : SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T) :
    SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T :=
  letI e := OrderQuasiIsogeny.ofAut (orderAutBaseChange (S := red) α g.1)
  { X with
    primalRigidifier := e.symm.trans X.primalRigidifier
    multiplier := g.2⁻¹ * X.multiplier }

/-- The inverse frame similitude on the actual full split special fibre. -/
def inverseFrameOnSpecialFibre (T : Nilp.{v, v} W (algebraMap 𝒪[K] W π))
    (hExact : FiniteCartierDualExactnessStatement.{v})
    (g : SplitFrameSimilitudes (Φ.pDivisibleAction hp he)) :=
  let q := OrderQuasiIsogeny.ofAut (orderAutBaseChange (S := specialFibre (π := π) T) α g.1)
  splitOrderRigidifierOnBaseChange (S := specialFibre (π := π) T) hExact α α q.symm g.2⁻¹

@[simp] theorem actFrame_multiplier (g : SplitFrameSimilitudes (Φ.pDivisibleAction hp he))
    (X : SplitPDivisibleAffinePoint (W := W) (π := π) Φ hp he T) :
    (actFrame g X).multiplier = g.2⁻¹ * X.multiplier := rfl

end Langlands.FormalGroup.Harris.SplitPDivisibleAffinePoint

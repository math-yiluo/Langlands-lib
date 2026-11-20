import Langlands.Geometry.FormalGroup.PolarizedFramedAffineFunctor
import Langlands.Geometry.FormalGroup.SplitOrderSpecialTangent
import Langlands.Geometry.FormalGroup.HarrisSplitSimilitudes
import Langlands.Geometry.FormalGroup.SpecialModule

/-! # Affine split-special polarized framing in the Harris moduli problem -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.Harris

open CategoryTheory ValuativeRel LocalDivision ModuleLaw

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable (prime : ℕ) [Fact prime.Prime]
variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable [Algebra ℤ_[prime] 𝒪[K]]
variable (W : Type) [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable [wTower : IsScalarTower ℤ_[prime] 𝒪[K] W] (ϖ : 𝒪[K])

local instance : Algebra ℤ_[prime] (IntegerRing K D) :=
  Algebra.compHom (IntegerRing K D) (algebraMap ℤ_[prime] 𝒪[K])

/-- A fixed frame for the actual product of the division order and its opposite,
with the involution exchanging the factors. -/
abbrev SplitPolarizedFrame :=
  PolarizedOrderModule ((IntegerRing K D)ᵐᵒᵖ × IntegerRing K D)
    (splitInvolution ℤ_[prime] (IntegerRing K D))
    (ResidueRing W (algebraMap 𝒪[K] W ϖ)) (prime : ℤ_[prime])

variable {prime K D W ϖ}
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
variable {frame : SplitPolarizedFrame prime K D W ϖ}
variable {T U : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}
variable (X : PolarizedFramedAffinePoint prime (algebraMap 𝒪[K] W ϖ) frame T)

/-- The tangent condition on the division-order summand uses the actual central
integer ring and the actual unramified integer subfield of full degree. -/
def HasSplitSpecialTangent : Prop :=
  IsUnramifiedSubfieldOfReducedDegree K D ι ∧
    X.target.order.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] T.obj) ∧
    X.target.order.HasGeometricDivisionTangentCharacters.{0, u, 0, u, s}
      (subfieldIntegerInclusion K D ι).toRingHom (CentralSimple.reducedDegree K D)

namespace HasSplitSpecialTangent

variable {ι X}

omit wTower in
/-- A polarized framed isomorphism transports the special condition on the target. -/
theorem ofIso {Y : PolarizedFramedAffinePoint prime (algebraMap 𝒪[K] W ϖ) frame T}
    (h : HasSplitSpecialTangent ι X) (e : PolarizedFramedAffinePoint.Iso X Y) :
    HasSplitSpecialTangent ι Y :=
  ⟨h.1, h.2.1.ofIso e.targetIso.orderIso, h.2.2.ofIso e.targetIso.orderIso⟩

omit wTower in
/-- Coefficient extension preserves the structural and geometric special conditions. -/
theorem baseChange (h : HasSplitSpecialTangent ι X) (j : T ⟶ U) :
    HasSplitSpecialTangent ι (X.baseChange j) := by
  let θ := Nilp.scalarMap ℤ_[prime] j
  have hθ : θ.toRingHom.comp (algebraMap 𝒪[K] T.obj) = algebraMap 𝒪[K] U.obj :=
    RingHom.ext (fun a => j.hom.hom.commutes (algebraMap 𝒪[K] W a))
  have hs := h.2.1.map θ
  rw [hθ] at hs
  exact ⟨h.1, hs, h.2.2.map θ⟩

end HasSplitSpecialTangent

/-- The special condition is an invariant of the actual affine framed isomorphism class. -/
def isSplitSpecialClass
    (q : PolarizedFramedAffinePoint.IsomorphismClass (frame := frame) (T := T)) : Prop :=
  Quotient.lift (HasSplitSpecialTangent ι) (by
    intro X Y h
    change Nonempty (PolarizedFramedAffinePoint.Iso X Y) at h
    obtain ⟨e⟩ := h
    exact propext ⟨fun h => h.ofIso e, fun h => h.ofIso e.symm⟩) q

omit wTower in
/-- The actual coefficient map sends special framed classes to special framed classes. -/
theorem isSplitSpecialClass_baseChange (ι : L →ₐ[K] D)
    {q : PolarizedFramedAffinePoint.IsomorphismClass (frame := frame) (T := T)}
    (h : isSplitSpecialClass ι q) (j : T ⟶ U) : isSplitSpecialClass ι (q.baseChange j) := by
  induction q using Quotient.inductionOn with
  | h X =>
    exact (show HasSplitSpecialTangent ι X from h).baseChange j

include wTower in
/-- Affine polarized framed classes satisfying the split-special tangent condition. -/
def splitSpecialAffineFunctor (frame : SplitPolarizedFrame prime K D W ϖ) :
    Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ) ⥤ Type (max 1 u) where
  obj T := {q : PolarizedFramedAffinePoint.IsomorphismClass (frame := frame) (T := T) //
    isSplitSpecialClass ι q}
  map j := ↾(fun q => ⟨q.val.baseChange j, isSplitSpecialClass_baseChange ι q.property j⟩)
  map_id _ := by
    ext q
    exact q.val.baseChange_id
  map_comp j k := by
    ext q
    exact (q.val.baseChange_comp j k).symm

/-- The inclusion forgets the tangent condition and retains the whole affine framed class. -/
def splitSpecialToPolarized (frame : SplitPolarizedFrame prime K D W ϖ) :
    splitSpecialAffineFunctor ι frame ⟶ PolarizedFramedAffinePoint.classFunctor frame where
  app _ := ↾Subtype.val
  naturality _ _ _ := rfl

end Langlands.FormalGroup.Harris

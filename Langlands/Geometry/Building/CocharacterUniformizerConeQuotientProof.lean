import Langlands.Geometry.Building.CocharacterUniformizerConeQuotientStatement
import Langlands.Geometry.Building.CocharacterUniformizerQuotientProof
import Langlands.GroupScheme.Rational.SimpleRootSplitCentralImageProof

/-! # The nonnegative cocharacter and actual split-central quotients: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

/-- The common-uniformizer group quotient comparison, with its kernel identified
as the simple-root annihilator, restricts to the nonnegative monoids. -/
theorem coneQuotientComparison : ConeQuotientComparisonStatement.{u} := by
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  intro ν hν A a ha f hf
  let R := simpleRelativeRoots i ν
  let P := RealTorusSpace.rootAnnihilatorInt T R
  let N := (CA F A).map (rationalPoints.map (CommGroupScheme.groupHom f))
  let q := QuotientGroup.mk' N
  have hP : P = (RealTorusSpace.cocharacterMapInt f).range :=
    simpleRootSplitCentralImage F G hG T i hi ν hν A a ha f hf
  have he := quotientComparison F A T hi.1.1 f
  rw [← hP] at he
  obtain ⟨e, he⟩ := he
  let g : Multiplicative (CocharacterCone.quotient T R) →*
      CAplusQuotient F T R A f :=
    { toFun := fun x =>
        ⟨(e (Multiplicative.ofAdd x.toAdd.val)).val, by
          obtain ⟨c, hc, hcx⟩ := x.toAdd.property
          change P.mkQ c = x.toAdd.val at hcx
          rw [← hcx]
          exact ⟨latticeSection F T (Multiplicative.ofAdd c),
            ⟨Multiplicative.ofAdd c, hc, rfl⟩, (he c).symm⟩⟩
      map_one' := by
        apply Subtype.ext
        change (e 1).val = (1 : rationalPoints T.toGrp ⧸ N)
        exact congrArg (fun z : (CA F T).map q => z.val) e.map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        change
          (e (Multiplicative.ofAdd x.toAdd.val *
            Multiplicative.ofAdd y.toAdd.val)).val =
          (e (Multiplicative.ofAdd x.toAdd.val)).val *
            (e (Multiplicative.ofAdd y.toAdd.val)).val
        exact congrArg (fun z : (CA F T).map q => z.val)
          (e.map_mul (Multiplicative.ofAdd x.toAdd.val)
            (Multiplicative.ofAdd y.toAdd.val)) }
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    have heq :
        e (Multiplicative.ofAdd x.toAdd.val) =
          e (Multiplicative.ofAdd y.toAdd.val) :=
      Subtype.ext
        (congrArg (fun z : CAplusQuotient F T R A f => z.val) hxy)
    exact congrArg Multiplicative.toAdd (e.injective heq)
  have hgsurj : Function.Surjective g := by
    intro b
    obtain ⟨a, ⟨c, hc, rfl⟩, hab⟩ := b.property
    refine ⟨Multiplicative.ofAdd ⟨P.mkQ c.toAdd, ⟨c.toAdd, hc, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (he c.toAdd).trans hab
  refine ⟨MulEquiv.ofBijective g ⟨hginj, hgsurj⟩, ?_⟩
  intro c hc
  exact he c

end Langlands.GroupScheme.CocharacterUniformizer

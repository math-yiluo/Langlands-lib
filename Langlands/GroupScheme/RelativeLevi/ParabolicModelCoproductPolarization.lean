import Langlands.GroupScheme.RelativeLevi.ParabolicAffineEtaleCover
import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleAmpleCover
import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleBaseChangeComp

/-! # Universal polarization on finite coproduct parabolic models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {hG : IsReductive G}

namespace SmoothProperModel

/-- On a finite coproduct of affine bases, ample local universal values of
the same coherent bundle give ampleness on the assembled smooth proper model. -/
theorem coproduct_universal_isAmple {I : Type u} [Finite I]
    (X : I → Scheme.{u}) [∀ i, IsAffine (X i)] (f : ∀ i, X i ⟶ S)
    (d : ∀ i, SmoothProperModel ((GroupScheme.baseChange (f i)).obj G)
      (hG.baseChange (f i)))
    (L : PresheafLineBundle (parabolicPresheaf G hG))
    (hL : ∀ i, ((L.baseChange (f i)).universal
      (restrictedRepresentation (f i) (d i))).IsAmple) :
    ((L.baseChange (Sigma.desc f)).universal
      (restrictedRepresentation (Sigma.desc f) (coproduct (hG := hG) X f d))).IsAmple := by
  let p := Sigma.desc f
  let D := coproduct (hG := hG) X f d
  let : IsProper D.scheme.hom := D.proper
  let e := restrictedRepresentation (hH := hG) p D
  let N : ∀ i : I, Over (X i) := fun i => (d i).scheme
  let eN : ∀ i : I, ((Over.map (Sigma.ι X i)).op ⋙
      (Over.map p).op ⋙ parabolicPresheaf G hG).RepresentableBy (N i) :=
    fun i => PresheafLineBundle.baseChangeCompRepresentation p (Sigma.ι X i)
      (f i) (by simp [p]) (restrictedRepresentation (f i) (d i))
  apply (L.baseChange p).isAmple_universal_of_affine_openCover e (sigmaOpenCover X) N eN
  intro i
  exact (hL i).of_iso ((LineBundle.forget _).mapIso
    (L.baseChangeCompUniversalIso p (Sigma.ι X i) (f i) (by simp [p])
      (restrictedRepresentation (f i) (d i))).symm)

/-- Assemble the supplied local models and package the ample universal value
of the same original coherent line bundle on their finite affine coproduct. -/
def coproductPolarized {I : Type u} [Finite I]
    (X : I → Scheme.{u}) [∀ i, IsAffine (X i)] (f : ∀ i, X i ⟶ S)
    (d : ∀ i, SmoothProperModel ((GroupScheme.baseChange (f i)).obj G)
      (hG.baseChange (f i)))
    (L : PresheafLineBundle (parabolicPresheaf G hG))
    (hL : ∀ i, ((L.baseChange (f i)).universal
      (restrictedRepresentation (f i) (d i))).IsAmple) :
    {D : SmoothProperModel ((GroupScheme.baseChange (Sigma.desc f)).obj G)
      (hG.baseChange (Sigma.desc f)) //
      ((L.baseChange (Sigma.desc f)).universal
        (restrictedRepresentation (Sigma.desc f) D)).IsAmple} :=
  ⟨coproduct (hG := hG) X f d,
    coproduct_universal_isAmple (hG := hG) X f d L hL⟩

end SmoothProperModel

end Langlands.GroupScheme.ParabolicSubgroupModuli

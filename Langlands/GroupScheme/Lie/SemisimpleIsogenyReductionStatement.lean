import Langlands.AbelianScheme.Isogeny
import Langlands.GroupScheme.Nilpotent.Basic
import Langlands.GroupScheme.Lie.SemisimpleElement
import Langlands.GroupScheme.Lie.ElementCentralizer

/-! # Statement: isogeny reduction to the nilpotent or semisimple case -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An isogeny reduces a connected group variety to a nilpotent group or one
with a geometric noncentral semisimple Lie element, while lifting target tori. -/
def SemisimpleIsogenyReductionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∃ (G' : GroupScheme (Spec (CommRingCat.of k))) (φ : G ⟶ G')
      (_ : Smooth G'.X.hom) (hAffine : IsAffineHom G'.X.hom)
      (_ : ConnectedSpace G'.X.left),
      letI : IsAffineHom G'.X.hom := hAffine
      let Gbar := (GroupScheme.baseChange (toAlgebraicClosure k)).obj G'
      letI : IsAffineHom Gbar.X.hom := by
        change IsAffineHom (pullback.snd G'.X.hom (toAlgebraicClosure k))
        infer_instance
      IsIsogeny φ ∧
        (IsNilpotentGroupScheme G' ∨
          ∃ X : lieKernel Gbar (AlgebraicClosure k),
            Lie.IsSemisimpleElement Gbar X ∧ Lie.elementCentralizerLie Gbar X ≠ ⊤) ∧
        ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G'),
          IsTorus T'.toGrp → IsClosedSubgroup i' →
            ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
              (f : T.toGrp ⟶ T'.toGrp),
              IsTorus T.toGrp ∧ IsClosedSubgroup i ∧ IsIsogeny f ∧ i ≫ φ = f ≫ i'

end Langlands.GroupScheme

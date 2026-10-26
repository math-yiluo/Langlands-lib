import Langlands.AlgebraicGeometry.Picard.CubeIsomorphismAssembly
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso

/-! # Three-pullback comparison using actual line-bundle inverses -/

universe u

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

namespace LineBundle

/-- Three ordinary pullback comparisons detect an isomorphism of line bundles
using their actual dual inverses and the supplied triviality criterion. -/
def carrierIsoOfThreePullbackComparisons
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S T₁ T₂ T₃ : Scheme.{u}}
    (f₁ : T₁ ⟶ S) (f₂ : T₂ ⟶ S) (f₃ : T₃ ⟶ S)
    (triviality : ∀ D : LineBundle S,
      Nonempty ((Scheme.Modules.pullback f₁).obj D.obj ≅ structureSheaf T₁) →
      Nonempty ((Scheme.Modules.pullback f₂).obj D.obj ≅ structureSheaf T₂) →
      Nonempty ((Scheme.Modules.pullback f₃).obj D.obj ≅ structureSheaf T₃) →
      Nonempty (D.obj ≅ structureSheaf S))
    (L M : LineBundle S)
    (e₁ : (Scheme.Modules.pullback f₁).obj L.obj ≅
      (Scheme.Modules.pullback f₁).obj M.obj)
    (e₂ : (Scheme.Modules.pullback f₂).obj L.obj ≅
      (Scheme.Modules.pullback f₂).obj M.obj)
    (e₃ : (Scheme.Modules.pullback f₃).obj L.obj ≅
      (Scheme.Modules.pullback f₃).obj M.obj) : L.obj ≅ M.obj := Classical.choice <| by
  obtain ⟨N, ⟨inverse⟩⟩ := M.exists_tensorObj_iso_structureSheaf
  let difference := LineBundle.tensor preservation L N
  obtain ⟨trivialization⟩ := triviality difference
    ⟨pullbackTensorInverseTrivialization preservation f₁ e₁ inverse⟩
    ⟨pullbackTensorInverseTrivialization preservation f₂ e₂ inverse⟩
    ⟨pullbackTensorInverseTrivialization preservation f₃ e₃ inverse⟩
  let inverse' : M.obj ⊗ N.obj ≅ 𝟙_ S.Modules :=
    localizedTensorIso S M.obj N.obj ≪≫ inverse
  exact ⟨(ρ_ L.obj).symm ≪≫
    (Iso.refl L.obj ⊗ᵢ ((β_ N.obj M.obj) ≪≫ inverse').symm) ≪≫
    (α_ L.obj N.obj M.obj).symm ≪≫
    ((localizedTensorIso S L.obj N.obj ≪≫ trivialization) ⊗ᵢ Iso.refl M.obj) ≪≫
    (λ_ M.obj)⟩

end LineBundle

namespace RigidifiedLineBundle

/-- Two relative restriction comparisons detect equality of actual rigidified
classes if the section and these restrictions detect ordinary triviality. -/
lemma classes_eq_of_threePullbackTrivialityWithDual
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)
    {T U V : Over S} (h : U ⟶ T) (k : V ⟶ T)
    (triviality : ∀ D : LineBundle ((relativeSpace f).obj T),
      Nonempty ((Scheme.Modules.pullback ((relativeSection f ε section_eq).app T)).obj
        D.obj ≅ structureSheaf T.left) →
      Nonempty ((Scheme.Modules.pullback ((relativeSpace f).map h)).obj D.obj ≅
        structureSheaf ((relativeSpace f).obj U)) →
      Nonempty ((Scheme.Modules.pullback ((relativeSpace f).map k)).obj D.obj ≅
        structureSheaf ((relativeSpace f).obj V)) →
      Nonempty (D.obj ≅ structureSheaf ((relativeSpace f).obj T)))
    (q r : Classes f ε section_eq T)
    (hh : classesPullback f ε section_eq h q = classesPullback f ε section_eq h r)
    (hk : classesPullback f ε section_eq k q = classesPullback f ε section_eq k r) :
    q = r := by
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M =>
      obtain ⟨e₂⟩ := Quotient.exact hh
      obtain ⟨e₃⟩ := Quotient.exact hk
      let e := LineBundle.carrierIsoOfThreePullbackComparisons preservation
        ((relativeSection f ε section_eq).app T)
        ((relativeSpace f).map h) ((relativeSpace f).map k) triviality
        ((forget _).obj L) ((forget _).obj M)
        (L.obj.rigidification.symm ≪≫ M.obj.rigidification)
        (((forget _ ⋙ LineBundle.forget _).mapIso e₂))
        (((forget _ ⋙ LineBundle.forget _).mapIso e₃))
      exact Quotient.sound ⟨isoOfCarrierIso preservation ((relativeProjection f).app T)
        (relativeSection_projection f ε section_eq T) e⟩

end RigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard

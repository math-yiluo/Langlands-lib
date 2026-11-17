import Langlands.GroupScheme.Reductive.FiniteFieldPinnedForm
import Langlands.GroupScheme.Reductive.StarActionFiniteStageLift

/-! # Constructing a form over a finite field with prescribed class -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k] [Fintype k]
    {G₀ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G₀.X.hom]
    (p : SplitPinning G₀) (θ : p.basedRootDatumAut)

/-- An actual form with Galois pinning data and the prescribed Frobenius class. -/
structure FiniteFieldForm where
  group : GroupScheme (Spec (CommRingCat.of k))
  [affine : IsAffineHom group.X.hom]
  [locallyOfFiniteType : LocallyOfFiniteType group.X.hom]
  pinningData : GaloisPinningData k (SeparableClosure k) group
  rootEquiv : RootPairing.Equiv p.rootDatum pinningData.toSplitPinning.rootDatum
  preserves_base : ∀ a, a ∈ p.base.support ↔
    rootEquiv.indexEquiv a ∈ pinningData.toSplitPinning.base.support
  frobenius : RootPairing.Equiv.comp rootEquiv θ.val =
    RootPairing.Equiv.comp
      (pinningData.starAction
        (FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k))).val rootEquiv

attribute [instance] FiniteFieldForm.affine FiniteFieldForm.locallyOfFiniteType

/-- Construct a form of each prescribed finite-order based automorphism. -/
def finiteFieldForm (hθ : IsOfFinOrder θ) : FiniteFieldForm p θ := by
  apply Classical.choice
  obtain ⟨K, hK, aK, hfin, hgal, G, haff, hlft, d, e, hb, hF⟩ :=
    p.exists_finiteFrobeniusClass θ hθ
  let := hK
  let := aK
  let := hfin
  let := hgal
  let := haff
  let := hlft
  obtain ⟨d', e', hb', hF'⟩ :=
    StarActionFiniteStage.exists_frobenius_class_of_stage p θ d e hb hF
  exact
    ⟨{
      group := G
      pinningData := d'
      rootEquiv := e'
      preserves_base := hb'
      frobenius := hF' }⟩

end Langlands.GroupScheme.SplitPinning

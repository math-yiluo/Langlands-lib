import Langlands.GroupScheme.Reductive.QuasiSplitStarCriterionProof
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneReduction
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.LinearAlgebra.CartanE7Root

/-! # Splitting of quasi-split simply connected groups of type `E_7` -/

universe u

open CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A quasi-split simply connected group with actual Cartan matrix of type `E_7`
has a split maximal torus over its ground field. -/
def QuasiSplitTypeE7SplittingStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
    IsSimplyConnected G →
    (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
    IsQuasiSplit G → HasSplitMaximalTorus G

set_option backward.isDefEq.respectTransparency false in
/-- Rigidity of the `E_7` diagram gives trivial star action on the full root datum
by the coroot span criterion for simply connected groups. -/
theorem quasiSplitTypeE7Splitting : QuasiSplitTypeE7SplittingStatement.{u} := by
  intro K _ G _ _ d e hsc hcart hqs
  have hvertices := d.starIsTrivial_of_cartan_rigid e hcart Langlands.CartanE7Root.rigid
  let bc := algebraBaseMap K (SeparableClosure K)
  have : IsAffineHom ((GroupScheme.baseChange bc).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom bc)
    infer_instance
  have hscSep := isSimplyConnectedFieldExtension K (SeparableClosure K) G hsc
  have hspan : d.pinning.toSplitPinning.rootDatum.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpan (SeparableClosure K) _ hscSep _ d.pinning.isSplitTorus
      _ d.pinning.isMaximalTorus _ _ d.pinning.isRootDatum d.pinning.isReduced
  apply (quasiSplitStarCriterion K G hqs d.pinning).mpr
  intro σ
  apply Subtype.ext
  exact InnerTypeANormOneReduction.aut_eq_one_of_simple d.pinning.base hspan
    (d.pinning.starAction σ).val (fun a => congrArg Subtype.val (hvertices σ a))

end Langlands.GroupScheme

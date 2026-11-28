import Langlands.GroupScheme.Reductive.QuasiSplitStarCriterionProof
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneReduction
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.SimplyConnected.SplitNecessityIndependentProof
import Langlands.LinearAlgebra.CartanENumbering

/-! # Splitting of quasi-split simply connected groups of type `E₈` -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A quasi-split simply connected group with actual Cartan matrix of type `E₈`
has a split maximal torus over the ground field. -/
def QuasiSplitTypeE8SplittingStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
    IsSimplyConnected G →
    (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
    IsQuasiSplit G → HasSplitMaximalTorus G

set_option backward.isDefEq.respectTransparency false in
/-- The absolute star action on the full based root datum of a simply connected
group of type `E₈` is trivial. -/
theorem TitsIndexData.starAction_eq_one_of_typeE8
    {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8) (hsc : IsSimplyConnected G)
    (hcart : ∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) : d.pinning.starAction σ = 1 := by
  have hvertices := d.starIsTrivial_of_cartan_rigid e hcart CartanENumbering.rigid_eight
  have hscSep := isSimplyConnectedFieldExtension K (SeparableClosure K) G hsc
  have hspan : d.pinning.toSplitPinning.rootDatum.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpanIndependent (SeparableClosure K) _ hscSep _
      d.pinning.isSplitTorus _ d.pinning.isMaximalTorus _ d.pinning.rootDatum
      d.pinning.isRootDatum d.pinning.isReduced
  apply Subtype.ext
  exact InnerTypeANormOneReduction.aut_eq_one_of_simple d.pinning.base hspan
    (d.pinning.starAction σ).val (fun a => congrArg Subtype.val (hvertices σ a))

/-- The trivial absolute star action gives a split maximal torus in the quasi-split group. -/
theorem quasiSplitTypeE8Splitting : QuasiSplitTypeE8SplittingStatement.{u} := by
  intro K _ G _ _ d e hsc hcart hqs
  exact (quasiSplitStarCriterion K G hqs d.pinning).mpr
    (d.starAction_eq_one_of_typeE8 e hsc hcart)

end Langlands.GroupScheme

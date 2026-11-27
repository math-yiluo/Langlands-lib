import Langlands.GroupScheme.Rational.QuasiSplitInnerFormFiniteSeparable
import Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Reductive.PinningGroupIsoTransport
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # The quasi-split model of an inner form shares its absolute invariants -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiSplitInnerForm

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (qf : QuasiSplitInnerForm G)

/-- The local isomorphisms of a quasi-split inner form, restricted along an embedding of its
carrier into a field `Ω`, give an isomorphism of the base changes to `Ω` of the model and of
the group. -/
def baseChangeIso (Ω : Type u) [Field Ω] [Algebra k Ω] (j : qf.carrier →ₐ[k] Ω) :
    (GroupScheme.baseChange (algebraBaseMap k Ω)).obj qf.model ≅
      (GroupScheme.baseChange (algebraBaseMap k Ω)).obj G :=
  (qf.localIso.refine (coverRefinement j)).toBaseChangeIso

/-- The model of a quasi-split inner form of a simply connected group is simply connected. -/
theorem isSimplyConnected_model (hG : IsSimplyConnected G) : IsSimplyConnected qf.model := by
  rw [← isSimplyConnected_fieldExtension_iff (K := qf.carrier)]
  exact IsSimplyConnected.of_iso (qf.baseChangeIso qf.carrier (AlgHom.id k qf.carrier))
    ((isSimplyConnected_fieldExtension_iff G).mpr hG)

/-- The model of a quasi-split inner form of an absolutely almost-simple group is absolutely
almost-simple. -/
theorem isAbsolutelyAlmostSimple_model (hG : IsAbsolutelyAlmostSimple G) :
    IsAbsolutelyAlmostSimple qf.model := by
  apply IsAbsolutelyAlmostSimple.of_fieldExtension (K := qf.carrier)
  exact (hG.baseChange_of_algebraicExtension (K := qf.carrier)).of_iso
    (qf.baseChangeIso qf.carrier (AlgHom.id k qf.carrier))

private instance separableClosureBaseChangeAffine (H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom _)
  infer_instance

/-- Any Tits index data of the model and of the group have the same Cartan pairings under a
bijection of their simple vertices. -/
theorem exists_vertexEquiv_cartan [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom qf.model.X.hom] [LocallyOfFiniteType qf.model.X.hom]
    (d : TitsIndexData G) (dH : TitsIndexData qf.model) :
    ∃ f : dH.Vertex ≃ d.Vertex, ∀ a b, d.cartan (f a) (f b) = dH.cartan a b := by
  let j : qf.carrier →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let φ := qf.baseChangeIso (SeparableClosure k) j
  let p := dH.pinning.toSplitPinning.mapGroupIso φ
  let q := d.pinning.toSplitPinning
  obtain ⟨-, -, e, -, -, hbase⟩ := StarActionIndependence.exists_conj_based p q
  refine ⟨e.indexEquiv.subtypeEquiv hbase, fun a b => ?_⟩
  exact e.toHom.pairing

end Langlands.GroupScheme.QuasiSplitInnerForm

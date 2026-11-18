import Langlands.GroupScheme.CentralIsogeny.TitsDiagram
import Langlands.GroupScheme.Reductive.TitsCartanComponentTransport
import Langlands.GroupScheme.SimplyConnected.CoverExistenceProof
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.Rational.CentralIsogenySplitRank

/-! # Component realization reduces to simply connected groups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace TitsIndexData.CartanStarEquiv

variable {k : Type u} [Field k]
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [LocallyOfFiniteType C.X.hom]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData C} {e : TitsIndexData G} (h : CartanStarEquiv d e)

/-- An actual full Cartan equivalence preserves and reflects connectivity,
without a condition on zero restrictions. -/
theorem cartanConnected_iff (a b : d.Vertex) :
    e.CartanConnected (h.vertices a) (h.vertices b) ↔ d.CartanConnected a b := by
  constructor
  · intro hab
    have hc : ∀ x y, d.cartan (h.vertices.symm x) (h.vertices.symm y) = e.cartan x y := by
      intro x y
      simpa only [Equiv.apply_symm_apply] using
        (h.cartan_eq (h.vertices.symm x) (h.vertices.symm y)).symm
    have h' := hab.map e h.vertices.symm.injective hc
    simpa only [Equiv.symm_apply_apply] using h'
  · exact fun hab => hab.map d h.vertices.injective h.cartan_eq

/-- Restrict the full diagram equivalence to the prescribed entire component. -/
def cartanComponentEquiv (a : d.Vertex) :
    d.CartanComponent a ≃ e.CartanComponent (h.vertices a) :=
  h.vertices.subtypeEquiv (fun b => (h.cartanConnected_iff a b).symm)

@[simp] theorem cartanComponentEquiv_val (a : d.Vertex) (b : d.CartanComponent a) :
    (h.cartanComponentEquiv a b).val = h.vertices b.val := rfl

/-- The full absolute-Galois component stabilizer is unchanged. -/
theorem cartanComponentStabilizer_eq (a : d.Vertex) :
    d.cartanComponentStabilizer a = e.cartanComponentStabilizer (h.vertices a) := by
  apply Subgroup.ext
  intro σ
  change d.CartanConnected a (d.star σ a) ↔
    e.CartanConnected (h.vertices a) (e.star σ (h.vertices a))
  rw [← h.star_eq]
  exact (h.cartanConnected_iff a (d.star σ a)).symm

/-- Transport a complete component factor through a central isogeny from a
simply connected source. The cover, all Cartan entries, both simultaneous
full-star lifts and anisotropy are retained. -/
def componentFactorOfCentralIsogeny (hC : IsSimplyConnected C)
    (π : C ⟶ G) (hπ : IsCentralIsogeny π) {a : d.Vertex} (F : d.ComponentFactor a) :
    e.ComponentFactor (h.vertices a) where
  extension := F.extension
  factor := F.factor
  simplyConnected := F.simplyConnected
  absolutelyAlmostSimple := F.absolutelyAlmostSimple
  complement := F.complement
  complement_simplyConnected := F.complement_simplyConnected
  cover := F.cover ≫ π
  cover_simplyConnected := F.cover_simplyConnected
  cover_centralIsogeny := by
    have : IsIso F.cover := hC.central_isogeny_isIso _ F.cover
      F.cover_simplyConnected.isSemisimple F.cover_centralIsogeny
    exact hπ.iso_comp (asIso F.cover)
  index := F.index
  vertexEquiv := F.vertexEquiv.trans (h.cartanComponentEquiv a)
  cartan_eq b c :=
    (h.cartan_eq (F.vertexEquiv b).val (F.vertexEquiv c).val).trans (F.cartan_eq b c)
  stabilizer_lift σ hσ := by
    have hd : d.CartanConnected a (d.star σ a) := by
      apply (h.cartanConnected_iff a (d.star σ a)).mp
      rw [h.star_eq]
      exact hσ
    obtain ⟨τ, hτ⟩ := F.stabilizer_lift σ hd
    refine ⟨τ, fun b => ?_⟩
    change h.vertices (F.vertexEquiv (F.index.star τ b)).val =
      e.star σ (h.vertices (F.vertexEquiv b).val)
    rw [hτ b, h.star_eq]
  star_lift τ := by
    obtain ⟨σ, hσ⟩ := F.star_lift τ
    refine ⟨σ, fun b => ?_⟩
    change h.vertices (F.vertexEquiv (F.index.star τ b)).val =
      e.star σ (h.vertices (F.vertexEquiv b).val)
    rw [hσ b, h.star_eq]
  anisotropic hG := by
    apply F.anisotropic
    have : IsFinite π.hom.hom.left := hπ.isFinite
    apply le_antisymm _ bot_le
    exact (splitRank_le_of_isFinite π).trans_eq hG

end TitsIndexData.CartanStarEquiv

/-- The component-realization obligation restricted to simply connected
semisimple groups, at the same arbitrary universe and field scope. -/
def SimplyConnectedTitsComponentFactorStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (C : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom C.X.hom]
    [LocallyOfFiniteType C.X.hom] (d : TitsIndexData C), IsSimplyConnected C →
      ∀ a : d.Vertex, Nonempty (d.ComponentFactor a)

/-- Actual simply connected covers, actual index existence and the exact
central-isogeny diagram comparison reduce the full target to simply
connected groups; every witness field of the original target is retained. -/
theorem semisimpleTitsComponentFactor_of_simplyConnected
    (h : SimplyConnectedTitsComponentFactorStatement.{u}) :
    SemisimpleTitsComponentFactorStatement.{u} := by
  intro k _ G _ _ d a
  obtain ⟨C, π, hπ⟩ := simplyConnectedCoverExistence k G d.isSemisimple
  let hCr := hπ.isSimplyConnected.isSemisimple.isConnectedReductive
  let := hCr.isAffineHom
  let := hCr.smooth
  let dC := Classical.choice (titsIndexExistence k C hπ.isSimplyConnected.isSemisimple)
  let E := dC.cartanStarEquivOfCentralIsogeny d π hπ.isCentralIsogeny
  obtain ⟨F⟩ := h k C dC hπ.isSimplyConnected (E.vertices.symm a)
  have hF := E.componentFactorOfCentralIsogeny hπ.isSimplyConnected π hπ.isCentralIsogeny F
  exact ⟨(E.vertices.apply_symm_apply a) ▸ hF⟩

end Langlands.GroupScheme

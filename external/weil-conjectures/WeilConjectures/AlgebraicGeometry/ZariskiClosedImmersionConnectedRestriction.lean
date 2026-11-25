/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import WeilConjectures.Topology.SpectralClosedRestriction
import WeilConjectures.Topology.ClosedEmbeddingRestrictionTransport

/-!
# Zariski restriction along a closed immersion with connected point closures

Source: Stacks Project, Tag 09ZG, `lemma-h0-topological`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Universe transport of the spectral restriction bijection to the Zariski inverse-image unit.
The proof follows the ULift/order-isomorphism transport in the blueprint.

Proof: transport the spectral restriction map along the ULift homeomorphism and the induced
order isomorphisms on opens; these preserve covers, sheaf sections, and the adjunction unit
at the top open, so bijectivity is preserved.
(blueprint: lem-weil-pbc-zariski-restriction-universe-transport) -/
theorem zariski_restriction_universe_transport
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hconn : ∀ x : X, IsConnected (closure ({x} : Set X) ∩ Set.range i)) :
      letI : ∀ P : X.Opensᵒᵖ ⥤ Type (u + 1),
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)).op.HasPointwiseLeftKanExtension P :=
            fun P U ↦
              @Types.hasColimit.{u, u + 1, u}
                (CostructuredArrow.{u, u, u, u} (Opens.map i.base).op U)
                inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X.toTopCat,
      Function.Bijective
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)) (Type (u + 1))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app G).hom.app
            (op (⊤ : X.Opens))) := by
  classical
  let : T0Space X.toTopCat := (inferInstance : T0Space X)
  let : CompactSpace X.toTopCat := (inferInstance : CompactSpace X)
  let : QuasiSober X.toTopCat := (inferInstance : QuasiSober X)
  let : PrespectralSpace X.toTopCat := (inferInstance : PrespectralSpace X)
  let : QuasiSeparatedSpace X.toTopCat := (inferInstance : QuasiSeparatedSpace X)
  let Y := TopCat.of (ULift.{u + 1} X)
  let e : Y ≃ₜ X.toTopCat := Homeomorph.ulift
  let : CompactSpace Y := e.symm.compactSpace
  let : T0Space Y := e.isEmbedding.t0Space
  let : QuasiSober Y := e.isClosedEmbedding.quasiSober
  let : PrespectralSpace Y := PrespectralSpace.of_isClosedEmbedding e e.isClosedEmbedding
  let : QuasiSeparatedSpace Y := e.isOpenEmbedding.quasiSeparatedSpace
  let : SpectralSpace Y := {}
  let D : Set Y := e ⁻¹' Set.range i.base
  have hD : IsClosed D := (Scheme.Hom.isClosedEmbedding i).isClosed_range.preimage e.continuous
  have hc (y : Y) : ConnectedSpace (↥(D ∩ closure ({y} : Set Y))) := by
    apply isConnected_iff_connectedSpace.mp
    have h := e.isConnected_preimage.mpr (hconn (e y))
    have he : e ⁻¹' ({e y} : Set X.toTopCat) = {y} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, e.injective.eq_iff]
    rw [Set.preimage_inter, e.preimage_closure, he, Set.inter_comm] at h
    exact h
  intro G
  obtain ⟨F, a, b, hsquare⟩ := TopCat.closed_embedding_restriction_transport_square
    i.base (Scheme.Hom.isClosedEmbedding i).isEmbedding Y e G
  have hb := TopCat.spectral_closed_restriction Y D hD hc F
  constructor
  · intro s t h
    apply a.injective
    apply hb.1
    exact (hsquare s).symm.trans ((congrArg b h).trans (hsquare t))
  · intro t
    obtain ⟨s, hs⟩ := hb.2 (b t)
    refine ⟨a.symm s, b.injective ?_⟩
    exact (hsquare (a.symm s)).trans
      ((congrArg _ (a.apply_symm_apply s)).trans hs)

end AlgebraicGeometry

import Langlands.GroupScheme.Reductive.SemilinearPinningCoherence

/-! # Identity normalization for actual semilinear pinned lifts -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Descent
variable {S : Scheme.{u}} (b : S ⟶ S) (hb : b = 𝟙 S)

/-- The canonical actual identity comparison with an explicitly equal base map. -/
def baseChangeEqIdentityIso (G : GroupScheme S) :
    (GroupScheme.baseChange b).obj G ≅ G :=
  eqToIso (congrArg (fun f => (GroupScheme.baseChange f).obj G) hb) ≪≫
    baseChangeIdIso G

@[simp] theorem baseChangeEqIdentityIso_hom_left (G : GroupScheme S) :
    (baseChangeEqIdentityIso b hb G).hom.hom.hom.left = pullback.fst G.X.hom b := by
  subst b
  simpa only [baseChangeEqIdentityIso, eqToIso_refl, Iso.refl_trans] using
    baseChangeIdIso_hom_left G

include hb in
theorem baseChangeEqIdentity_map_injective {G H : GroupScheme S} {f g : G ⟶ H}
    (hfg : (GroupScheme.baseChange b).map f = (GroupScheme.baseChange b).map g) : f = g := by
  subst b
  have hf := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫
    Functor.mapGrpIdIso).hom.naturality f
  have hg := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫
    Functor.mapGrpIdIso).hom.naturality g
  change (GroupScheme.baseChange (𝟙 S)).map f ≫ (baseChangeIdIso H).hom =
    (baseChangeIdIso G).hom ≫ f at hf
  change (GroupScheme.baseChange (𝟙 S)).map g ≫ (baseChangeIdIso H).hom =
    (baseChangeIdIso G).hom ≫ g at hg
  exact (cancel_epi (baseChangeIdIso G).hom).mp
    (hf.symm.trans ((congrArg (fun a => a ≫ (baseChangeIdIso H).hom) hfg).trans hg))

theorem baseChangeEqIdentity_tower (G : GroupScheme S) (hbb : b ≫ b = b) :
    (GroupScheme.baseChange b).mapIso (baseChangeEqIdentityIso b hb G) =
      pullbackComparison b b b hbb G := by
  apply CategoryTheory.Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change _ ≫ pullback.fst G.X.hom b = _
    rw [pullbackComparison_hom_fst]
    change pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_fst, baseChangeEqIdentityIso_hom_left]
  · exact (Over.w ((GroupScheme.baseChange b).mapIso
        (baseChangeEqIdentityIso b hb G)).hom.hom.hom).trans
      (Over.w (pullbackComparison b b b hbb G).hom.hom.hom).symm

end Descent

namespace SplitPinning
variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The identity semilinear lift is the canonical actual pullback identity. -/
theorem semilinearPinnedIso_one_groupIso :
    (p.semilinearPinnedIso (RingEquiv.refl k) 1).groupIso =
      Descent.baseChangeEqIdentityIso
        (Spec.map (CommRingCat.ofHom (RingEquiv.refl k).toRingHom))
        (by change Spec.map (𝟙 (CommRingCat.of k)) = _; exact Spec.map_id _) G := by
  let b := Spec.map (CommRingCat.ofHom (RingEquiv.refl k).toRingHom)
  have hb : b = 𝟙 _ := by
    change Spec.map (𝟙 (CommRingCat.of k)) = _
    exact Spec.map_id _
  let f := (p.semilinearPinnedIso (RingEquiv.refl k) 1).groupIso
  have hcomp := p.semilinearPinnedIso_comp_groupIso (RingEquiv.refl k)
    (RingEquiv.refl k) 1 1
  simp only [one_mul] at hcomp
  have hcancel := (cancel_mono f.hom).mp (congrArg CategoryTheory.Iso.hom hcomp)
  apply CategoryTheory.Iso.ext
  apply Descent.baseChangeEqIdentity_map_injective b hb
  exact hcancel.symm.trans
    (congrArg CategoryTheory.Iso.hom (Descent.baseChangeEqIdentity_tower b hb G
      (by rw [hb]; exact Category.id_comp _))).symm

end SplitPinning
end Langlands.GroupScheme

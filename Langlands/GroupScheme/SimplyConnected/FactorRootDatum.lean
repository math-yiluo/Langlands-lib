import Langlands.GroupScheme.SimplyConnected.FactorRoots
import Langlands.GroupScheme.CentralIsogeny.CorootCompatibility
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Actual factor root indices and integral Cartan pairings -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
namespace FactorMaximalTorus

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct G) (hG : IsSemisimple G)
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
  {i : D.Index} (F : D.FactorMaximalTorus t i)

private instance factorRootDatum_factorAffine : IsAffineHom (D.factor i).X.hom :=
  (D.isSimplyConnected i).isSemisimple.isConnectedReductive.isAffineHom

private instance factorRootDatum_factorSmooth : Smooth (D.factor i).X.hom :=
  (D.isSimplyConnected i).isSemisimple.isConnectedReductive.smooth

variable {J K : Type u}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum K (characterLattice F.torus) (cocharacterLattice F.torus)}
  (hP : IsRootDatumOf t P) (hQ : IsRootDatumOf F.subgroupHom Q)

/-- The actual ambient root index of each actual factor root, via literal
character pullback along the split torus projection. -/
def rootIndex (b : K) : J :=
  (Equiv.ofInjective P.root P.root.injective).symm
    ⟨F.projectionHom ≫ Q.root b, by
      rw [hP.2.1]
      exact (F.root_inflation hG hT ht (Q.root b) (by
        rw [← hQ.2.1]
        exact Set.mem_range_self b)).choose⟩

/-- The index map preserves the literal actual root character. -/
theorem rootIndex_root (b : K) :
    P.root (F.rootIndex D hG hT t ht hP hQ b) = F.projectionHom ≫ Q.root b :=
  Equiv.apply_ofInjective_symm P.root.injective _

/-- Every actual factor-root index maps into its specified ambient factor. -/
theorem rootIndex_factor (b : K) :
    D.rootDatumFactorIndex hG hT t ht hP (F.rootIndex D hG hT t ht hP hQ b) = i := by
  have h := (F.root_inflation hG hT ht (Q.root b) (by
    rw [← hQ.2.1]
    exact Set.mem_range_self b)).choose_spec
  unfold rootDatumFactorIndex
  simpa only [F.rootIndex_root D hG hT t ht hP hQ] using h

/-- Root-index pullback is injective, since the torus projection has a section. -/
theorem rootIndex_injective : Function.Injective (F.rootIndex D hG hT t ht hP hQ) := by
  intro b c h
  apply Q.root.injective
  apply F.characterPullback_injective
  simpa only [← F.rootIndex_root D hG hT t ht hP hQ] using congrArg P.root h

/-- Every ambient root assigned to this factor comes from its actual root datum. -/
theorem rootIndex_surjective {r : J} (hr : D.rootDatumFactorIndex hG hT t ht hP r = i) :
    ∃ b : K, F.rootIndex D hG hT t ht hP hQ b = r := by
  have hα : P.root r ∈ roots t := by
    rw [← hP.2.1]
    exact Set.mem_range_self r
  obtain ⟨β, hβ, hβα⟩ := F.root_restriction hG hT ht hα hr
  rw [← hQ.2.1] at hβ
  obtain ⟨b, rfl⟩ := hβ
  refine ⟨b, P.root.injective ?_⟩
  rw [F.rootIndex_root D hG hT t ht hP hQ]
  exact hβα

/-- The exact full root-index equivalence with the actual ambient factor fibre. -/
def rootIndexEquiv : K ≃ {r : J // D.rootDatumFactorIndex hG hT t ht hP r = i} :=
  Equiv.ofBijective
    (fun b => ⟨F.rootIndex D hG hT t ht hP hQ b,
      F.rootIndex_factor D hG hT t ht hP hQ b⟩)
    ⟨fun _ _ h => F.rootIndex_injective D hG hT t ht hP hQ (congrArg Subtype.val h), by
      intro r
      obtain ⟨b, hb⟩ := F.rootIndex_surjective D hG hT t ht hP hQ r.property
      exact ⟨b, Subtype.ext hb⟩⟩

/-- Matching actual coroots are carried by the actual torus projection.
The finite normalizer-image criterion requires no group isogeny. -/
theorem coroot_projection (b : K) :
    P.coroot (F.rootIndex D hG hT t ht hP hQ b) ≫ F.projectionHom = Q.coroot b := by
  have : IsSplitEpi (CommGroupScheme.groupHom F.projectionHom) :=
    IsSplitEpi.mk' ⟨CommGroupScheme.groupHom F.torusHom, F.projection_section⟩
  have : IsClosedImmersion F.subgroupHom.hom.hom.left := F.isMaximalTorus.2.1
  have : Finite (weylImage F.subgroupHom) :=
    splitTorusWeylImageFinite k (D.factor i) _ F.split F.subgroupHom F.isMaximalTorus.2.1
  apply hP.coroot_comp_of_finite_weylImage t F.subgroupHom (D.projection i) F.projectionHom
    F.projection_comp.symm hQ hT
  exact (F.rootIndex_root D hG hT t ht hP hQ b).symm

/-- Every ordered integral root-coroot pairing is unchanged. -/
theorem pairing_rootIndex (b c : K) :
    P.pairing (F.rootIndex D hG hT t ht hP hQ b)
        (F.rootIndex D hG hT t ht hP hQ c) = Q.pairing b c := by
  rw [← P.root_coroot_eq_pairing, hP.1, F.rootIndex_root D hG hT t ht hP hQ,
    ← Q.root_coroot_eq_pairing, hQ.1]
  change gmEndEquiv k (P.coroot (F.rootIndex D hG hT t ht hP hQ c) ≫
    (F.projectionHom ≫ Q.root b)) = gmEndEquiv k (Q.coroot c ≫ Q.root b)
  rw [← Category.assoc, F.coroot_projection D hG hT t ht hP hQ]

end FactorMaximalTorus
end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

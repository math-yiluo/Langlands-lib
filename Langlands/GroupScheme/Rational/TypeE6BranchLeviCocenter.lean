import Langlands.GroupScheme.Rational.TypeE6BranchLeviRootDatum
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.Torus.CharacterFaithfullyFlat
import Langlands.GroupScheme.Torus.SplitOfDomination

/-! # The split torus quotient of the E6 branch Levi -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G M D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom D.X.hom]

local notation "E" => SeparableClosure k
local notation "b" => algebraBaseMap k (SeparableClosure k)
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))

set_option backward.isDefEq.respectTransparency false in
/-- The cocenter of the branch Levi is split. The image of the rational branch
cocharacter dominates it, as seen on the geometric character lattice. -/
theorem TypeE6BranchDerivedPinning.exists_splitCocenter
    {d : TitsIndexData G} {e : d.Vertex ≃ Fin 6} {i : D ⟶ M}
    (p : TypeE6BranchDerivedPinning d e i)
    (hsc : IsSimplyConnected G) (hM : IsConnectedReductive M) (hi : IsDerivedSubgroup i)
    (ν : cocharacterLattice d.splitTorus)
    (hν : cocharacterLattice.baseChange b d.pinning.torus (ν ≫ d.torusMap) =
      d.typeE6BranchCoweight e) :
    ∃ (Q : CommGroupScheme (Spec (CommRingCat.of k))) (q : M ⟶ Q.toGrp),
      IsSplitTorus Q.toGrp ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q := by
  obtain ⟨Q, q, -, hq, hQt, hsurj⟩ := cocenterQuotientExistence k M D i hM hi
  obtain ⟨hQE, hCE⟩ := hsurj d.pinning.torus p.centralizerTorus p.centralizerTorus_maximal
    E d.pinning.isSplitTorus
  let : IsSeparated Q.X.hom := fieldSeparated k Q.toGrp
  let h : d.pinning.torus ⟶ Q := Additive.ofMul (p.centralizerTorus ≫ q)
  let hE := (BC).map h
  have hτ : p.torusMap ≫ h = 0 := by
    change Additive.ofMul (CommGroupScheme.groupHom p.torusMap ≫ p.centralizerTorus ≫ q) = 0
    rw [← Category.assoc, p.square, Category.assoc, hi.comp_eq_one q]
    simp
  have hτE : (BC).map p.torusMap ≫ hE = 0 := by
    rw [← Functor.map_comp, hτ, Functor.map_zero]
  let Q_E := (BC).obj Q
  let T_E := (BC).obj d.pinning.torus
  let r (a : Fin 6) : cocharacterLattice T_E := d.pinning.rootDatum.coroot (e.symm a).val
  have hr (a : Fin 6) (ha : a ≠ 1) : r a ≫ hE = 0 := by
    let x : {v : d.Vertex // e v ≠ 1} := ⟨e.symm a, by simpa only [e.apply_symm_apply] using ha⟩
    have hx : (p.vertices (p.vertices.symm x)).val.val = (e.symm a).val := by
      rw [Equiv.apply_symm_apply]
    change d.pinning.rootDatum.coroot (e.symm a).val ≫ hE = 0
    rw [← hx, ← p.coroot_eq, Category.assoc, hτE, comp_zero]
  let f : cocharacterLattice Q := (ν ≫ d.torusMap) ≫ h
  have hf : cocharacterLattice.baseChange b Q f = d.typeE6BranchCoweight e ≫ hE := by
    change cocharacterLattice.baseChange b Q ((ν ≫ d.torusMap) ≫ h) = _
    rw [cocharacterLattice.baseChange_comp, hν]
  have hχ : Function.Injective (characterLattice.comapHom (CommGroupScheme.groupHom ((BC).map f))) := by
    rw [injective_iff_map_eq_zero]
    intro ψ hψ
    change (BC).map f ≫ ψ = 0 at hψ
    let s : cocharacterLattice T_E →ₗ[ℤ] ℤ :=
      (latticePairing Q_E ψ).comp (RealTorusSpace.cocharacterMapInt hE)
    have hs (a : Fin 6) (ha : a ≠ 1) : s (r a) = 0 := by
      change latticePairing Q_E ψ (r a ≫ hE) = 0
      rw [hr a ha, map_zero]
    have hc : s (d.typeE6BranchCoweight e) = 0 := by
      change latticePairing Q_E ψ (d.typeE6BranchCoweight e ≫ hE) = 0
      rw [← hf, latticePairing_apply]
      change gmEndEquiv E (((Gm.commBaseChangeIso b).inv ≫ (BC).map f) ≫ ψ) = 0
      rw [Category.assoc, hψ, comp_zero]
      exact (gmEndEquiv E).map_zero
    have hs₁ : s (r 1) = 0 := by
      change s (∑ a : Fin 6, Langlands.CartanE6Root.coefficients a • r a) = 0 at hc
      rw [map_sum, Finset.sum_eq_single (1 : Fin 6)] at hc
      · have htwo : Langlands.CartanE6Root.coefficients 1 = 2 := by decide
        rw [map_zsmul, htwo, zsmul_eq_mul] at hc
        exact (mul_eq_zero.mp hc).resolve_left (by decide)
      · intro a _ ha
        rw [map_zsmul, hs a ha, smul_zero]
      · simp
    have hsall (a : Fin 6) : s (r a) = 0 := by
      rcases eq_or_ne a 1 with rfl | ha
      · exact hs₁
      · exact hs a ha
    let B := Langlands.RootDatum.simpleCorootBasis d.pinning.rootDatum d.pinning.base
      (d.pinning_corootSpan_eq_top hsc)
    have hs0 : s = 0 := by
      apply B.ext
      intro a
      simp only [B, Langlands.RootDatum.simpleCorootBasis_apply, LinearMap.zero_apply]
      simpa only [r, Equiv.symm_apply_apply] using hsall (e a)
    let : (latticePairing Q_E).IsPerfPair := hQE.isPerfPair_latticePairing
    apply (LinearMap.IsPerfPair.bijective_left (latticePairing Q_E)).injective
    ext v
    change Function.Surjective (fun x : cocharacterLattice T_E => x ≫ hE) at hCE
    obtain ⟨x, rfl⟩ := hCE v
    rw [map_zero, LinearMap.zero_apply]
    change s x = 0
    exact LinearMap.congr_fun hs0 x
  have hsE := IsSplitTorus.flat_and_surjective_of_injective_characterPullback
    ((isSplitTorus_gm (S := Spec (CommRingCat.of k))).baseChange b) hQE
    (CommGroupScheme.groupHom ((BC).map f)) hχ
  let : Surjective b := (fieldExtension_fpqc k E).1
  let : Surjective (CommGroupScheme.groupHom f).hom.hom.left :=
    surjective_overHom_of_baseChange b (CommGroupScheme.groupHom f).hom.hom hsE.2
  have hQsplit := hQt.isSplitTorus_of_pointed_dominant_morphism isSplitTorus_gm
    (CommGroupScheme.groupHom f).hom.hom (MonObj.one_comp _) inferInstance
  exact ⟨Q, q, hQsplit, hq⟩

end Langlands.GroupScheme

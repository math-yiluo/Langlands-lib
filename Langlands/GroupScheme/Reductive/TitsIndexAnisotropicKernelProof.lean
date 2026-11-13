import Langlands.GroupScheme.Reductive.TitsIndexAnisotropicKernelStatement
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Proof: the semisimple anisotropic kernel is semisimple and anisotropic -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- A closed split torus of a semisimple group whose inclusion is central has empty
index type. -/
theorem IsSemisimple.isEmpty_of_isCentral_splitTorus
    {D : GroupScheme (Spec (CommRingCat.of k))} (hD : IsSemisimple D)
    (I : Type u) [Finite I] (t : splitTorus (Spec (CommRingCat.of k)) I ⟶ D)
    (ht : IsClosedSubgroup t) (hc : IsCentral t) : IsEmpty I := by
  have hB : IsSplitTorus (splitTorus (Spec (CommRingCat.of k)) I) := isSplitTorus_splitTorus I
  have := hB.smooth
  have := hB.isAffineHom
  have := hB.connectedSpace
  obtain ⟨Z, z, hz, hfin⟩ := hD.hasFiniteCenter
  have hr := hz.isRepresentedBy
  have hl := hr.liftOfLE_comp t ((isCentral_iff_range_le_center t).1 hc)
  let q : Z ⟶ Grp.trivial (Over (Spec (CommRingCat.of k))) := default
  have : IsFinite q.hom.hom.left := by
    have hw : q.hom.hom.left = Z.X.hom :=
      (Category.comp_id _).symm.trans (Over.w q.hom.hom)
    rw [hw]
    exact hfin
  have hab := finiteHom_cancel q (a := hr.liftOfLE t ((isCentral_iff_range_le_center t).1 hc))
    (b := 0) (Subsingleton.elim _ _)
  have ht0 : t = 0 := by
    rw [← hl, hab, zero_comp]
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  refine ⟨fun a => ?_⟩
  have hs : splitTorus.single (Spec (CommRingCat.of k)) I a = 0 := by
    apply CommGroupScheme.hom_ext_points
    intro U x
    apply (cancel_mono t.hom.hom).mp
    rw [Category.assoc, show t.hom.hom = 1 from congrArg (fun f => f.hom.hom) ht0]
    simp only [MonObj.comp_one]
  have hid : (𝟙 (Gm (Spec (CommRingCat.of k)))) = 0 := by
    have h := congrArg
      (fun f : cocharacterLattice
          (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) =>
        f ≫ splitTorus.proj (Spec (CommRingCat.of k)) I a) hs
    simpa [splitTorus.single_comp_proj] using h
  have h := congrArg (gmEndEquiv k) hid
  simp at h

/-- **Tits §2.2.** The derived group of every actual representative of the centralizer
of the maximal split torus of actual Tits index data is semisimple and anisotropic. -/
theorem titsAnisotropicKernel : TitsAnisotropicKernelStatement.{u} := by
  intro k _ G _ _ d M j hj D i hi
  have hG : IsConnectedReductive G := d.isSemisimple.isConnectedReductive
  have hM : IsConnectedReductive M :=
    splitTorusCentralizerReductive k G hG d.splitTorus d.splitInclusion
      d.maximalSplit.1.1 M j hj
  have hD : IsSemisimple D := derivedSubgroupSemisimple k M D i hM hi
  refine ⟨hD, ?_⟩
  apply isAnisotropic_iff.mpr
  intro I _ t ht
  -- Points of `M`, mapped to `G`, centralize the maximal split torus.
  have hcent : ∀ (U : Over (Spec (CommRingCat.of k))) (m : U ⟶ M.X)
      (y : U ⟶ d.splitTorus.X),
      Commute (m ≫ j.hom.hom) (y ≫ d.splitInclusion.hom.hom) := by
    intro U m y
    have hm : m ≫ j.hom.hom ∈ (torusCentralizer d.splitInclusion).carrier U := by
      rw [← hj.2]
      exact ⟨m, rfl⟩
    have h := hm U (𝟙 U) y
    rwa [Category.id_comp] at h
  -- The composite split torus of `G` commutes with the maximal split torus.
  have hcomm : ∀ (U : Over (Spec (CommRingCat.of k)))
      (x : U ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) (y : U ⟶ d.splitTorus.X),
      Commute (x ≫ (t ≫ i ≫ j).hom.hom) (y ≫ d.splitInclusion.hom.hom) := by
    intro U x y
    have h := hcent U (x ≫ t.hom.hom ≫ i.hom.hom) y
    simpa only [Grp.comp_hom_hom, Category.assoc] using h
  obtain ⟨f, hf⟩ := d.maximalSplit.exists_factor_of_commute
    (isSplitTorus_splitTorus I) (t ≫ i ≫ j) hcomm
  -- Hence `t` is central in `D`.
  have hiclosed : IsClosedImmersion i.hom.hom.left := hi.1
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := hj.1
  have htc : IsCentral t := by
    intro U x T' a h
    show (a ≫ x ≫ t.hom.hom) * h = h * (a ≫ x ≫ t.hom.hom)
    apply (cancel_mono i.hom.hom).mp
    apply (cancel_mono j.hom.hom).mp
    simp only [MonObj.mul_comp]
    have hx : ((a ≫ x ≫ t.hom.hom) ≫ i.hom.hom) ≫ j.hom.hom =
        (a ≫ x ≫ f.hom.hom) ≫ d.splitInclusion.hom.hom := by
      have := congrArg (fun g => (a ≫ x) ≫ g.hom.hom) hf
      simpa only [Grp.comp_hom_hom, Category.assoc] using this.symm
    rw [hx]
    exact (hcent T' (h ≫ i.hom.hom) (a ≫ x ≫ f.hom.hom)).symm.eq
  exact hD.isEmpty_of_isCentral_splitTorus I t ht htc

end Langlands.GroupScheme

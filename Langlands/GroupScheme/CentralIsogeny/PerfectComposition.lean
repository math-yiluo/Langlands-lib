import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.FieldFixedSubgroupRepresentabilityProof
import Mathlib.GroupTheory.Commutator.Basic

/-! # Composites of central isogenies out of a perfect field group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme

/-- If every commutator `⁅w, z⁆` is central, then `z` commutes with every commutator: the map
`w ↦ ⁅w, z⁆` is then a homomorphism into the centre, so it kills commutators. -/
theorem commute_commutatorElement_of_forall_commute {M : Type*} [Group M] (z : M)
    (hz : ∀ w g : M, Commute ⁅w, z⁆ g) (x y : M) : Commute z ⁅x, y⁆ := by
  have hmul : ∀ a b : M, ⁅a * b, z⁆ = ⁅a, z⁆ * ⁅b, z⁆ := by
    intro a b
    calc ⁅a * b, z⁆ = a * (⁅b, z⁆ * z) * a⁻¹ * z⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (a * ⁅b, z⁆) * z * a⁻¹ * z⁻¹ := by group
      _ = (⁅b, z⁆ * a) * z * a⁻¹ * z⁻¹ := by rw [(hz b a).eq]
      _ = ⁅b, z⁆ * ⁅a, z⁆ := by simp only [commutatorElement_def]; group
      _ = ⁅a, z⁆ * ⁅b, z⁆ := (hz b _).eq
  let ψ : M →* Subgroup.center M :=
    MonoidHom.mk' (fun w => ⟨⁅w, z⁆, Subgroup.mem_center_iff.2 fun g => (hz w g).eq.symm⟩)
      fun a b => Subtype.ext (hmul a b)
  have hψ : ψ ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (Subtype.ext (hz x _).eq)
  have h : ⁅⁅x, y⁆, z⁆ = 1 := congrArg Subtype.val hψ
  exact (commutatorElement_eq_one_iff_commute.1 h).symm

variable {k : Type u} [Field k] {H' H G : GroupScheme (Spec (CommRingCat.of k))}

namespace IsCentralIsogeny

variable {f : H' ⟶ H} {q : H ⟶ G}

/-- A point of `H'` killed by `f ≫ q` commutes with every commutator of points of `H'`. -/
theorem commute_commutator_of_comp_eq_one (hf : IsCentralIsogeny f) (hq : IsCentralIsogeny q)
    {T : Over (Spec (CommRingCat.of k))} {z : T ⟶ H'.X} (hz : z ≫ (f ≫ q).hom.hom = 1)
    (x y : T ⟶ H'.X) : Commute z ⁅x, y⁆ := by
  apply commute_commutatorElement_of_forall_commute
  intro w g
  apply commute_of_mem_center
  apply hf.mem_center_of_comp_eq_one
  have hzf : z ≫ f.hom.hom ∈ (center H).carrier T := by
    apply hq.mem_center_of_comp_eq_one
    rwa [Category.assoc, ← Grp.comp_hom_hom]
  rw [commutatorElement_def, MonObj.mul_comp, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, GrpObj.inv_comp, ((commute_of_mem_center hzf) (w ≫ f.hom.hom)).eq.symm]
  group

/-- **Composites of central isogenies out of a perfect group are central.** Over a field, if
the source `H'` has total scheme-theoretic derived subgroup, then the composite of two central
isogenies `f : H' ⟶ H` and `q : H ⟶ G` is a central isogeny. The kernel of `f ≫ q` acts on
`H'` by conjugation; its fixed subgroup is closed (`fieldFixedSubgroupRepresentability`) and
contains every commutator, hence contains the derived subgroup, which is everything. -/
theorem comp_of_derivedSubgroup_eq_top (hperf : derivedSubgroup H' = ⊤)
    (hf : IsCentralIsogeny f) (hq : IsCentralIsogeny q) : IsCentralIsogeny (f ≫ q) := by
  have hiso : IsIsogeny (f ≫ q) := IsIsogeny.comp hf.isIsogeny hq.isIsogeny
  have hlfp : LocallyOfFinitePresentation (f ≫ q).hom.hom.left := by
    have := hf.locallyOfFinitePresentation
    have := hq.locallyOfFinitePresentation
    change LocallyOfFinitePresentation (f.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  refine ⟨hiso, hlfp, ?_⟩
  have hfin : IsFinite (kernel (f ≫ q)).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme (f ≫ q)) hiso.1
  let a := AutomorphicAction.conjugation (kernelι (f ≫ q))
  obtain ⟨C, j, hj, hjc⟩ :=
    fieldFixedSubgroupRepresentability k (kernel (f ≫ q)) H' inferInstance a
  have hcomm : (SubgroupFunctor.range j).ContainsCommutators := by
    intro T x y
    rw [hj.2, AutomorphicAction.mem_fixedSubgroup]
    intro T' b h
    have hz : (h ≫ (kernelι (f ≫ q)).hom.hom) ≫ (f ≫ q).hom.hom = 1 :=
      (mem_range_kernelι_iff (f ≫ q) _).mp ⟨h, rfl⟩
    have hc := commute_commutator_of_comp_eq_one hf hq hz (b ≫ x) (b ≫ y)
    rw [AutomorphicAction.conjugation_act]
    have hb : b ≫ (x * y * x⁻¹ * y⁻¹) = ⁅b ≫ x, b ≫ y⁆ := by
      rw [commutatorElement_def, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul,
        GrpObj.comp_inv, GrpObj.comp_inv]
    rw [hb, hc.eq, mul_inv_cancel_right]
  have hle : derivedSubgroup H' ≤ a.fixedSubgroup := by
    rw [← hj.2]
    exact derivedSubgroup_le_range j hjc hcomm
  apply (isCentral_kernelι_iff (f ≫ q)).mpr
  intro T x hx T' b g
  have hg : g ∈ a.fixedSubgroup.carrier T' := hle T' (by rw [hperf]; exact Subgroup.mem_top g)
  have hbx : (b ≫ x) ≫ (f ≫ q).hom.hom = 1 := by
    rw [Category.assoc, hx, MonObj.comp_one]
  let h : T' ⟶ (kernel (f ≫ q)).X := (kernelPointsEquiv (f ≫ q) T').symm ⟨b ≫ x, hbx⟩
  have hh : h ≫ (kernelι (f ≫ q)).hom.hom = b ≫ x :=
    congrArg Subtype.val ((kernelPointsEquiv (f ≫ q) T').apply_symm_apply ⟨b ≫ x, hbx⟩)
  have e := hg T' (𝟙 T') h
  simp only [a] at e
  rw [Category.id_comp, AutomorphicAction.conjugation_act, hh] at e
  exact (mul_inv_eq_iff_eq_mul.mp e)

end IsCentralIsogeny

end Langlands.GroupScheme

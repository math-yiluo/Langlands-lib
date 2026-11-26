import Langlands.GroupScheme.Absolute.SolvableSemisimpleCentralizer.CommutatorKernel
import Langlands.GroupScheme.Absolute.SolvableSemisimpleCentralizer.DerivedStages
import Langlands.GroupScheme.KernelMonomorphism
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Lifting semisimple centralizers through normal unipotent quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme.SemisimpleCentralizer

variable {k : Type u} [Field k] {G Q N C C' : GroupScheme (Spec (CommRingCat.of k))}
  {s : rationalPoints G}

/-- On rational points, the represented centralizer expresses ordinary commutation. -/
theorem mem_pointCentralizer_rational (x : rationalPoints G) :
    x ∈ (G.pointCentralizer s).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ↔ Commute s x := by
  have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ := toUnit_unique _ _
  rw [G.mem_pointCentralizer, hu, Category.id_comp]
  exact eq_comm

/-- Any representative of the centralizer of a rational point of a separated group is closed. -/
theorem pointCentralizer_closed [IsSeparated G.X.hom] {c : C ⟶ G}
    (hc : (G.pointCentralizer s).IsRepresentedBy c) : IsClosedSubgroup c := by
  obtain ⟨B, b, hb, hbc⟩ := G.pointCentralizer_isClosedRepresentable s
  exact hc.isClosedSubgroup hb hbc

private theorem range_le_pointCentralizer_map {c : C ⟶ G}
    (hc : (G.pointCentralizer s).IsRepresentedBy c) (q : G ⟶ Q) :
    SubgroupFunctor.range (c ≫ q) ≤ Q.pointCentralizer (rationalPoints.map q s) := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have h : y ≫ c.hom.hom ∈ (G.pointCentralizer s).carrier T := hc.2 ▸ ⟨y, rfl⟩
  rw [G.mem_pointCentralizer] at h
  rw [Q.mem_pointCentralizer, rationalPoints.map_apply, Grp.comp_hom_hom,
    ← Category.assoc, ← Category.assoc (toUnit T), ← MonObj.mul_comp, ← MonObj.mul_comp, h]

section Lift

variable [IsAlgClosed k]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom] [IsCommMonObj N.X]
  (i : N ⟶ G) [Mono i.hom.hom] (hi : (SubgroupFunctor.range i).IsNormal)
  (q : G ⟶ Q) (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
  (hN : IsUnipotent N) (hs : SemisimplePoint.IsSemisimple s)

include i hi hk hN hs

/-- For a quotient by a normal commutative unipotent subgroup, every centralizing rational
point in the quotient lifts to a centralizing rational point of the source. -/
theorem exists_centralizing_lift (hq : Function.Surjective (rationalPoints.map q))
    (b : rationalPoints Q) (hb : Commute (rationalPoints.map q s) b) :
    ∃ z : rationalPoints G, Commute s z ∧ rationalPoints.map q z = b := by
  obtain ⟨g, hg⟩ := hq b
  have hγ : rationalPoints.map q ⁅s, g⁆ = 1 := by
    rw [map_commutatorElement, hg, commutatorElement_eq_one_iff_commute]
    exact hb
  have hmem : ⁅s, g⁆ ∈ (SubgroupFunctor.range i).carrier _ := by
    rw [← hk, mem_range_kernelι_iff]
    exact hγ
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hmem
  change rationalPoints.map i w = ⁅s, g⁆ at hw
  obtain ⟨y, v, hv, hyv⟩ := commutator_point_cover i hi s hN hs w
  let U := rationalPoints.map i y
  let V := rationalPoints.map i v
  have hcommV : Commute s V := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← commutator_point_map i hi s v, hv, map_one]
  have hcommUV : Commute V⁻¹ U := ((Commute.all v y).map (rationalPoints.map i)).inv_left
  have hw' := congrArg (rationalPoints.map i) hyv
  rw [map_mul, commutator_point_map i hi s y, hw] at hw'
  change ⁅s, U⁆ * V = ⁅s, g⁆ at hw'
  let z := U⁻¹ * g
  have he : s * V⁻¹ = z * s * z⁻¹ := by
    calc
      s * V⁻¹ = V⁻¹ * s := hcommV.inv_right.eq
      _ = U⁻¹ * V⁻¹ * U * s := by rw [mul_assoc U⁻¹ V⁻¹ U, hcommUV.eq, inv_mul_cancel_left]
      _ = U⁻¹ * (⁅s, U⁆ * V)⁻¹ * s * U := by rw [commutatorElement_def]; group
      _ = z * s * z⁻¹ := by rw [hw', commutatorElement_def]; dsimp [z]; group
  have hprod : SemisimplePoint.IsSemisimple (s * V⁻¹) := by
    rw [he]
    exact SemisimplePoint.conj hs z
  have hV : V⁻¹ = 1 := by
    simpa only [map_inv] using SemisimplePoint.eq_one_of_commute_of_mul i hN v⁻¹ hs
      (by simpa only [map_inv] using hcommV.inv_right) (by simpa only [map_inv] using hprod)
  have hz : Commute s z := by
    rw [hV, mul_one] at he
    change s * z = z * s
    calc
      s * z = (z * s * z⁻¹) * z := congrArg (· * z) he
      _ = z * s := inv_mul_cancel_right _ _
  have hU : rationalPoints.map q U = 1 :=
    (mem_range_kernelι_iff q U).mp (by rw [hk]; exact ⟨y, rfl⟩)
  exact ⟨z, hz, by simp only [z, map_mul, map_inv, hU, inv_one, one_mul, hg]⟩

/-- The homomorphism between represented point centralizers is surjective on rational points
and has connected full kernel. -/
theorem exists_centralizer_quotient [ConnectedSpace N.X.left]
    (hci : IsClosedSubgroup i) (hq : Function.Surjective (rationalPoints.map q))
    {c : C ⟶ G} (hc : (G.pointCentralizer s).IsRepresentedBy c) (hcc : IsClosedSubgroup c)
    {c' : C' ⟶ Q} (hc' : (Q.pointCentralizer (rationalPoints.map q s)).IsRepresentedBy c') :
    ∃ r : C ⟶ C', r ≫ c' = c ≫ q ∧ Function.Surjective (rationalPoints.map r) ∧
      ConnectedSpace (kernel r).X.left := by
  let r := hc'.factorHom (c ≫ q) (range_le_pointCentralizer_map hc q)
  have hr : r ≫ c' = c ≫ q := hc'.factorHom_comp _ _
  have : Mono c'.hom.hom := hc'.1
  refine ⟨r, hr, ?_, ?_⟩
  · intro a
    let b := rationalPoints.map c' a
    have hb : Commute (rationalPoints.map q s) b :=
      (mem_pointCentralizer_rational b).mp (hc'.2 ▸ ⟨a, rfl⟩)
    obtain ⟨g, hg, hgq⟩ := exists_centralizing_lift i hi q hk hN hs hq b hb
    have hcg : g ∈ (SubgroupFunctor.range c).carrier _ :=
      hc.2.symm ▸ (mem_pointCentralizer_rational g).mpr hg
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hcg
    change rationalPoints.map c z = g at hz
    refine ⟨z, (cancel_mono c'.hom.hom).mp ?_⟩
    change rationalPoints.map c' (rationalPoints.map r z) = b
    rw [← MonoidHom.comp_apply, ← pointMap_comp, hr, pointMap_comp, MonoidHom.comp_apply, hz, hgq]
  · have hiClosed : IsClosedSubgroup (subgroupIntersectionFst i c) :=
      isClosedSubgroup_subgroupIntersectionFst i hcc
    have : IsClosedImmersion (subgroupIntersectionFst i c).hom.hom.left := hiClosed
    let d := commutatorHom i hi s
    have hI : ((G.pointCentralizer s).comap i).IsRepresentedBy (subgroupIntersectionFst i c) :=
      ⟨Over.mono_of_mono_left _, by rw [range_subgroupIntersectionFst_eq_comap, hc.2]⟩
    let e₁ := KernelRepresentative.iso (c ≫ q) (kernelι r)
      (by rw [← hr, range_kernelι_comp_mono r c'])
    let e₂ := kernelCompositeIntersectionIso c i q hci hk
    let e₃ : subgroupIntersection c i ≅ subgroupIntersection i c := pullbackSymmetry c i
    let e₄ := hI.isoOfIsRepresentedBy
      (show ((G.pointCentralizer s).comap i).IsRepresentedBy (kernelι d) from
        ⟨inferInstance, range_kernel_commutatorHom i hi s⟩)
    exact connectedSpace_of_over_iso ((Grp.forget _).mapIso (e₁.symm ≪≫ e₂ ≪≫ e₃ ≪≫ e₄))
      (connectedSpace_kernel_commutatorHom i hi s hN hs)

end Lift

end Langlands.GroupScheme.SemisimpleCentralizer

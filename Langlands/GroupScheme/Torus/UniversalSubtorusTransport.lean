import Langlands.GroupScheme.Torus.UniversalSubtorus
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Transport of the universal largest subtorus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace IsUniversalSubtorus

variable {S : Scheme.{u}} {H T : GroupScheme S} {j : T ⟶ H}

/-- The universal property includes factorization over the original base. -/
theorem factor (hj : IsUniversalSubtorus j) {T' : GroupScheme S}
    (f : T' ⟶ H) (hT' : RelativeTorus.IsTorus T') :
    ∃ a : T' ⟶ T, a ≫ j = f := by
  obtain ⟨a, ha⟩ := hj.2.2 S (𝟙 S) T' (f ≫ (baseChangeIdIso H).inv) hT'
  have hn : (GroupScheme.baseChange (𝟙 S)).map j ≫ (baseChangeIdIso H).hom =
      (baseChangeIdIso T).hom ≫ j :=
    (((Functor.mapGrpNatIso Over.pullbackId) ≪≫ Functor.mapGrpIdIso).hom.naturality j)
  refine ⟨a ≫ (baseChangeIdIso T).hom, ?_⟩
  calc
    (a ≫ (baseChangeIdIso T).hom) ≫ j =
        (a ≫ (GroupScheme.baseChange (𝟙 S)).map j) ≫ (baseChangeIdIso H).hom := by
      simp only [Category.assoc, hn]
    _ = f := by rw [ha]; simp

/-- The stronger universal property survives any change of base. -/
theorem baseChange (hj : IsUniversalSubtorus j) {S' : Scheme.{u}} (b : S' ⟶ S) :
    IsUniversalSubtorus ((GroupScheme.baseChange b).map j) := by
  refine ⟨hj.1.baseChange b, hj.2.1.baseChange b, ?_⟩
  intro S'' c T' f hT'
  obtain ⟨a, ha⟩ := hj.2.2 S'' (c ≫ b) T'
    (f ≫ (baseChangeCompIso b c H).inv) hT'
  have hn : (GroupScheme.baseChange (c ≫ b)).map j ≫ (baseChangeCompIso b c H).hom =
      (baseChangeCompIso b c T).hom ≫
        (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map j) :=
    (((Functor.mapGrpNatIso (Over.pullbackComp c b)) ≪≫
      Functor.mapGrpCompIso).hom.naturality j)
  refine ⟨a ≫ (baseChangeCompIso b c T).hom, ?_⟩
  calc
    (a ≫ (baseChangeCompIso b c T).hom) ≫
        (GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map j) =
        (a ≫ (GroupScheme.baseChange (c ≫ b)).map j) ≫
          (baseChangeCompIso b c H).hom := by
      simp only [Category.assoc, hn]
    _ = f := by rw [ha]; simp

/-- Changing the representative of the source preserves universality. -/
theorem iso_comp (hj : IsUniversalSubtorus j) {T' : GroupScheme S} (e : T' ≅ T) :
    IsUniversalSubtorus (e.hom ≫ j) := by
  refine ⟨hj.1.iso_comp e, RelativeTorus.IsTorus.of_iso e hj.2.1, ?_⟩
  intro S' b T'' f hT''
  obtain ⟨a, ha⟩ := hj.2.2 S' b T'' f hT''
  refine ⟨a ≫ (GroupScheme.baseChange b).map e.inv, ?_⟩
  calc
    (a ≫ (GroupScheme.baseChange b).map e.inv) ≫
        (GroupScheme.baseChange b).map (e.hom ≫ j) =
        a ≫ (GroupScheme.baseChange b).map (e.inv ≫ e.hom) ≫
          (GroupScheme.baseChange b).map j := by
      simp only [Functor.map_comp, Category.assoc]
    _ = f := by simpa using ha

/-- Changing the ambient group by an isomorphism preserves universality. -/
theorem comp_iso (hj : IsUniversalSubtorus j) {H' : GroupScheme S} (e : H ≅ H') :
    IsUniversalSubtorus (j ≫ e.hom) := by
  refine ⟨hj.1.comp_iso e, hj.2.1, ?_⟩
  intro S' b T' f hT'
  obtain ⟨a, ha⟩ := hj.2.2 S' b T' (f ≫ (GroupScheme.baseChange b).map e.inv) hT'
  refine ⟨a, ?_⟩
  rw [Functor.map_comp, ← Category.assoc, ha]
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    (GroupScheme.baseChange b).map_id, Category.comp_id]

/-- A closed relative torus containing a universal subtorus is universal. -/
theorem of_factor (hj : IsUniversalSubtorus j) {T' : GroupScheme S} {k : T' ⟶ H}
    (hk : IsClosedSubgroup k) (hT' : RelativeTorus.IsTorus T')
    (a : T ⟶ T') (ha : a ≫ k = j) : IsUniversalSubtorus k := by
  refine ⟨hk, hT', ?_⟩
  intro S' b T'' f hT''
  obtain ⟨c, hc⟩ := hj.2.2 S' b T'' f hT''
  refine ⟨c ≫ (GroupScheme.baseChange b).map a, ?_⟩
  rw [Category.assoc, ← Functor.map_comp, ha, hc]

/-- A universal subtorus contains the range of every relative-torus homomorphism. -/
theorem range_le (hj : IsUniversalSubtorus j) {T' : GroupScheme S} (k : T' ⟶ H)
    (hT' : RelativeTorus.IsTorus T') :
    SubgroupFunctor.range k ≤ SubgroupFunctor.range j := by
  obtain ⟨a, ha⟩ := hj.factor k hT'
  intro U x hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨y ≫ a.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, ha, hy]

/-- Any two universal subtorus representatives have the same subgroup functor. -/
theorem range_eq (hj : IsUniversalSubtorus j) {T' : GroupScheme S} {k : T' ⟶ H}
    (hk : IsUniversalSubtorus k) : SubgroupFunctor.range j = SubgroupFunctor.range k :=
  le_antisymm (hk.range_le j hj.2.1) (hj.range_le k hk.2.1)

/-- Universality transfers to a closed relative torus with the same range. -/
theorem of_range_eq (hj : IsUniversalSubtorus j) {T' : GroupScheme S} {k : T' ⟶ H}
    (hk : IsClosedSubgroup k) (hT' : RelativeTorus.IsTorus T')
    (heq : SubgroupFunctor.range j = SubgroupFunctor.range k) : IsUniversalSubtorus k := by
  have hrep : (SubgroupFunctor.range k).IsRepresentedBy k := ⟨hk.mono_overHom, rfl⟩
  exact hj.of_factor hk hT' (hrep.factorHom j heq.le) (hrep.factorHom_comp j heq.le)

/-- The universal predicate implies the published largest-subtorus predicate. -/
theorem isLargest (hj : IsUniversalSubtorus j) :
    IsClosedSubgroup j ∧ RelativeTorus.IsTorus T ∧
      ∀ (T' : GroupScheme S) (k : T' ⟶ H),
        IsClosedSubgroup k → RelativeTorus.IsTorus T' → ∃ a : T' ⟶ T, a ≫ j = k :=
  ⟨hj.1, hj.2.1, fun _ k _ hk => hj.factor k hk⟩

end IsUniversalSubtorus

end Langlands.GroupScheme

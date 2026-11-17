import Langlands.GroupScheme.RelativeUnipotent.RootWeightQuotient
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Successive represented root-weight kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Langlands.GroupTheory

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))} {C : RootHeightChart U}
    (W : RootWeightData C)

/-- Inclusion of consecutive generated point subgroups. -/
def subgroupStep (d : ℕ) (T : Over (Spec (CommRingCat.of R))) :
    (W.subgroup (d + 1)).carrier T →* (W.subgroup d).carrier T :=
  Subgroup.inclusion (HeightFiltration.antitone_level
    (rootFactor C.roots ULift.up T) W.weight (Nat.le_succ (d + 1)))

/-- Inclusion of the represented point groups, using their subgroup equivalences. -/
def stepPoints (d : ℕ) (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (W.groupScheme (d + 1)).X) →* (T ⟶ (W.groupScheme d).X) :=
  ((W.isRepresentedBy_inclusion d).pointsEquiv T).symm.toMonoidHom.comp
    ((W.subgroupStep d T).comp
      ((W.isRepresentedBy_inclusion (d + 1)).pointsEquiv T).toMonoidHom)

theorem stepPoints_comp_inclusion (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (W.groupScheme (d + 1)).X) :
    W.stepPoints d T x ≫ (W.inclusion d).hom.hom =
      x ≫ (W.inclusion (d + 1)).hom.hom := by
  change ((W.isRepresentedBy_inclusion d).pointsEquiv T).symm _ ≫ _ = _
  rw [SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
  rfl

theorem stepPoints_natural (d : ℕ) {T T' : Over (Spec (CommRingCat.of R))}
    (f : T' ⟶ T) (x : T ⟶ (W.groupScheme (d + 1)).X) :
    W.stepPoints d T' (f ≫ x) = f ≫ W.stepPoints d T x := by
  let := (W.isRepresentedBy_inclusion d).1
  apply (cancel_mono (W.inclusion d).hom.hom).1
  calc
    _ = (f ≫ x) ≫ (W.inclusion (d + 1)).hom.hom :=
      W.stepPoints_comp_inclusion d T' (f ≫ x)
    _ = f ≫ (x ≫ (W.inclusion (d + 1)).hom.hom) := Category.assoc _ _ _
    _ = f ≫ (W.stepPoints d T x ≫ (W.inclusion d).hom.hom) :=
      congrArg (fun z => f ≫ z) (W.stepPoints_comp_inclusion d T x).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The inclusion of successive positive-weight terms, induced by their represented
all-test subgroup functors. -/
def step (d : ℕ) : W.groupScheme (d + 1) ⟶ W.groupScheme d :=
  homOfPoints (fun T => W.stepPoints d T) (W.stepPoints_natural d)

theorem comp_step_inclusion (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (W.groupScheme (d + 1)).X) :
    (x ≫ (W.step d).hom.hom) ≫ (W.inclusion d).hom.hom =
      x ≫ (W.inclusion (d + 1)).hom.hom := by
  rw [step, comp_homOfPoints, stepPoints_comp_inclusion]

/-- Successive inclusions agree with the original inclusions into the group. -/
theorem step_comp_inclusion (d : ℕ) :
    W.step d ≫ W.inclusion d = W.inclusion (d + 1) := by
  apply (Grp.forget (Over (Spec (CommRingCat.of R)))).map_injective
  change (W.step d).hom.hom ≫ (W.inclusion d).hom.hom =
    (W.inclusion (d + 1)).hom.hom
  simpa only [Category.id_comp] using
    W.comp_step_inclusion d (W.groupScheme (d + 1)).X (𝟙 _)

/-- Factoring through the next represented term is precisely membership of
the ambient point in the next positive-weight subgroup. -/
theorem mem_range_step_iff (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (W.groupScheme d).X) :
    x ∈ (SubgroupFunctor.range (W.step d)).carrier T ↔
      x ≫ (W.inclusion d).hom.hom ∈ (W.subgroup (d + 1)).carrier T := by
  rw [← (W.isRepresentedBy_inclusion (d + 1)).2]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (W.comp_step_inclusion d T y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    let := (W.isRepresentedBy_inclusion d).1
    apply (cancel_mono (W.inclusion d).hom.hom).1
    change (y ≫ (W.step d).hom.hom) ≫ (W.inclusion d).hom.hom =
      x ≫ (W.inclusion d).hom.hom
    change y ≫ (W.inclusion (d + 1)).hom.hom =
      x ≫ (W.inclusion d).hom.hom at hy
    rw [comp_step_inclusion, hy]

/-- The next positive-weight term is a closed subgroup of the current one. -/
theorem isClosedSubgroup_step (d : ℕ) : IsClosedSubgroup (W.step d) := by
  have : IsClosedImmersion (W.inclusion d).hom.hom.left :=
    W.isClosedSubgroup_inclusion d
  have : IsClosedImmersion
      ((W.step d).hom.hom.left ≫ (W.inclusion d).hom.hom.left) := by
    change IsClosedImmersion ((W.step d ≫ W.inclusion d).hom.hom.left)
    rw [step_comp_inclusion]
    exact W.isClosedSubgroup_inclusion (d + 1)
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (W.inclusion d).hom.hom.left

/-- Normality of the next term inside the current represented term. -/
theorem isNormal_range_step (d : ℕ) :
    (SubgroupFunctor.range (W.step d)).IsNormal := by
  intro T g x _ hx
  rw [mem_range_step_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  exact W.isNormal_subgroup (d + 1) T _ _ (Subgroup.mem_top _) hx

/-- A point of a positive-weight term is killed by its exact-weight quotient if and
only if its ambient point lies in the next positive-weight subgroup. -/
theorem quotientMap_eq_one_iff (d : ℕ)
    (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (W.groupScheme d).X) :
    x ≫ (W.quotientMap d).hom.hom = 1 ↔
      x ≫ (W.inclusion d).hom.hom ∈ (W.subgroup (d + 1)).carrier T := by
  rw [comp_quotientMap, mem_subgroup_iff]
  constructor
  · intro h k hk
    by_cases hkd : W.weight k < d + 1
    · exact (W.mem_subgroup_iff T d _).1 (W.pointInLevel T d x).property k hkd
    · have heq : W.weight k = d + 1 := by omega
      let a : W.exactSupport d := ⟨k, heq⟩
      let j := (W.exactEnumeration d).symm a
      have hj : (W.exactEnumeration d j).val = k := by
        simp only [j, Equiv.apply_symm_apply, a]
      rw [← hj, ← quotientPoints_coord W T d x j, h, map_one]
      rfl
  · intro h
    apply VectorGroup.points_ext
    intro j
    rw [quotientPoints_coord, h _ (by
      rw [(W.exactEnumeration d j).property]
      omega), map_one]
    rfl

/-- The scheme-theoretic quotient kernel is exactly the next represented
positive-weight term on every scheme test. -/
theorem range_kernelι_quotientMap (d : ℕ) :
    SubgroupFunctor.range (kernelι (W.quotientMap d)) =
      SubgroupFunctor.range (W.step d) := by
  ext T x
  rw [mem_range_kernelι_iff, quotientMap_eq_one_iff, mem_range_step_iff]

/-- Each positive-weight quotient is a represented fppf quotient with the
actual next term as its full kernel. -/
theorem isFppfQuotient_quotientMap (d : ℕ) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (W.step d))
      (W.quotientMap d) :=
  ⟨W.flat_quotientMap d, W.surjective_quotientMap d,
    W.locallyOfFinitePresentation_quotientMap d, W.range_kernelι_quotientMap d⟩

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData

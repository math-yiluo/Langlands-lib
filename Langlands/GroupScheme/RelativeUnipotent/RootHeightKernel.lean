import Langlands.GroupScheme.RelativeUnipotent.RootHeightQuotient
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Successive represented root-height kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootHeightChart

open LocalSplitCell Langlands.GroupTheory

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))} (C : RootHeightChart U)

/-- Inclusion of consecutive generated point subgroups. -/
def subgroupStep (d : ℕ) (T : Over (Spec (CommRingCat.of R))) :
    (C.subgroup (d + 1)).carrier T →* (C.subgroup d).carrier T :=
  Subgroup.inclusion (HeightFiltration.antitone_level
    (rootFactor C.roots ULift.up T) C.height (Nat.le_succ d))

/-- Inclusion of the represented point groups, using their subgroup equivalences. -/
def stepPoints (d : ℕ) (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (C.groupScheme (d + 1)).X) →* (T ⟶ (C.groupScheme d).X) :=
  ((C.isRepresentedBy_inclusion d).pointsEquiv T).symm.toMonoidHom.comp
    ((C.subgroupStep d T).comp
      ((C.isRepresentedBy_inclusion (d + 1)).pointsEquiv T).toMonoidHom)

theorem stepPoints_comp_inclusion (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (C.groupScheme (d + 1)).X) :
    C.stepPoints d T x ≫ (C.inclusion d).hom.hom =
      x ≫ (C.inclusion (d + 1)).hom.hom := by
  change ((C.isRepresentedBy_inclusion d).pointsEquiv T).symm _ ≫ _ = _
  rw [SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
  rfl

theorem stepPoints_natural (d : ℕ) {T W : Over (Spec (CommRingCat.of R))}
    (f : W ⟶ T) (x : T ⟶ (C.groupScheme (d + 1)).X) :
    C.stepPoints d W (f ≫ x) = f ≫ C.stepPoints d T x := by
  let := (C.isRepresentedBy_inclusion d).1
  apply (cancel_mono (C.inclusion d).hom.hom).1
  calc
    _ = (f ≫ x) ≫ (C.inclusion (d + 1)).hom.hom :=
      C.stepPoints_comp_inclusion d W (f ≫ x)
    _ = f ≫ (x ≫ (C.inclusion (d + 1)).hom.hom) := Category.assoc _ _ _
    _ = f ≫ (C.stepPoints d T x ≫ (C.inclusion d).hom.hom) :=
      congrArg (fun z => f ≫ z) (C.stepPoints_comp_inclusion d T x).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The inclusion of successive height terms, induced by their represented
all-test subgroup functors. -/
def step (d : ℕ) : C.groupScheme (d + 1) ⟶ C.groupScheme d :=
  homOfPoints (fun T => C.stepPoints d T) (C.stepPoints_natural d)

theorem comp_step_inclusion (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (C.groupScheme (d + 1)).X) :
    (x ≫ (C.step d).hom.hom) ≫ (C.inclusion d).hom.hom =
      x ≫ (C.inclusion (d + 1)).hom.hom := by
  rw [step, comp_homOfPoints, stepPoints_comp_inclusion]

/-- Successive inclusions agree with the original inclusions into the group. -/
theorem step_comp_inclusion (d : ℕ) :
    C.step d ≫ C.inclusion d = C.inclusion (d + 1) := by
  apply (Grp.forget (Over (Spec (CommRingCat.of R)))).map_injective
  change (C.step d).hom.hom ≫ (C.inclusion d).hom.hom =
    (C.inclusion (d + 1)).hom.hom
  simpa only [Category.id_comp] using
    C.comp_step_inclusion d (C.groupScheme (d + 1)).X (𝟙 _)

/-- Factoring through the next represented term is precisely membership of
the ambient point in the next height subgroup. -/
theorem mem_range_step_iff (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (C.groupScheme d).X) :
    x ∈ (SubgroupFunctor.range (C.step d)).carrier T ↔
      x ≫ (C.inclusion d).hom.hom ∈ (C.subgroup (d + 1)).carrier T := by
  rw [← (C.isRepresentedBy_inclusion (d + 1)).2]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (C.comp_step_inclusion d T y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    let := (C.isRepresentedBy_inclusion d).1
    apply (cancel_mono (C.inclusion d).hom.hom).1
    change (y ≫ (C.step d).hom.hom) ≫ (C.inclusion d).hom.hom =
      x ≫ (C.inclusion d).hom.hom
    change y ≫ (C.inclusion (d + 1)).hom.hom =
      x ≫ (C.inclusion d).hom.hom at hy
    rw [comp_step_inclusion, hy]

/-- The next height term is a closed subgroup of the current one. -/
theorem isClosedSubgroup_step (d : ℕ) : IsClosedSubgroup (C.step d) := by
  have : IsClosedImmersion (C.inclusion d).hom.hom.left :=
    C.isClosedSubgroup_inclusion d
  have : IsClosedImmersion
      ((C.step d).hom.hom.left ≫ (C.inclusion d).hom.hom.left) := by
    change IsClosedImmersion ((C.step d ≫ C.inclusion d).hom.hom.left)
    rw [step_comp_inclusion]
    exact C.isClosedSubgroup_inclusion (d + 1)
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (C.inclusion d).hom.hom.left

/-- Normality of the next term inside the current represented term. -/
theorem isNormal_range_step (d : ℕ) :
    (SubgroupFunctor.range (C.step d)).IsNormal := by
  intro T g x _ hx
  rw [mem_range_step_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  exact C.isNormal_subgroup (d + 1) T _ _ (Subgroup.mem_top _) hx

/-- A point of a height term is killed by its exact-height quotient if and
only if its ambient point lies in the next height subgroup. -/
theorem quotientMap_eq_one_iff (d : ℕ) (hd : 0 < d)
    (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (C.groupScheme d).X) :
    x ≫ (C.quotientMap d hd).hom.hom = 1 ↔
      x ≫ (C.inclusion d).hom.hom ∈ (C.subgroup (d + 1)).carrier T := by
  rw [comp_quotientMap, mem_subgroup_iff]
  constructor
  · intro h k hk
    by_cases hkd : C.height k < d
    · exact (C.mem_subgroup_iff T d _).1 (C.pointInLevel T d x).property k hkd
    · have heq : C.height k = d := by omega
      let a : C.exactSupport d := ⟨k, heq⟩
      let j := (C.exactEnumeration d).symm a
      have hj : (C.exactEnumeration d j).val = k := by
        simp only [j, Equiv.apply_symm_apply, a]
      rw [← hj, ← quotientPoints_coord C T d hd x j, h, map_one]
      rfl
  · intro h
    apply VectorGroup.points_ext
    intro j
    rw [quotientPoints_coord, h _ (by
      rw [(C.exactEnumeration d j).property]
      omega), map_one]
    rfl

/-- The scheme-theoretic quotient kernel is exactly the next represented
height term on every scheme test. -/
theorem range_kernelι_quotientMap (d : ℕ) (hd : 0 < d) :
    SubgroupFunctor.range (kernelι (C.quotientMap d hd)) =
      SubgroupFunctor.range (C.step d) := by
  ext T x
  rw [mem_range_kernelι_iff, quotientMap_eq_one_iff, mem_range_step_iff]

/-- Each positive-height quotient is a represented fppf quotient with the
actual next term as its full kernel. -/
theorem isFppfQuotient_quotientMap (d : ℕ) (hd : 0 < d) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (C.step d))
      (C.quotientMap d hd) :=
  ⟨C.flat_quotientMap d hd, C.surjective_quotientMap d hd,
    C.locallyOfFinitePresentation_quotientMap d hd, C.range_kernelι_quotientMap d hd⟩

end Langlands.GroupScheme.RelativeUnipotent.RootHeightChart

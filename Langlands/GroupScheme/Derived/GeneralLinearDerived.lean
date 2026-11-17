import Langlands.GroupScheme.Derived.GeneralLinearCenterDerivedStatement
import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.SpecialLinearSimplyConnected
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # The special-linear inclusion exhibits the derived group of GL -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})

/-- The full range of the special-linear inclusion consists of determinant-one points. -/
theorem mem_range_inclusion_iff (T : Over (Spec R))
    (g : T ⟶ (GeneralLinear.groupScheme n R).X) :
    g ∈ (SubgroupFunctor.range (inclusion n R)).carrier T ↔
      Matrix.GeneralLinearGroup.det (GeneralLinear.pointsEquiv n R T g) = 1 := by
  constructor
  · intro hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    rw [pointsEquiv_inclusion]
    apply Units.ext
    exact (pointsEquiv n R T x).property
  · intro hg
    let x : Matrix.SpecialLinearGroup n Γ(T.left, ⊤) :=
      ⟨(GeneralLinear.pointsEquiv n R T g).val, congrArg Units.val hg⟩
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨(pointsEquiv n R T).symm x, ?_⟩
    apply (GeneralLinear.pointsEquiv n R T).injective
    rw [pointsEquiv_inclusion, MulEquiv.apply_symm_apply]
    exact Units.ext rfl

/-- The special-linear inclusion is monomorphic on schemes over the base. -/
instance inclusion_mono : Mono (inclusion n R).hom.hom where
  right_cancellation f g h := by
    apply (pointsEquiv n R _).injective
    apply Matrix.SpecialLinearGroup.toGL_injective
    simpa only [← pointsEquiv_inclusion] using congrArg (GeneralLinear.pointsEquiv n R _) h

/-- The full range of SL is the full scheme-theoretic determinant kernel. -/
theorem range_inclusion_eq_range_kernelι :
    SubgroupFunctor.range (inclusion n R) =
      SubgroupFunctor.range (kernelι (GeneralLinear.determinantCharacter n R).toMul) := by
  ext T g
  rw [mem_range_inclusion_iff, mem_range_kernelι_iff,
    GeneralLinear.comp_determinantCharacter]
  constructor
  · intro hg
    apply (Gm.pointsEquiv (Spec R) T).injective
    simpa only [GeneralLinear.determinantPoints, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_one] using hg
  · intro hg
    have h := congrArg (Gm.pointsEquiv (Spec R) T) hg
    simpa only [GeneralLinear.determinantPoints, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_one] using h

/-- SL is a closed subgroup of GL, in all ranks and over every commutative ring. -/
theorem isClosedSubgroup_inclusion : IsClosedSubgroup (inclusion n R) := by
  have : IsAffineHom (Gm (Spec R)).X.hom := isSplitTorus_gm.isAffineHom
  let j := kernelι (GeneralLinear.determinantCharacter n R).toMul
  have hi : (SubgroupFunctor.range (inclusion n R)).IsRepresentedBy (inclusion n R) :=
    ⟨inferInstance, rfl⟩
  have hj : (SubgroupFunctor.range (inclusion n R)).IsRepresentedBy j :=
    ⟨inferInstance, (range_inclusion_eq_range_kernelι n R).symm⟩
  rw [← hi.isoOfIsRepresentedBy_hom_comp hj]
  exact IsClosedSubgroup.iso_comp _ (inferInstance : IsClosedImmersion j.hom.hom.left)

/-- All commutators of GL points have determinant one. -/
theorem range_inclusion_containsCommutators :
    (SubgroupFunctor.range (inclusion n R)).ContainsCommutators := by
  intro T x y
  rw [mem_range_inclusion_iff]
  simp only [map_mul, map_inv]
  generalize Matrix.GeneralLinearGroup.det (GeneralLinear.pointsEquiv n R T x) = a
  generalize Matrix.GeneralLinearGroup.det (GeneralLinear.pointsEquiv n R T y) = b
  rw [mul_assoc, mul_mul_mul_comm, mul_inv_cancel, mul_inv_cancel, one_mul]

variable (k : Type u) [Field k]

/-- The special-linear group scheme is perfect, including the empty index type. -/
theorem derivedSubgroup_eq_top :
    derivedSubgroup (groupScheme n (CommRingCat.of k)) = ⊤ := by
  classical
  by_cases hn : Nonempty n
  · let := hn
    exact semisimplePerfect k _ (isSimplyConnected n k).isSemisimple
  · have : IsEmpty n := not_nonempty_iff.mp hn
    apply SubgroupFunctor.ext
    intro T
    apply (Subgroup.eq_top_iff' _).mpr
    intro x
    have hx : x = 1 := by
      apply (pointsEquiv n (CommRingCat.of k) T).injective
      ext i j
      exact isEmptyElim i
    rw [hx]
    exact (derivedSubgroup _).carrier T |>.one_mem

/-- The actual special-linear inclusion exhibits the full derived group of GL. -/
theorem isDerivedSubgroup_inclusion :
    IsDerivedSubgroup (inclusion n (CommRingCat.of k)) := by
  refine ⟨isClosedSubgroup_inclusion n _, le_antisymm ?_ ?_⟩
  · intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply mem_derivedSubgroup_comp
    rw [derivedSubgroup_eq_top]
    exact Subgroup.mem_top _
  · exact derivedSubgroup_le_range _ (isClosedSubgroup_inclusion n _)
      (range_inclusion_containsCommutators n _)

end Langlands.GroupScheme.SpecialLinear

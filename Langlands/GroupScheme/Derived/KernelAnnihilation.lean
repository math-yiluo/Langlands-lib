import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Kernels and annihilation of an actual derived subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H D : GroupScheme S}

namespace SubgroupFunctor

/-- The pointwise kernel of a group-scheme homomorphism on all test schemes. -/
def kernel (f : G ⟶ H) : SubgroupFunctor G where
  carrier T := ((yonedaGrp.map f).app (.op T)).hom.ker
  comp_mem a x hx := by
    change (a ≫ x) ≫ f.hom.hom = 1
    change x ≫ f.hom.hom = 1 at hx
    rw [Category.assoc, hx, MonObj.comp_one]

theorem mem_kernel (f : G ⟶ H) {T : Over S} {x : T ⟶ G.X} :
    x ∈ (kernel f).carrier T ↔ x ≫ f.hom.hom = 1 :=
  Iff.rfl

/-- The actual kernel represents the pointwise kernel on every test scheme. -/
theorem range_kernelι (f : G ⟶ H) : range (kernelι f) = kernel f := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  exact mem_range_kernelι_iff f x

/-- The kernel of a homomorphism to a commutative group contains every commutator. -/
theorem containsCommutators_range_kernelι (f : G ⟶ H) [IsCommMonObj H.X] :
    (range (kernelι f)).ContainsCommutators := by
  intro T x y
  apply (mem_range_kernelι_iff f _).mpr
  simp [MonObj.mul_comp, GrpObj.inv_comp, mul_assoc, mul_comm, mul_left_comm]

end SubgroupFunctor

/-- A separated commutative target annihilates the scheme-theoretic derived subgroup functor. -/
theorem derivedSubgroup_le_range_kernelι (f : G ⟶ H)
    [IsCommMonObj H.X] [IsSeparated H.X.hom] :
    derivedSubgroup G ≤ SubgroupFunctor.range (kernelι f) :=
  derivedSubgroup_le_range (kernelι f) (by
    change IsClosedImmersion (kernelι f).hom.hom.left
    infer_instance) (SubgroupFunctor.containsCommutators_range_kernelι f)

/-- Every morphism to a separated commutative group is trivial on an actual derived subgroup. -/
theorem IsDerivedSubgroup.comp_eq_one {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    (f : G ⟶ H) [IsCommMonObj H.X] [IsSeparated H.X.hom] :
    d ≫ f = 1 := by
  apply hom_ext_points
  intro T x
  have hx : x ≫ d.hom.hom ∈ (SubgroupFunctor.range d).carrier T := ⟨x, rfl⟩
  rw [hd.2] at hx
  have h := (mem_range_kernelι_iff f _).mp
    (derivedSubgroup_le_range_kernelι f T hx)
  simpa only [Grp.comp_hom_hom, ← Category.assoc, Grp.Hom.hom_one, Mon.Hom.hom_one,
    MonObj.comp_one] using h

/-- Every rational character is zero on an actual derived subgroup over the same base. -/
theorem IsDerivedSubgroup.characterRestrict_eq_zero {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) (χ : rationalCharacters G) :
    characterRestrict d χ = 0 := by
  have : IsSeparated (Gm S).X.hom := by
    have : IsSeparated Gm.overSpecZ.{u}.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ S))
    infer_instance
  exact congrArg Additive.ofMul (hd.comp_eq_one χ.toMul)

end Langlands.GroupScheme

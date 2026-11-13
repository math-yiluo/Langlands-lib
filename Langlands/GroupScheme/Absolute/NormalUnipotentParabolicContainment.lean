import Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentProof
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Reductive.ParabolicUnipotentKernel

/-! # Normal unipotent subgroups lie in every geometric parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G U P : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A smooth connected normal unipotent closed subgroup lies in every
geometric parabolic, on all relative scheme tests over the original field. -/
theorem IsParabolicSubgroup.normalUnipotent_le
    {p : P ⟶ G} (hp : IsParabolicSubgroup p)
    (i : U ⟶ G) (hi : IsClosedSubgroup i)
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (hU : IsUnipotent U) (hn : (SubgroupFunctor.range i).IsNormal) :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range p := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : IsAffineHom U.X.hom := hi.isAffineHom
  have : Smooth (F.obj G).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace (F.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have hUs : Smooth (F.obj U).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd U.X.hom b)
    infer_instance
  have hUc : ConnectedSpace (F.obj U).X.left :=
    U.connectedSpace_baseChange_of_smooth_affine b
  have hUn : (SubgroupFunctor.range (F.map i)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  obtain ⟨B, j, f, hj, hf⟩ := hp.exists_isBorelSubgroup
  have hUB : SubgroupFunctor.range (F.map i) ≤ SubgroupFunctor.range j :=
    normalUnipotentBorelContainment (AlgebraicClosure k) (F.obj G) (F.obj U)
      (F.map i) (hi.baseChange b) hUs hUc hU.baseChange hUn B j hj
  have hUP : SubgroupFunctor.range (F.map i) ≤ SubgroupFunctor.range (F.map p) := by
    intro T x hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hUB T hx)
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ f.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
    exact hy
  have : Surjective b := (fieldExtension_fpqc k (AlgebraicClosure k)).1
  have : Flat b := (fieldExtension_fpqc k (AlgebraicClosure k)).2.1
  have : QuasiCompact b := (fieldExtension_fpqc k (AlgebraicClosure k)).2.2
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.le_range_of_baseChange_le b p
  change SubgroupFunctor.range ((GroupScheme.baseChange b).map i) ≤
    SubgroupFunctor.range ((GroupScheme.baseChange b).map p) at hUP
  rw [SubgroupFunctor.range_baseChangeHom,
    SubgroupFunctor.range_baseChangeHom] at hUP
  exact hUP

/-- Arbitrary-field normal-unipotent containment in geometric parabolics. -/
def NormalUnipotentParabolicContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (U P : GroupScheme (Spec (CommRingCat.of k)))
    (i : U ⟶ G) (p : P ⟶ G),
    IsClosedSubgroup i → Smooth U.X.hom → ConnectedSpace U.X.left →
    IsUnipotent U → (SubgroupFunctor.range i).IsNormal → IsParabolicSubgroup p →
      SubgroupFunctor.range i ≤ SubgroupFunctor.range p

/-- The full statement follows from geometric containment and fpqc reflection. -/
theorem normalUnipotentParabolicContainment :
    NormalUnipotentParabolicContainmentStatement.{u} := by
  intro k _ G _ _ _ U P i p hi hUs hUc hU hn hp
  exact hp.normalUnipotent_le i hi hU hn

end Langlands.GroupScheme

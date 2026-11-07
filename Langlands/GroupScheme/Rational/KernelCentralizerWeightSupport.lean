import Langlands.GroupScheme.Rational.KernelCentralizerStructureProof
import Langlands.GroupScheme.Rational.GenericLieWeights
import Langlands.GroupScheme.Rational.StandardLeviLieWeights
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Integral character support and full character-kernel centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A nonzero vector of one character weight in the integral weight span
forces that character itself to be an integral multiple. -/
theorem mem_zmultiples_of_weightSpace_integralWeightSpan
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a b : characterLattice S) {X : Additive (lieKernel G k)}
    (hX : X ∈ weightSpace i b) (hX0 : X ≠ 0)
    (hspan : X ∈ integralWeightSpan i a) :
    b ∈ AddSubgroup.zmultiples a := by
  classical
  by_contra hb
  let p := weightSpaceProjection hS i b
  have hkill : integralWeightSpan i a ≤ LinearMap.ker p := by
    apply iSup_le
    intro n Y hY
    change p Y = 0
    exact weightSpaceProjection_of_mem_ne hS i b hY
      (fun h => hb (AddSubgroup.mem_zmultiples_iff.mpr ⟨n, h⟩))
  have hzero : p X = 0 := hkill hspan
  rw [weightSpaceProjection_of_mem hS i b hX] at hzero
  exact hX0 hzero

/-- Every root of a monic subgroup contained in the full kernel centralizer
restricts to an integral multiple of the original character. -/
theorem root_restrict_mem_zmultiples_of_range_le_kernelCentralizer
    [IsAffineHom M.X.hom]
    (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)
    (t : T.toGrp ⟶ M) (q : M ⟶ G) [Mono q.hom.hom]
    (a : characterLattice S)
    (hq : SubgroupFunctor.range q ≤
      kernelCentralizer (CommGroupScheme.groupHom f ≫ (t ≫ q)) a)
    {α : characterLattice T} (hα : α ∈ roots t) :
    f ≫ α ∈ AddSubgroup.zmultiples a := by
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  let Y := Lie.targetMapLinear q k X
  have hY : Y ∈ weightSpace (CommGroupScheme.groupHom f ≫ (t ≫ q)) (f ≫ α) :=
    weightSpace_le_comp f (t ≫ q) α (lieKernelHomLinear_mem_weightSpace q t α hX)
  have hY0 : Y ≠ 0 := by
    intro h
    apply hX0
    apply Lie.targetMapLinear_injective q k
    simpa only [map_zero] using h
  have hfixed : Y.toMul.val ∈
      (kernelCentralizer (CommGroupScheme.groupHom f ≫ (t ≫ q)) a).carrier _ := by
    apply hq
    exact SubgroupFunctor.mem_range.mpr ⟨X.toMul.val, rfl⟩
  have hinv := (kernelCentralizer_hasLieImage
    (CommGroupScheme.groupHom f ≫ (t ≫ q)) a Y).mp hfixed
  exact mem_zmultiples_of_weightSpace_integralWeightSpan hS _ a _ hY hY0
    (kernelLieInvariants_le_integralWeightSpan G S hS _ a hinv)

/-- If every nonzero torus weight restricts to an integral multiple, the
restricted integral weight span is the whole actual Lie algebra. -/
theorem integralWeightSpan_eq_top_of_root_restrictions
    (hT : IsSplitTorus T.toGrp) (f : S ⟶ T) (t : T.toGrp ⟶ G)
    (a : characterLattice S)
    (hroot : ∀ α ∈ roots t, f ≫ α ∈ AddSubgroup.zmultiples a) :
    integralWeightSpan (CommGroupScheme.groupHom f ≫ t) a = ⊤ := by
  classical
  apply top_unique
  rw [← (isInternal_weightSpace_of_isSplitTorus k G T hT t).submodule_iSup_eq_top]
  apply iSup_le
  intro α
  by_cases hbot : weightSpace t α = ⊥
  · rw [hbot]
    exact bot_le
  have hm : f ≫ α ∈ AddSubgroup.zmultiples a := by
    by_cases hα : α = 0
    · simp [hα]
    · exact hroot α ⟨hα, hbot⟩
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  have hw := weightSpace_le_comp f t α
  rw [← hn] at hw
  exact hw.trans (le_iSup (fun n : ℤ => weightSpace
    (CommGroupScheme.groupHom f ≫ t) (n • a)) n)

omit [LocallyOfFiniteType G.X.hom] in
/-- A full integral tangent span forces the actual character-kernel centralizer
to be the whole smooth connected affine group, on all scheme tests. -/
theorem kernelCentralizer_eq_top_of_integralWeightSpan_eq_top
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0)
    (hspan : integralWeightSpan i a = ⊤) : kernelCentralizer i a = ⊤ := by
  obtain ⟨C, j, hj, hclosed, hsmooth, hlie⟩ :=
    kernelCentralizerStructure k G inferInstance inferInstance S hS i a ha
  let : Smooth C.X.hom := hsmooth
  let : IsClosedImmersion j.hom.hom.left := hclosed
  let : IsAffineHom C.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have hsurj : Function.Surjective (Lie.targetMapLinear j k) := by
    intro X
    apply (hj.mem_range_lieKernelHomLinear X).mpr
    apply (hlie X).mpr
    rw [hspan]
    trivial
  have : IsIso j := Lie.isIso_of_surjective_targetMapLinear j hclosed hsurj
  rw [← hj.2]
  apply SubgroupFunctor.ext
  intro V
  apply Subgroup.ext
  intro x
  constructor
  · intro _
    trivial
  intro _
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨x ≫ (inv j).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

/-- A representative of a full-span character-kernel centralizer is canonically
isomorphic to the ambient smooth connected affine group. -/
def kernelCentralizerIsoOfIntegralWeightSpanEqTop
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0)
    (hspan : integralWeightSpan i a = ⊤)
    {C : GroupScheme (Spec (CommRingCat.of k))} {j : C ⟶ G}
    (hj : (kernelCentralizer i a).IsRepresentedBy j) : C ≅ G :=
  (show (⊤ : SubgroupFunctor G).IsRepresentedBy j from
    (kernelCentralizer_eq_top_of_integralWeightSpan_eq_top hS i a ha hspan) ▸ hj).topIso

omit [LocallyOfFiniteType G.X.hom] in
/-- The canonical full-span isomorphism has the original representing inclusion
as its forward map. -/
theorem kernelCentralizerIsoOfIntegralWeightSpanEqTop_hom
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0)
    (hspan : integralWeightSpan i a = ⊤)
    {C : GroupScheme (Spec (CommRingCat.of k))} {j : C ⟶ G}
    (hj : (kernelCentralizer i a).IsRepresentedBy j) :
    (kernelCentralizerIsoOfIntegralWeightSpanEqTop hS i a ha hspan hj).hom = j :=
  SubgroupFunctor.IsRepresentedBy.topIso_hom _

end Langlands.GroupScheme.RelativeRoot

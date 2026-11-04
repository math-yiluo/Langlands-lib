import Langlands.GroupScheme.Rational.SemigroupIntersectionGeometry
import Langlands.GroupScheme.Rational.SemigroupFunctorialityProof
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # Semigroup transport under fppf homomorphisms with contained kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp Q)
    (q : G ⟶ Q)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ G.X),
      b.act s x ≫ q.hom.hom = c.act s (x ≫ q.hom.hom))

include heq

/-- Full kernel containment controls the weights in the inverse image of the
semigroup subgroup, even when the differential of the homomorphism is singular. -/
theorem actionWeightSupport_comap_semigroup_subset_of_kernel_le
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType Q.X.hom]
    (hS : IsSplitTorus S.toGrp) (A : AddSubsemigroup (characterLattice S))
    (hLieG : HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A))
    (hLieQ : HasLieImage (semigroupSubgroup c A) (semigroupWeightSpan c A))
    (hker : SubgroupFunctor.range (kernelι q) ≤ semigroupSubgroup b A) :
    actionWeightSupport b ((semigroupSubgroup c A).comap q) ⊆ A := by
  rintro χ ⟨X, hX0, hXχ, hXP⟩
  by_contra hχ
  let Y := Lie.targetMapLinear q k X
  have hYχ : Y ∈ actionWeightSpace c χ :=
    lieKernelTargetLinear_mem_actionWeightSpace c b q heq χ hXχ
  have hYA : Y ∈ semigroupWeightSpan c A := (hLieQ Y).mp hXP
  have hY0 : Y = 0 := (Submodule.disjoint_def.mp
    (disjoint_actionWeightSpace_semigroupWeightSpan c hS A χ hχ)) Y hYχ hYA
  have hXker : X.toMul.val ∈ (SubgroupFunctor.range (kernelι q)).carrier _ := by
    apply (mem_range_kernelι_iff q _).mpr
    exact congrArg (fun Z : Additive (lieKernel Q k) => Z.toMul.val) hY0
  have hXA : X ∈ semigroupWeightSpan b A := (hLieG X).mp (hker _ hXker)
  exact hX0 ((Submodule.disjoint_def.mp
    (disjoint_actionWeightSpace_semigroupWeightSpan b hS A χ hχ)) X hXχ hXA)

/-- A represented stable inverse image has the same exact Lie image as the
source semigroup subgroup, provided it contains the entire actual kernel. -/
theorem hasLieImage_comap_semigroup_of_kernel_le
    [Smooth G.X.hom] [Smooth Q.X.hom]
    (hS : IsSplitTorus S.toGrp) (A : AddSubsemigroup (characterLattice S))
    (hker : SubgroupFunctor.range (kernelι q) ≤ semigroupSubgroup b A)
    {P : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom P.X.hom] [LocallyOfFiniteType P.X.hom]
    (p : P ⟶ G) (hp : ((semigroupSubgroup c A).comap q).IsRepresentedBy p) :
    HasLieImage ((semigroupSubgroup c A).comap q) (semigroupWeightSpan b A) := by
  have hRG := semigroupRealization k G inferInstance inferInstance S hS b A
  have hRQ := semigroupRealization k Q inferInstance inferInstance S hS c A
  apply (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
  apply le_antisymm
  · exact (actionWeightSupport_subset_iff_tangentSubmodule_le b hS p hp
      (isStable_comap_of_equivariant c b q heq hRQ.2.1) A).mp
      (actionWeightSupport_comap_semigroup_subset_of_kernel_le b c q heq hS A
        hRG.2.2.1 hRQ.2.2.1 hker)
  · rw [← (hasLieImage_iff_tangentSubmodule_eq _ _).mp hRG.2.2.1]
    exact tangentSubmodule_mono (SubgroupFunctor.map_le_iff_le_comap.mp
      (semigroupFunctoriality k G Q inferInstance inferInstance inferInstance
        inferInstance S hS b c q heq A))

/-- An equivariant fppf homomorphism induces an actual fppf semigroup image
when its full scheme-theoretic kernel lies in the source semigroup subgroup.
Neither the homomorphism nor its kernel is required to be smooth. -/
theorem isFppfImage_semigroup_of_kernel_le
    [Smooth G.X.hom] [Smooth Q.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (A : AddSubsemigroup (characterLattice S))
    (hker : SubgroupFunctor.range (kernelι q) ≤ semigroupSubgroup b A) :
    SubgroupFunctor.IsFppfImage (semigroupSubgroup b A) (semigroupSubgroup c A) q := by
  have hRG := semigroupRealization k G inferInstance inferInstance S hS b A
  have hRQ := semigroupRealization k Q inferInstance inferInstance S hS c A
  obtain ⟨H, i, hi, hic, his, _⟩ := hRG.1
  obtain ⟨K, j, hj, hjc, hjs, hjconn⟩ := hRQ.1
  let : Smooth H.X.hom := his
  let : Smooth K.X.hom := hjs
  let : ConnectedSpace K.X.left := hjconn
  let : IsAffineHom K.X.hom := hjc.isAffineHom
  let P := SubgroupPreimage.groupScheme q j
  let p : P ⟶ G := SubgroupPreimage.inclusion q j
  let v : P ⟶ K := SubgroupPreimage.projection q j
  have hpc : IsClosedSubgroup p := SubgroupPreimage.isClosedSubgroup q j hjc
  let : IsClosedImmersion p.hom.hom.left := hpc
  let : IsAffineHom P.X.hom := by
    rw [← p.hom.hom.w]
    infer_instance
  let : LocallyOfFiniteType P.X.hom := by
    rw [← p.hom.hom.w]
    infer_instance
  have hp : ((semigroupSubgroup c A).comap q).IsRepresentedBy p :=
    hj.comap_subgroupIntersectionFst hjc q
  have hle : semigroupSubgroup b A ≤ (semigroupSubgroup c A).comap q :=
    SubgroupFunctor.map_le_iff_le_comap.mp
      (semigroupFunctoriality k G Q inferInstance inferInstance inferInstance
        inferInstance S hS b c q heq A)
  have hLieP := hasLieImage_comap_semigroup_of_kernel_le b c q heq hS A hker p hp
  let a := hi.homOfLe hp hle
  have hac : IsClosedSubgroup a := hi.homOfLe_isClosedSubgroup hp hle hic hpc
  let : IsOpenImmersion a.hom.hom.left := isOpenImmersion_of_fullLie a hac
    (fullLie_homOfLe_of_hasLieImage hi hp hle hRG.2.2.1 hLieP)
  let : Flat v.hom.hom.left := SubgroupPreimage.flat_projection q j
  let : LocallyOfFinitePresentation v.hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q j)
      (inferInstance : LocallyOfFinitePresentation q.hom.hom.left)
  let f : H ⟶ K := a ≫ v
  have hflat : Flat f.hom.hom.left := by
    change Flat (a.hom.hom.left ≫ v.hom.hom.left)
    infer_instance
  have hlfp : LocallyOfFinitePresentation f.hom.hom.left := by
    change LocallyOfFinitePresentation (a.hom.hom.left ≫ v.hom.hom.left)
    infer_instance
  let : GeometricallyIntegral K.X.hom := smoothConnectedAffineGeometry.1 k K
    inferInstance inferInstance inferInstance
  let : IsIntegral K.X.left := GeometricallyIntegral.isIntegral_of_subsingleton K.X.hom
  let : Flat f.hom.hom.left := hflat
  have hsurj : Surjective f.hom.hom.left := DominantHomFlat.surjective_of_flat f
  have hsq : i ≫ q = f ≫ j := by
    change i ≫ q = (hi.homOfLe hp hle ≫ v) ≫ j
    rw [Category.assoc, ← subgroupIntersection_condition q j, ← Category.assoc,
      hi.homOfLe_comp hp hle]
  exact ⟨H, K, i, j, f, hi, hj, hsq, hflat, hsurj, hlfp⟩

/-- With full kernel containment, the actual semigroup subgroup is exactly
the full inverse image of the target semigroup subgroup. -/
theorem semigroup_comap_eq_of_fppf_of_kernel_le
    [Smooth G.X.hom] [Smooth Q.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (A : AddSubsemigroup (characterLattice S))
    (hker : SubgroupFunctor.range (kernelι q) ≤ semigroupSubgroup b A) :
    (semigroupSubgroup c A).comap q = semigroupSubgroup b A :=
  (isFppfImage_semigroup_of_kernel_le b c q heq hS A hker).comap_eq_of_kernel_le hker

section Restriction

variable [Smooth G.X.hom] [Smooth Q.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (A : AddSubsemigroup (characterLattice S))
    (hker : SubgroupFunctor.range (kernelι q) ≤ semigroupSubgroup b A)
    {H K : GroupScheme (Spec (CommRingCat.of k))}
    (i : H ⟶ G) (j : K ⟶ Q)
    (hi : (semigroupSubgroup b A).IsRepresentedBy i)
    (hj : (semigroupSubgroup c A).IsRepresentedBy j)

/-- The canonical actual fppf homomorphism on any supplied semigroup subgroup
representatives, under containment of the entire actual kernel. -/
def semigroupFppfRestriction : H ⟶ K :=
  hi.restrictionHom hj q
    (semigroup_comap_eq_of_fppf_of_kernel_le b c q heq hS A hker).ge

/-- The restriction commutes with the original ambient homomorphism. -/
theorem semigroupFppfRestriction_comp :
    semigroupFppfRestriction b c q heq hS A hker i j hi hj ≫ j = i ≫ q :=
  hi.restrictionHom_comp hj q _

/-- The canonical restriction square is cartesian on actual schemes. -/
theorem semigroupFppfRestriction_isPullback_scheme :
    CategoryTheory.IsPullback i.hom.hom.left
      (semigroupFppfRestriction b c q heq hS A hker i j hi hj).hom.hom.left
      q.hom.hom.left j.hom.hom.left :=
  (hi.isPullback_of_comap_eq hj q _
    (semigroupFppfRestriction_comp b c q heq hS A hker i j hi hj).symm
    (semigroup_comap_eq_of_fppf_of_kernel_le b c q heq hS A hker)).map (Over.forget _)

/-- The canonical restriction is flat. -/
theorem semigroupFppfRestriction_flat :
    Flat (semigroupFppfRestriction b c q heq hS A hker i j hi hj).hom.hom.left :=
  MorphismProperty.of_isPullback
    (semigroupFppfRestriction_isPullback_scheme b c q heq hS A hker i j hi hj)
    (inferInstance : Flat q.hom.hom.left)

/-- The canonical restriction is surjective as a scheme morphism. -/
theorem semigroupFppfRestriction_surjective :
    Surjective (semigroupFppfRestriction b c q heq hS A hker i j hi hj).hom.hom.left :=
  MorphismProperty.of_isPullback
    (semigroupFppfRestriction_isPullback_scheme b c q heq hS A hker i j hi hj)
    (inferInstance : Surjective q.hom.hom.left)

/-- The canonical restriction is locally of finite presentation. -/
theorem semigroupFppfRestriction_locallyOfFinitePresentation :
    LocallyOfFinitePresentation
      (semigroupFppfRestriction b c q heq hS A hker i j hi hj).hom.hom.left :=
  MorphismProperty.of_isPullback
    (semigroupFppfRestriction_isPullback_scheme b c q heq hS A hker i j hi hj)
    (inferInstance : LocallyOfFinitePresentation q.hom.hom.left)

end Restriction

end Langlands.GroupScheme.RelativeRoot

import Langlands.GroupScheme.Reductive.AlmostSimpleFiniteKernelRepresentationStatement
import Langlands.GroupScheme.Absolute.SolvableUnipotentKernelAssembly
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof
import Langlands.GroupScheme.CentralIsogeny.CommutingLifts
import Langlands.GroupScheme.MatrixRepresentation.CompositionFactors
import Langlands.GroupScheme.Reductive.FiniteKernelOfTorusRestriction
import Langlands.GroupScheme.Reductive.UnipotentPointKernel
import Langlands.GroupScheme.SmoothConnectedNormalClosure
import Langlands.GroupScheme.Torus.CentralRigidityReduction
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeLargestSubtorusProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.RelativeReductive

/-! # Simple representations of almost-simple groups with finite kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A nontrivial homomorphism from an almost-simple group has finite kernel.
The largest subtorus of its kernel on a maximal torus detects geometric cocharacters. -/
private theorem finiteKernel_of_almostSimple (hG : IsAlmostSimple G)
    (q : G ⟶ H) (hq : q ≠ 0) : IsFinite (kernel q).X.hom := by
  let hred := hG.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hred.smooth
  let : IsAffineHom G.X.hom := hred.isAffineHom
  let : ConnectedSpace G.X.left := hred.connectedSpace
  let : IsSeparated H.X.hom := fieldSeparated k H
  obtain ⟨T, t, ht⟩ := TorusExistence.exists_isMaximalTorus G
  let i := kernelι (t ≫ q)
  have hi : IsClosedSubgroup i := kernelι_isClosedImmersion _
  have hK : IsMultiplicativeType (kernel (t ≫ q)) :=
    ht.1.isMultiplicativeType.of_isClosedSubgroup i hi
  obtain ⟨U, j, hU, hj, Q, p, hQ, hp⟩ := hK.exists_torus_finiteQuotient
  have hu := LargestSubtorus.isUniversalSubtorus_of_finiteQuotient hK j hU hj p hQ hp
  let s := (j ≫ i) ≫ t
  have hs : s ≫ q = 0 := by
    dsimp only [s, i]
    rw [Category.assoc, Category.assoc, kernelι_comp_eq_zero, comp_zero]
  let : Smooth U.X.hom := hU.smooth
  let : IsAffineHom U.X.hom := hU.isRelativeTorus.isAffineHom
  let : ConnectedSpace U.X.left := hU.connectedSpace
  let D := smoothConnectedNormalClosure s
  have hDle := D.range_le (kernelι q) (kernelι_isClosedImmersion q)
    (HopfPrimitive.isNormal_range_kernelι q) (range_le_kernelι_of_comp_eq_zero s q hs)
  let : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : GeometricallyConnected D.group.X.hom := D.hasSmoothConnectedGeneration.2.2.1
  have hDc : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  have hD0 : SubgroupFunctor.range D.inclusion = ⊥ := by
    rcases hG.normalSubgroup_trivial_or_full D.group D.inclusion D.closed
      D.hasSmoothConnectedGeneration.1 hDc D.isNormal with hbot | htop
    · exact hbot
    · exfalso
      apply hq
      have hx : (𝟙 G.X) ∈ (SubgroupFunctor.range D.inclusion).carrier G.X := by
        rw [htop]
        exact Subgroup.mem_top _
      apply (CentralRigidity.hom_eq_one_iff_eq_zero q).mp
      simpa only [Category.id_comp] using (mem_range_kernelι_iff q _).mp (hDle _ hx)
  let : Mono t.hom.hom := ht.2.1.mono_overHom
  have hj0 : j = 0 := by
    have hs0 : SubgroupFunctor.range ((j ≫ i) ≫ t) = ⊥ :=
      le_antisymm (D.contains.trans hD0.le) (fun _ => bot_le)
    apply SubgroupFunctor.eq_zero_of_range_eq_bot
    exact (SubgroupFunctor.range_comp_eq_bot_iff j i).mp
      ((SubgroupFunctor.range_comp_eq_bot_iff (j ≫ i) t).mp hs0)
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let B := GroupScheme.baseChange b
  have hG' : IsConnectedReductive (B.obj G) := hred.baseChange_toAlgebraicClosure
  let : Smooth (B.obj G).X.hom := hG'.smooth
  let : IsAffineHom (B.obj G).X.hom := hG'.isAffineHom
  let : ConnectedSpace (B.obj G).X.left := hG'.connectedSpace
  let : IsSeparated (B.obj H).X.hom := fieldSeparated K (B.obj H)
  have ht' : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T) (B.map t) :=
    (maximalTorusBaseChange k K G T t ht.1 ht.2.1).mp ht
  have hfin : IsFinite (kernel (B.map q)).X.hom := by
    apply kernel_isFinite_of_cocharacter_injective_algClosed hG' (B.map q)
    apply cocharacter_eq_zero_of_homConjugate (B.map q) (exists_homConjugate_of_isMaximalTorus ht')
    intro w hw
    have hw' : w ≫ B.map (t ≫ q) = 0 := by rwa [B.map_comp]
    have hm : SubgroupFunctor.range w ≤ SubgroupFunctor.range (B.map i) := by
      change SubgroupFunctor.range w ≤
        SubgroupFunctor.range ((GroupScheme.baseChange b).map (kernelι (t ≫ q)))
      rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_kernel_baseChange]
      exact range_le_kernelι_of_comp_eq_zero w (B.map (t ≫ q)) hw'
    let hi' : (SubgroupFunctor.range (B.map i)).IsRepresentedBy (B.map i) :=
      ⟨(hi.baseChange b).mono_overHom, rfl⟩
    let f := hi'.factorHom w hm
    have hf : f ≫ B.map i = w := hi'.factorHom_comp w hm
    obtain ⟨a, ha⟩ := hu.2.2 _ b _ f isSplitTorus_gm.isTorus.isRelativeTorus
    have hj' : B.map j = 0 := by
      change (GroupScheme.baseChange b).map j = 0
      rw [hj0, CentralRigidity.baseChange_map_zero]
    change a ≫ B.map j = f at ha
    rw [hj', comp_zero] at ha
    rw [← hf, ← ha, zero_comp]
    rfl
  let e := kernelBaseChangeIso b q
  let : IsFinite (kernel (B.map q)).X.hom := hfin
  let : IsIso e.hom.hom.hom.left := ((Grp.forget _) ⋙ Over.forget _).map_isIso e.hom
  have hfin' : IsFinite (B.obj (kernel q)).X.hom := by
    rw [← Over.w e.hom.hom.hom]
    infer_instance
  change IsFinite (pullback.snd (kernel q).X.hom b) at hfin'
  obtain ⟨hbS, hbF, hbQ⟩ := fieldExtension_fpqc k K
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨hbS, hbF⟩, hbQ⟩ hfin'

open MatrixRepresentation in
/-- Every almost-simple group over a field admits a nonzero simple representation
whose full scheme-theoretic kernel is finite. -/
theorem almostSimpleFiniteKernelRepresentation :
    AlmostSimpleFiniteKernelRepresentationStatement.{u} := by
  classical
  intro k _ G hG
  let hred := hG.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hred.smooth
  let : IsAffineHom G.X.hom := hred.isAffineHom
  let : ConnectedSpace G.X.left := hred.connectedSpace
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement_viaCorepresented k G hred.isAffineHom
    (inferInstance : LocallyOfFiniteType G.X.hom)
  let F := simpleFactorFamily ρ
  have hsome : ∃ i, F.factor i ≠ 0 := by
    by_contra! hall
    have hU : ρ.HasUnipotentPointMatrices := by
      intro T x
      refine ⟨F.length, F.nilpotent T x fun i => ?_⟩
      rw [pointMatrix_apply, hall i, CentralRigidity.zero_hom_hom, MonObj.comp_one, map_one]
    let : IsFinite G.X.hom :=
      hred.isFinite_of_normal_of_unipotentPointMatrices ρ hρ (𝟙 G)
        (by change IsClosedImmersion (𝟙 G.X.left); infer_instance)
        (by
          rw [SubgroupFunctor.range_id]
          intro T g x _ _
          exact Subgroup.mem_top _)
        (by simpa only [restrict_id] using hU)
    have hId : (𝟙 G.X : G.X ⟶ G.X) = 1 :=
      finiteTargetOverHom_eq_one G G (𝟙 G.X) (Category.comp_id _)
    apply hG.noncommutative
    intro T x y
    have hx : x = 1 := by rw [← Category.comp_id x, hId, MonObj.comp_one]
    rw [hx]
    exact Commute.one_left y
  obtain ⟨i, hi⟩ := hsome
  let : Nontrivial (Fin (F.dimension i) → k) := (F.simple i).1
  exact ⟨F.dimension i, F.factor i, top_ne_bot, (F.simple i).2,
    finiteKernel_of_almostSimple hG (F.factor i) hi⟩

end Langlands.GroupScheme

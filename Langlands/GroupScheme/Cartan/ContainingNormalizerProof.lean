import Langlands.GroupScheme.Cartan.ContainingNormalizerStatement
import Langlands.GroupScheme.Rational.ClassFunctionsTorusDensity
import Langlands.GroupScheme.Lie.SmoothOpenSubgroup
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange

/-! # Normalizers of smooth subgroups containing a torus centralizer -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace CartanContainingNormalizer

open Langlands.GroupScheme.Lie TorusConjugation

/-- A split torus centralizer contained in a subgroup forces every infinitesimal
normalizer point into that subgroup over an algebraically closed field. -/
theorem lie_mem_range_of_split {k : Type u} [Field k] [IsAlgClosed k]
    {G H N : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ N) (hT : IsSplitTorus T.toGrp)
    (h : H ⟶ G) (n : N ⟶ G)
    (hn : SubgroupFunctor.range n ≤ (SubgroupFunctor.range h).normalizer)
    (hc : torusCentralizer (t ≫ n) ≤ SubgroupFunctor.range h)
    (Z : lieKernel N k) :
    Z.val ≫ n.hom.hom ∈ (SubgroupFunctor.range h).carrier (dualTest k) := by
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  obtain ⟨τ, hreg⟩ := exists_regular t hT
  obtain ⟨ξ, W, hW, hZ⟩ := exists_adjoint_sub_add t hT τ hreg (Additive.ofMul Z)
  let C := N.constantPoint (τ ≫ t.hom.hom) (dualTest k)
  have hC : C ≫ n.hom.hom ∈ (SubgroupFunctor.range h).carrier (dualTest k) := by
    apply hc _
    apply range_le_torusCentralizer (t ≫ n) _
    refine ⟨GroupScheme.constantPoint T.toGrp τ (dualTest k), ?_⟩
    rfl
  have hξ : ξ.toMul.val ≫ n.hom.hom ∈
      (SubgroupFunctor.range h).normalizer.carrier (dualTest k) := hn _ ⟨ξ.toMul.val, rfl⟩
  have hcomm : (C⁻¹ * ξ.toMul.val * C * ξ.toMul.val⁻¹) ≫ n.hom.hom ∈
      (SubgroupFunctor.range h).carrier (dualTest k) := by
    have hp := SubgroupFunctor.conj_mem_of_mem_normalizer hξ hC
    have hm := ((SubgroupFunctor.range h).carrier (dualTest k)).mul_mem
      (((SubgroupFunctor.range h).carrier (dualTest k)).inv_mem hC) hp
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, mul_assoc] using hm
  have hWc := mem_torusCentralizer_of_mem_weightSpace_zero t W.toMul hW
  have hWn : W.toMul.val ≫ n.hom.hom ∈
      (SubgroupFunctor.range h).carrier (dualTest k) := by
    apply hc _
    intro V a s
    change (a ≫ W.toMul.val ≫ n.hom.hom) * (s ≫ (t ≫ n).hom.hom) =
      (s ≫ (t ≫ n).hom.hom) * (a ≫ W.toMul.val ≫ n.hom.hom)
    have he := congrArg (fun p => p ≫ n.hom.hom) (hWc V a s).eq
    simpa only [MonObj.mul_comp, Category.assoc, Grp.comp_hom_hom] using he
  have hZv : Z.val = C⁻¹ * ξ.toMul.val * C * ξ.toMul.val⁻¹ * W.toMul.val := by
    have he := congrArg (fun x : Additive (lieKernel N k) => x.toMul.val) hZ
    simp only [toMul_ofMul, toMul_add, toMul_sub, div_eq_mul_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, adjoint_val] at he
    rw [he, constant_constantPoint, constantPoint_inv, inv_inv]
  rw [hZv, MonObj.mul_comp]
  exact ((SubgroupFunctor.range h).carrier (dualTest k)).mul_mem hcomm hWn

/-- Over an algebraically closed field, a smooth closed subgroup containing
the centralizer of a split torus is open in each closed normalizer representative. -/
theorem isOpenImmersion_of_split {k : Type u} [Field k] [IsAlgClosed k]
    {G H N : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth H.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hc : torusCentralizer j ≤ SubgroupFunctor.range h)
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (hrep : (SubgroupFunctor.range h).normalizer.IsRepresentedBy n)
    (f : H ⟶ N) (hf : f ≫ n = h) :
    IsOpenImmersion f.hom.hom.left := by
  have : IsClosedImmersion n.hom.hom.left := hn
  have : Mono n.hom.hom := hrep.1
  have : IsAffineHom N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  have : LocallyOfFiniteType N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  have hfclosed : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hn (by rwa [hf])
  have : IsClosedImmersion f.hom.hom.left := hfclosed
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  have htRange : SubgroupFunctor.range j ≤ (SubgroupFunctor.range h).normalizer :=
    ((range_le_torusCentralizer j).trans hc).trans (SubgroupFunctor.range h).le_normalizer
  let t : T.toGrp ⟶ N := hrep.factorHom j htRange
  have ht : t ≫ n = j := hrep.factorHom_comp j htRange
  apply isOpenImmersion_of_fullLie f hfclosed
  intro X
  have hX := lie_mem_range_of_split t hT h n (by rw [hrep.2])
    (by rwa [ht]) X
  change ∃ y : dualTest k ⟶ H.X, y ≫ h.hom.hom = X.val ≫ n.hom.hom at hX
  obtain ⟨y, hy⟩ := hX
  have hyf : y ≫ f.hom.hom = X.val := by
    apply (cancel_mono n.hom.hom).mp
    calc
      (y ≫ f.hom.hom) ≫ n.hom.hom = y ≫ (f ≫ n).hom.hom := by
        rw [Grp.comp_hom_hom, Category.assoc]
      _ = y ≫ h.hom.hom := by rw [hf]
      _ = _ := hy
  refine ⟨⟨y, mem_lieKernel_of_comp f y ?_⟩, hyf⟩
  rw [hyf]
  exact X.property

set_option backward.isDefEq.respectTransparency false in
/-- A smooth closed subgroup containing the centralizer of a torus is open
in its closed normalizer over an arbitrary field. -/
theorem isOpenImmersion_of_torus {k : Type u} [Field k]
    {G H N : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth H.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hc : torusCentralizer j ≤ SubgroupFunctor.range h)
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (hrep : (SubgroupFunctor.range h).normalizer.IsRepresentedBy n)
    (f : H ⟶ N) (hf : f ≫ n = h) :
    IsOpenImmersion f.hom.hom.left := by
  obtain ⟨K, _, _, hK⟩ := hT
  let Ω : Type u := AlgebraicClosure K
  let b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let G' := (GroupScheme.baseChange b).obj G
  let H' := (GroupScheme.baseChange b).obj H
  let N' := (GroupScheme.baseChange b).obj N
  let T' := (CommGroupScheme.baseChange b).obj T
  let j' : T'.toGrp ⟶ G' := (GroupScheme.baseChange b).map j
  let h' : H' ⟶ G' := (GroupScheme.baseChange b).map h
  let n' : N' ⟶ G' := (GroupScheme.baseChange b).map n
  let f' : H' ⟶ N' := (GroupScheme.baseChange b).map f
  have hT' : IsSplitTorus T'.toGrp :=
    hK.baseChange_fieldTower k K Ω T.toGrp
  have : IsAffineHom G'.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have : LocallyOfFiniteType G'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have : Smooth H'.X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd H.X.hom b))
  have hc' : torusCentralizer j' ≤ SubgroupFunctor.range h' := by
    have hc' := SubgroupFunctor.baseChange_mono b hc
    rwa [← torusCentralizer_baseChange, ← SubgroupFunctor.range_baseChangeHom] at hc'
  have hrep' : (SubgroupFunctor.range h').normalizer.IsRepresentedBy n' := by
    have hrep' := hrep.baseChange b
    rwa [SubgroupFunctor.normalizer_baseChange,
      ← SubgroupFunctor.range_baseChangeHom] at hrep'
  have hf' : f' ≫ n' = h' := by
    change (GroupScheme.baseChange b).map f ≫ (GroupScheme.baseChange b).map n =
      (GroupScheme.baseChange b).map h
    rw [← Functor.map_comp, hf]
  have hopen : IsOpenImmersion f'.hom.hom.left :=
    isOpenImmersion_of_split j' hT' h' (hh.baseChange b) hc'
      n' (hn.baseChange b) hrep' f' hf'
  have houter : IsPullback
      (f'.hom.hom.left ≫ CategoryTheory.Limits.pullback.snd N.X.hom b)
      (CategoryTheory.Limits.pullback.fst H.X.hom b) b
      (f.hom.hom.left ≫ N.X.hom) := by
    change IsPullback (((Over.pullback b).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left,
      CategoryTheory.Limits.pullback.lift_snd] using
      (IsPullback.of_hasPullback H.X.hom b).flip
  have hp := houter.of_right
    (show f'.hom.hom.left ≫ CategoryTheory.Limits.pullback.fst N.X.hom b =
        CategoryTheory.Limits.pullback.fst H.X.hom b ≫ f.hom.hom.left by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, CategoryTheory.Limits.pullback.lift_fst])
    (IsPullback.of_hasPullback N.X.hom b).flip
  obtain ⟨hb1, hb2, hb3⟩ := fieldExtension_fpqc k Ω
  have : Surjective b := hb1
  have : Flat b := hb2
  have : QuasiCompact b := hb3
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hopen

end CartanContainingNormalizer

/-- Milne, Lemma 17.47, over every field and universe. -/
theorem cartanContainingNormalizer : CartanContainingNormalizerStatement.{u} := by
  intro k _ G _ _ _ H h hh hH C c hc hch N n hrep hn
  let : Smooth H.X.hom := hH
  obtain ⟨_, T, j, hj, heq⟩ := hc
  rw [heq] at hch
  have hopen : ∀ f : H ⟶ N, f ≫ n = h → IsOpenImmersion f.hom.hom.left :=
    fun f hf => CartanContainingNormalizer.isOpenImmersion_of_torus
      j hj.1 h hh hch n hn hrep f hf
  let f : H ⟶ N := hrep.factorHom h (SubgroupFunctor.range h).le_normalizer
  have hf : f ≫ n = h := hrep.factorHom_comp h (SubgroupFunctor.range h).le_normalizer
  have : IsOpenImmersion f.hom.hom.left := hopen f hf
  have : IsClosedImmersion n.hom.hom.left := hn
  have : LocallyOfFiniteType N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  exact ⟨smooth_of_smooth_open_subgroup N H f, hopen⟩

end Langlands.GroupScheme

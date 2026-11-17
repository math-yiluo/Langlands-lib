import Langlands.GroupScheme.Absolute.WeylBorelSimplyTransitiveStatement
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.BorelNormalizerProof
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof
import Langlands.GroupScheme.Cartan.StructureReduction
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Absolute.SolvableTorusNormalizer

/-! # Simple transitivity of the Weyl action on Borels through a maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace WeylBorel

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
  {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G}

/-- Correct a Borel conjugacy inside its target Borel to preserve the chosen torus. -/
theorem transitive (hj : IsMaximalTorus j) (hb : IsBorelSubgroup b)
    (hjb : SubgroupFunctor.range j ≤ SubgroupFunctor.range b)
    {B' : GroupScheme (Spec (CommRingCat.of k))} (b' : B' ⟶ G)
    (hb' : IsBorelSubgroup b')
    (hjb' : SubgroupFunctor.range j ≤ SubgroupFunctor.range b') :
    ∃ n ∈ normalizerPoints j,
      SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = SubgroupFunctor.range b' := by
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : IsClosedImmersion b'.hom.hom.left := hb'.isClosedSubgroup
  have hr : (SubgroupFunctor.range b).IsRepresentedBy b :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hr' : (SubgroupFunctor.range b').IsRepresentedBy b' :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let f := hr.factorHom j hjb
  let f' := hr'.factorHom j hjb'
  have hf : f ≫ b = j := hr.factorHom_comp j hjb
  have hf' : f' ≫ b' = j := hr'.factorHom_comp j hjb'
  have : Smooth B'.X.hom := hb'.smooth
  have : ConnectedSpace B'.X.left := hb'.connectedSpace
  have : IsAffineHom B'.X.hom := by
    rw [← Over.w b'.hom.hom]
    infer_instance
  obtain ⟨g, φ, hg⟩ := (borelConjugacy k G).2 B B' b b' hb hb'
  have hfg : (f ≫ φ.hom) ≫ b' = j ≫ (G.innerIso g).hom := by
    rw [Category.assoc, ← hg, ← Category.assoc, hf]
  have hfmax : IsMaximalTorus (f ≫ φ.hom) :=
    IsMaximalTorus.of_comp hb'.isClosedSubgroup (by rw [hfg]; exact hj.comp_iso _)
  have hf'max : IsMaximalTorus f' :=
    IsMaximalTorus.of_comp hb'.isClosedSubgroup (by rwa [hf'])
  obtain ⟨p, σ, hp⟩ := maximalTorusConjugacy k B' T T (f ≫ φ.hom) f' hfmax hf'max
  let n := (p ≫ b'.hom.hom) * g
  have hn : j ≫ (G.innerIso n).hom = CommGroupScheme.groupHom σ.hom ≫ j := by
    change j ≫ (G.innerIso ((p ≫ b'.hom.hom) * g)).hom = _
    rw [innerIso_mul_hom, ← Category.assoc, ← hfg, Category.assoc,
      ← innerIso_hom_comp, ← Category.assoc, hp, Category.assoc, hf']
  refine ⟨n, ⟨σ, hn⟩, ?_⟩
  change SubgroupFunctor.range
    (b ≫ (G.innerIso ((p ≫ b'.hom.hom) * g)).hom) = _
  rw [innerIso_mul_hom, ← Category.assoc, hg, Category.assoc,
    ← innerIso_hom_comp, SubgroupFunctor.range_iso_comp,
    SubgroupFunctor.range_iso_comp]

/-- The centralizer of a maximal torus lies in each Borel containing that torus. -/
theorem centralizer_le (hj : IsMaximalTorus j) (hb : IsBorelSubgroup b)
    (hjb : SubgroupFunctor.range j ≤ SubgroupFunctor.range b) :
    torusCentralizer j ≤ SubgroupFunctor.range b := by
  have hsplit : IsSplitTorus T.toGrp :=
    hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ := hsplit.exists_cocharacter_centralizer j
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, c, hc, hrep⟩ := exists_isCartanSubgroup_of_isMaximalTorus hj
  obtain ⟨hCs, hCc, hCn⟩ := hc.structure_of_isAlgClosed
  have hsol : IsSolvableGroupScheme C := hCn.isSolvableGroupScheme
  have hrepχ : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy c := by
    rwa [hν]
  have hχb : SubgroupFunctor.range (CommGroupScheme.groupHom ν ≫ j) ≤
      SubgroupFunctor.range b := by
    intro V x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply hjb
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨t ≫ (CommGroupScheme.groupHom ν).hom.hom, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc]
  obtain ⟨D, d, hd, hdb⟩ := centralizerBorelIntersection k G
    (CommGroupScheme.groupHom ν ≫ j) C c hc.1 hrepχ hCs hCc B b hb hχb
  have hid : IsClosedSubgroup (𝟙 C) := by
    change IsClosedImmersion (𝟙 C.X.left)
    infer_instance
  have : IsIso d := hd.maximal C (𝟙 C) d hid hCs hCc hsol (Category.comp_id d)
  have he := SubgroupFunctor.range_iso_comp (asIso d) c
  simp only [asIso_hom] at he
  rw [he, hrep.2] at hdb
  exact hdb

/-- Centralizer points preserve a Borel through the torus. -/
theorem centralizer_fixes (hj : IsMaximalTorus j) (hb : IsBorelSubgroup b)
    (hjb : SubgroupFunctor.range j ≤ SubgroupFunctor.range b)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hn : n ∈ centralizerPoints j) :
    SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = SubgroupFunctor.range b := by
  have hnC : n ∈ (torusCentralizer j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    (mem_torusCentralizer_base_iff j n).mpr ((mem_centralizerPoints j).mp hn)
  obtain ⟨p, rfl⟩ := SubgroupFunctor.mem_range.mp (centralizer_le hj hb hjb _ hnC)
  rw [← innerIso_hom_comp, SubgroupFunctor.range_iso_comp]

omit [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] in
/-- Range invariance under conjugation implies abstract normalizer membership on base points. -/
theorem mem_pointNormalizer_of_range_eq
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (heq : SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = SubgroupFunctor.range b) :
    n ∈ Subgroup.normalizer
      ((SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [← heq]
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨p, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_self]
  · intro hx
    rw [← heq] at hx
    obtain ⟨p, hp⟩ := SubgroupFunctor.mem_range.mp hx
    refine ⟨p, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_self] at hp
    exact mul_left_cancel (mul_right_cancel hp)

omit [Smooth G.X.hom] [ConnectedSpace G.X.left] in
/-- A point of a solvable group normalizing a maximal torus centralizes it. -/
theorem normalizer_in_borel_centralizes (hj : IsMaximalTorus j) (hb : IsBorelSubgroup b)
    (hjb : SubgroupFunctor.range j ≤ SubgroupFunctor.range b)
    (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X)
    (hn : p ≫ b.hom.hom ∈ normalizerPoints j) :
    p ≫ b.hom.hom ∈ centralizerPoints j := by
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : Mono b := (Grp.forget _).mono_of_mono_map (inferInstance : Mono b.hom.hom)
  have : Smooth B.X.hom := hb.smooth
  have : ConnectedSpace B.X.left := hb.connectedSpace
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  have hr : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨inferInstance, rfl⟩
  let f := hr.factorHom j hjb
  have hf : f ≫ b = j := hr.factorHom_comp j hjb
  have hfmax : IsMaximalTorus f :=
    IsMaximalTorus.of_comp hb.isClosedSubgroup (by rwa [hf])
  obtain ⟨σ, hσ⟩ := hn
  have hσB : f ≫ (B.innerIso p).hom = CommGroupScheme.groupHom σ.hom ≫ f := by
    apply (cancel_mono b).mp
    rw [Category.assoc, innerIso_hom_comp, ← Category.assoc, hf,
      Category.assoc, hf]
    exact hσ
  have hpC := hfmax.mem_centralizerPoints_of_mem_normalizerPoints_of_isSolvable
    hb.isSolvableGroupScheme p ⟨σ, hσB⟩
  apply (mem_centralizerPoints j).mpr
  change j ≫ (G.innerIso (p ≫ b.hom.hom)).hom = _
  rw [← hf, Category.assoc, ← innerIso_hom_comp, ← Category.assoc,
    (mem_centralizerPoints f).mp hpC]

end WeylBorel

/-- The Weyl group acts simply transitively on the Borel subgroups containing a maximal torus. -/
theorem weylBorelSimplyTransitive : WeylBorelSimplyTransitiveStatement.{u} := by
  intro k _ _ G _ _ _ T j hj B b hb hjb
  refine ⟨fun B' b' hb' hjb' => WeylBorel.transitive hj hb hjb b' hb' hjb',
    WeylBorel.centralizer_fixes hj hb hjb, ?_⟩
  intro n hn heq
  have hnN := WeylBorel.mem_pointNormalizer_of_range_eq n heq
  rw [borelNormalizer k G B b hb] at hnN
  obtain ⟨p, rfl⟩ := SubgroupFunctor.mem_range.mp hnN
  exact WeylBorel.normalizer_in_borel_centralizes hj hb hjb p hn

end Langlands.GroupScheme

import Langlands.GroupScheme.Rational.RootKernelIdentityRoot
import Langlands.GroupScheme.Rational.RootFactorPairReflection
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.CharacterFpqcProof

/-! # Actual opposite factor pairs in full-kernel identity components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Normalizer

variable {B : Scheme.{u}} {T : CommGroupScheme B} {H G : GroupScheme B}
    {iH : T.toGrp ⟶ H}

/-- A monomorphic homomorphism reflects normalization through the same torus
automorphism. -/
theorem IsNormalizingPoint.of_comp (j : H ⟶ G) [Mono j.hom.hom]
    {n : Over.mk (𝟙 B) ⟶ H.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint (iH ≫ j) (n ≫ j.hom.hom) σ) :
    IsNormalizingPoint iH n σ := by
  have : Mono j := (Grp.forget _).mono_of_mono_map (f := j) ‹Mono j.hom.hom›
  apply (cancel_mono j).mp
  change (iH ≫ (H.innerIso n).hom) ≫ j =
    (CommGroupScheme.groupHom σ.hom ≫ iH) ≫ j
  rw [Category.assoc, innerIso_hom_comp, ← Category.assoc]
  exact hn

/-- Normalization of the torus is unchanged by a monomorphic ambient
inclusion containing that torus. -/
theorem mem_normalizerPoints_comp_iff (iH : T.toGrp ⟶ H)
    (j : H ⟶ G) [Mono j.hom.hom] (n : Over.mk (𝟙 B) ⟶ H.X) :
    n ≫ j.hom.hom ∈ normalizerPoints (iH ≫ j) ↔
      n ∈ normalizerPoints iH := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, hσ.of_comp j⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, hσ.comp j⟩

end Normalizer

namespace RelativeRoot

section PairMap

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    {iH : T.toGrp ⟶ H} {iG : T.toGrp ⟶ G}
    {a : characterLattice T} {x : rationalPoints H}
    {p : rationalPoints H × rationalPoints H}

/-- A homomorphism containing the same torus carries actual opposite factor
pairs to actual opposite factor pairs. -/
theorem IsOppositeFactorPair.map (j : H ⟶ G) (hij : iH ≫ j = iG)
    (hp : IsOppositeFactorPair iH a x p) :
    IsOppositeFactorPair iG a (rationalPoints.map j x)
      (rationalPoints.map j p.1, rationalPoints.map j p.2) := by
  subst iG
  refine ⟨comp_mem_subgroup iH (-a) j hp.1,
    comp_mem_subgroup iH (-a) j hp.2.1, ?_⟩
  have hn := (normalizerPointsMap iH j (iH ≫ j) rfl
    ⟨p.1 * x * p.2, hp.2.2⟩).property
  simpa only [normalizerPointsMap_val, rationalPoints.map_apply,
    MonObj.mul_comp] using hn

/-- The map on the actual types of ordered normalizing opposite pairs,
induced by a homomorphism carrying the same torus. -/
def oppositeFactorPairsMap (j : H ⟶ G) (hij : iH ≫ j = iG)
    (a : characterLattice T) (x : rationalPoints H) :
    {p // IsOppositeFactorPair iH a x p} →
      {p // IsOppositeFactorPair iG a (rationalPoints.map j x) p} :=
  fun p => ⟨(rationalPoints.map j p.val.1, rationalPoints.map j p.val.2),
    p.property.map j hij⟩

end PairMap

section IdentityComponent

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (ha : a ≠ 0) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j)

/-- Negating the character leaves the actual torus embedding into the same
kernel-centralizer identity component unchanged. -/
theorem kernelCentralizerIdentityTorus_neg :
    kernelCentralizerIdentityTorus i hT (-a) j
        (by simpa only [kernelCentralizer_neg] using hj) =
      kernelCentralizerIdentityTorus i hT a j hj := by
  have : Mono j.hom.hom := hj.1
  have : Mono (identityComponentι C ≫ j).hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ j.hom.hom)
    infer_instance
  have : Mono (identityComponentι C ≫ j) :=
    (Grp.forget _).mono_of_mono_map (f := identityComponentι C ≫ j)
      ‹Mono (identityComponentι C ≫ j).hom.hom›
  apply (cancel_mono (identityComponentι C ≫ j)).mp
  rw [kernelCentralizerIdentityTorus_comp_ambient,
    kernelCentralizerIdentityTorus_comp_ambient]

include ha hjc

/-- The same actual component inclusion identifies the opposite intrinsic
root functor as well as the original one. -/
theorem kernelCentralizerIdentity_subgroup_neg_map :
    (subgroup (kernelCentralizerIdentityTorus i hT a j hj) (-a)).map
        (identityComponentι C ≫ j) = subgroup i (-a) := by
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k T hT (-a) (neg_ne_zero.mpr ha)
  let : QuasiCompact (CommGroupScheme.groupHom (-a)).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom (-a)).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom (-a)).hom.hom.left := hsurj
  have hneg : (kernelCentralizer i (-a)).IsRepresentedBy j := by
    simpa only [kernelCentralizer_neg] using hj
  have hmap := kernelCentralizerIdentity_subgroup_map i hT (-a) j hneg hjc
  rw [kernelCentralizerIdentityTorus_neg i hT a j hj] at hmap
  exact hmap

/-- Every ambient opposite factor pair lifts through the same actual
identity-component inclusion, preserving both ordered factors. -/
theorem kernelCentralizerIdentity_lift_oppositeFactorPair
    (x : rationalPoints (identityComponent C))
    {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a
      (rationalPoints.map (identityComponentι C ≫ j) x) p) :
    ∃ q, IsOppositeFactorPair (kernelCentralizerIdentityTorus i hT a j hj) a x q ∧
      (rationalPoints.map (identityComponentι C ≫ j) q.1,
        rationalPoints.map (identityComponentι C ≫ j) q.2) = p := by
  let f := identityComponentι C ≫ j
  let iC := kernelCentralizerIdentityTorus i hT a j hj
  have hfi : iC ≫ f = i := kernelCentralizerIdentityTorus_comp_ambient i hT a j hj
  have : Mono j.hom.hom := hj.1
  have : Mono f.hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ j.hom.hom)
    infer_instance
  have hmap := kernelCentralizerIdentity_subgroup_neg_map i hT a ha j hj hjc
  have hlift : ∀ y : rationalPoints G,
      y ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)) →
      ∃ z : rationalPoints (identityComponent C),
        z ∈ (subgroup iC (-a)).carrier (Over.mk (𝟙 _)) ∧
          rationalPoints.map f z = y := by
    intro y hy
    rw [← hmap] at hy
    exact SubgroupFunctor.mem_map.mp hy
  obtain ⟨y, hy, hpy⟩ := hlift p.1 hp.1
  obtain ⟨z, hz, hpz⟩ := hlift p.2 hp.2.1
  refine ⟨(y, z), ⟨hy, hz, ?_⟩, Prod.ext hpy hpz⟩
  apply (mem_normalizerPoints_comp_iff iC f (y * x * z)).mp
  rw [hfi]
  change rationalPoints.map f (y * x * z) ∈ normalizerPoints i
  rw [map_mul, map_mul, hpy, hpz]
  exact hp.2.2

/-- The actual inclusion gives an equivalence of the complete types of
normalizing opposite pairs, for each middle point of the component. -/
def kernelCentralizerIdentityOppositeFactorPairsEquiv
    (x : rationalPoints (identityComponent C)) :
    {p // IsOppositeFactorPair (kernelCentralizerIdentityTorus i hT a j hj) a x p} ≃
      {p // IsOppositeFactorPair i a
        (rationalPoints.map (identityComponentι C ≫ j) x) p} := by
  let f := identityComponentι C ≫ j
  have : Mono j.hom.hom := hj.1
  have : Mono f.hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ j.hom.hom)
    infer_instance
  refine Equiv.ofBijective
    (oppositeFactorPairsMap f (kernelCentralizerIdentityTorus_comp_ambient i hT a j hj) a x)
    ⟨?_, ?_⟩
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply (cancel_mono f.hom.hom).mp
      exact congrArg (fun r => r.val.1) hpq
    · apply (cancel_mono f.hom.hom).mp
      exact congrArg (fun r => r.val.2) hpq
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq, hqp⟩ :=
      kernelCentralizerIdentity_lift_oppositeFactorPair i hT a ha j hj hjc x hp
    exact ⟨⟨q, hq⟩, Subtype.ext hqp⟩

@[simp]
theorem kernelCentralizerIdentityOppositeFactorPairsEquiv_apply
    (x : rationalPoints (identityComponent C))
    (p : {p // IsOppositeFactorPair (kernelCentralizerIdentityTorus i hT a j hj) a x p}) :
    (kernelCentralizerIdentityOppositeFactorPairsEquiv i hT a ha j hj hjc x p).val =
      (rationalPoints.map (identityComponentι C ≫ j) p.val.1,
        rationalPoints.map (identityComponentι C ≫ j) p.val.2) := rfl

/-- Actual factor-pair existence in the ambient group is equivalent to
existence inside the actual full-kernel identity component. The middle
point is carried by the actual inclusion. -/
theorem exists_oppositeFactorPair_kernelCentralizerIdentity_iff
    (x : rationalPoints (identityComponent C)) :
    (∃ p, IsOppositeFactorPair (kernelCentralizerIdentityTorus i hT a j hj) a x p) ↔
      ∃ p, IsOppositeFactorPair i a
        (rationalPoints.map (identityComponentι C ≫ j) x) p := by
  have he :=
    (kernelCentralizerIdentityOppositeFactorPairsEquiv i hT a ha j hj hjc x).nonempty_congr
  simpa only [nonempty_subtype] using he

/-- Existence for every nonidentity point of the original actual root
subgroup is equivalent to the same assertion inside the actual full-kernel
identity component. -/
theorem forall_exists_oppositeFactorPair_kernelCentralizerIdentity_iff :
    (∀ x : rationalPoints (identityComponent C),
      x ∈ (subgroup (kernelCentralizerIdentityTorus i hT a j hj) a).carrier
        (Over.mk (𝟙 _)) →
      x ≠ 1 → ∃ p,
        IsOppositeFactorPair (kernelCentralizerIdentityTorus i hT a j hj) a x p) ↔
    (∀ x : rationalPoints G,
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) →
      x ≠ 1 → ∃ p, IsOppositeFactorPair i a x p) := by
  let f := identityComponentι C ≫ j
  let iC := kernelCentralizerIdentityTorus i hT a j hj
  have hfi : iC ≫ f = i := kernelCentralizerIdentityTorus_comp_ambient i hT a j hj
  have : Mono j.hom.hom := hj.1
  have : Mono f.hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ j.hom.hom)
    infer_instance
  have hinj : Function.Injective (rationalPoints.map f) := by
    intro x y hxy
    exact (cancel_mono f.hom.hom).mp hxy
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k T hT a ha
  let : QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom a).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom a).hom.hom.left := hsurj
  have hmap := kernelCentralizerIdentity_subgroup_map i hT a j hj hjc
  constructor
  · intro hC x hx hx1
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := SubgroupFunctor.mem_map.mp hx
    have hy1 : y ≠ 1 := by
      intro hyone
      apply hx1
      rw [← hyx, hyone]
      exact map_one (rationalPoints.map f)
    obtain ⟨p, hp⟩ := hC y hy hy1
    refine ⟨(rationalPoints.map f p.1, rationalPoints.map f p.2), ?_⟩
    have hyx' : rationalPoints.map f y = x := hyx
    simpa only [hyx'] using hp.map f hfi
  · intro hG x hx hx1
    have hxG : rationalPoints.map f x ∈
        (subgroup i a).carrier (Over.mk (𝟙 _)) := by
      rw [← hfi]
      exact comp_mem_subgroup iC a f hx
    have hxG1 : rationalPoints.map f x ≠ 1 := by
      intro h
      exact hx1 (hinj (h.trans (map_one (rationalPoints.map f)).symm))
    exact (exists_oppositeFactorPair_kernelCentralizerIdentity_iff
      i hT a ha j hj hjc x).mpr (hG _ hxG hxG1)

end IdentityComponent

end RelativeRoot

end Langlands.GroupScheme

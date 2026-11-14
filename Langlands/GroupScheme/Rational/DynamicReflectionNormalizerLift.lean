import Langlands.GroupScheme.Rational.CyclicDynamicRootComparison
import Langlands.GroupScheme.Rational.RootReflectionTranslatedCell
import Langlands.GroupScheme.Rational.RootFactorPairExistenceReduction
import Langlands.GroupScheme.Rational.KernelCentralizerWeightSupport

/-! # A fixed lifted reflection cell for a descended cyclic action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section DescendedSupport

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ H) (a : characterLattice T)
    (e : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp H)
    (he : e.restrict (CommGroupScheme.groupHom a) = AutomorphicAction.conjugation i)

include he

/-- An actually descended conjugation action is trivial on the full
scheme-theoretic kernel of its defining character. -/
theorem kernelCentralizer_eq_top_of_descendedAction :
    kernelCentralizer i a = ⊤ := by
  apply SubgroupFunctor.ext
  intro V
  apply Subgroup.ext
  intro x
  constructor
  · intro _
    trivial
  intro _
  change ∀ (W : Over _) (b : W ⟶ V) (c : W ⟶ (characterKernel a).X), _
  intro W b c
  rw [← he]
  exact e.restrict_kernelActsTrivially (CommGroupScheme.groupHom a) W c (b ≫ x)

variable [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- Every actual root of a descended conjugation action is an integral
multiple of its original character, even when that character is not a root. -/
theorem root_mem_zmultiples_of_descendedAction
    (hT : IsSplitTorus T.toGrp)
    {c : characterLattice T} (hc : c ∈ relativeRoots i) :
    c ∈ AddSubgroup.zmultiples a := by
  have htop := kernelCentralizer_eq_top_of_descendedAction i a e he
  have hid : CommGroupScheme.groupHom (𝟙 T) = 𝟙 T.toGrp := rfl
  have hrange' : SubgroupFunctor.range (𝟙 H) ≤ kernelCentralizer i a := by
    rw [htop]
    intro V x _
    trivial
  have hrange : SubgroupFunctor.range (𝟙 H) ≤
      kernelCentralizer (CommGroupScheme.groupHom (𝟙 T) ≫ (i ≫ 𝟙 H)) a := by
    simpa only [hid, Category.id_comp, Category.comp_id] using hrange'
  simpa only [Category.id_comp] using
    root_restrict_mem_zmultiples_of_range_le_kernelCentralizer
      hT (𝟙 T) i (𝟙 H) a hrange hc

end DescendedSupport

section Lift

variable {k : Type u} [Field k] [PerfectField k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (r : N ⟶ G) (hr : IsClosedSubgroup r) (hN : IsUnipotent N)
    (q : G ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range r) q)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp)
    (hQ : IsConnectedReductive Q) (hi : IsMaximalSplitTorus (i ≫ q))
    [IsAffineHom Q.X.hom] [Mono (i ≫ q).hom.hom.left]
    (a : characterLattice T)
    (e : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp Q)
    (he : e.restrict (CommGroupScheme.groupHom a) =
      AutomorphicAction.conjugation (i ≫ q))
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν)
    (hne : Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ (i ≫ q)) ≠ ⊥)

/-- Choose one source normalizer and one actual torus automorphism, negating
the original character, whose quotient image gives a translated cell for every
nonidentity positive dynamic point. The original character need not be a root. -/
def dynamicReflectionNormalizerLift :
    {m : rationalPoints G × (T ≅ T) //
      IsNormalizingPoint i m.1 m.2 ∧ characterAut m.2 a = -a ∧
        ∀ (x : rationalPoints Q),
          x ∈ (Dynamic.unipotent
            (CommGroupScheme.groupHom ν ≫ (i ≫ q))).carrier (Over.mk (𝟙 _)) →
          x ≠ 1 →
          ∃ y ∈ (Dynamic.unipotent
              (CommGroupScheme.groupHom (-ν) ≫ (i ≫ q))).carrier (Over.mk (𝟙 _)),
            ∃ z ∈ (Dynamic.centralizer
                (CommGroupScheme.groupHom ν ≫ (i ≫ q))).carrier (Over.mk (𝟙 _)),
              ∃ w ∈ (Dynamic.unipotent
                  (CommGroupScheme.groupHom (-ν) ≫ (i ≫ q))).carrier (Over.mk (𝟙 _)),
                x = y * z * rationalPoints.map q m.1 * w} := by
  let : Smooth Q.X.hom := hQ.smooth
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [map_zero, LinearMap.zero_apply, lt_self_iff_false] at hpos
  have hcyclic : ∀ c ∈ relativeRoots (i ≫ q), c ∈ AddSubgroup.zmultiples a :=
    fun _ hc => root_mem_zmultiples_of_descendedAction (i ≫ q) a e he
      hi.isSplitSubtorus.1 hc
  let b := cyclicDynamicRoot (i ≫ q) ν hi.isSplitSubtorus.1
    (relativeRootSystem k Q hQ T (i ≫ q) hi) hcyclic hpos hne
  have hb : b.val ∈ relativeRoots (i ≫ q) := b.property.1.1.1
  let m := reflectionNormalizerLift r hr hN q hq i hT hQ hi hb
  refine ⟨m.val, m.property.2.1, ?_, ?_⟩
  · exact characterAut_eq_neg_of_pos_multiple ν hi.isSplitSubtorus.1 hpos
      (hcyclic b.val hb) b.property.1.2 m.val.2 m.property.2.2
  · intro x hx hx1
    have hx' : x ∈ (subgroup (i ≫ q) b.val).carrier (Over.mk (𝟙 _)) := by
      rwa [← b.property.2.1]
    obtain ⟨y, hy, z, hz, w, hw, heq⟩ :=
      reflectionNormalizerLift_translatedCell r hr hN q hq i hT hQ hi hb x hx' hx1
    refine ⟨y, ?_, z, ?_, w, ?_, heq⟩
    · rwa [b.property.2.2]
    · rw [dynamicCentralizer_eq_torusCentralizer_of_descendedAction
        (i ≫ q) hi.isSplitSubtorus.1 a ha e he ν hpos.ne']
      rwa [torusCentralizer_carrier_base]
    · rwa [b.property.2.2]

end Lift

end Langlands.GroupScheme.RelativeRoot

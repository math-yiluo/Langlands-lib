import Langlands.GroupScheme.Reductive.NormalUnipotentCentralizer
import Langlands.GroupScheme.Reductive.RootReducednessReduction
import Langlands.GroupScheme.Torus.ActionWeightDecomposition
import Langlands.GroupScheme.Lie.SelfCentralizing
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Detecting reductivity through actual proportional-root centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RankOneCentralizerDetection

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
  (α : characterLattice T) (hα : α ≠ 0)

local instance affine_ambient : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- A generic cocharacter annihilating the specified character and no
ambient roots independent from it. -/
def cocharacter : cocharacterLattice T :=
  RootReducedness.kernelCocharacter hT hα (hT.finite_relativeRoots i)

/-- The actual centralizer in which the roots proportional to the specified
character remain. This definition uses no reductivity hypothesis. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom (cocharacter i hT α hα) ≫ i)

/-- The actual closed centralizer inclusion. -/
def inclusion : groupScheme i hT α hα ⟶ G :=
  Dynamic.Affine.centralizerHom _

theorem isClosedSubgroup_inclusion : IsClosedSubgroup (inclusion i hT α hα) :=
  Dynamic.Affine.isClosedSubgroup_centralizerHom _

theorem isRepresentedBy_inclusion :
    (Dynamic.centralizer (CommGroupScheme.groupHom (cocharacter i hT α hα) ≫ i)).IsRepresentedBy
      (inclusion i hT α hα) :=
  Dynamic.Affine.isRepresentedBy_centralizerHom _

instance affine_groupScheme : IsAffineHom (groupScheme i hT α hα).X.hom :=
  (isClosedSubgroup_inclusion i hT α hα).isAffineHom

instance smooth_groupScheme : Smooth (groupScheme i hT α hα).X.hom :=
  (dynamicSmooth k G _ _ (inclusion i hT α hα)).2.1
    (isRepresentedBy_inclusion i hT α hα)

instance connected_groupScheme [ConnectedSpace G.X.left] :
    ConnectedSpace (groupScheme i hT α hα).X.left :=
  DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G _
    (isRepresentedBy_inclusion i hT α hα)

/-- The original torus factors canonically through this actual centralizer. -/
def torusHom : T.toGrp ⟶ groupScheme i hT α hα :=
  Dynamic.torusFactor i (CommGroupScheme.groupHom (cocharacter i hT α hα))
    (isRepresentedBy_inclusion i hT α hα)

@[reassoc (attr := simp)] theorem torusHom_comp :
    torusHom i hT α hα ≫ inclusion i hT α hα = i :=
  Dynamic.torusFactor_comp _ _ _

theorem isClosedSubgroup_torusHom (hi : IsClosedSubgroup i) :
    IsClosedSubgroup (torusHom i hT α hα) :=
  IsClosedSubgroup.of_comp (isClosedSubgroup_inclusion i hT α hα) (by
    rwa [torusHom_comp])

theorem pairing_cocharacter : latticePairing T α (cocharacter i hT α hα) = 0 :=
  RootReducedness.latticePairing_kernelCocharacter hT hα (hT.finite_relativeRoots i)

/-- All nonzero adjoint characters in the constructed actual centralizer
are pairwise linearly dependent over the integers. -/
theorem roots_pairwise_dependent :
    ∀ beta ∈ roots (torusHom i hT α hα), ∀ chi ∈ roots (torusHom i hT α hα),
      ¬ LinearIndependent ℤ ![beta, chi] := by
  intro beta hβ chi hγ
  obtain ⟨hβ', hβζ⟩ := RootReducedness.mem_roots_of_mem_roots_torusFactor i
    (cocharacter i hT α hα) (isRepresentedBy_inclusion i hT α hα) hβ
  obtain ⟨hγ', hγζ⟩ := RootReducedness.mem_roots_of_mem_roots_torusFactor i
    (cocharacter i hT α hα) (isRepresentedBy_inclusion i hT α hα) hγ
  apply RootReducedness.not_linearIndependent_of_not_linearIndependent hT hα hγ'.1
  · exact RootReducedness.not_linearIndependent_of_latticePairing_kernelCocharacter
      hT hα (hT.finite_relativeRoots i) hβ' hβζ
  · exact RootReducedness.not_linearIndependent_of_latticePairing_kernelCocharacter
      hT hα (hT.finite_relativeRoots i) hγ' hγζ

end RankOneCentralizerDetection

namespace Lie

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {T : CommGroupScheme (Spec R)} (i : T.toGrp ⟶ G) (j : H ⟶ G)
  [Mono j.hom.hom]
  (hn : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range i))

/-- The actual differential of normalized conjugation intertwines with the
ambient adjoint action through the specified inclusion. -/
theorem targetMapLinear_normalizedConjugation_differential
    {A : Type u} [CommRing A] [Algebra R A]
    (t : AffinePoints T.toGrp A) (X : Additive (lieKernel H A)) :
    targetMapLinear j A
        ((AutomorphicAction.ofNormalizedConjugation j i hn).differential t X) =
      adjoint G A (t ≫ i.hom.hom) (targetMapLinear j A X) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (CategoryTheory.CartesianMonoidalCategory.lift (constant T.toGrp t) X.toMul.val ≫
      SubgroupFunctor.normalizedConjugation j i hn) ≫ j.hom.hom = _
  rw [SubgroupFunctor.lift_comp_normalizedConjugation_comp]
  rfl

/-- A weight of the induced action on a normalized subgroup is an actual
ambient adjoint weight under the actual inclusion differential. -/
theorem normalizedConjugation_mem_weightSpace (α : characterLattice T)
    {X : Additive (lieKernel H R)}
    (hX : X ∈ (AutomorphicAction.ofNormalizedConjugation j i hn).lieWeightSpace
      (𝟙 T.toGrp) α) :
    targetMapLinear j R X ∈ weightSpace i α := by
  intro A _ _ t
  rw [← lieKernelHomLinear_map, ← targetMapLinear_normalizedConjugation_differential i j hn]
  simpa only [Grp.id_hom_hom, Category.comp_id, LinearMap.map_smul] using
    congrArg (targetMapLinear j A) (hX A t)

end Lie

namespace RankOneCentralizerDetection

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H Z : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  [Smooth H.X.hom] [ConnectedSpace H.X.left] [IsAffineHom H.X.hom]
  (j : H ⟶ G) (hj : IsClosedSubgroup j)
  (hn : (SubgroupFunctor.range j).IsNormal) (hu : IsUnipotent H)

include hj hn hu

omit [Smooth G.X.hom] in
/-- An infinitesimal point of a normal unipotent subgroup lying in a
cocharacter centralizer with trivial radical vanishes in the ambient group. -/
theorem normal_lie_zero_of_centralizer
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (z : Z ⟶ G)
    (hz : (Dynamic.centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)
    (hZ : HasTrivialUnipotentRadical Z) (X : Additive (lieKernel H k))
    (hX : X.toMul.val ≫ j.hom.hom ∈ (Dynamic.centralizer χ).carrier _) :
    Lie.targetMapLinear j k X = 0 := by
  rw [← hz.2] at hX
  obtain ⟨Y, hY⟩ := SubgroupFunctor.mem_range.mp hX
  let hpb := subgroupIntersection_isPullback j z
  have hm : Y ∈ (SubgroupFunctor.range (subgroupIntersectionSnd j z)).carrier _ :=
    ⟨hpb.lift X.toMul.val Y hY.symm, hpb.lift_snd _ _ _⟩
  rw [range_normalUnipotentCentralizer_eq_bot χ j z hj hz hzc hn hu hZ,
    SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hm
  apply Additive.toMul.injective
  apply Subtype.ext
  change X.toMul.val ≫ j.hom.hom = 1
  rw [← hY, hm, MonObj.one_comp]

/-- A weight annihilating a cocharacter vanishes in a normal unipotent
subgroup if the corresponding actual centralizer has trivial radical. -/
theorem normal_weight_zero_of_centralizer [IsAffineHom Z.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (ζ : cocharacterLattice T) (z : Z ⟶ G)
    (hz : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy z)
    (hzc : IsClosedSubgroup z) (hZ : HasTrivialUnipotentRadical Z)
    (α : characterLattice T) (hαζ : latticePairing T α ζ = 0)
    (X : Additive (lieKernel H k)) (hX : Lie.targetMapLinear j k X ∈ weightSpace i α) :
    Lie.targetMapLinear j k X = 0 := by
  apply normal_lie_zero_of_centralizer j hj hn hu
    (CommGroupScheme.groupHom ζ ≫ i) z hz hzc hZ X
  obtain ⟨Y, hY⟩ := RootReducedness.weightSpace_le_range_centralizer i ζ hz hαζ hX
  rw [← hz.2]
  exact ⟨Y.toMul.val, congrArg (fun W : Additive (lieKernel G k) => W.toMul.val) hY⟩

end RankOneCentralizerDetection

namespace RankOneCentralizerDetection

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
  (hself : torusCentralizer i = SubgroupFunctor.range i)

include hi hself

/-- It suffices to kill the radicals of the actual generic centralizers
attached to the finitely many ambient roots. -/
theorem hasTrivialUnipotentRadical
    (hsmall : ∀ (α : characterLattice T) (hα : α ∈ roots i),
      HasTrivialUnipotentRadical (groupScheme i hT α hα.1)) :
    HasTrivialUnipotentRadical G := by
  classical
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  intro H j hj hs hc hu hn
  let := hs
  let := hc
  let : IsAffineHom H.X.hom := hj.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hnT : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range i) :=
    fun V g x _ hx => hn V g x (Subgroup.mem_top _) hx
  let a := AutomorphicAction.ofNormalizedConjugation j i hnT
  have hweight (α : characterLattice T) (X : Additive (lieKernel H k))
      (hX : X ∈ a.lieWeightSpace (𝟙 T.toGrp) α) : X = 0 := by
    apply Lie.targetMapLinear_injective j k
    rw [map_zero]
    have hY := Lie.normalizedConjugation_mem_weightSpace i j hnT α hX
    by_cases hα : α = 0
    · subst α
      let ζ := centralizingCocharacter hT i
      have hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy i := by
        rw [centralizingCocharacter_spec hT i, hself]
        exact ⟨inferInstance, rfl⟩
      exact normal_weight_zero_of_centralizer j hj hn hu i ζ i hrep hi
        hT.hasTrivialUnipotentRadical 0 (by simp) X hY
    · by_cases hzero : Lie.targetMapLinear j k X = 0
      · exact hzero
      · have hroot : α ∈ roots i := ⟨hα, fun hb =>
          hzero (by simpa only [hb, Submodule.mem_bot] using hY)⟩
        exact normal_weight_zero_of_centralizer j hj hn hu i (cocharacter i hT α hα)
          (inclusion i hT α hα) (isRepresentedBy_inclusion i hT α hα)
          (isClosedSubgroup_inclusion i hT α hα) (hsmall α hroot)
          α (pairing_cocharacter i hT α hα) X hY
  have hbot (α : characterLattice T) : a.lieWeightSpace (𝟙 T.toGrp) α = ⊥ :=
    eq_bot_iff.mpr (fun X hX => hweight α X hX)
  have hdec := AutomorphicAction.isInternal_lieWeightSpace_of_isSplitTorus
    k H T hT a (𝟙 T.toGrp)
  have htop : (⊤ : Submodule k (Additive (lieKernel H k))) = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [← hdec.submodule_iSup_eq_top]
    exact iSup_le (fun α => (hbot α).le)
  let : Subsingleton (Additive (lieKernel H k)) := by
    have hz (X : Additive (lieKernel H k)) : X = 0 := by
      have hx : X ∈ (⊤ : Submodule k (Additive (lieKernel H k))) := trivial
      rwa [htop, Submodule.mem_bot] at hx
    exact ⟨fun X Y => (hz X).trans (hz Y).symm⟩
  have hunit : IsClosedSubgroup (kernelUnit H) := kernelUnit_isClosedSubgroup H
  let : Smooth (Grp.trivial (Over (Spec (CommRingCat.of k)))).X.hom := by
    change Smooth (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  let : IsAffineHom (Grp.trivial (Over (Spec (CommRingCat.of k)))).X.hom := by
    change IsAffineHom (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  have : IsIso (kernelUnit H) :=
    Lie.isIso_of_surjective_targetMapLinear (kernelUnit H) hunit
      (fun X => ⟨0, Subsingleton.elim _ _⟩)
  have hcomp : kernelUnit H ≫ j = kernelUnit G := by
    apply (Grp.forget _).map_injective
    exact IsMonHom.one_hom j.hom.hom
  rw [← SubgroupFunctor.range_iso_comp (asIso (kernelUnit H)) j]
  change SubgroupFunctor.range (kernelUnit H ≫ j) = ⊥
  rw [hcomp, range_kernelUnit]

/-- Over an algebraically closed field, reductivity of these actual
proportional-root centralizers detects connected reductivity. -/
theorem isConnectedReductive [ConnectedSpace G.X.left]
    (hsmall : ∀ (α : characterLattice T) (hα : α ∈ roots i),
      IsConnectedReductive (groupScheme i hT α hα.1)) :
    IsConnectedReductive G := by
  have hG : IsPseudoReductive G :=
    ⟨inferInstance, inferInstance, inferInstance,
      hasTrivialUnipotentRadical i hT hi hself (fun α hα =>
        (hsmall α hα).hasTrivialUnipotentRadical)⟩
  exact hG.isConnectedReductive_of_isAlgClosed

end RankOneCentralizerDetection

end Langlands.GroupScheme

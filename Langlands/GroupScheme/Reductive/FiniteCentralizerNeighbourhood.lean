import Langlands.GroupScheme.Reductive.RankOneCentralizerDetection
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Torus.RelativeCocharacterCentralizers
import Langlands.GroupScheme.Reductive.IdentityComponentLocusOpenDescent

/-! # Finite actual cocharacter centralizers and reductive neighbourhoods -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- An actual centralizer of a cocharacter annihilating a specified character,
with its all-test representing inclusion and trivial unipotent radical. -/
structure RadicalFreeRootCentralizerData
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (α : characterLattice T) where
  cocharacter : cocharacterLattice T
  groupScheme : GroupScheme (Spec (CommRingCat.of k))
  inclusion : groupScheme ⟶ G
  represents : (Dynamic.centralizer (CommGroupScheme.groupHom cocharacter ≫ i)).IsRepresentedBy
    inclusion
  annihilates : latticePairing T α cocharacter = 0
  radical : HasTrivialUnipotentRadical groupScheme

namespace RadicalFreeRootCentralizerData

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
  (hself : torusCentralizer i = SubgroupFunctor.range i)

include hT hi hself

local instance affine_ambient : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Any actual rootwise annihilating centralizers with trivial radicals detect
the ambient radical. The cocharacters need not be canonical choices. -/
theorem hasTrivialUnipotentRadical
    (hsmall : ∀ (α : characterLattice T) (_ : α ∈ roots i),
      Nonempty (RadicalFreeRootCentralizerData i α)) :
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
      exact RankOneCentralizerDetection.normal_weight_zero_of_centralizer j hj hn hu i ζ i hrep hi
        hT.hasTrivialUnipotentRadical 0 (by simp) X hY
    · by_cases hzero : Lie.targetMapLinear j k X = 0
      · exact hzero
      · have hroot : α ∈ roots i := ⟨hα, fun hb =>
          hzero (by simpa only [hb, Submodule.mem_bot] using hY)⟩
        let d := Classical.choice (hsmall α hroot)
        have hdc := Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer
          (CommGroupScheme.groupHom d.cocharacter ≫ i) d.represents
        let : IsAffineHom d.groupScheme.X.hom := hdc.isAffineHom
        exact RankOneCentralizerDetection.normal_weight_zero_of_centralizer
          j hj hn hu i d.cocharacter d.inclusion d.represents hdc d.radical
          α d.annihilates X hY
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

/-- The same rootwise data detect connected reductivity over an algebraically
closed field. -/
theorem isConnectedReductive [ConnectedSpace G.X.left]
    (hsmall : ∀ (α : characterLattice T) (_ : α ∈ roots i),
      Nonempty (RadicalFreeRootCentralizerData i α)) :
    IsConnectedReductive G := by
  have hG : IsPseudoReductive G :=
    ⟨inferInstance, inferInstance, inferInstance,
      hasTrivialUnipotentRadical i hT hi hself hsmall⟩
  exact hG.isConnectedReductive_of_isAlgClosed

end RadicalFreeRootCentralizerData

namespace splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance finiteCentralizer_smooth_geometricFiber (t : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G t).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ t)))

local instance finiteCentralizer_affine_geometricFiber (t : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G t).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ t)))

omit [DecidableEq I] in
/-- The actual geometric roots have a finite integral-coordinate enumeration,
without any reductivity premise. -/
theorem finite_geometricExponentRoots (s : Spec (CommRingCat.of r)) :
    (geometricExponentRoots I G i s).Finite := by
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)
  have hf := (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I).finite_relativeRoots
    (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
  have he : geometricExponentRoots I G i s =
      (characterLatticeEquiv k I).symm ⁻¹'
        roots (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s) := by
    ext m
    simp only [geometricExponentRoots, Set.mem_ofPred_eq, Set.mem_preimage,
      exponentCharacter_eq_characterLatticeEquiv_symm]
    rfl
  rw [he]
  exact hf.preimage (characterLatticeEquiv k I).symm.injective.injOn

/-- A finite list of exactly the actual integral-coordinate geometric roots. -/
def geometricExponentRootFinset (s : Spec (CommRingCat.of r)) : Finset (I → ℤ) :=
  (finite_geometricExponentRoots I G i s).toFinset

omit [DecidableEq I] in
@[simp] theorem mem_geometricExponentRootFinset
    (s : Spec (CommRingCat.of r)) (m : I → ℤ) :
    m ∈ geometricExponentRootFinset I G i s ↔ m ∈ geometricExponentRoots I G i s :=
  Set.Finite.mem_toFinset _

/-- An actual reductive geometric centralizer fibre gives the root-centralizer
witness in the original geometric identity component. -/
def geometricRadicalFreeRootCentralizerData (s : Spec (CommRingCat.of r))
    (m n : I → ℤ) (hmn : ∑ j, m j * n j = 0)
    (hred : s ∈ identityComponentReductiveLocus
      (RelativeCocharacterCentralizer.groupScheme I G i n)) :
    RadicalFreeRootCentralizerData (T := commGroupScheme _ I)
      (geometricIdentityComponentHom I G i s) (exponentCharacter _ I m) where
  cocharacter := exponentCocharacter _ I n
  groupScheme := identityComponent
    (geometricFiber (RelativeCocharacterCentralizer.groupScheme I G i n) s)
  inclusion := RelativeCocharacterCentralizer.geometricIdentityInclusion I G i n s
  represents := RelativeCocharacterCentralizer.isRepresentedBy_geometricIdentityInclusion
    I G i n s
  annihilates := by
    simpa only [latticePairing_exponentCharacter_exponentCocharacter] using hmn
  radical := hred.hasTrivialUnipotentRadical

/-- Intersect finitely many actual centralizer good neighbourhoods to obtain
an actual good neighbourhood for the ambient family. The finite index set is
exactly the original fibre's actual roots. -/
def identityComponentReductiveNeighbourhood_of_rootCentralizers
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i)
    (n : geometricExponentRootFinset I G i s → (I → ℤ))
    (hn : ∀ a, ∑ j, a.val j * n a j = 0)
    (d : ∀ a, IdentityComponentReductiveOpenNeighbourhood
      (RelativeCocharacterCentralizer.groupScheme I G i (n a)) s) :
    IdentityComponentReductiveOpenNeighbourhood G s := by
  classical
  let U := Classical.choose (exists_open_geometricRootProfiles_eq I G i s)
  have hU : IsOpen U := (Classical.choose_spec
    (exists_open_geometricRootProfiles_eq I G i s)).1
  have hsU : s ∈ U := (Classical.choose_spec
    (exists_open_geometricRootProfiles_eq I G i s)).2.1
  have hconst := (Classical.choose_spec
    (exists_open_geometricRootProfiles_eq I G i s)).2.2
  let W : Set (Spec (CommRingCat.of r)) :=
    ⋂ a, ((d a).neighbourhood : Set (Spec (CommRingCat.of r)))
  have hW : IsOpen W := isOpen_iInter_of_finite (fun a => (d a).neighbourhood.isOpen)
  refine
    { neighbourhood := ⟨U ∩ (geometricSelfCentralizingTorusLocus I G i ∩ W),
        hU.inter ((isOpen_geometricSelfCentralizingTorusLocus I G i hi).inter hW)⟩
      mem_neighbourhood := ⟨hsU, hself,
        Set.mem_iInter.mpr (fun a => (d a).mem_neighbourhood)⟩
      subset_locus := ?_ }
  intro t ht
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField t)
  apply RadicalFreeRootCentralizerData.isConnectedReductive
    (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i t)
    (isSplitTorus_splitTorus I)
    (isClosedSubgroup_geometricIdentityComponentHom I G i hi t) ht.2.1
  intro α hα
  obtain ⟨m, hm⟩ := (characterLatticeEquiv k I).symm.surjective α
  have hchar : exponentCharacter (Spec (CommRingCat.of k)) I m = α :=
    (exponentCharacter_eq_characterLatticeEquiv_symm I k m).trans hm
  have hmt : m ∈ geometricExponentRoots I G i t := by
    change exponentCharacter _ I m ∈ roots
      (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i t)
    rwa [hchar]
  have hms : m ∈ geometricExponentRootFinset I G i s := by
    rw [mem_geometricExponentRootFinset, ← (hconst t ht.1).1]
    exact hmt
  let a : geometricExponentRootFinset I G i s := ⟨m, hms⟩
  have hred : t ∈ identityComponentReductiveLocus
      (RelativeCocharacterCentralizer.groupScheme I G i (n a)) :=
    (d a).subset_locus (Set.mem_iInter.mp ht.2.2 a)
  rw [← hchar]
  exact ⟨geometricRadicalFreeRootCentralizerData I G i t m (n a) (hn a) hred⟩

end splitTorus

end Langlands.GroupScheme

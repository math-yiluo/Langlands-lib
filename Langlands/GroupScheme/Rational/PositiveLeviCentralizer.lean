import Langlands.GroupScheme.Rational.PositiveSourceContraction
import Langlands.GroupScheme.Rational.RadicalContractionParabolicContainment

/-! # The original Levi centralizer from positive source weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section CentralImage

variable {S : Scheme.{u}} {L G : GroupScheme S} {A : CommGroupScheme S}
    (a : A.toGrp ⟶ L) (ha : IsCentral a) (j : L ⟶ G)

include ha

/-- The image of a group centralizes the ambient image of any central
commutative subgroup of that group, on every test scheme. -/
theorem IsCentral.range_le_torusCentralizer_comp :
    SubgroupFunctor.range j ≤ torusCentralizer (a ≫ j) := by
  intro V x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  intro W q z
  have hc := (commute_of_mem_center (ha W z) (q ≫ y)).symm
  have he := congrArg (fun w : W ⟶ L.X => w ≫ j.hom.hom) hc.eq
  apply (commute_iff_eq _ _).mpr
  simpa only [Grp.comp_hom_hom, MonObj.mul_comp, Category.assoc] using he

end CentralImage

section PositiveLevi

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G P L U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom U.X.hom]
    (l : L ⟶ P) (r : U ⟶ P) (j : P ⟶ G)
    [IsIso (subgroupMultiplication l r)]
    (hj : IsClosedSubgroup j)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    {A T : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : A.toGrp ⟶ L) (ha : IsCentral a)
    (nuA : cocharacterLattice A)
    (t : T.toGrp ⟶ L) (nuT : cocharacterLattice T)
    (hnu : CommGroupScheme.groupHom nuT ≫ t =
      CommGroupScheme.groupHom nuA ≫ a)
    (d : AutomorphicAction T.toGrp U)
    (hi : d.IsEquivariant
      (AutomorphicAction.conjugation (t ≫ l ≫ j)) (r ≫ j))

local notation "b" => algebraBaseMap k K
local notation "T_K" => Functor.obj (CommGroupScheme.baseChange b) T
local notation "omega" => toAlgebraicClosure k
local notation "B" => GroupScheme.baseChange omega
local notation "chi" => CommGroupScheme.groupHom nuA ≫ a ≫ l ≫ j

local instance positiveLeviCentralizerExtensionIsAffineHomU : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj U).X.hom := by
  change IsAffineHom (Limits.pullback.snd U.X.hom (algebraBaseMap k K))
  infer_instance

local instance positiveLeviCentralizerClosureIsAffineHomG :
    IsAffineHom (Functor.obj B G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom omega)
  infer_instance

local instance positiveLeviCentralizerClosureSmoothG : Smooth (Functor.obj B G).X.hom := by
  change Smooth (Limits.pullback.snd G.X.hom omega)
  infer_instance

local instance positiveLeviCentralizerClosureConnectedSpaceG :
    ConnectedSpace (Functor.obj B G).X.left :=
  G.connectedSpace_baseChange_of_smooth_affine omega

variable (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (hpos : ∀ alpha : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T),
      RelativeRoot.actionWeightSpace
        (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        (d.baseChange (algebraBaseMap k K)) alpha ≠ ⊥ →
        0 < latticePairing
          ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) alpha
          (cocharacterLattice.baseChange (algebraBaseMap k K) T nuT))

include hr hnu hi hT hpos

omit [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsIso (subgroupMultiplication l r)] in
/-- Positive intrinsic weights after a splitting extension contract the
original supplied radical under the compatible central cocharacter. -/
theorem range_radical_le_unipotent_of_positive_source :
    SubgroupFunctor.range (r ≫ j) ≤ Dynamic.unipotent chi := by
  let : Smooth U.X.hom := hr.1.smooth
  let : ConnectedSpace U.X.left := hr.1.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have h := d.range_le_unipotent_of_source_weights_baseChange
    k K (t ≫ l ≫ j) (r ≫ j) hi hT nuT hpos
  simpa only [← Category.assoc, hnu] using h

variable
    {C : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    (c : C.toGrp ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G)
    (hC : IsSplitTorus C.toGrp) (eta mu : cocharacterLattice C)
    (hneg : ∀ alpha ∈ relativeRoots c, -alpha ∈ relativeRoots c)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ c)).IsRepresentedBy
      ((GroupScheme.baseChange (toAlgebraicClosure k)).map j))
    (hmu : CommGroupScheme.groupHom mu ≫ c =
      Dynamic.baseChangeCocharacter (toAlgebraicClosure k)
        (CommGroupScheme.groupHom nuA ≫ a ≫ l ≫ j))

include hj ha c hC eta mu hneg hP hmu

/-- A common-torus calculation only over the algebraic closure suffices
to identify the original parabolic and Levi centralizers over the ground field. -/
theorem parabolic_and_centralizers_eq_of_positive_source :
    Dynamic.parabolic chi = SubgroupFunctor.range j ∧
      Dynamic.centralizer chi = SubgroupFunctor.range (l ≫ j) ∧
      torusCentralizer (a ≫ l ≫ j) = SubgroupFunctor.range (l ≫ j) := by
  have hU := range_radical_le_unipotent_of_positive_source
    k K l r j hr a nuA t nuT hnu d hi hT hpos
  have hUomega := SubgroupFunctor.baseChange_mono omega hU
  rw [← SubgroupFunctor.range_baseChangeHom, ← Dynamic.unipotent_baseChange,
    ← hmu, Functor.map_comp] at hUomega
  have hpar := Dynamic.parabolic_le_range_of_radical_contraction
    hC c eta mu hneg (CategoryTheory.Functor.map B j) hP (CategoryTheory.Functor.map B r) hr.2 hUomega
  rw [hmu, Dynamic.parabolic_baseChange, SubgroupFunctor.range_baseChangeHom] at hpar
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hb : Flat omega ∧ Surjective omega :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))).mpr
        (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat omega := hb.1
  let : Surjective omega := hb.2
  have hpar0 : Dynamic.parabolic chi ≤ SubgroupFunctor.range j :=
    SubgroupFunctor.le_range_of_baseChange_le omega j hpar
  have hL := IsCentral.range_le_torusCentralizer_comp a ha (l ≫ j)
  have hfixed : SubgroupFunctor.range (l ≫ j) ≤ Dynamic.centralizer chi :=
    hL.trans (torusCentralizer_le_dynamicCentralizer
      (a ≫ l ≫ j) (CommGroupScheme.groupHom nuA))
  have hZ := (Dynamic.centralizer_le_parabolic chi).trans hpar0
  refine ⟨le_antisymm hpar0
    (Dynamic.range_le_parabolic_of_subgroupMultiplication l r j chi hfixed hU),
    Dynamic.centralizer_eq_of_subgroupMultiplication l r j chi hfixed hU hZ, ?_⟩
  exact torusCentralizer_eq_of_subgroupMultiplication
    l r j (a ≫ l ≫ j) (CommGroupScheme.groupHom nuA) hL hU
      ((torusCentralizer_le_dynamicCentralizer
        (a ≫ l ≫ j) (CommGroupScheme.groupHom nuA)).trans hZ)

variable (hl : IsClosedSubgroup l)
    {M : GroupScheme (Spec (CommRingCat.of k))} {m : M ⟶ G}
    (hm : (torusCentralizer (a ≫ l ≫ j)).IsRepresentedBy m)

include ha hl hm

/-- The original first multiplication factor is isomorphic to any supplied
whole-torus centralizer representative, retaining its exact ambient inclusion. -/
def positiveSourceLeviCentralizerIso : L ≅ M := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsClosedImmersion l.hom.hom.left := hl
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Mono (l ≫ j).hom.hom := by
    change Mono (l.hom.hom ≫ j.hom.hom)
    infer_instance
  have heq := (parabolic_and_centralizers_eq_of_positive_source
    k K l r j hj hr a ha nuA t nuT hnu d hi hT hpos c hC eta mu hneg hP hmu).2.2
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (show (torusCentralizer (a ≫ l ≫ j)).IsRepresentedBy (l ≫ j) from
      ⟨inferInstance, heq.symm⟩) hm

@[simp]
theorem positiveSourceLeviCentralizerIso_hom_comp :
    (positiveSourceLeviCentralizerIso k K l r j hj hr a ha nuA t nuT hnu
      d hi hT hpos c hC eta mu hneg hP hmu hl hm).hom ≫ m = l ≫ j := by
  unfold positiveSourceLeviCentralizerIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

@[simp]
theorem positiveSourceLeviCentralizerIso_inv_comp :
    (positiveSourceLeviCentralizerIso k K l r j hj hr a ha nuA t nuT hnu
      d hi hT hpos c hC eta mu hneg hP hmu hl hm).inv ≫ l ≫ j = m := by
  have h := congrArg (fun f : L ⟶ G =>
    (positiveSourceLeviCentralizerIso k K l r j hj hr a ha nuA t nuT hnu
      d hi hT hpos c hC eta mu hneg hP hmu hl hm).inv ≫ f)
    (positiveSourceLeviCentralizerIso_hom_comp
      k K l r j hj hr a ha nuA t nuT hnu d hi hT hpos c hC eta mu hneg hP hmu hl hm)
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm

end PositiveLevi

end Langlands.GroupScheme

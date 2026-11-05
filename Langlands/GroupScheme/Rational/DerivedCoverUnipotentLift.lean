import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.Derived.DynamicRootContainment
import Langlands.GroupScheme.Derived.SplitTorusCommutators
import Langlands.GroupScheme.Dynamic.CentralIsogenyRationalLift
import Langlands.GroupScheme.Dynamic.CentralShifts
import Langlands.GroupScheme.Dynamic.PositivePowers
import Langlands.GroupScheme.Rational.NormKernelCocharacter
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Contracting rational points lift through a simply connected derived cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G D C : GroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {π : C ⟶ D}

namespace Dynamic

/-- A point contracting under a cocharacter of the actual derived group lifts
through the supplied simply connected cover of that derived group. -/
theorem exists_derivedCover_lift_of_mem_unipotent
    (hcover : IsSimplyConnectedDerivedCover d π)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D)
    (g : rationalPoints G)
    (hg : g ∈ (unipotent (χ ≫ d)).carrier (Over.mk (𝟙 _))) :
    ∃ c : rationalPoints C, rationalPoints.map (π ≫ d) c = g := by
  have hgder := unipotent_le_derivedSubgroup (χ ≫ d) _ hg
  let hd := hcover.isDerivedSubgroup
  let gD : rationalPoints D :=
    (hd.isRepresentedBy.pointsEquiv _).symm ⟨g, hgder⟩
  have hgD : gD ≫ d.hom.hom = g :=
    hd.isRepresentedBy.pointsEquiv_symm_comp _
  have hgcontract : gD ∈ (unipotent χ).carrier (Over.mk (𝟙 _)) := by
    rw [unipotent_eq_comap_of_isClosedSubgroup χ d hd.1]
    change gD ≫ d.hom.hom ∈ (unipotent (χ ≫ d)).carrier _
    rwa [hgD]
  let : IsAffineHom C.X.hom :=
    hcover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let : IsAffineHom D.X.hom :=
    hcover.isSimplyConnectedCover.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  obtain ⟨c, hc⟩ := exists_lift_of_mem_unipotent π
    hcover.isSimplyConnectedCover.isCentralIsogeny χ gD hgcontract
  refine ⟨c, ?_⟩
  change c ≫ (π ≫ d).hom.hom = g
  rw [Grp.comp_hom_hom, ← Category.assoc, hc, hgD]

end Dynamic

section Correction

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  [Fintype (relativeWeylGroup i)]

/-- The integral Weyl correction lands in the actual derived subgroup on every
test scheme: it is a sum of differences between cocharacters and their conjugates. -/
theorem normKernelCocharacter_mem_cocharactersLandingIn_derived
    (ν : cocharacterLattice T) :
    normKernelCocharacter i ν ∈ cocharactersLandingIn i (derivedSubgroup G) := by
  classical
  have heq : normKernelCocharacter i ν =
      ∑ w : relativeWeylGroup i, (ν - relativeWeylCocharacterAction i w ν) := by
    rw [normKernelCocharacter, relativeWeylCocharacterSum_apply, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ]
  rw [heq]
  apply (cocharactersLandingIn i (derivedSubgroup G)).sum_mem
  intro w _
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  have hn := (cocharactersLandingIn i (derivedSubgroup G)).neg_mem
    (cocharacter_torusCommutatorEnd_mem i (derivedSubgroup_containsCommutators G) n ν)
  simpa only [torusCommutatorEnd, Preadditive.comp_sub, Category.comp_id,
    neg_sub, relativeWeylCocharacterAction_mk, cocharacterAut_apply] using hn

namespace Dynamic

variable [IsAffine G.X.left]

/-- If the Weyl sum is central, the integral Weyl correction preserves the
entire contracting subgroup on every test scheme. -/
theorem unipotent_normKernelCocharacter
    (ν : cocharacterLattice T)
    (hcentral : relativeWeylCocharacterSum i ν ∈ centralCocharacters i) :
    unipotent (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i) =
      unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  have hneg : IsCentral
      (CommGroupScheme.groupHom (-relativeWeylCocharacterSum i ν) ≫ i) :=
    (mem_centralCocharacters i _).mp ((centralCocharacters i).neg_mem hcentral)
  rw [normKernelCocharacter, sub_eq_add_neg,
    unipotent_add_of_isCentral i _ _ hneg]
  simpa only [natCast_zsmul] using
    unipotent_zsmul T i ν
      (n := (Fintype.card (relativeWeylGroup i) : ℤ))
      (by exact_mod_cast Fintype.card_pos (α := relativeWeylGroup i))

end Dynamic

/-- Factor the integral Weyl correction through the supplied actual derived
subgroup, retaining its literal ambient composite. -/
def derivedNormKernelCocharacter (hd : IsDerivedSubgroup d)
    (ν : cocharacterLattice T) : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D :=
  hd.isRepresentedBy.factorHom
    (CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i) (by
      rintro U _ ⟨z, rfl⟩
      exact normKernelCocharacter_mem_cocharactersLandingIn_derived i ν U z)

@[reassoc]
theorem derivedNormKernelCocharacter_comp (hd : IsDerivedSubgroup d)
    (ν : cocharacterLattice T) :
    derivedNormKernelCocharacter i hd ν ≫ d =
      CommGroupScheme.groupHom (normKernelCocharacter i ν) ≫ i :=
  hd.isRepresentedBy.factorHom_comp _ _

namespace Dynamic

/-- Centrality of the integral Weyl sum suffices to lift every ambient
contracting rational point through the simply connected derived cover. -/
theorem exists_derivedCover_lift_of_mem_unipotent_of_central_weylSum
    (hcover : IsSimplyConnectedDerivedCover d π)
    (ν : cocharacterLattice T)
    (hcentral : relativeWeylCocharacterSum i ν ∈ centralCocharacters i)
    (g : rationalPoints G)
    (hg : g ∈ (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    ∃ c : rationalPoints C, rationalPoints.map (π ≫ d) c = g := by
  let : IsAffineHom G.X.hom := hcover.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply exists_derivedCover_lift_of_mem_unipotent hcover
    (derivedNormKernelCocharacter i hcover.isDerivedSubgroup ν) g
  rwa [derivedNormKernelCocharacter_comp, unipotent_normKernelCocharacter i ν hcentral]

end Dynamic

end Correction

namespace Dynamic

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- The actual relative-root-system realization implies rational lifting of the
whole contracting subgroup through the simply connected derived cover. -/
theorem exists_derivedCover_lift_of_mem_unipotent_of_relativeRootSystem
    (hcover : IsSimplyConnectedDerivedCover d π)
    (hT : IsSplitTorus T.toGrp) (hroot : HasRelativeRootSystem i)
    (ν : cocharacterLattice T)
    (g : rationalPoints G)
    (hg : g ∈ (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    ∃ c : rationalPoints C, rationalPoints.map (π ≫ d) c = g := by
  let := relativeWeylGroupFintype i hroot
  let : Smooth G.X.hom := hcover.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := hcover.isConnectedReductive.connectedSpace
  exact exists_derivedCover_lift_of_mem_unipotent_of_central_weylSum i hcover ν
    (relativeWeylCocharacterSum_mem_centralCocharacters i hT
      (fun _ hα => hroot.exists_isRelativeReflection hα) ν) g hg

/-- Under the actual root-system realization, the entire contracting rational
subgroup lies in the actual simply connected image. -/
theorem unipotentPoints_le_derivedCoverImage_of_relativeRootSystem
    (hcover : IsSimplyConnectedDerivedCover d π)
    (hT : IsSplitTorus T.toGrp) (hroot : HasRelativeRootSystem i)
    (ν : cocharacterLattice T) :
    (unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) ≤
      (rationalPoints.map (π ≫ d)).range := by
  intro g hg
  exact exists_derivedCover_lift_of_mem_unipotent_of_relativeRootSystem
    i hcover hT hroot ν g hg

end Dynamic

end Langlands.GroupScheme

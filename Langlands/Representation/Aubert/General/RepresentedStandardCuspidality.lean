import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.Representation.Aubert.General.SupportCategory
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Rational.RootParabolicProper
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.GeometricUnipotentRadicalComparison
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof
import Langlands.GroupScheme.Rational.LeviMultiplication

/-! # From represented-parabolic vanishing to standard cuspidality -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open GroupScheme

namespace RationalPointFamily

section Properness

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

/-- Every proper finite standard face defines a proper all-test subgroup.
The witness lies over dual numbers; no nonidentity rational root point is needed. -/
theorem standardParabolic_ne_top_of_ne_univ [Smooth G.X.hom]
    [Fintype (SimpleRoot i ν)]
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {I : Finset (SimpleRoot i ν)} (hI : I ≠ Finset.univ) :
    standardParabolic i ν (rootSet i ν I) ≠ ⊤ := by
  classical
  have hmissing : ¬ ∀ α, α ∈ I := fun h => hI (Finset.eq_univ_of_forall h)
  obtain ⟨α, hα⟩ := not_forall.mp hmissing
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  have hpos : 0 < latticePairing T α.val ζ :=
    hζ.2.2 α.val α.property ((val_mem_rootSet i ν I α).not.mpr hα)
  have hnegroot : -α.val ∈ relativeRoots i :=
    hRoots.neg_mem_relativeRoots i hT α.property.1.1
  have hproper := RelativeRoot.negativeParabolic_ne_top i hT hnegroot (-ζ)
    (by simpa using hpos)
  simpa only [neg_neg, ← (hcompare ζ hζ).1] using hproper

end Properness

end RationalPointFamily

namespace RepresentedParabolic

open RationalPointFamily

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

omit [Mono i.hom.hom.left] in
/-- Geometric recognition of the choice-free standard representatives.
The standard-cocharacter statement remains explicit; dynamic parabolicity is proved. -/
theorem standard_representatives_geometric_of_standardCocharacter
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    IsParabolicSubgroup (Standard.parabolicHom i ν (rootSet i ν I)) ∧
      IsRationalLeviSubgroup (Standard.leviToParabolic i ν (rootSet i ν I)) ∧
      LeviSubgroup.IsGeometricUnipotentRadical
        (Standard.unipotentToParabolic i ν (rootSet i ν I)) ∧
      IsIso (subgroupMultiplication
        (Standard.leviToParabolic i ν (rootSet i ν I))
        (Standard.unipotentToParabolic i ν (rootSet i ν I))) := by
  have := hG.smooth
  have := hG.isSeparated
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨hP, hM, hU⟩ := hcompare ζ hζ
  let χ := CommGroupScheme.groupHom ζ ≫ i
  have hp : (Dynamic.parabolic χ).IsRepresentedBy
      (Standard.parabolicHom i ν (rootSet i ν I)) := by
    rw [← hP]
    exact Standard.isRepresentedBy_parabolicHom i ν _
  have hm : (Dynamic.centralizer χ).IsRepresentedBy
      (Standard.leviHom i ν (rootSet i ν I)) := by
    rw [← hM]
    exact Standard.isRepresentedBy_leviHom i ν _
  have hu : (Dynamic.unipotent χ).IsRepresentedBy
      (Standard.unipotentToParabolic i ν (rootSet i ν I) ≫
        Standard.parabolicHom i ν (rootSet i ν I)) := by
    rw [Standard.unipotentToParabolic_comp, ← hU]
    exact Standard.isRepresentedBy_unipotentHom i ν _
  have hpc := Standard.isClosedSubgroup_parabolicHom i ν (rootSet i ν I)
  have hmc := Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
  have hMred := dynamicCentralizerReductive k G hG χ _ _ hmc hm
  let : IsAffineHom (Standard.parabolicScheme i ν (rootSet i ν I)).X.hom :=
    hpc.isAffineHom
  have hRad := Dynamic.isGeometricUnipotentRadical_of_centralizer χ
    (Standard.leviHom i ν (rootSet i ν I))
    (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I)) hp hu hm hMred
  have hRad' := hRad.leviSubgroup_of_unipotentFieldExtension
    unipotentFieldExtensionStatement
  have hMult := Dynamic.isIso_subgroupMultiplication hp hm
    (show (Dynamic.unipotent χ).IsRepresentedBy
      (Standard.unipotentHom i ν (rootSet i ν I)) by
        rw [← hU]; exact Standard.isRepresentedBy_unipotentHom i ν _)
    (Standard.leviToParabolic i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I))
    (Standard.leviToParabolic_comp i ν _) (Standard.unipotentToParabolic_comp i ν _)
  refine ⟨isParabolicSubgroup_of_range_eq_dynamicParabolic hG _ hpc χ hp.2,
    ?_, hRad', hMult⟩
  exact ⟨hpc.isAffineHom, IsClosedSubgroup.of_comp hpc (by
    rw [Standard.leviToParabolic_comp]
    exact hmc), hMred, ⟨_, _, hRad', hMult⟩⟩

omit [Mono i.hom.hom.left] in
/-- Compatibility form of standard geometric recognition with its former
parabolic-dynamic argument. Only the standard-cocharacter premise is used. -/
theorem standard_representatives_geometric
    (hPD : ParabolicDynamicStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    IsParabolicSubgroup (Standard.parabolicHom i ν (rootSet i ν I)) ∧
      IsRationalLeviSubgroup (Standard.leviToParabolic i ν (rootSet i ν I)) ∧
      LeviSubgroup.IsGeometricUnipotentRadical
        (Standard.unipotentToParabolic i ν (rootSet i ν I)) ∧
      IsIso (subgroupMultiplication
        (Standard.leviToParabolic i ν (rootSet i ν I))
        (Standard.unipotentToParabolic i ν (rootSet i ν I))) := by
  have _ := hPD
  exact standard_representatives_geometric_of_standardCocharacter i ν hStandard hG hi hν I

omit [Mono i.hom.hom.left] in
/-- The point image of the represented standard radical is the exact
standard point subgroup. -/
theorem standard_unipotent_pointImage (I : Finset (SimpleRoot i ν)) :
    pointImage (Standard.unipotentToParabolic i ν (rootSet i ν I) ≫
      Standard.parabolicHom i ν (rootSet i ν I)) = unipotent i ν I := by
  rw [Standard.unipotentToParabolic_comp]
  exact congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _)))
    (Standard.isRepresentedBy_unipotentHom i ν (rootSet i ν I)).2

section Topology

variable [TopologicalSpace k] [T2Space k]

local instance : TopologicalSpace (rationalPoints G) := pointTopology

omit [Mono i.hom.hom.left] [T2Space k] in
/-- The canonical linear equivalence from the represented standard radical's
coinvariants to the exact standard point-subgroup coinvariants. -/
def standardUnipotentCoinvariantsEquiv (I : Finset (SimpleRoot i ν))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    Jacquet.Localization.Coinvariants A.representation
      (pointImage (Standard.unipotentToParabolic i ν (rootSet i ν I) ≫
        Standard.parabolicHom i ν (rootSet i ν I))) 1 ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants A.representation (unipotent i ν I) 1 :=
  Submodule.quotEquivOfEq _ _ (by rw [standard_unipotent_pointImage i ν I])

omit [Mono i.hom.hom.left] [T2Space k] in
/-- The comparison preserves the class of every original vector. -/
@[simp] theorem standardUnipotentCoinvariantsEquiv_mk
    (I : Finset (SimpleRoot i ν))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (w : A) :
    standardUnipotentCoinvariantsEquiv i ν I A
      (Jacquet.Localization.mk A.representation
        (pointImage (Standard.unipotentToParabolic i ν (rootSet i ν I) ≫
          Standard.parabolicHom i ν (rootSet i ν I))) 1 w) =
      Jacquet.Localization.mk A.representation (unipotent i ν I) 1 w := rfl

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Vanishing for all proper represented rational parabolics implies
cuspidality for the exact actual standard family. Only standard cocharacters
remain an explicit universal structural premise. -/
theorem isCuspidal_of_all_represented_parabolics_of_standardCocharacter
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    [Fintype (SimpleRoot i ν)]
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hA : ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      ¬ IsIso p → Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj A)) :
    IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
      hU A := by
  have := hG.smooth
  intro I
  obtain ⟨hp, hl, hr, hmul⟩ :=
    standard_representatives_geometric_of_standardCocharacter i ν hStandard hG hi hν I.val
  have hproper : ¬ IsIso (Standard.parabolicHom i ν (rootSet i ν I.val)) := by
    intro hiso
    let := hiso
    apply standardParabolic_ne_top_of_ne_univ i ν hi.isSplitSubtorus.1
      hRoots hStandard hG hi hν I.property
    rw [← (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν I.val)).2]
    apply SubgroupFunctor.ext
    intro Q
    apply top_unique
    intro x _
    refine ⟨x ≫ (inv (Standard.parabolicHom i ν (rootSet i ν I.val))).hom.hom, ?_⟩
    change (x ≫ (inv (Standard.parabolicHom i ν (rootSet i ν I.val))).hom.hom) ≫
      (Standard.parabolicHom i ν (rootSet i ν I.val)).hom.hom = x
    rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]
  have hvanish := hA _ _ _ (Standard.parabolicHom i ν (rootSet i ν I.val))
    (Standard.leviToParabolic i ν (rootSet i ν I.val))
    (Standard.unipotentToParabolic i ν (rootSet i ν I.val)) hp hl hr hmul hproper
  change Subsingleton (Jacquet.Localization.Coinvariants A.representation
    (unipotent i ν I.val) 1)
  change Subsingleton (Jacquet.Localization.Coinvariants A.representation
    (pointImage (Standard.unipotentToParabolic i ν (rootSet i ν I.val) ≫
      Standard.parabolicHom i ν (rootSet i ν I.val))) 1) at hvanish
  let := hvanish
  exact (standardUnipotentCoinvariantsEquiv i ν I.val A).surjective.subsingleton

/-- Compatibility form of represented-parabolic cuspidality with its former
parabolic-dynamic argument. Only the standard-cocharacter premise is used. -/
theorem isCuspidal_of_all_represented_parabolics
    (hPD : ParabolicDynamicStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    [Fintype (SimpleRoot i ν)]
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hA : ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      ¬ IsIso p → Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj A)) :
    IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
      hU A := by
  have _ := hPD
  exact isCuspidal_of_all_represented_parabolics_of_standardCocharacter
    i ν hStandard hG hi hν hRoots hU A hA

end Topology

end RepresentedParabolic
end Langlands.Aubert.General

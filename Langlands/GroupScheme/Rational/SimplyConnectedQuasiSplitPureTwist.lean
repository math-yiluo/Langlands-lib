import Langlands.GroupScheme.Rational.SimplyConnectedBorelTorusCocycles
import Langlands.GroupScheme.Rational.GeometricBorelOppositeCocharacter
import Langlands.GroupScheme.Rational.ParabolicNormalizerProof
import Langlands.GroupScheme.LocalGroupIsoBorelRefinement
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.LeviMultiplication
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.WeilSolvableCocycle
import Langlands.GroupScheme.GaloisCocycle

/-! # Pure inner cocycles with quasi-split twist -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

section Borel

variable {F : Type u} [Field F] [PerfectField F]
  {B G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {U : Over (Spec (CommRingCat.of F))} [IsAffine U.left] [Flat U.hom] [Surjective U.hom]

/-- Cocycles in a geometric Borel of a simply connected group are trivial
on the original affine faithfully flat cover over a perfect field. -/
theorem IsGeometricBorelSubgroup.isTrivial_cocycle_of_simplyConnected
    {i : B ⟶ G} (hi : IsGeometricBorelSubgroup i) (hsc : IsSimplyConnected G)
    (ξ : Cocycle B U) : ξ.IsTrivial := by
  let hG := hsc.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom U.hom := inferInstance
  obtain ⟨T, t, ht⟩ := StarActionQuasiSplit.exists_isMaximalTorus_comp_of_isGeometricBorel hG hi
  obtain ⟨ν, hp, hcent, _⟩ := hi.exists_oppositeDynamicBorel hG ht t rfl
  let χ := CommGroupScheme.groupHom ν ≫ t ≫ i
  let N := Dynamic.Affine.unipotentScheme χ
  let n := Dynamic.Affine.unipotentHom χ
  have hn : (Dynamic.unipotent χ).IsRepresentedBy n :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let : IsClosedImmersion (t ≫ i).hom.hom.left := ht.2.1
  have hz : (Dynamic.centralizer χ).IsRepresentedBy (t ≫ i) :=
    ⟨Over.mono_of_mono_left _, hcent.symm⟩
  let r := hp.factorHom n (hn.2.le.trans (Dynamic.unipotent_le_parabolic χ))
  have hr : r ≫ i = n := hp.factorHom_comp n _
  obtain ⟨hclosed, hsmooth, hconn, hunip, hnormal, _⟩ :=
    dynamicGeometricUnipotentRadical F G hG χ B N i r hp (hr ▸ hn)
  let : IsIso (subgroupMultiplication t r) :=
    Dynamic.isIso_subgroupMultiplication hp hz hn t r rfl hr
  let : IsClosedImmersion r.hom.hom.left := hclosed
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  let : Smooth N.X.hom := hsmooth
  have hNa : IsAffineHom N.X.hom := (Dynamic.Affine.isClosedSubgroup_unipotentHom χ).isAffineHom
  let : IsAffineHom N.X.hom := hNa
  let q := leviRetraction t r hnormal
  have hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range r := by
    ext Z x
    exact (mem_range_kernelι_iff q x).trans (comp_leviRetraction_eq_one_iff t r hnormal x)
  have hsection := congrArg (fun f : T.toGrp ⟶ T.toGrp => f.hom.hom)
    (levi_comp_leviRetraction t r hnormal)
  obtain ⟨n, hsplit⟩ := perfectFieldUnipotentSplit F N hconn hunip
  have hv := SplitUnipotentAffineTorsor.cocyclesVanish_of_hasSplitSeries
    (fun V hV X _ W _ _ _ ζ => Cocycle.isTrivial_of_isVectorGroupOfDimension_one hV X W ζ)
    n N hsplit hNa
  exact ξ.isTrivial_of_extension_section r q hq t.hom.hom hsection
    (fun ζ => hv.isTrivial_on_affine U ζ)
    ((ξ.map q).isTrivial_of_isInducedTorus (isInducedTorus_of_borelMaximalTorus hsc i hi t ht))

end Borel

private theorem isRangeConjugator_of_comp_innerIso {S : Scheme.{u}}
    {B C G : GroupScheme S} {i : B ⟶ G} {j : C ⟶ G}
    (g : Over.mk (𝟙 S) ⟶ G.X) (e : B ≅ C) (h : i ≫ (G.innerIso g).hom = e.hom ≫ j) :
    RelativeLevi.IsRangeConjugator i j g := by
  intro Z f x
  rw [← SubgroupFunctor.range_iso_comp e j, ← h,
    MaximalTorusParameterExistence.mem_range_comp_innerIso_iff]
  have hf : G.constantPoint g Z = f ≫ g := by
    unfold GroupScheme.constantPoint
    congr 1
    apply Over.OverMorphism.ext
    simpa using (Over.w f).symm
  rw [hf]

section Twist

variable {F L : Type u} [Field F] [PerfectField F] [Field L] [Algebra F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- A pure inner cocycle between quasi-split forms of a simply connected
field group is a coboundary. -/
theorem LocalGroupIso.HasDiscrepancy.isTrivial_of_quasiSplit
    {ξ : Cocycle G (GaloisCocycle.cover F L)}
    {e : LocalGroupIso G H (GaloisCocycle.cover F L)}
    (hξ : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (hsc : IsSimplyConnected G) (hG : IsQuasiSplit G) (hH : IsQuasiSplit H) : ξ.IsTrivial := by
  let K := AlgebraicClosure L
  let : Algebra F K := inferInstanceAs (Algebra F (AlgebraicClosure L))
  let : IsScalarTower F L K := inferInstanceAs (IsScalarTower F L (AlgebraicClosure L))
  let V := GaloisCocycle.cover F K
  let a := algebraBaseMap F K
  let f : V ⟶ GaloisCocycle.cover F L := ringTestMap F (IsScalarTower.toAlgHom F L K)
  let eK := e.refine f
  let E := GroupScheme.baseChange a
  let HK := E.obj H
  have hHK := connectedReductiveFieldExtensionStatement F K H hH.isConnectedReductive
  let : Smooth HK.X.hom := hHK.smooth
  let : IsAffineHom HK.X.hom := hHK.isAffineHom
  let : ConnectedSpace HK.X.left := hHK.connectedSpace
  obtain ⟨B, i, hi⟩ := hG.exists_isGeometricBorelSubgroup
  obtain ⟨C, j, hj⟩ := hH.exists_isGeometricBorelSubgroup
  have hiK : IsBorelSubgroup (E.map i ≫ eK.toBaseChangeIso.hom) :=
    ((hi.baseChange hG.isConnectedReductive a).1).comp_iso eK.toBaseChangeIso
  have hjK : IsBorelSubgroup (E.map j) := (hj.baseChange hH.isConnectedReductive a).1
  obtain ⟨g, φ, hφ⟩ := (borelConjugacy K HK).2 (E.obj B) (E.obj C)
    (E.map i ≫ eK.toBaseChangeIso.hom) (E.map j) hiK hjK
  let P : Over V.left := Over.mk (𝟙 _)
  let W := (Over.map V.hom).obj P
  let p : W ⟶ V := LocalGroupIso.baseChangeTestPoint P
  let c : W ⟶ G.X := (eK.toFun p).symm (baseChangePointsEquiv V.hom H P g)
  have hp : ((eK.refine p).twist (AutomorphicAction.conjugation (𝟙 G)) c).PreservesSubgroup
      (SubgroupFunctor.range i) (SubgroupFunctor.range j) :=
    eK.preservesSubgroup_of_baseChange_conjugator i j P g
      (isRangeConjugator_of_comp_innerIso g φ hφ)
  let ζ := ((ξ.refine f).refine p).twist c
  have he' : ((eK.refine p).twist (AutomorphicAction.conjugation (𝟙 G)) c).HasDiscrepancy
      (AutomorphicAction.conjugation (𝟙 G)) ζ :=
    HasDiscrepancy.twist (HasDiscrepancy.refine (HasDiscrepancy.refine hξ f) p) c
  let : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hval : ∀ {Z : Over (Spec (CommRingCat.of F))} (b c : Z ⟶ W),
      ∃ y : Z ⟶ B.X, y ≫ i.hom.hom = ζ.toFun b c := by
    intro Z b c
    have h := he'.mem_subgroupStabilizer hp b c
    rw [AutomorphicAction.conjugation_subgroupStabilizer,
      parabolicSelfNormalizer F G hG.isConnectedReductive B i hi.isParabolicSubgroup] at h
    exact SubgroupFunctor.mem_range.mp h
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc F K
  let : IsAffine W.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  let : Flat W.hom := by change Flat (𝟙 _ ≫ a); simpa only [Category.id_comp] using hf
  let : Surjective W.hom := by change Surjective (𝟙 _ ≫ a); simpa only [Category.id_comp] using hs
  let : QuasiCompact W.hom := by change QuasiCompact (𝟙 _ ≫ a); simpa only [Category.id_comp] using hq
  let : Flat V.hom := hf
  let : Surjective V.hom := hs
  let : QuasiCompact V.hom := hq
  have hW := hi.isTrivial_cocycle_of_simplyConnected hsc (ζ.lift i hval)
  have hV : (ξ.refine f).IsTrivial := Cocycle.IsTrivial.of_refine_fpqcCover p
    (Cocycle.IsTrivial.of_twist (Cocycle.IsTrivial.of_lift hW))
  exact hV.of_refine_fpqcCover f

end Twist

end Langlands.GroupScheme

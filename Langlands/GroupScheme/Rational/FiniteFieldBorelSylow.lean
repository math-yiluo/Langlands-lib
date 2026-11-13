import Langlands.GroupScheme.Rational.FiniteFieldDynamicSylow
import Langlands.GroupScheme.Rational.GeometricBorelMinimalParabolic
import Langlands.GroupScheme.Rational.QuasiSplitCentralizerTorus
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.AffineWeilParabolicRadicalTransportProof
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.FiniteFieldSylowBorelStatement
import Langlands.GroupScheme.Rational.NormalSylowBorelReduction

/-! # Actual Sylow subgroups from geometric Borel radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Borel

variable {k : Type u} [Field k] [Finite k]
    {G B U : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (i : B ⟶ G) (j : U ⟶ B)
    (hi : IsGeometricBorelSubgroup i) (hj : IsUnipotentRadical j)

include hG hi hj in
/-- The point image of each supplied geometric Borel radical is the underlying
subgroup of an actual Sylow subgroup. -/
theorem exists_sylow_eq_geometricBorelRadical :
    ∃ S : Sylow (ringChar k) (rationalPoints G),
      S.toSubgroup = (rationalPoints.map (j ≫ i)).range := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨A, a, ha, C, c, hc, hclosed, hC⟩ :=
    hi.exists_maximalSplitTorus_with_torusCentralizer
      dynamicCentralizerReductive parabolicDynamic hG
  obtain ⟨ν, hν⟩ := ha.isSplitSubtorus.1.exists_genericCocharacter a
  let χ := CommGroupScheme.groupHom ν ≫ a
  let P := Dynamic.Affine.parabolicScheme χ
  let p : P ⟶ G := Dynamic.Affine.parabolicHom χ
  have hp : (Dynamic.parabolic χ).IsRepresentedBy p :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hmin : IsMinimalParabolicFunctor (SubgroupFunctor.range p) := by
    rw [hp.2]
    exact genericMinimalParabolic k G hG A a ha ν hν
  have hminP : IsMinimalParabolicSubgroup p := by
    refine ⟨AffineWeilParabolicRadicalTransport.isParabolicSubgroup_of_isRepresentedBy
      hG χ hp, ?_⟩
    intro Q q hq hle
    exact hmin.2 (SubgroupFunctor.range q) ⟨Q, q, hq, rfl⟩ hle
  obtain ⟨g, e, he⟩ := minimalParabolicConjugacy k G hG P B p i hminP
    hi.isMinimalParabolicSubgroup
  have hr : (Dynamic.unipotent χ).IsRepresentedBy ((j ≫ e.inv) ≫ p) :=
    AffineWeilParabolicRadicalTransport.isRepresentedBy_unipotent_of_isUnipotentRadical
      hG χ hp (hj.comp_iso e.symm)
  have he' : ((j ≫ e.inv) ≫ p) ≫ (G.innerIso g).hom = j ≫ i := by
    calc
      ((j ≫ e.inv) ≫ p) ≫ (G.innerIso g).hom =
          j ≫ e.inv ≫ (p ≫ (G.innerIso g).hom) := by simp only [Category.assoc]
      _ = j ≫ e.inv ≫ (e.hom ≫ i) := by rw [he]
      _ = j ≫ i := by simp
  let S := genericUnipotentSylowOfTorusCentralizer hG A a ha ν c hc hclosed hC hν
  refine ⟨g • S, ?_⟩
  change S.toSubgroup.map (MulAut.conj g).toMonoidHom = _
  rw [genericUnipotentSylowOfTorusCentralizer_toSubgroup]
  change (Dynamic.unipotent χ).rationalPoints.map (MulAut.conj g).toMonoidHom = _
  rw [SubgroupFunctor.rationalPoints_eq_range hr, ← rationalPoints_range_comp_innerIso, he']

/-- An actual Sylow subgroup whose underlying subgroup is exactly the rational
point image of the specified geometric Borel radical. -/
def geometricBorelRadicalSylow : Sylow (ringChar k) (rationalPoints G) :=
  (exists_sylow_eq_geometricBorelRadical hG i j hi hj).choose

@[simp] theorem geometricBorelRadicalSylow_toSubgroup :
    (geometricBorelRadicalSylow hG i j hi hj).toSubgroup =
      (rationalPoints.map (j ≫ i)).range :=
  (exists_sylow_eq_geometricBorelRadical hG i j hi hj).choose_spec

end Borel

/-- Maximal defining-characteristic p-subgroups of the actual finite-field
rational-point group are precisely geometric Borel radical point images. -/
theorem finiteFieldSylowBorel : FiniteFieldSylowBorelStatement.{u} := by
  intro k _ _ G hG H
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Finite (rationalPoints G) := finite_rationalPoints_of_finite_field G
  let : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  constructor
  · rintro ⟨hH, hmax⟩
    obtain ⟨B, i, hi⟩ := (finiteFieldQuasiSplit k G hG).exists_isGeometricBorelSubgroup
    let : IsAffineHom B.X.hom := hi.1.isClosedSubgroup.isAffineHom
    let : Smooth B.X.hom := hi.1.smooth
    let : ConnectedSpace B.X.left := hi.1.connectedSpace
    obtain ⟨U, j, hj⟩ := unipotentRadicalExistence k B
    let S := geometricBorelRadicalSylow hG i j hi hj
    let T : Sylow (ringChar k) (rationalPoints G) := {
      toSubgroup := H
      isPGroup' := hH
      is_maximal' := fun hQ hle => hmax _ hle hQ }
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (rationalPoints G) S T
    refine ⟨B, U, i ≫ (G.innerIso g).hom, j, hi.comp_iso (G.innerIso g), hj, ?_⟩
    calc
      H = (g • S).toSubgroup := (congrArg Sylow.toSubgroup hg).symm
      _ = (rationalPoints.map (j ≫ i)).range.map (MulAut.conj g).toMonoidHom := by
        change S.toSubgroup.map (MulAut.conj g).toMonoidHom = _
        rw [geometricBorelRadicalSylow_toSubgroup]
      _ = (rationalPoints.map (j ≫ (i ≫ (G.innerIso g).hom))).range := by
        rw [← rationalPoints_range_comp_innerIso, Category.assoc]
  · rintro ⟨B, U, i, j, hi, hj, rfl⟩
    let S := geometricBorelRadicalSylow hG i j hi hj
    have hS := geometricBorelRadicalSylow_toSubgroup hG i j hi hj
    rw [← hS]
    exact ⟨S.isPGroup', fun H' hle hH' => S.is_maximal' hH' hle⟩

/-- A normal maximal defining-characteristic p-subgroup forces a connected
reductive finite-field group to be a torus. -/
theorem finiteFieldNormalSylowTorus : FiniteFieldNormalSylowTorusStatement.{u} :=
  finiteFieldNormalSylowTorus_of_sylowBorel finiteFieldSylowBorel

end Langlands.GroupScheme

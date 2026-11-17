import Langlands.GroupScheme.Torus.FiniteTorsionNormalizer
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeNormalizerSmooth
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerOpen
import Langlands.GroupScheme.Torus.EndomorphismDichotomy
import Langlands.GroupScheme.Torus.DiagonalizableDecomposition

/-! # Scheme normalizers detected by finite diagonalizable subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace CharacterAction

open Corepresented

variable {R : CommRingCat.{u}} {M N : Type u} [AddCommGroup M] [AddCommGroup N]
  {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

@[ext] theorem CharacterEmbedding.ext_hom {a b : CharacterEmbedding F M}
    (h : ∀ A, a.hom A = b.hom A) : a = b := by
  have hh : a.hom = b.hom := funext h
  cases a
  cases b
  cases hh
  rfl

/-- Restricting a diagonalizable-group point is precomposition on characters. -/
theorem characterPoint_restrictMap (q : M →+ N) {A : CommAlgCat.{u} R}
    (t : Multiplicative N →* Aˣ) :
    characterPoint t ≫ (Diagonalizable.restrictMap R q).hom.hom =
      characterPoint (t.comp (AddMonoidHom.toMultiplicative q)) := by
  apply (affinePointsEquiv (Diagonalizable.functor R M)
    (Diagonalizable.grpCorepresentation R M) A).injective
  rw [Diagonalizable.restrictMap, groupSchemeMap_affinePoints]
  simp only [characterPoint, MulEquiv.apply_symm_apply]
  rfl

/-- The algebraic quotient-character embedding is the actual embedding of
the corresponding closed diagonalizable subgroup. -/
theorem diagonalizableEmbedding_restrictMap
    (j : (Diagonalizable.groupScheme R M).toGrp ⟶ groupScheme F e)
    [Mono j.hom.hom] (q : M →+ N) (hq : Function.Surjective q)
    [Mono (Diagonalizable.restrictMap R q ≫ j).hom.hom] :
    diagonalizableEmbedding e (Diagonalizable.restrictMap R q ≫ j) =
      quotientEmbedding (diagonalizableEmbedding e j) q hq := by
  ext A t
  change affinePointsEquiv F e A
      (characterPoint t ≫ (Diagonalizable.restrictMap R q ≫ j).hom.hom) =
    affinePointsEquiv F e A
      (characterPoint (t.comp (AddMonoidHom.toMultiplicative q)) ≫ j.hom.hom)
  rw [Grp.comp_hom_hom, ← Category.assoc, characterPoint_restrictMap]

end CharacterAction

namespace FiniteTorsionNormalizerScheme

open Corepresented CharacterAction

/-- An ideal quotient representing a closed diagonalizable subgroup is its
actual group algebra over the original base ring. -/
def quotientAlgebraEquiv
    {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    {M : Type u} [AddCommGroup M]
    (j : (Diagonalizable.groupScheme R M).toGrp ⟶ groupScheme F e) [Mono j.hom.hom]
    {I : Ideal B}
    (hI : ∀ (U : Over (Spec R)) (y : U ⟶ (groupScheme F e).X),
      y ∈ (SubgroupFunctor.range j).carrier U ↔
        ∀ b ∈ I, (e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0) :
    (B ⧸ I) ≃ₐ[R] AddMonoidAlgebra R M := by
  let hcut := isCutOutBy_range hI
  have hrep₁ : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  have hrep₂ : (SubgroupFunctor.range j).IsRepresentedBy (cutHom hcut) :=
    isRepresentedBy_cutHom_affineSubgroups (isAffineCutOutBy_range hI)
  let eH := hrep₁.isoOfIsRepresentedBy hrep₂
  let eA : CommAlgCat.of R (B ⧸ I) ≅
      ((algΓ R).obj (Diagonalizable.groupScheme R M).X).unop :=
    (affineSectionsIso (CommAlgCat.of R (B ⧸ I))).symm ≪≫
      ((algΓ R).mapIso ((Grp.forget _).mapIso eH)).unop
  exact (CommAlgCat.algEquivOfIso eA).trans
    (affineSectionsAlgEquiv (Diagonalizable.algebra R M))

/-- Closed affine-cutout subgroup functors agreeing on algebra spectra agree
on every relative scheme test. -/
theorem eq_of_affineSubgroups
    {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
    {e : (F ⋙ forget GrpCat).CorepresentableBy B}
    {K L : SubgroupFunctor (groupScheme F e)} {I J : Ideal B}
    (hK : IsCutOutBy e (affineSubgroups K) I)
    (hL : IsCutOutBy e (affineSubgroups L) J)
    (h : affineSubgroups K = affineSubgroups L) : K = L := by
  ext U x
  rw [mem_iff_points_mem_affineSubgroups_of_isCutOutBy hK,
    mem_iff_points_mem_affineSubgroups_of_isCutOutBy hL, h]

/-- A closed diagonalizable subgroup of a finitely presented affine group
has the same full scheme normalizer as some finite characteristic torsion subgroup. -/
theorem exists_integerTorsion_same_normalizer
    {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B) [Algebra.FinitePresentation R B]
    {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    (j : (Diagonalizable.groupScheme R M).toGrp ⟶ groupScheme F e)
    (hj : IsClosedSubgroup j) :
    ∃ n : ℕ, 0 < n ∧
      (SubgroupFunctor.range (Diagonalizable.restrictMap R
        (QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples (M := M) n)) ≫ j)).normalizer =
      (SubgroupFunctor.range j).normalizer := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom.left := SurjectiveOnStalks.mono_of_injective j.hom.hom.left.isClosedEmbedding.injective
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨I, hI⟩ := exists_ideal_range j
  let eQ := quotientAlgebraEquiv e j hI
  let : Module.Projective R (B ⧸ I) := Module.Projective.of_equiv eQ.symm.toLinearEquiv
  let : Algebra.FinitePresentation R (AddMonoidAlgebra R M) :=
    Diagonalizable.finitePresentation_groupAlgebra_of_fg R M
  let : Algebra.FinitePresentation R (B ⧸ I) := Algebra.FinitePresentation.equiv eQ.symm
  have hIfg : I.FG := by
    have h := Algebra.FinitePresentation.ker_fG_of_surjective
      (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
    simpa only [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] using h
  let emb := diagonalizableEmbedding e j
  have hrange : emb.range = affineSubgroups (SubgroupFunctor.range j) :=
    funext (diagonalizableEmbedding_range e j)
  have hIfam : IsCutOutBy e emb.range I := by
    rw [hrange]
    exact isCutOutBy_range hI
  obtain ⟨n, hn, hnorm⟩ := CharacterAction.exists_integerTorsion_same_normalizer emb e hIfam hIfg
  let q : M →+ M ⧸ FiniteCharacterSeparation.multiples n :=
    QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples n)
  let jn := Diagonalizable.restrictMap R q ≫ j
  have hkclosed : IsClosedSubgroup (Diagonalizable.restrictMap R q) :=
    Diagonalizable.isClosedImmersion_restrictMap R q QuotientAddGroup.mk_surjective
  have hjnclosed : IsClosedSubgroup jn := hkclosed.comp hj
  let : IsClosedImmersion jn.hom.hom.left := hjnclosed
  let : Mono jn.hom.hom.left := SurjectiveOnStalks.mono_of_injective jn.hom.hom.left.isClosedEmbedding.injective
  let : Mono jn.hom.hom := Over.mono_of_mono_left _
  obtain ⟨J, hJ⟩ := exists_ideal_range jn
  let : Module.Projective R (B ⧸ J) :=
    Module.Projective.of_equiv (quotientAlgebraEquiv e jn hJ).symm.toLinearEquiv
  have hrangeN : (diagonalizableEmbedding e jn).range = affineSubgroups (SubgroupFunctor.range jn) :=
    funext (diagonalizableEmbedding_range e jn)
  have hEmbN : diagonalizableEmbedding e jn = integerTorsionEmbedding emb n :=
    diagonalizableEmbedding_restrictMap e j q QuotientAddGroup.mk_surjective
  have hA : affineSubgroups (SubgroupFunctor.range jn).normalizer =
      affineSubgroups (SubgroupFunctor.range j).normalizer := by
    funext A
    rw [affineSubgroups_normalizer hJ, affineSubgroups_normalizer hI,
      ← hrangeN, ← hrange, hEmbN]
    exact hnorm A
  refine ⟨n, hn, ?_⟩
  exact eq_of_affineSubgroups (isCutOutBy_affineSubgroups_normalizer hJ)
    (isCutOutBy_affineSubgroups_normalizer hI) hA

end FiniteTorsionNormalizerScheme

/-- Over any affine base, some finite characteristic torsion subgroup of a
closed diagonalizable subgroup has the same full scheme normalizer in a smooth affine group. -/
theorem diagonalizable_exists_integerTorsion_same_normalizer_overRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {G : GroupScheme (Spec R)} [IsAffine G.X.left] [Smooth G.X.hom]
    (j : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hj : IsClosedSubgroup j) :
    ∃ n : ℕ, 0 < n ∧
      (SubgroupFunctor.range (Diagonalizable.restrictMap R
        (QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples (M := M) n)) ≫ j)).normalizer =
      (SubgroupFunctor.range j).normalizer := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Algebra.Smooth R (AffineCoordinates.algebra G) :=
    AffineCoordinates.smooth_algebra G inferInstance
  obtain ⟨n, hn, h⟩ := FiniteTorsionNormalizerScheme.exists_integerTorsion_same_normalizer
    (AffineCoordinates.corepresentation G) (AffineCoordinates.coordinateHom j)
      (inferInstance : IsClosedImmersion (AffineCoordinates.coordinateHom j).hom.hom.left)
  refine ⟨n, hn, ?_⟩
  rw [SubgroupFunctor.normalizer_range_eq_comap_of_iso
      (Diagonalizable.restrictMap R
        (QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples (M := M) n)) ≫ j)
      (AffineCoordinates.groupSchemeIso G).symm,
    SubgroupFunctor.normalizer_range_eq_comap_of_iso j (AffineCoordinates.groupSchemeIso G).symm]
  exact congrArg (fun K => K.comap (AffineCoordinates.groupSchemeIso G).inv) h

/-- Choose an actual finite closed diagonalizable subgroup with exactly the
normalizer of the original subgroup over every relative scheme test. -/
def finiteTorsionNormalizerOverRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {G : GroupScheme (Spec R)} [IsAffine G.X.left] [Smooth G.X.hom]
    (j : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hj : IsClosedSubgroup j) :
    Σ n : ℕ, {_hn : 0 < n //
      IsClosedSubgroup (Diagonalizable.restrictMap R
        (QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples (M := M) n)) ≫ j) ∧
      IsFinite (Diagonalizable.groupScheme R (M ⧸ FiniteCharacterSeparation.multiples n)).X.hom ∧
      (SubgroupFunctor.range (Diagonalizable.restrictMap R
        (QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples (M := M) n)) ≫ j)).normalizer =
      (SubgroupFunctor.range j).normalizer} := by
  let h := diagonalizable_exists_integerTorsion_same_normalizer_overRing j hj
  let n := h.choose
  have hn : 0 < n := h.choose_spec.1
  let : Finite (M ⧸ FiniteCharacterSeparation.multiples n) :=
    FiniteCharacterSeparation.finite_quotient hn.ne'
  have hc : IsClosedSubgroup (Diagonalizable.restrictMap R
      (QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples (M := M) n))) :=
    Diagonalizable.isClosedImmersion_restrictMap R _ QuotientAddGroup.mk_surjective
  exact ⟨n, hn, hc.comp hj, inferInstance, h.choose_spec.2⟩

end Langlands.GroupScheme

import Langlands.GroupScheme.Derived.GeneralLinearCenterDerivedStatement
import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.UnitPowerFppfCover
import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality

/-! # Perfectness of every fppf quotient of GL by its centre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (k : Type u) [Field k]
  {Q : GroupScheme (Spec (CommRingCat.of k))}
  (q : groupScheme n (CommRingCat.of k) ⟶ Q)
  (hdetOne : ∀ (T : Over (Spec (CommRingCat.of k)))
    (g : T ⟶ (groupScheme n (CommRingCat.of k)).X),
    Matrix.GeneralLinearGroup.det (pointsEquiv n (CommRingCat.of k) T g) = 1 →
      g ∈ (derivedSubgroup (groupScheme n (CommRingCat.of k))).carrier T)

include hdetOne

/-- Over an affine test, if determinant-one points lie in the derived group, killing the centre
carries every GL point into the full derived
subgroup of the target. -/
theorem image_mem_derivedSubgroup_affine
    (hker : center (groupScheme n (CommRingCat.of k)) ≤ SubgroupFunctor.range (kernelι q))
    (T : Over (Spec (CommRingCat.of k))) [IsAffine T.left]
    (g : T ⟶ (groupScheme n (CommRingCat.of k)).X) :
    g ≫ q.hom.hom ∈ (derivedSubgroup Q).carrier T := by
  classical
  intro H i hi hc
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  by_cases hn : Fintype.card n = 0
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    have hg : g = 1 := by
      apply (pointsEquiv n (CommRingCat.of k) T).injective
      apply Units.ext
      ext a b
      exact isEmptyElim a
    rw [hg, MonObj.one_comp]
    exact (SubgroupFunctor.range i).carrier T |>.one_mem
  · obtain ⟨W, a, hW, hf, hs, hl, r, hr⟩ :=
      UnitPowerExtension.exists_roots_test T (Fintype.card n) hn
        (fun _ : Fin 1 => Matrix.GeneralLinearGroup.det (pointsEquiv n _ T g))
    have : Flat a.left := hf
    have : Surjective a.left := hs
    have : LocallyOfFinitePresentation a.left := hl
    let s : W ⟶ (groupScheme n (CommRingCat.of k)).X :=
      (Gm.pointsEquiv (Spec (CommRingCat.of k)) W).symm (r 0) ≫
        (scalarTorus n (CommRingCat.of k)).hom.hom
    have hdet : Matrix.GeneralLinearGroup.det (pointsEquiv n _ W (a ≫ g)) =
        (r 0) ^ Fintype.card n := by
      rw [pointsEquiv_naturality, Matrix.GeneralLinearGroup.map_det]
      exact (hr 0).symm
    have hds : Matrix.GeneralLinearGroup.det (pointsEquiv n _ W s) =
        (r 0) ^ Fintype.card n := by
      dsimp only [s]
      rw [pointsEquiv_scalarTorus, MulEquiv.apply_symm_apply,
        Matrix.GeneralLinearGroup.det_scalar]
    have hhd : s⁻¹ * (a ≫ g) ∈
        (derivedSubgroup (groupScheme n (CommRingCat.of k))).carrier W := by
      apply hdetOne W
      rw [map_mul, map_inv, map_mul, map_inv, hdet, hds, inv_mul_cancel]
    have hq : s ≫ q.hom.hom = 1 :=
      (mem_range_kernelι_iff q s).mp (hker W (isCentral_scalarTorus W _))
    have h := mem_derivedSubgroup_comp q hhd H i hi hc
    apply SubgroupFunctor.mem_range_of_comp_mem_range i a
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, hq, inv_one, one_mul,
      Category.assoc] using h

/-- If determinant-one points lie in the derived group, a homomorphism out of GL
which kills its centre has image in the target's full
scheme-theoretic derived subgroup. -/
theorem range_le_derivedSubgroup_of_center_kernel
    (hker : center (groupScheme n (CommRingCat.of k)) ≤ SubgroupFunctor.range (kernelι q)) :
    SubgroupFunctor.range q ≤ derivedSubgroup Q := by
  intro T x hx
  obtain ⟨g, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  intro H i hi hc
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  apply (SubgroupFunctor.mem_range_iff_openCover i T.left.affineOpenCover.openCover _).mpr
  intro j
  let V := SubgroupFunctor.coverObj T.left.affineOpenCover.openCover j
  let a : V ⟶ T := SubgroupFunctor.coverMap T.left.affineOpenCover.openCover j
  have : IsAffine V.left :=
    inferInstanceAs (IsAffine (Spec (T.left.affineOpenCover.X j)))
  have h := image_mem_derivedSubgroup_affine n k q hdetOne hker V (a ≫ g) H i hi hc
  simpa only [Category.assoc] using h

/-- If determinant-one points lie in the full derived group of GL, every fppf
quotient of GL by its scheme-theoretic centre is perfect. -/
theorem quotient_derivedSubgroup_eq_top
    (hq : RelativeRoot.IsFppfQuotient (center (groupScheme n (CommRingCat.of k))) q) :
    derivedSubgroup Q = ⊤ := by
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have himage := range_le_derivedSubgroup_of_center_kernel n k q hdetOne hq.2.2.2.ge
  apply SubgroupFunctor.ext
  intro T
  change (derivedSubgroup Q).carrier T = ⊤
  apply top_unique
  intro x hx H i hi hc
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let V : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst x.left q.hom.hom.left ≫ T.hom)
  let a : V ⟶ T := Over.homMk (pullback.fst x.left q.hom.hom.left) rfl
  let z : V ⟶ (groupScheme n (CommRingCat.of k)).X :=
    Over.homMk (pullback.snd x.left q.hom.hom.left) (by
      rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
        Category.assoc, Over.w x]
      rfl)
  have haz : a ≫ x = z ≫ q.hom.hom := Over.OverMorphism.ext pullback.condition
  have : EffectiveEpi a.left := by
    change EffectiveEpi (pullback.fst _ _)
    infer_instance
  apply SubgroupFunctor.mem_range_of_comp_mem_range i a
  rw [haz]
  exact himage V (SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩) H i hi hc

end Langlands.GroupScheme.GeneralLinear

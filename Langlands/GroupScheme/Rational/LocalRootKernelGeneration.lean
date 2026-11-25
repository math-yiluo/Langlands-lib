import Langlands.GroupScheme.Rational.LocalRootGeneration
import Langlands.GroupScheme.Rational.SmoothQuotientRootCoordinates
import Langlands.GroupScheme.IntegralModel

/-! # Integral ordered root factors preserving a field-fibre quotient kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.RelativeRoot

private theorem section_baseChange_mem {B B' : Scheme.{u}} (b : B' ⟶ B)
    {G : GroupScheme B} (D : SubgroupFunctor G)
    {x : Over.mk (𝟙 B) ⟶ G.X} (hx : x ∈ D.carrier _) :
    baseChangeSectionHom b G x ∈ (D.baseChange b).carrier (Over.mk (𝟙 B')) := by
  rw [SubgroupFunctor.mem_baseChange]
  have h := D.comp_mem (Over.homMk b (by simp) :
    (Over.map b).obj (Over.mk (𝟙 B')) ⟶ Over.mk (𝟙 B)) hx
  convert h using 1
  apply Over.OverMorphism.ext
  exact baseChangeSectionHom_fst b G x

variable {R k l : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field k] [Algebra R k] [Field l] [Algebra R l]
    (I : Type u) [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {Q : GroupScheme (Spec (CommRingCat.of l))}
    [IsAffineHom Q.X.hom] [Smooth Q.X.hom]
    (q : (GroupScheme.baseChange (algebraBaseMap R l)).obj G ⟶ Q)

local instance localRootKernelAffine {A : Type u} [CommRing A] [Algebra R A] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))

local instance localRootKernelAbsoluteAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Integral dynamic points in the field-fibre quotient kernel are generated
by integral root points in the same kernel, with roots selected on `k`. -/
def ExponentRootKernelGeneration (ν : I → ℤ) : Prop :=
  ∀ P : Subgroup (rationalPoints G),
    (∀ m : I → ℤ,
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        relativeRoots (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
          (splitTorus.baseChangeHom (K := k) G I i) →
      (subgroup i (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m)).carrier
          (Over.mk (𝟙 _)) ⊓
        ((rationalPoints.map q).comp
          (baseChangeSectionHom (algebraBaseMap R l) G)).ker ≤ P) →
    (Dynamic.unipotent (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier
        (Over.mk (𝟙 _)) ⊓
      ((rationalPoints.map q).comp
        (baseChangeSectionHom (algebraBaseMap R l) G)).ker ≤ P

/-- A smooth quotient of one field fibre preserves the kernel condition on
all factors of the integral ordered positive-root decomposition. -/
theorem exponentRootKernelGeneration
    [Mono (splitTorus.baseChangeHom (K := k) G I i).hom.hom.left]
    (hroot : HasRelativeRootSystem
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i))
    (hq : Smooth q.hom.hom.left) (ν : I → ℤ) :
    ExponentRootKernelGeneration (k := k) I i q ν := by
  classical
  let ik : (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap R k)).obj G :=
    splitTorus.baseChangeHom (K := k) G I i
  let νk := splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν
  obtain ⟨n, a, hinj, ha⟩ := exists_fin_enumeration_indivisiblePositiveRoots ik νk
    (hroot.finite_relativeRoots ik (isSplitTorus_splitTorus I))
  let m (r : Fin n) : I → ℤ := splitTorus.characterLatticeEquiv k I (a r)
  have hmk (r : Fin n) :
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r) = a r := by
    rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
    exact AddEquiv.symm_apply_apply _ _
  have ham (r : Fin n) : a r ∈ indivisiblePositiveRoots ik νk :=
    ha ▸ Set.mem_range_self r
  have hmR (r : Fin n) :
      splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r) ≠ 0 := by
    have hcoord : splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r) =
        (splitTorus.characterLatticeEquiv R I).symm (m r) :=
      (splitTorus.characterLatticeEquiv_symm_eq R I (m r)).symm
    intro hz
    have hmzero : m r = 0 := by
      apply (splitTorus.characterLatticeEquiv R I).symm.injective
      simpa only [AddEquiv.map_zero] using hcoord.symm.trans hz
    have hakzero : a r = 0 := by
      rw [← hmk r, hmzero,
        splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, AddEquiv.map_zero]
    exact (ham r).1.1.1 hakzero
  have hrep (r : Fin n) := Domain.subgroup_has_smooth_geometricallyConnected_closed_representative
    (isSplitTorus_splitTorus I) i
    (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r)) (hmR r)
  choose H j hj hclosed haff hsm hconn using hrep
  let χ := CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i
  let jU := Dynamic.Affine.unipotentHom χ
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hdisj : ∀ a ∈ indivisiblePositiveRoots ik νk,
      ∀ b ∈ indivisiblePositiveRoots ik νk, a ≠ b →
      Disjoint (cyclicTail a 1 : Set (characterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)))
        (cyclicTail b 1 : Set (characterLattice
          (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))) := by
    intro a ha b hb hne
    exact disjoint_cyclicTail_indivisibleRoots ik hroot (isSplitTorus_splitTorus I)
      ha.1 hb.1 hne
  obtain ⟨e, he⟩ := exists_orderedRootProductIso_localRing (k := k) I i ν
    hdisj m (by simpa only [hmk] using hinj)
    (by simpa only [hmk] using ha) hU j hj hsm
  intro P hP x hx
  obtain ⟨xU, hxU⟩ := SubgroupFunctor.mem_range.mp (hU.2 ▸ hx.1)
  let z := finiteProductPointsEquiv H (Over.mk (𝟙 _)) (xU ≫ e.inv)
  let y : Fin n → rationalPoints G := fun r => z r ≫ (j r).hom.hom
  have hymem (r : Fin n) : y r ∈ (subgroup i
      (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (m r))).carrier
        (Over.mk (𝟙 _)) :=
    ((hj r).pointsEquiv _ (z r)).property
  have hprod : (List.ofFn y).prod = x := by
    change orderedPoints j z = x
    rw [← comp_orderedMultiplication]
    rw [← he]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hxU
  let b := algebraBaseMap R l
  let Gl := (GroupScheme.baseChange b).obj G
  let il := splitTorus.baseChangeHom (K := l) G I i
  let νl := splitTorus.exponentCocharacter (Spec (CommRingCat.of l)) I ν
  let al := fun r => splitTorus.exponentCharacter (Spec (CommRingCat.of l)) I (m r)
  let red := baseChangeSectionHom b G
  let φ := (rationalPoints.map q).comp red
  have : Smooth Gl.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have hal : Set.range al = indivisiblePositiveRoots il νl := by
    have hak : Set.range (fun r =>
        splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)) =
        indivisiblePositiveRoots (splitTorus.baseChangeHom (K := k) G I i)
          (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν) := by
      simpa only [hmk] using ha
    simpa only [splitTorus.fieldCharacterEquiv_exponentCharacter,
      splitTorus.fieldCocharacterEquiv_exponentCocharacter] using
      splitTorus.range_fieldCharacterEquiv_indivisiblePositiveRoots
        (k := k) (l := l) I G i
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν) _ hak
  have hinjl : Function.Injective al := by
    have h := (splitTorus.fieldCharacterEquiv (k := k) (l := l) I).injective.comp hinj
    simpa only [Function.comp_def, ← hmk,
      splitTorus.fieldCharacterEquiv_exponentCharacter] using h
  have hdisjl : ∀ a ∈ indivisiblePositiveRoots il νl,
      ∀ c ∈ indivisiblePositiveRoots il νl, a ≠ c →
        Disjoint (cyclicTail a 1 :
          Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I)))
          (cyclicTail c 1 :
            Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I))) := by
    simpa only [splitTorus.fieldCocharacterEquiv_exponentCocharacter] using
      splitTorus.disjoint_positive_rays_fieldBaseChange (k := k) (l := l) I G i
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν) hdisj
  have hyred (r : Fin n) : red (y r) ∈ (subgroup il (al r)).carrier (Over.mk (𝟙 _)) := by
    dsimp only [il, al, splitTorus.baseChangeHom]
    rw [exponentRoot_subgroup_baseChange I i b (m r)]
    exact section_baseChange_mem b _ (hymem r)
  have hyker : ∀ r, φ (y r) = 1 := by
    change ∀ r, red (y r) ≫ q.hom.hom = 1
    apply (root_product_comp_eq_one_iff_of_smooth
      (k := l) (S := splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I)
      (G := Gl) (Q := Q) il (isSplitTorus_splitTorus I)
      νl q hq hdisjl al hinjl hal
      (T := Over.mk (𝟙 (Spec (CommRingCat.of l))))
      (fun r => red (y r)) hyred).mp
    change rationalPoints.map q ((List.ofFn (fun r => red (y r))).prod) = 1
    have hredprod : (List.ofFn (fun r => red (y r))).prod = red x := by
      simpa only [map_list_prod, List.map_ofFn, Function.comp_def] using congrArg red hprod
    rw [hredprod]
    exact hx.2
  rw [← hprod]
  apply P.list_prod_mem
  intro v hv
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hv
  exact hP (m r) (by rw [hmk]; exact (ham r).1.1) ⟨hymem r, hyker r⟩

end Langlands.GroupScheme.RelativeRoot

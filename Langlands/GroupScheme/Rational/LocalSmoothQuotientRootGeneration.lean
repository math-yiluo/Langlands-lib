import Langlands.GroupScheme.Rational.LocalRootGeneration
import Langlands.GroupScheme.Rational.RootSmoothQuotientProduct
import Langlands.GroupScheme.IntegralModel

/-! # Integral root generation in smooth fibre-quotient kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.RelativeRoot

/-- Sections whose restriction is killed by the specified fibre homomorphism. -/
def baseChangeQuotientKernel {B B' : Scheme.{u}} (b : B' ⟶ B)
    (G : GroupScheme B) {Q : GroupScheme B'}
    (q : (GroupScheme.baseChange b).obj G ⟶ Q) :
    Subgroup (𝟙_ (Over B) ⟶ G.X) :=
  ({ toFun := fun x => baseChangeSectionHom b G x ≫ q.hom.hom
     map_one' := by rw [map_one]; exact MonObj.one_comp _
     map_mul' := by intro x y; simp only [map_mul, MonObj.mul_comp] } :
    (𝟙_ (Over B) ⟶ G.X) →* (𝟙_ (Over B') ⟶ Q.X)).ker

/-- Restricting an ordered product restricts its original coordinates. -/
theorem baseChangeSectionHom_orderedPoints
    {B B' : Scheme.{u}} (b : B' ⟶ B)
    {G : GroupScheme B} {n : ℕ} {H : Fin n → GroupScheme B}
    (j : ∀ r, H r ⟶ G)
    (x : ∀ r, (𝟙_ (Over B)) ⟶ (H r).X) :
    baseChangeSectionHom b G (orderedPoints j x) =
      orderedPoints (fun r => (GroupScheme.baseChange b).map (j r))
        (fun r => baseChangeSectionHom b (H r) (x r)) := by
  unfold orderedPoints
  rw [map_list_prod]
  simp only [List.map_ofFn, Function.comp_def, baseChangeSectionHom_naturality]

/-- Kernel reflection in restricted coordinates transfers a factorwise bound
through the original integral ordered chart. -/
theorem range_inf_baseChangeQuotientKernel_le_of_orderedProductIso
    {B B' : Scheme.{u}} (b : B' ⟶ B)
    {G U : GroupScheme B} {Q : GroupScheme B'} {n : ℕ}
    {H : Fin n → GroupScheme B} (j : ∀ r, H r ⟶ G) (jU : U ⟶ G)
    (e : (∏ᶜ H).X ≅ U.X)
    (he : e.hom ≫ jU.hom.hom = orderedMultiplication j)
    (q : (GroupScheme.baseChange b).obj G ⟶ Q)
    (hcoord : ∀ x : ∀ r, (𝟙_ (Over B)) ⟶ (H r).X,
      orderedPoints (fun r => (GroupScheme.baseChange b).map (j r))
          (fun r => baseChangeSectionHom b (H r) (x r)) ≫ q.hom.hom = 1 ↔
        ∀ r, baseChangeSectionHom b (H r) (x r) ≫
          ((GroupScheme.baseChange b).map (j r) ≫ q).hom.hom = 1)
    (S : Subgroup (𝟙_ (Over B) ⟶ G.X))
    (hS : ∀ r, (SubgroupFunctor.range (j r)).carrier (𝟙_ (Over B)) ⊓
      baseChangeQuotientKernel b G q ≤ S) :
    (SubgroupFunctor.range jU).carrier (𝟙_ (Over B)) ⊓
      baseChangeQuotientKernel b G q ≤ S := by
  rintro g ⟨hg, hgq⟩
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  let p := y ≫ e.inv
  let x := finiteProductPointsEquiv H (𝟙_ (Over B)) p
  have hp : orderedPoints j x = y ≫ jU.hom.hom := by
    rw [← comp_orderedMultiplication, ← he]
    simp only [p, Category.assoc, Iso.inv_hom_id_assoc]
  have hx : ∀ r, baseChangeSectionHom b (H r) (x r) ≫
      ((GroupScheme.baseChange b).map (j r) ≫ q).hom.hom = 1 := by
    apply (hcoord x).mp
    rw [← baseChangeSectionHom_orderedPoints, hp]
    exact hgq
  rw [← hp]
  unfold orderedPoints
  apply S.list_prod_mem
  intro z hz
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hz
  apply hS r
  refine ⟨SubgroupFunctor.mem_range.mpr ⟨x r, rfl⟩, ?_⟩
  change baseChangeSectionHom b G (x r ≫ (j r).hom.hom) ≫ q.hom.hom = 1
  rw [baseChangeSectionHom_naturality, Category.assoc]
  exact hx r

section LocalDomain

variable {R k l : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field k] [Algebra R k] [Field l] [Algebra R l]
    (I : Type u) [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {Q : GroupScheme (Spec (CommRingCat.of l))}
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom]
    (q : (GroupScheme.baseChange (algebraBaseMap R l)).obj G ⟶ Q)
    (hq : Smooth q.hom.hom.left)

local instance localSmoothQuotientRootGenerationFibreAffine {F : Type u}
    [Field F] [Algebra R F] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R F)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R F)))

local instance localSmoothQuotientRootGenerationFibreSmooth {F : Type u}
    [Field F] [Algebra R F] :
    Smooth ((GroupScheme.baseChange (algebraBaseMap R F)).obj G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom (algebraBaseMap R F)))

local instance localSmoothQuotientRootGenerationAbsoluteAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

include hq in
/-- The part of a dynamic radical killed in a smooth field-fibre quotient
is controlled by the corresponding original integral root intersections. -/
theorem dynamicUnipotent_inf_baseChangeQuotientKernel_le_of_exponentRoots
    [Mono (splitTorus.baseChangeHom (K := k) G I i).hom.hom.left]
    (hroot : HasRelativeRootSystem
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i))
    (ν : I → ℤ) (S : Subgroup (rationalPoints G))
    (hS : ∀ m : I → ℤ,
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        relativeRoots (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
          (splitTorus.baseChangeHom (K := k) G I i) →
      (subgroup i (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m)).carrier
        (𝟙_ (Over (Spec (CommRingCat.of R)))) ⊓
          baseChangeQuotientKernel (algebraBaseMap R l) G q ≤ S) :
    (Dynamic.unipotent (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier
        (𝟙_ (Over (Spec (CommRingCat.of R)))) ⊓
          baseChangeQuotientKernel (algebraBaseMap R l) G q ≤ S := by
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
      simpa only [map_zero] using hcoord.symm.trans hz
    have hakzero : a r = 0 := by
      rw [← hmk r, hmzero,
        splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, map_zero]
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
  let b := algebraBaseMap R l
  let il := splitTorus.baseChangeHom (K := l) G I i
  let νl := splitTorus.exponentCocharacter (Spec (CommRingCat.of l)) I ν
  let al := fun r => splitTorus.exponentCharacter (Spec (CommRingCat.of l)) I (m r)
  have hal : Set.range al = indivisiblePositiveRoots il νl := by
    simpa only [splitTorus.fieldCharacterEquiv_exponentCharacter,
      splitTorus.fieldCocharacterEquiv_exponentCocharacter] using
      splitTorus.range_fieldCharacterEquiv_indivisiblePositiveRoots
        (k := k) (l := l) I G i
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν) _
        (show Set.range (fun r =>
          splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)) =
            indivisiblePositiveRoots ik νk by simpa only [hmk] using ha)
  have hinjl : Function.Injective al := by
    have h := (splitTorus.fieldCharacterEquiv (k := k) (l := l) I).injective.comp
      (show Function.Injective (fun r =>
        splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m r)) by
          simpa only [hmk] using hinj)
    simpa only [Function.comp_def, splitTorus.fieldCharacterEquiv_exponentCharacter] using h
  have hdisjl : ∀ a ∈ indivisiblePositiveRoots il νl,
      ∀ c ∈ indivisiblePositiveRoots il νl, a ≠ c →
      Disjoint (cyclicTail a 1 : Set (characterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I)))
        (cyclicTail c 1 : Set (characterLattice
          (splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I))) := by
    simpa only [splitTorus.fieldCocharacterEquiv_exponentCocharacter] using
      splitTorus.disjoint_positive_rays_fieldBaseChange (k := k) (l := l) I G i
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ν) hdisj
  have hjl (r : Fin n) : (subgroup
      (S := splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I) il (al r)).IsRepresentedBy
        ((GroupScheme.baseChange b).map (j r)) := by
    dsimp only [il, al, splitTorus.baseChangeHom]
    rw [exponentRoot_subgroup_baseChange I i b (m r)]
    exact (hj r).baseChange b
  rw [← hU.2]
  apply range_inf_baseChangeQuotientKernel_le_of_orderedProductIso b j jU e he q
  · intro x
    exact SmoothQuotient.orderedPoints_comp_eq_one_iff
      (k := l) (G := (GroupScheme.baseChange b).obj G)
      (Q := Q) (S := splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I)
      (n := n) il
      (isSplitTorus_splitTorus I) q hq νl hdisjl al hinjl hal
      (fun r => (GroupScheme.baseChange b).map (j r)) hjl
      (fun r => baseChangeSectionHom b (H r) (x r))
  · intro r
    rw [(hj r).2]
    exact hS (m r) (by rw [hmk]; exact (ham r).1.1)

end LocalDomain

end Langlands.GroupScheme.RelativeRoot

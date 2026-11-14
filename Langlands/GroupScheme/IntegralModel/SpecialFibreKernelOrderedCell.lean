import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelOpenContainment
import Langlands.GroupScheme.Rational.OrderedProductPoints

/-! # Integral sections over the special-fibre kernel lie in an ordered open cell -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

section Local

variable [IsLocalRing R]

omit [IsDomain R] in
/-- **Sections through an open subscheme.** Over a local ring, a section of a scheme over
`Spec R` whose closed point lies in the range of an open immersion factors through it. -/
theorem exists_section_lift_of_closedPoint_mem {X P : Over (Spec (CommRingCat.of R))}
    (j : P ⟶ X) [IsOpenImmersion j.left]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X)
    (hx : x.left (IsLocalRing.closedPoint R) ∈ Set.range j.left) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ P, y ≫ j = x := by
  have hrange : Set.range x.left ⊆ Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map x.left.continuous).mem_open
      (IsOpenImmersion.isOpen_range j.left) hx
  let y := IsOpenImmersion.lift j.left x.left hrange
  have hy : y ≫ j.left = x.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk y ?_, ?_⟩
  · change y ≫ P.hom = 𝟙 _
    rw [← Over.w j, ← Category.assoc, hy, Over.w x]
    rfl
  · ext1
    exact hy

/-- An integral section with trivial reduction has its closed point at the closed point of the
identity section. -/
theorem closedPoint_eq_one_of_reduction_eq_one (M : IntegralModel R K G)
    (x : M.integralSections) (hx : M.reduction x = 1) :
    x.left (IsLocalRing.closedPoint R) =
      (1 : M.integralSections).left (IsLocalRing.closedPoint R) := by
  rw [← specialFibreProjection_reduction, ← specialFibreProjection_reduction, hx, map_one]

end Local

section Ordered

variable {n : ℕ} {H : Fin n → GroupScheme (Spec (CommRingCat.of K))}
  {M : ∀ i, IntegralModel R K (H i)} {N : IntegralModel R K G}
  {g : ∀ i, H i ⟶ G}

/-- The generic point of an ordered product of integral sections is the ordered product of
their generic points. -/
theorem integralPointMap_orderedPoints (p : ∀ i, (M i).Hom N (g i))
    (y : ∀ i, (M i).integralSections) :
    N.integralPointMap (RelativeRoot.orderedPoints (fun i => (p i).hom) y) =
      (List.ofFn fun i => rationalPoints.map (g i) ((M i).integralPointMap (y i))).prod := by
  unfold RelativeRoot.orderedPoints
  change N.integralPointMap
      (List.ofFn fun i => rationalPoints.map (p i).hom (y i)).prod = _
  rw [map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact (p i).integralPointMap_naturality (y i)

/-- The identity section lies in the range of an ordered multiplication of group
homomorphisms. -/
theorem one_eq_comp_orderedMultiplication (p : ∀ i, (M i).group ⟶ N.group) :
    (1 : N.integralSections) =
      (RelativeRoot.finiteProductPointsEquiv (fun i => (M i).group)
          (Over.mk (𝟙 (Spec (CommRingCat.of R))))).symm 1 ≫
        RelativeRoot.orderedMultiplication p := by
  rw [RelativeRoot.finiteProductPointsEquiv_symm_orderedMultiplication]
  unfold RelativeRoot.orderedPoints
  symm
  apply List.prod_eq_one
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact MonObj.one_comp _

variable [IsLocalRing R]
  {H' : Fin n → GroupScheme (Spec (CommRingCat.of K))}
  {M' : ∀ i, IntegralModel R K (H' i)} {N' : IntegralModel R K G}
  {g' : ∀ i, H' i ⟶ G}

/-- **Integral sections over the special-fibre kernel lie in an ordered open cell.** Let `R`
be a local domain with fraction field `K`, and `ψ : N' → N` a model morphism with identity
generic fibre. Let `p i : M i → N` and `p' i : M' i → N'` be model morphisms over
`g i : H i → G` and `g' i : H' i → G`, such that the ordered multiplication of the `p i` is an
open immersion. Assume the factorization property: whenever generic points `h i` lie in the
images of the integral points of the `M i` and their ordered product is an integral point of
`N'`, each `h i` lies in the image of the integral points of `M' i`. Then every integral
section `x` of `N'` whose image in `N` reduces to the identity has its closed point in the
range of the ordered multiplication of the `p' i`. -/
theorem closedPoint_mem_range_orderedMultiplication (ψ : N'.Hom N (𝟙 G))
    (p : ∀ i, (M i).Hom N (g i)) (p' : ∀ i, (M' i).Hom N' (g' i))
    [IsOpenImmersion (RelativeRoot.orderedMultiplication fun i => (p i).hom).left]
    (hfac : ∀ h : Fin n → rationalPoints G,
      (∀ i, h i ∈ (M i).integralPoints.map (rationalPoints.map (g i))) →
      (List.ofFn h).prod ∈ N'.integralPoints →
      ∀ i, h i ∈ (M' i).integralPoints.map (rationalPoints.map (g' i)))
    (x : N'.integralSections) (hx : N.reduction (rationalPoints.map ψ.hom x) = 1) :
    x.left (IsLocalRing.closedPoint R) ∈
      Set.range (RelativeRoot.orderedMultiplication fun i => (p' i).hom).left := by
  have hmem : (rationalPoints.map ψ.hom x).left (IsLocalRing.closedPoint R) ∈
      Set.range (RelativeRoot.orderedMultiplication fun i => (p i).hom).left := by
    rw [closedPoint_eq_one_of_reduction_eq_one N _ hx,
      one_eq_comp_orderedMultiplication (fun i => (p i).hom)]
    exact ⟨_, rfl⟩
  obtain ⟨yt, hyt⟩ := exists_section_lift_of_closedPoint_mem _ _ hmem
  let y := RelativeRoot.finiteProductPointsEquiv (fun i => (M i).group) _ yt
  have hgen : N'.integralPointMap x =
      (List.ofFn fun i => rationalPoints.map (g i) ((M i).integralPointMap (y i))).prod := by
    rw [← integralPointMap_orderedPoints p y, ← RelativeRoot.comp_orderedMultiplication, hyt,
      ψ.integralPointMap_naturality]
    rfl
  have hB := hfac (fun i => rationalPoints.map (g i) ((M i).integralPointMap (y i)))
    (fun i => ⟨_, ⟨y i, rfl⟩, rfl⟩) ⟨x, hgen⟩
  choose w hw hwg using hB
  choose z hz using hw
  have hx' : ((RelativeRoot.finiteProductPointsEquiv (fun i => (M' i).group) _).symm z ≫
      RelativeRoot.orderedMultiplication fun i => (p' i).hom) = x := by
    apply N'.integralPointMap_injective
    rw [hgen, RelativeRoot.finiteProductPointsEquiv_symm_orderedMultiplication,
      integralPointMap_orderedPoints p' z]
    congr 1
    apply congrArg List.ofFn
    funext i
    rw [hz i, hwg i]
  rw [← hx']
  exact ⟨_, rfl⟩

end Ordered

end Langlands.GroupScheme.IntegralModel

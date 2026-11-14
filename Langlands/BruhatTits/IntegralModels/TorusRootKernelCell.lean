import Langlands.BruhatTits.IntegralModels.TorusRootModelFamily
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelOrderedCell

/-! # Killed integral sections in the ordered torus/root chart -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)

/-- The subgroup of `G(K)` attached to one slot of a torus/root enumeration: the image
`T(K)^0` of the torus Iwahori subgroup for the torus slot `none`, and the root fixer
`U_{a,Ω,0}` for the root slot `some a`. -/
def orderedFactorImage (Ω : Set C.Apartment) :
    Option (relativeRoots C.i) → Subgroup (rationalPoints G)
  | none => E.torusIwahori.map (rationalPoints.map E.i)
  | some a => C.rootFixer a Ω

/-- **Ordered fixer factorization.** For an enumeration `e` of torus and root slots and
two subsets `Ω, Ω'` of the apartment: whenever elements `h i` lie in the slot subgroups
for `Ω` and their ordered product lies in `G(K)^0 ∩ G(K)_{Ω'}`, every `h i` lies in the
slot subgroup for `Ω'`. This is the property used in the proof of KP Proposition 8.4.15;
it is a hypothesis here, not a theorem. -/
def OrderedFixerFactorization {n : ℕ} (e : Fin n → Option (relativeRoots C.i))
    (Ω Ω' : Set C.Apartment) : Prop :=
  ∀ h : Fin n → rationalPoints G,
    (∀ i, h i ∈ orderedFactorImage C E Ω (e i)) →
    (List.ofFn h).prod ∈ E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω') →
    ∀ i, h i ∈ orderedFactorImage C E Ω' (e i)

namespace TorusRootModelFamilyData

variable {C E} {x : C.Apartment} {Ω Ω' : Set C.Apartment}
  {N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G}

/-- For a nonempty affine-bounded `Ω`, the generic image of the integral points of each
factor model of a torus/root family is the corresponding slot subgroup. -/
theorem integralImage_eq (A : TorusRootModelFamilyData C E x Ω N) (hne : Ω.Nonempty)
    (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    ∀ j : Option (relativeRoots C.i),
      (A.model j).integralPoints.map (rationalPoints.map (A.genericMap j)) =
        orderedFactorImage C E Ω j
  | none => by
    change A.torusModel.integralPoints.map (rationalPoints.map E.i) = _
    rw [A.torusPoints_eq]
    rfl
  | some a =>
    (A.rootModel a).integralPoints_eq.trans
      (C.apartment.rootFixer_eq_filtration_of_bounded a x hne hb).symm

variable (A : TorusRootModelFamilyData C E x Ω N)
  (B : TorusRootModelFamilyData C E x Ω' N')
  {n : ℕ} (e : Fin n → Option (relativeRoots C.i))
  (ψ : N'.Hom N (𝟙 G))

/-- **Killed integral sections lie in the ordered chart of the smaller model.** Let `A`
and `B` be torus/root families for `N` (over `Ω`) and `N'` (over `Ω'`), with nonempty
affine-bounded `Ω` and `Ω'`, let `ψ : N' → N` have identity generic fibre, and suppose the
ordered multiplication of `A`'s factor maps along `e` is an open immersion. If the integral
points of `N'` lie in `G(K)^0 ∩ G(K)_{Ω'}` and the ordered fixer factorization holds for
`e`, `Ω`, `Ω'`, then every integral section of `N'` whose image in `N` reduces to the
identity has its closed point in the range of the ordered multiplication of `B`'s factor
maps along `e`. -/
theorem closedPoint_mem_range_orderedChart
    [IsOpenImmersion (RelativeRoot.orderedMultiplication
      (fun i => (A.modelMap (e i)).hom)).left]
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hne' : Ω'.Nonempty) (hb' : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω'))
    (hN' : N'.integralPoints ≤ E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (hfac : OrderedFixerFactorization C E e Ω Ω') :
    ∀ s : N'.integralSections,
      N.reduction (rationalPoints.map ψ.hom s) = 1 →
        s.left (IsLocalRing.closedPoint (fixedFieldIntegers F)) ∈
          Set.range (RelativeRoot.orderedMultiplication
            (fun i => (B.modelMap (e i)).hom)).left := by
  intro s hs
  refine IntegralModel.closedPoint_mem_range_orderedMultiplication
    (M := fun i => A.model (e i)) (M' := fun i => B.model (e i))
    (g := fun i => A.genericMap (e i)) (g' := fun i => B.genericMap (e i))
    ψ (fun i => A.modelMap (e i)) (fun i => B.modelMap (e i)) ?_ s hs
  intro h hA hprod i
  rw [B.integralImage_eq hne' hb' (e i)]
  refine hfac h (fun j => ?_) (hN' hprod) i
  rw [← A.integralImage_eq hne hb (e j)]
  exact hA j

end TorusRootModelFamilyData

end Langlands.BruhatTits.IntegralModels

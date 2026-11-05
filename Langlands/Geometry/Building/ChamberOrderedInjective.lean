import Langlands.Geometry.Building.ChamberFiltration
import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.GroupScheme.Rational.OrderedProductPoints
import Langlands.GroupScheme.RepresentedSubgroup

/-!
# Ordered chamber and facet block embeddings from the Dynamic root product

Monic ordered multiplication distinguishes every root factor on every test.
Restricting to the actual chamber and facet blocks gives injective products.
The Dynamic ordered root product statement remains an explicit premise.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme.RelativeRoot

/-- A monic ordered multiplication of representing group schemes is injective
on the actual subgroup points, for every test scheme. -/
theorem orderedSubgroupPoints_injective_of_mono
    {B : Scheme.{u}} {G : GroupScheme B} {n : ℕ}
    {H : Fin n → GroupScheme B} (j : ∀ r, H r ⟶ G)
    (F : Fin n → SubgroupFunctor G)
    (hH : ∀ r, (F r).IsRepresentedBy (j r))
    [Mono (orderedMultiplication j)] (T : Over B) :
    Function.Injective (fun x : ∀ r, (F r).carrier T =>
      (List.ofFn fun r => (x r : T ⟶ G.X)).prod) := by
  let lift (x : ∀ r, (F r).carrier T) : T ⟶ (∏ᶜ H).X :=
    (finiteProductPointsEquiv H T).symm
      (fun r => ((hH r).pointsEquiv T).symm (x r))
  have hlift (x : ∀ r, (F r).carrier T) :
      lift x ≫ orderedMultiplication j =
        (List.ofFn fun r => (x r : T ⟶ G.X)).prod := by
    simp only [lift, finiteProductPointsEquiv_symm_orderedMultiplication,
      orderedPoints, SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
  intro x y hxy
  have hxy' : lift x = lift y := (cancel_mono (orderedMultiplication j)).mp
    (by rw [hlift, hlift]; exact hxy)
  funext r
  apply Subtype.ext
  have hcoords := congrArg
    (fun z : T ⟶ (∏ᶜ H).X =>
      (z ≫ (Pi.π H r).hom.hom) ≫ (j r).hom.hom) hxy'
  simpa only [lift, finiteProductPointsEquiv_symm_π,
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp] using hcoords

/-- The Dynamic ordered root product statement gives injectivity on every
test scheme, for every ordering of the indivisible positive roots. -/
theorem orderedRootSubgroupPoints_injective_of_statement
    (hprod : DynamicRootOrderedProductStatement.{u})
    {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Function.Injective a)
    (hrange : Set.range a = indivisiblePositiveRoots i ν)
    (T : Over (Spec (CommRingCat.of k))) :
    Function.Injective
      (fun x : ∀ r, (subgroup i (a r)).carrier T =>
        (List.ofFn fun r => (x r : T ⟶ G.X)).prod) := by
  obtain ⟨U, jU, H, j, e, hU, -, -, -, -, -, hH, he⟩ :=
    hprod k G hG S i hi ν n a ha hrange
  have : Mono jU.hom.hom := hU.1
  have : Mono (orderedMultiplication j) := by
    rw [← he]
    infer_instance
  exact orderedSubgroupPoints_injective_of_mono j
    (fun r => subgroup i (a r)) (fun r => (hH r).1) T

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Each actual chamber block lies in its corresponding actual root group,
including the retained doubled-root factor and either depth. -/
theorem chamberRootBlock_subset_rootGroupPoints (x : D.Apartment) (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.chamberRootBlock x strict a ⊆ rootGroupPoints i a := by
  rw [D.chamberRootBlock_eq_rootGroup x strict ha]
  change D.chamberRootGroup x strict a ≤ rootGroupPoints i a
  cases strict with
  | false => exact D.filtration_le_rootGroupPoints x a 0
  | true => exact D.filtrationPlus_le_rootGroupPoints x a 0

/-- The corresponding root-group containment for both actual facet blocks
holds for arbitrary subsets, including the empty subset. -/
theorem facetRootBlock_subset_rootGroupPoints (Fa : Set D.Apartment) (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.facetRootBlock Fa strict a ⊆ rootGroupPoints i a := by
  rw [D.facetRootBlock_eq_rootGroup Fa strict ha]
  change D.facetRootGroup Fa strict a ≤ rootGroupPoints i a
  cases strict <;> exact inf_le_left

private theorem orderedSubsetProduct_injective {n : ℕ}
    (a : Fin n → characterLattice S)
    (hinj : Function.Injective (fun x : ∀ r, rootGroupPoints i (a r) =>
      (List.ofFn fun r => (x r : rationalPoints G)).prod))
    (B : Fin n → Set (rationalPoints G))
    (hB : ∀ r, B r ⊆ rootGroupPoints i (a r)) :
    Function.Injective (fun x : ∀ r, B r =>
      (List.ofFn fun r => (x r : rationalPoints G)).prod) := by
  let f (x : ∀ r, B r) : ∀ r, rootGroupPoints i (a r) :=
    fun r => ⟨x r, hB r (x r).property⟩
  intro x y hxy
  have hf : f x = f y := hinj hxy
  funext r
  exact Subtype.ext (congrArg (fun z => (z r : rationalPoints G)) hf)

/-- Conditional injectivity of the existing chamber block product, at either
depth and for every ordering of the indivisible positive roots. -/
theorem orderedChamberBlockProduct_injective_of_dynamicRootOrderedProduct
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Function.Injective (D.orderedChamberBlockProduct x strict a) := by
  apply orderedSubsetProduct_injective a
    (RelativeRoot.orderedRootSubgroupPoints_injective_of_statement
      hprod hG hi ν a ha hrange (Over.mk (𝟙 _)))
    (fun r => D.chamberRootBlock x strict (a r))
  intro r
  have hr : a r ∈ RelativeRoot.indivisiblePositiveRoots i ν := hrange ▸ Set.mem_range_self r
  exact D.chamberRootBlock_subset_rootGroupPoints x strict hr.1.1

/-- Conditional injectivity of the actual facet block product, at either
depth, without imposing a facet or chamber geometry premise. -/
theorem orderedFacetBlockProduct_injective_of_dynamicRootOrderedProduct
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (Fa : Set D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Function.Injective (D.orderedFacetBlockProduct Fa strict a) := by
  apply orderedSubsetProduct_injective a
    (RelativeRoot.orderedRootSubgroupPoints_injective_of_statement
      hprod hG hi ν a ha hrange (Over.mk (𝟙 _)))
    (fun r => D.facetRootBlock Fa strict (a r))
  intro r
  have hr : a r ∈ RelativeRoot.indivisiblePositiveRoots i ν := hrange ▸ Set.mem_range_self r
  exact D.facetRootBlock_subset_rootGroupPoints Fa strict hr.1.1

/-- The unchanged chamber product as an embedding under the explicit
Dynamic root product premise. -/
def orderedChamberBlockProductEmbedding
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    (∀ r, D.chamberRootBlock x strict (a r)) ↪ rationalPoints G where
  toFun := D.orderedChamberBlockProduct x strict a
  inj' := D.orderedChamberBlockProduct_injective_of_dynamicRootOrderedProduct
    hprod hG hi x strict ν a ha hrange

/-- The unchanged facet product as an embedding under the same explicit
Dynamic root product premise. -/
def orderedFacetBlockProductEmbedding
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (Fa : Set D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    (∀ r, D.facetRootBlock Fa strict (a r)) ↪ rationalPoints G where
  toFun := D.orderedFacetBlockProduct Fa strict a
  inj' := D.orderedFacetBlockProduct_injective_of_dynamicRootOrderedProduct
    hprod hG hi Fa strict ν a ha hrange

end Langlands.Geometry.Building.KPApartmentData

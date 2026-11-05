import Langlands.Geometry.Building.ChamberOrderedInjective
import Langlands.Geometry.Building.ChamberProductInjective
import Langlands.GroupScheme.Rational.RootSubgroupPositive

/-!
# Injectivity of ordered sharp and full chamber products

Ordered products of positive root blocks lie in the corresponding Dynamic
unipotent group. Three-factor uniqueness then distinguishes the negative,
central and positive coordinates. The Dynamic ordered root product statement
remains explicit and supplies only the injectivity within each sign.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section Restriction

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Injective maps into opposite Dynamic unipotent groups retain three-factor
uniqueness with any injectively mapped central factor. -/
theorem unipotentTripleProduct_injective_of_maps
    {A Z B : Type u} (f : A → rationalPoints G) (j : Z → rationalPoints G)
    (g : B → rationalPoints G)
    (hf : Function.Injective f) (hj : Function.Injective j) (hg : Function.Injective g)
    (hminus : ∀ a, f a ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _)))
    (hplus : ∀ b, g b ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hcentral : ∀ z, j z ∈ centralizerPoints i) :
    Function.Injective (fun p : A × Z × B => f p.1 * j p.2.1 * g p.2.2) := by
  let Uminus := (Dynamic.unipotent
    (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _))
  let Uplus := (Dynamic.unipotent
    (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))
  let lift (p : A × Z × B) : Uminus × Z × Uplus :=
    (⟨f p.1, hminus p.1⟩, p.2.1, ⟨g p.2.2, hplus p.2.2⟩)
  have hinj := unipotentTripleProduct_injective i ν Uminus Uplus j hj
    le_rfl le_rfl hcentral
  intro p q hpq
  have h : lift p = lift q := hinj hpq
  exact Prod.ext
    (hf (congrArg (fun r : Uminus × Z × Uplus => (r.1 : rationalPoints G)) h))
    (Prod.ext (congrArg (fun r : Uminus × Z × Uplus => r.2.1) h)
      (hg (congrArg (fun r : Uminus × Z × Uplus => (r.2.2 : rationalPoints G)) h)))

omit [IsAffineHom G.X.hom] in
/-- An ordered product of subsets of positive root groups lies in the
corresponding Dynamic unipotent subgroup. No factorization premise is needed. -/
theorem orderedRootSubsetProduct_mem_dynamicUnipotent
    {n : ℕ} (a : Fin n → characterLattice S)
    (hpos : ∀ r, 0 < latticePairing S (a r) ν)
    (B : Fin n → Set (rationalPoints G))
    (hB : ∀ r, B r ⊆ rootGroupPoints i (a r))
    (v : ∀ r, B r) :
    (List.ofFn fun r => (v r : rationalPoints G)).prod ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hg
  exact RelativeRoot.subgroup_le_dynamicUnipotent i ν (hpos r)
    (Over.mk (𝟙 _)) (hB r (v r).property)

end Restriction

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The actual chamber block product lies in the Dynamic unipotent group
whenever all indicated roots have positive pairing. -/
theorem orderedChamberBlockProduct_mem_dynamicUnipotent
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hroot : ∀ r, a r ∈ relativeRoots i)
    (hpos : ∀ r, 0 < latticePairing S (a r) ν)
    (v : ∀ r, D.chamberRootBlock x strict (a r)) :
    D.orderedChamberBlockProduct x strict a v ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :=
  orderedRootSubsetProduct_mem_dynamicUnipotent i ν a hpos
    (fun r => D.chamberRootBlock x strict (a r))
    (fun r => D.chamberRootBlock_subset_rootGroupPoints x strict (hroot r)) v

/-- The same containment for the actual facet blocks, including empty
subsets and either Boolean depth. -/
theorem orderedFacetBlockProduct_mem_dynamicUnipotent
    (Fa : Set D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hroot : ∀ r, a r ∈ relativeRoots i)
    (hpos : ∀ r, 0 < latticePairing S (a r) ν)
    (v : ∀ r, D.facetRootBlock Fa strict (a r)) :
    D.orderedFacetBlockProduct Fa strict a v ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :=
  orderedRootSubsetProduct_mem_dynamicUnipotent i ν a hpos
    (fun r => D.facetRootBlock Fa strict (a r))
    (fun r => D.facetRootBlock_subset_rootGroupPoints Fa strict (hroot r)) v

/-- Conditional injectivity of the unchanged ordered sharp chamber map,
for both depths and arbitrary orders separately within each sign. -/
theorem orderedSharpChamberProduct_injective_of_dynamicRootOrderedProduct
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice S)
    (apos : Fin npos → characterLattice S)
    (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots i ν) :
    Function.Injective (D.orderedSharpChamberProduct x strict aneg apos) := by
  have hn r : aneg r ∈ RelativeRoot.indivisiblePositiveRoots i (-ν) :=
    hrneg ▸ Set.mem_range_self r
  have hp r : apos r ∈ RelativeRoot.indivisiblePositiveRoots i ν :=
    hrpos ▸ Set.mem_range_self r
  exact unipotentTripleProduct_injective_of_maps i ν
    (D.orderedChamberBlockProduct x strict aneg)
    (fun z : D.sharpCentralizer {x} => (z : rationalPoints G))
    (D.orderedChamberBlockProduct x strict apos)
    (D.orderedChamberBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod hG hi x strict (-ν) aneg haneg hrneg)
    Subtype.val_injective
    (D.orderedChamberBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod hG hi x strict ν apos hapos hrpos)
    (D.orderedChamberBlockProduct_mem_dynamicUnipotent x strict (-ν) aneg
      (fun r => (hn r).1.1) (fun r => (hn r).2))
    (D.orderedChamberBlockProduct_mem_dynamicUnipotent x strict ν apos
      (fun r => (hp r).1.1) (fun r => (hp r).2))
    (fun z => z.property.1)

/-- Conditional injectivity of the unchanged sharp facet map, with negative
depth `0+`, positive depth `0` and the original sharp central factor. -/
theorem orderedSharpFacetProduct_injective_of_dynamicRootOrderedProduct
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (Fa : Set D.Apartment) (x : D.Apartment) (ν : cocharacterLattice S)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice S)
    (apos : Fin npos → characterLattice S)
    (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots i ν) :
    Function.Injective (D.orderedSharpFacetProduct Fa x aneg apos) := by
  have hn r : aneg r ∈ RelativeRoot.indivisiblePositiveRoots i (-ν) :=
    hrneg ▸ Set.mem_range_self r
  have hp r : apos r ∈ RelativeRoot.indivisiblePositiveRoots i ν :=
    hrpos ▸ Set.mem_range_self r
  exact unipotentTripleProduct_injective_of_maps i ν
    (D.orderedFacetBlockProduct Fa true aneg)
    (fun z : D.sharpCentralizer {x} => (z : rationalPoints G))
    (D.orderedFacetBlockProduct Fa false apos)
    (D.orderedFacetBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod hG hi Fa true (-ν) aneg haneg hrneg)
    Subtype.val_injective
    (D.orderedFacetBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod hG hi Fa false ν apos hapos hrpos)
    (D.orderedFacetBlockProduct_mem_dynamicUnipotent Fa true (-ν) aneg
      (fun r => (hn r).1.1) (fun r => (hn r).2))
    (D.orderedFacetBlockProduct_mem_dynamicUnipotent Fa false ν apos
      (fun r => (hp r).1.1) (fun r => (hp r).2))
    (fun z => z.property.1)

end KPApartmentData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

private theorem centralizerZero_map_injective :
    Function.Injective
      (fun z : P.centralizerZero => rationalPoints.map P.centralizer.j z) := by
  intro z w h
  apply Subtype.ext
  have : Mono P.centralizer.j.hom.hom := P.centralizer.isRepresentedBy.1
  exact (cancel_mono P.centralizer.j.hom.hom).mp h

/-- Conditional injectivity of the actual full ordered chamber map, retaining
`Z(F)^0` and its actual representing inclusion. -/
theorem orderedIwahoriChamberProduct_injective_of_dynamicRootOrderedProduct
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (x : P.Apartment) (strict : Bool) (ν : cocharacterLattice P.S)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S)
    (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν) :
    Function.Injective (P.orderedIwahoriChamberProduct x strict aneg apos) := by
  have hn r : aneg r ∈ RelativeRoot.indivisiblePositiveRoots P.i (-ν) :=
    hrneg ▸ Set.mem_range_self r
  have hp r : apos r ∈ RelativeRoot.indivisiblePositiveRoots P.i ν :=
    hrpos ▸ Set.mem_range_self r
  exact unipotentTripleProduct_injective_of_maps P.i ν
    (P.apartment.orderedChamberBlockProduct x strict aneg)
    (fun z : P.centralizerZero => rationalPoints.map P.centralizer.j z)
    (P.apartment.orderedChamberBlockProduct x strict apos)
    (P.apartment.orderedChamberBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod P.isConnectedReductive P.isMaximalSplitTorus x strict (-ν) aneg haneg hrneg)
    (P.centralizerZero_map_injective)
    (P.apartment.orderedChamberBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod P.isConnectedReductive P.isMaximalSplitTorus x strict ν apos hapos hrpos)
    (P.apartment.orderedChamberBlockProduct_mem_dynamicUnipotent x strict (-ν) aneg
      (fun r => (hn r).1.1) (fun r => (hn r).2))
    (P.apartment.orderedChamberBlockProduct_mem_dynamicUnipotent x strict ν apos
      (fun r => (hp r).1.1) (fun r => (hp r).2))
    (fun z => map_mem_centralizerPoints P.centralizer.isRepresentedBy z)

/-- Conditional injectivity of the actual full ordered facet map with its
prescribed mixed depths and unchanged centralizer-zero subtype. -/
theorem orderedIwahoriFacetProduct_injective_of_dynamicRootOrderedProduct
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (Fa : Set P.Apartment) (ν : cocharacterLattice P.S)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S)
    (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν) :
    Function.Injective (P.orderedIwahoriFacetProduct Fa aneg apos) := by
  have hn r : aneg r ∈ RelativeRoot.indivisiblePositiveRoots P.i (-ν) :=
    hrneg ▸ Set.mem_range_self r
  have hp r : apos r ∈ RelativeRoot.indivisiblePositiveRoots P.i ν :=
    hrpos ▸ Set.mem_range_self r
  exact unipotentTripleProduct_injective_of_maps P.i ν
    (P.apartment.orderedFacetBlockProduct Fa true aneg)
    (fun z : P.centralizerZero => rationalPoints.map P.centralizer.j z)
    (P.apartment.orderedFacetBlockProduct Fa false apos)
    (P.apartment.orderedFacetBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod P.isConnectedReductive P.isMaximalSplitTorus Fa true (-ν) aneg haneg hrneg)
    (P.centralizerZero_map_injective)
    (P.apartment.orderedFacetBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod P.isConnectedReductive P.isMaximalSplitTorus Fa false ν apos hapos hrpos)
    (P.apartment.orderedFacetBlockProduct_mem_dynamicUnipotent Fa true (-ν) aneg
      (fun r => (hn r).1.1) (fun r => (hn r).2))
    (P.apartment.orderedFacetBlockProduct_mem_dynamicUnipotent Fa false ν apos
      (fun r => (hp r).1.1) (fun r => (hp r).2))
    (fun z => map_mem_centralizerPoints P.centralizer.isRepresentedBy z)

/-- The original full ordered chamber map as an embedding, under the explicit
Dynamic root product premise. -/
def orderedIwahoriChamberProductEmbedding
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (x : P.Apartment) (strict : Bool) (ν : cocharacterLattice P.S)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S)
    (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν) :
    ((∀ r, P.apartment.chamberRootBlock x strict (aneg r)) ×
      P.centralizerZero × (∀ r, P.apartment.chamberRootBlock x strict (apos r))) ↪
      rationalPoints G where
  toFun := P.orderedIwahoriChamberProduct x strict aneg apos
  inj' := P.orderedIwahoriChamberProduct_injective_of_dynamicRootOrderedProduct
    hprod x strict ν aneg apos haneg hrneg hapos hrpos

end ParahoricBuildingData

end Langlands.Geometry.Building

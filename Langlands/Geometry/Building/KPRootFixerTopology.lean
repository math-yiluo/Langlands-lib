import Langlands.Geometry.Building.KPFiltrationTopology
import Langlands.Geometry.Building.ChamberRootProducts

/-! # Compact root-fixer intersections and finite root products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance kpRootFixerTopologyAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance kpRootFixerTopologyAmbient : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable (B : ValuationBuildingData G)
  (hB : B.apartment.IsTopologyCompatible)

include hB

/-- The strict-depth subgroup is open in the actual root group, with its
canonical ambient subspace topology. -/
def filtrationPlusOpenSubgroup (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    OpenSubgroup (B.rootGroup a) where
  toSubgroup := (B.filtrationPlus x a r).subgroupOf (B.rootGroup a)
  isOpen' := by
    let : Smooth G.X.hom := B.isConnectedReductive.smooth
    let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    apply Subgroup.isOpen_mono (H₁ := (B.filtration x a (r + 1)).subgroupOf _)
    · intro g hg
      exact B.apartment.filtration_le_filtrationPlus x a (lt_add_one r) hg
    · exact (B.filtrationOpenSubgroup hB x a (r + 1)).isOpen

/-- Strict-depth root groups are closed in the ambient rational-point group. -/
theorem isClosed_filtrationPlus (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    IsClosed (B.filtrationPlus x a r : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have he := (B.isClosed_rootGroup a).isClosedEmbedding_subtypeVal
  refine (he.isClosed_iff_preimage_isClosed ?_).2 ?_
  · intro g hg
    exact ⟨⟨g, B.apartment.filtrationPlus_le_rootGroupPoints x a r hg⟩, rfl⟩
  · exact (B.filtrationPlusOpenSubgroup hB x a r).isClosed

/-- Strict-depth root groups are closed subsets of the compact weak-depth groups. -/
theorem isCompact_filtrationPlus (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    IsCompact (B.filtrationPlus x a r : Set (rationalPoints G)) :=
  (B.isCompact_filtration hB x a r).of_isClosed_subset
    (B.isClosed_filtrationPlus hB x a r)
    (B.apartment.filtrationPlus_le_filtration x a r)

/-- Any intersection of actual weak-depth root groups is ambient closed. -/
theorem isClosed_rootFixer (a : relativeRoots B.i) (Ω : Set B.Apartment) :
    IsClosed (B.rootFixer a Ω : Set (rationalPoints G)) := by
  change IsClosed
    ((B.rootGroup a : Set (rationalPoints G)) ∩
      (↑(⨅ x ∈ Ω, B.filtration x a 0) : Set (rationalPoints G)))
  simp only [Subgroup.coe_iInf]
  exact (B.isClosed_rootGroup a).inter
    (isClosed_iInter fun x => isClosed_iInter fun _ => B.isClosed_filtration hB x a 0)

/-- A root fixer of a nonempty apartment subset is compact, without a facet assumption. -/
theorem isCompact_rootFixer (a : relativeRoots B.i)
    {Ω : Set B.Apartment} {x : B.Apartment} (hx : x ∈ Ω) :
    IsCompact (B.rootFixer a Ω : Set (rationalPoints G)) :=
  (B.isCompact_filtration hB x a 0).of_isClosed_subset
    (B.isClosed_rootFixer hB a Ω)
    (fun _ hg => (B.apartment.mem_rootFixer.mp hg).2 x hx)

/-- Any intersection of actual strict-depth root groups is ambient closed. -/
theorem isClosed_rootFixerPlus (a : relativeRoots B.i) (Ω : Set B.Apartment) :
    IsClosed (B.rootFixerPlus a Ω : Set (rationalPoints G)) := by
  change IsClosed
    ((B.rootGroup a : Set (rationalPoints G)) ∩
      (↑(⨅ x ∈ Ω, B.filtrationPlus x a 0) : Set (rationalPoints G)))
  simp only [Subgroup.coe_iInf]
  exact (B.isClosed_rootGroup a).inter
    (isClosed_iInter fun x => isClosed_iInter fun _ => B.isClosed_filtrationPlus hB x a 0)

/-- The strict root fixer of a nonempty apartment subset is compact. -/
theorem isCompact_rootFixerPlus (a : relativeRoots B.i)
    {Ω : Set B.Apartment} {x : B.Apartment} (hx : x ∈ Ω) :
    IsCompact (B.rootFixerPlus a Ω : Set (rationalPoints G)) :=
  (B.isCompact_rootFixer hB a hx).of_isClosed_subset
    (B.isClosed_rootFixerPlus hB a Ω) (B.rootFixerPlus_le_rootFixer a Ω)

/-- Both point-block depths have compact carriers, retaining the doubled-root factor. -/
theorem isCompact_chamberRootBlock
    (x : B.Apartment) (strict : Bool) (a : relativeRoots B.i) :
    IsCompact (B.apartment.chamberRootBlock x strict a) := by
  classical
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  cases strict with
  | false => exact B.isCompact_filtrationBlock hB x (fun _ => 0) a
  | true =>
    change IsCompact
      ((B.filtrationPlus x a 0 : Set (rationalPoints G)) *
        (↑(if 2 • (a : characterLattice B.S) ∈ relativeRoots B.i then
          B.filtrationPlus x (2 • (a : characterLattice B.S)) 0 else ⊥) :
          Set (rationalPoints G)))
    apply (B.isCompact_filtrationPlus hB x a 0).mul
    split_ifs with ha
    · exact B.isCompact_filtrationPlus hB x ⟨_, ha⟩ 0
    · simpa only [Subgroup.coe_bot] using isCompact_singleton (x := (1 : rationalPoints G))

/-- Both facet-block depths are compact on every nonempty apartment subset. -/
theorem isCompact_facetRootBlock
    {Ω : Set B.Apartment} {x : B.Apartment} (hx : x ∈ Ω)
    (strict : Bool) (a : relativeRoots B.i) :
    IsCompact (B.apartment.facetRootBlock Ω strict a) := by
  classical
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hc (b : relativeRoots B.i) :
      IsCompact (B.apartment.facetRootGroup Ω strict b : Set (rationalPoints G)) := by
    cases strict with
    | false => exact B.isCompact_rootFixer hB b hx
    | true => exact B.isCompact_rootFixerPlus hB b hx
  unfold KPApartmentData.facetRootBlock
  apply (hc a).mul
  split_ifs with ha
  · exact hc ⟨_, ha⟩
  · simpa only [Subgroup.coe_bot] using isCompact_singleton (x := (1 : rationalPoints G))

omit hB in
private theorem continuous_orderedSubtypeProduct (B : ValuationBuildingData G)
    {n : ℕ} (s : Fin n → Set (rationalPoints G)) :
    Continuous (fun p : ∀ j, s j =>
      (List.ofFn fun j => (p j : rationalPoints G)).prod) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  simpa only [List.map_ofFn, Function.comp_def] using
    (continuous_list_prod (List.ofFn (fun j : Fin n => j))
      (f := fun j (p : ∀ j, s j) => (p j : rationalPoints G))
      (fun j _ => continuous_subtype_val.comp (continuous_apply j)))

omit hB in
/-- Finite ordered filtration multiplication is continuous in its actual factors. -/
theorem continuous_orderedFiltrationBlockProduct
    (x : B.Apartment) (f : characterLattice B.S → ℝ)
    {n : ℕ} (a : Fin n → characterLattice B.S) :
    Continuous (B.apartment.orderedFiltrationBlockProduct x f a) :=
  B.continuous_orderedSubtypeProduct (fun j => B.apartment.filtrationBlock x f (a j))

omit hB in
/-- Finite ordered chamber multiplication is continuous at both depths. -/
theorem continuous_orderedChamberBlockProduct
    (x : B.Apartment) (strict : Bool)
    {n : ℕ} (a : Fin n → characterLattice B.S) :
    Continuous (B.apartment.orderedChamberBlockProduct x strict a) :=
  B.continuous_orderedSubtypeProduct (fun j => B.apartment.chamberRootBlock x strict (a j))

omit hB in
/-- Finite ordered facet multiplication is continuous for every apartment subset. -/
theorem continuous_orderedFacetBlockProduct
    (Ω : Set B.Apartment) (strict : Bool)
    {n : ℕ} (a : Fin n → characterLattice B.S) :
    Continuous (B.apartment.orderedFacetBlockProduct Ω strict a) :=
  B.continuous_orderedSubtypeProduct (fun j => B.apartment.facetRootBlock Ω strict (a j))

/-- The range of each actual finite ordered filtration product is compact. -/
theorem isCompact_range_orderedFiltrationBlockProduct
    (x : B.Apartment) (f : characterLattice B.S → ℝ)
    {n : ℕ} (a : Fin n → relativeRoots B.i) :
    IsCompact (Set.range
      (B.apartment.orderedFiltrationBlockProduct x f (fun j => (a j : characterLattice B.S)))) := by
  let (j : Fin n) : CompactSpace (B.apartment.filtrationBlock x f (a j)) :=
    isCompact_iff_compactSpace.mp (B.isCompact_filtrationBlock hB x f (a j))
  exact isCompact_range (B.continuous_orderedFiltrationBlockProduct x f _)

/-- The range of each finite ordered chamber product is compact at either depth. -/
theorem isCompact_range_orderedChamberBlockProduct
    (x : B.Apartment) (strict : Bool)
    {n : ℕ} (a : Fin n → relativeRoots B.i) :
    IsCompact (Set.range
      (B.apartment.orderedChamberBlockProduct x strict
        (fun j => (a j : characterLattice B.S)))) := by
  let (j : Fin n) : CompactSpace (B.apartment.chamberRootBlock x strict (a j)) :=
    isCompact_iff_compactSpace.mp (B.isCompact_chamberRootBlock hB x strict (a j))
  exact isCompact_range (B.continuous_orderedChamberBlockProduct x strict _)

/-- The range of each finite ordered facet product over a nonempty subset is compact. -/
theorem isCompact_range_orderedFacetBlockProduct
    {Ω : Set B.Apartment} {x : B.Apartment} (hx : x ∈ Ω) (strict : Bool)
    {n : ℕ} (a : Fin n → relativeRoots B.i) :
    IsCompact (Set.range
      (B.apartment.orderedFacetBlockProduct Ω strict
        (fun j => (a j : characterLattice B.S)))) := by
  let (j : Fin n) : CompactSpace (B.apartment.facetRootBlock Ω strict (a j)) :=
    isCompact_iff_compactSpace.mp (B.isCompact_facetRootBlock hB hx strict (a j))
  exact isCompact_range (B.continuous_orderedFacetBlockProduct Ω strict _)

end Langlands.Geometry.Building.ValuationBuildingData

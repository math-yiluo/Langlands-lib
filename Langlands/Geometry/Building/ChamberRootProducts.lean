import Langlands.Geometry.Building.FilteredRootProducts
import Langlands.Geometry.Building.KPRootFixerPlus

/-!
# Chamber and facet root-product maps

These are actual point and facet root blocks at the two depths `0` and
`0+`, the corresponding ordered multiplication maps, and the geometric
sign-choice predicate in KP Fact 7.4.6 and Corollary 7.4.9.

The maps take values in `G(k)`. Their ranges and injectivity are separate
structural assertions, not part of these definitions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The actual Dynamic unipotent radical for `ν`, intersected with the
actual sharp fixer of `Ω`. For generic `ν` the Dynamic parabolic is the
chosen minimal parabolic in the intended reductive scope. -/
def sharpUnipotentPoints (ν : cocharacterLattice S) (Ω : Set D.Apartment) :
    Subgroup (rationalPoints G) :=
  (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) ⊓
    D.sharpFixer Ω

/-- `false` selects depth `0`, and `true` selects depth `0+`. -/
def chamberRootGroup (x : D.Apartment) (strict : Bool) (a : characterLattice S) :
    Subgroup (rationalPoints G) :=
  if strict then D.filtrationPlus x a 0 else D.filtration x a 0

open Classical in
/-- The constant-depth root block, retaining `U_{2a}` at the same depth.
At depth zero this is the published `filtrationBlock` for the zero function. -/
def chamberRootBlock (x : D.Apartment) (strict : Bool) (a : characterLattice S) :
    Set (rationalPoints G) :=
  if strict then
    (D.filtrationPlus x a 0 : Set (rationalPoints G)) *
      (↑(if 2 • a ∈ relativeRoots i then D.filtrationPlus x (2 • a) 0 else ⊥) :
        Set (rationalPoints G))
  else D.filtrationBlock x (fun _ => 0) a

/-- Multiply elements of the indicated actual constant-depth blocks in order. -/
def orderedChamberBlockProduct (x : D.Apartment) (strict : Bool)
    {n : ℕ} (a : Fin n → characterLattice S)
    (u : ∀ j, D.chamberRootBlock x strict (a j)) : rationalPoints G :=
  (List.ofFn fun j => (u j : rationalPoints G)).prod

/-- Negative/central/positive multiplication with the central factor `Z_x^sharp`
at both depths `0` and `0+`. -/
def orderedSharpChamberProduct (x : D.Apartment) (strict : Bool)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice S)
    (apos : Fin npos → characterLattice S)
    (p : (∀ j, D.chamberRootBlock x strict (aneg j)) ×
      D.sharpCentralizer {x} × (∀ j, D.chamberRootBlock x strict (apos j))) :
    rationalPoints G :=
  D.orderedChamberBlockProduct x strict aneg p.1 *
    (p.2.1 : rationalPoints G) *
      D.orderedChamberBlockProduct x strict apos p.2.2

/-- The unipotent-intersection form of the sharp chamber product. -/
def sharpUnipotentProduct (C : Set D.Apartment) (x : D.Apartment)
    (ν : cocharacterLattice S)
    (p : D.sharpUnipotentPoints (-ν) C × D.sharpCentralizer {x} ×
      D.sharpUnipotentPoints ν C) : rationalPoints G :=
  (p.1 : rationalPoints G) * (p.2.1 : rationalPoints G) * (p.2.2 : rationalPoints G)

/-- The geometric sign requirement of Fact 7.4.6 and Corollary 7.4.9:
the chosen positive system contains the derivatives of all affine roots
vanishing on `F` and positive on `C`. -/
def FacetChamberPositiveSystem (F C : Set D.Apartment)
    (ν : cocharacterLattice S) : Prop :=
  ∀ ψ ∈ D.affineRoots,
    (∀ y ∈ F, ψ y = 0) →
    (∀ y ∈ C, 0 < ψ y) →
    ∃ a : relativeRoots i, ψ.linear = rootForm i a ∧ 0 < latticePairing S a ν

/-- The actual facet intersection at depth `0` or `0+`. -/
def facetRootGroup (F : Set D.Apartment) (strict : Bool) (a : characterLattice S) :
    Subgroup (rationalPoints G) :=
  if strict then D.rootFixerPlus a F else D.rootFixer a F

open Classical in
/-- The facet block retains the doubled-root intersection, with the trivial
convention precisely when `2a` is absent from the actual root set. -/
def facetRootBlock (F : Set D.Apartment) (strict : Bool) (a : characterLattice S) :
    Set (rationalPoints G) :=
  (D.facetRootGroup F strict a : Set (rationalPoints G)) *
    (↑(if 2 • a ∈ relativeRoots i then D.facetRootGroup F strict (2 • a) else ⊥) :
      Set (rationalPoints G))

/-- The ordered product of the actual facet blocks. -/
def orderedFacetBlockProduct (F : Set D.Apartment) (strict : Bool)
    {n : ℕ} (a : Fin n → characterLattice S)
    (u : ∀ j, D.facetRootBlock F strict (a j)) : rationalPoints G :=
  (List.ofFn fun j => (u j : rationalPoints G)).prod

/-- The facet variant uses negative depth `0+`, positive depth `0`, and
the same central group `Z_x^sharp` for a point `x` in the chamber. -/
def orderedSharpFacetProduct (F : Set D.Apartment) (x : D.Apartment)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice S)
    (apos : Fin npos → characterLattice S)
    (p : (∀ j, D.facetRootBlock F true (aneg j)) ×
      D.sharpCentralizer {x} × (∀ j, D.facetRootBlock F false (apos j))) :
    rationalPoints G :=
  D.orderedFacetBlockProduct F true aneg p.1 *
    (p.2.1 : rationalPoints G) *
      D.orderedFacetBlockProduct F false apos p.2.2

end Langlands.Geometry.Building.KPApartmentData

import Langlands.GroupScheme.Examples.HermitianRootReductive
import Langlands.GroupScheme.Examples.HermitianRootSimplyConnected
import Langlands.Geometry.Building.DepthZero.Definitions
import Langlands.Geometry.Building.BuildingFacetClosure
import Langlands.Geometry.Building.GeneralLinearTreeStatement

/-!
# The quasi-split `SU_3`: relative roots, affine roots, reduced building and depth zero

Regression examples for Kaletha–Prasad building data of the quasi-split special unitary group
`G = SU_3` of a separable quadratic extension `E/F` of a nonarchimedean local field `F`
(KP §2.7 and §3.2), for the Library's model `HermitianRoot.SchemeModel.groupScheme F E H w hw`
with middle index `Unit`: the special unitary group of the Hermitian form
`hyperbolic plane ⊕ ⟨w⟩` on `E³`.

* `IsUnramifiedLocalQuadratic F E` and `IsRamifiedLocalQuadratic F E`: the two cases of `E/F`,
  through the parity of `v_F(N_{E/F}(z))`.
* `ValuationBuildingData.IsUnramifiedSU3BasePoint` and
  `ValuationBuildingData.IsRamifiedSU3BasePoint`: a point `x₀` of the apartment at which the
  affine roots have the form of KP Corollary 3.2.6 (1), resp. (2).
* `SU3RelativeRootsStatement`: the maximal split torus has rank one and the relative roots are
  `{a, -a, 2a, -2a}`; `G` is not split (KP §2.7).
* `SU3AffineRootsStatement`: the affine roots in the unramified and ramified cases
  (KP Corollary 3.2.6).
* `SU3ReducedBuildingStatement`: incidence numbers of chambers and vertices of the reduced
  building (KP §3.2(f)).
* `SU3ReducedBuildingTreeStatement` asserts that the chamber vertex graph of the reduced
  building is a tree (KP §3.2(f)).
* `SU3DepthZeroQuotientsStatement`: the neutral special fibres and the orders of the finite
  reductive quotients at the two kinds of vertices and at the chambers (KP Corollary 3.2.6,
  Axiom 4.1.22, Proposition 9.4.23, Theorem 9.9.3).
* `SU3BuildingRegressionStatement` is the conjunction of the relative-root, affine-root,
  incidence and depth-zero statements.

All are statements; nothing here proves them.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

/-! ### The two cases of the quadratic extension -/

section Quadratic

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (E : Type u) [Field E] [Algebra F E]

/-- `E/F` is unramified: the normalized valuation `v_F` of the norm `N_{E/F}(z)` is even for
every `z ∈ E^×`. For a separable quadratic extension of a nonarchimedean local field the
valuation of `E` extending `v_F` is `z ↦ v_F(N_{E/F}(z))/2`, so this says that the
ramification index is `1`. -/
def IsUnramifiedLocalQuadratic : Prop :=
  ∀ z : Eˣ, Even (Plancherel.fieldOrderUnits F (Units.map (Algebra.norm F : E →* F) z)).toAdd

/-- `E/F` is ramified: `v_F(N_{E/F}(z))` is odd for some `z ∈ E^×`, i.e. the ramification index
of the separable quadratic extension `E/F` is `2`. -/
def IsRamifiedLocalQuadratic : Prop :=
  ∃ z : Eˣ, Odd (Plancherel.fieldOrderUnits F (Units.map (Algebra.norm F : E →* F) z)).toAdd

end Quadratic

/-! ### Base points of the apartment -/

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The affine roots of `B` have the form of KP Corollary 3.2.6 (1) at `x₀`: they are exactly
the affine functions `ψ` on the apartment whose derivative is a relative root `b` and whose
value `ψ(x₀)` is an integer, i.e. `Ψ = {±a + ℤ, ±2a + ℤ}` with origin `x₀`. -/
def IsUnramifiedSU3BasePoint (x₀ : B.Apartment) : Prop :=
  ∀ ψ : B.Apartment →ᵃ[ℝ] ℝ, ψ ∈ B.affineRoots ↔
    ∃ b : relativeRoots B.i, ψ.linear = rootForm B.i b ∧ ∃ n : ℤ, ψ x₀ = n

/-- The affine roots of `B` have the form of KP Corollary 3.2.6 (2) at `x₀` for the relative
root `a`: they are exactly the affine functions `ψ` on the apartment whose derivative is a
relative root `b` with either `b = ±a` and `ψ(x₀) ∈ ½ℤ`, or `b = ±2a` and `ψ(x₀) ∈ ½ + ℤ`,
i.e. `Ψ = {±a + ½ℤ, ±2a + ½ + ℤ}` with origin `x₀`. -/
def IsRamifiedSU3BasePoint (a : characterLattice B.S) (x₀ : B.Apartment) : Prop :=
  ∀ ψ : B.Apartment →ᵃ[ℝ] ℝ, ψ ∈ B.affineRoots ↔
    ∃ b : relativeRoots B.i, ψ.linear = rootForm B.i b ∧
      ((((b : characterLattice B.S) = a ∨ (b : characterLattice B.S) = -a) ∧
          ∃ n : ℤ, ψ x₀ = (n : ℝ) / 2) ∨
        (((b : characterLattice B.S) = 2 • a ∨ (b : characterLattice B.S) = -(2 • a)) ∧
          ∃ n : ℤ, ψ x₀ = (n : ℝ) + 1 / 2))

end ValuationBuildingData

/-! ### The statements -/

/-- **Relative roots of `SU_3`** (KP §2.7). For every separable quadratic extension `E/F` of a
nonarchimedean local field, every weight `w` and every KP building datum `D` of
`G = HermitianRoot.SchemeModel.groupScheme F E H w hw` satisfying the group axioms, the maximal
split torus `S` of `D` has rank one, there is a character `a` of `S` with
`Φ(S, G) = {a, -a, 2a, -2a}` (so `a` is multipliable), and `G` is not split: no maximal torus
of `G` is a split torus. -/
def SU3RelativeRootsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type u) [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E]
    (H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution F E) Unit) (w : Unit → Eˣ)
    (hw : ∀ i, (w i : E) = H.weight i)
    (D : KPBuildingDatum (HermitianRoot.SchemeModel.groupScheme F E H w hw)),
    D.SatisfiesGroupAxioms →
      Module.finrank ℤ (characterLattice D.base.S) = 1 ∧
        (∃ a : characterLattice D.base.S,
          relativeRoots D.base.i = {a, -a, 2 • a, -(2 • a)} ∧
            2 • a ∈ relativeRoots D.base.i) ∧
        ∀ (T : CommGroupScheme (Spec (CommRingCat.of F)))
          (j : T.toGrp ⟶ HermitianRoot.SchemeModel.groupScheme F E H w hw),
          IsMaximalTorus j → ¬ IsSplitTorus T.toGrp

/-- **Affine roots of `SU_3`** (KP Corollary 3.2.6). With the valuation of `F` normalized by
`v(F^×) = ℤ` (the Library's `localFieldOrder`) and the Library's affine roots
(KP Definition 6.3.4):

* if `E/F` is unramified, some point `x₀` of the apartment is an unramified base point: the
  affine roots are the `ψ` with derivative a relative root and `ψ(x₀) ∈ ℤ`;
* if `E/F` is ramified, in every residue characteristic, there are a character `a` with
  `Φ(S, G) = {a, -a, 2a, -2a}` and a point `x₀` at which the affine roots are the `ψ` with
  derivative `±a` and `ψ(x₀) ∈ ½ℤ`, and the `ψ` with derivative `±2a` and `ψ(x₀) ∈ ½ + ℤ`. -/
def SU3AffineRootsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type u) [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E]
    (H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution F E) Unit) (w : Unit → Eˣ)
    (hw : ∀ i, (w i : E) = H.weight i)
    (D : KPBuildingDatum (HermitianRoot.SchemeModel.groupScheme F E H w hw)),
    D.SatisfiesGroupAxioms →
      (IsUnramifiedLocalQuadratic F E →
        ∃ x₀ : D.base.Apartment, D.base.IsUnramifiedSU3BasePoint x₀) ∧
      (IsRamifiedLocalQuadratic F E →
        ∃ (a : characterLattice D.base.S) (x₀ : D.base.Apartment),
          relativeRoots D.base.i = {a, -a, 2 • a, -(2 • a)} ∧
            D.base.IsRamifiedSU3BasePoint a x₀)

/-- **The reduced building of `SU_3`** (KP §3.2(f)), with `q = #𝓀[F]` and the Library's facet
incidence (a vertex `y` is incident to a chamber `C` when `y` lies in the closure
`buildingFacetClosure C`):

* every chamber is incident to exactly two vertices;
* if `E/F` is unramified and `x₀` is an unramified base point, every vertex in the
  `G(F)`-orbit of `x₀` is incident to exactly `q³ + 1` chambers, every other vertex to exactly
  `q + 1` chambers, and of the two vertices of a chamber exactly one lies in that orbit;
* if `E/F` is ramified, every vertex is incident to exactly `q + 1` chambers. -/
def SU3ReducedBuildingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type u) [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E]
    (H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution F E) Unit) (w : Unit → Eˣ)
    (hw : ∀ i, (w i : E) = H.weight i)
    (D : KPBuildingDatum (HermitianRoot.SchemeModel.groupScheme F E H w hw)),
    D.SatisfiesGroupAxioms →
      (∀ C : BuildingFacet D.base.toValuationBuildingData, D.base.IsChamber C.val →
        {y : D.base.ReducedBuilding |
          D.base.IsVertex y ∧ y ∈ D.base.buildingFacetClosure C}.ncard = 2) ∧
      (IsUnramifiedLocalQuadratic F E →
        ∀ x₀ : D.base.Apartment, D.base.IsUnramifiedSU3BasePoint x₀ →
          (∀ y : D.base.ReducedBuilding, D.base.IsVertex y →
            (y ∈ MulAction.orbit (rationalPoints (HermitianRoot.SchemeModel.groupScheme F E H w hw))
                (D.base.apartmentMap x₀) →
              {C : BuildingFacet D.base.toValuationBuildingData |
                D.base.IsChamber C.val ∧ y ∈ D.base.buildingFacetClosure C}.ncard =
                Nat.card 𝓀[F] ^ 3 + 1) ∧
            (y ∉ MulAction.orbit (rationalPoints (HermitianRoot.SchemeModel.groupScheme F E H w hw))
                (D.base.apartmentMap x₀) →
              {C : BuildingFacet D.base.toValuationBuildingData |
                D.base.IsChamber C.val ∧ y ∈ D.base.buildingFacetClosure C}.ncard =
                Nat.card 𝓀[F] + 1)) ∧
          ∀ C : BuildingFacet D.base.toValuationBuildingData, D.base.IsChamber C.val →
            ∀ y y' : D.base.ReducedBuilding, D.base.IsVertex y → D.base.IsVertex y' →
              y ∈ D.base.buildingFacetClosure C → y' ∈ D.base.buildingFacetClosure C → y ≠ y' →
                (y ∈ MulAction.orbit
                    (rationalPoints (HermitianRoot.SchemeModel.groupScheme F E H w hw))
                    (D.base.apartmentMap x₀) ↔
                  y' ∉ MulAction.orbit
                    (rationalPoints (HermitianRoot.SchemeModel.groupScheme F E H w hw))
                    (D.base.apartmentMap x₀))) ∧
      (IsRamifiedLocalQuadratic F E →
        ∀ y : D.base.ReducedBuilding, D.base.IsVertex y →
          {C : BuildingFacet D.base.toValuationBuildingData |
            D.base.IsChamber C.val ∧ y ∈ D.base.buildingFacetClosure C}.ncard =
            Nat.card 𝓀[F] + 1)

/-- **The tree of `SU_3`** (KP §3.2(f)). For every KP building datum `D` of the quasi-split
`SU_3` satisfying the group axioms, the `chamberVertexGraph` of its reduced building is a
tree. This applies to both ramification cases and every residue characteristic. -/
def SU3ReducedBuildingTreeStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type u) [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E]
    (H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution F E) Unit) (w : Unit → Eˣ)
    (hw : ∀ i, (w i : E) = H.weight i)
    (D : KPBuildingDatum (HermitianRoot.SchemeModel.groupScheme F E H w hw)),
    D.SatisfiesGroupAxioms →
      D.base.toValuationBuildingData.chamberVertexGraph.IsTree

/-- **Depth zero at the two kinds of vertices of `SU_3`** (KP Corollary 3.2.6, Axiom 4.1.22,
Proposition 9.4.23 and Theorem 9.9.3), with `q = #𝓀[F]`, `𝒢_x` the neutral model of a building
facet `x` (whose integral points are the parahoric `D.parahoric x`) and `Ḡ_x` the specified
reductive quotient of its special fibre (`D.reductiveQuotient x`):

* if `E/F` is unramified and `x₀` is an unramified base point, at the facet of a vertex in the
  `G(F)`-orbit of `x₀` the special fibre of `𝒢_x` is connected reductive and
  `#Ḡ_x(𝓀) = q³(q² - 1)(q³ + 1)`; at the facet of any other vertex it is not connected
  reductive and `#Ḡ_x(𝓀) = q(q² - 1)(q + 1)`; at a chamber `#Ḡ_C(𝓀) = q² - 1`;
* if `E/F` is ramified, at the facet of every vertex the special fibre of `𝒢_x` is not
  connected reductive and `#Ḡ_x(𝓀) = q(q² - 1)`; at a chamber `#Ḡ_C(𝓀) = q - 1`. -/
def SU3DepthZeroQuotientsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type u) [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E]
    (H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution F E) Unit) (w : Unit → Eˣ)
    (hw : ∀ i, (w i : E) = H.weight i)
    (D : KPBuildingDatum (HermitianRoot.SchemeModel.groupScheme F E H w hw)),
    D.SatisfiesGroupAxioms →
      (IsUnramifiedLocalQuadratic F E →
        ∀ x₀ : D.base.Apartment, D.base.IsUnramifiedSU3BasePoint x₀ →
          ∀ (x : BuildingFacet D.base.toValuationBuildingData) (y : D.base.ReducedBuilding),
            D.base.IsVertex y → y ∈ x.val →
              (y ∈ MulAction.orbit
                  (rationalPoints (HermitianRoot.SchemeModel.groupScheme F E H w hw))
                  (D.base.apartmentMap x₀) →
                IsConnectedReductive (D.models.facetModels.model x).neutral.specialFibre ∧
                  Nat.card (D.reductiveQuotientPoints x) =
                    Nat.card 𝓀[F] ^ 3 * (Nat.card 𝓀[F] ^ 2 - 1) * (Nat.card 𝓀[F] ^ 3 + 1)) ∧
              (y ∉ MulAction.orbit
                  (rationalPoints (HermitianRoot.SchemeModel.groupScheme F E H w hw))
                  (D.base.apartmentMap x₀) →
                ¬ IsConnectedReductive (D.models.facetModels.model x).neutral.specialFibre ∧
                  Nat.card (D.reductiveQuotientPoints x) =
                    Nat.card 𝓀[F] * (Nat.card 𝓀[F] ^ 2 - 1) * (Nat.card 𝓀[F] + 1))) ∧
      (IsUnramifiedLocalQuadratic F E →
        ∀ C : BuildingFacet D.base.toValuationBuildingData, D.base.IsChamber C.val →
          Nat.card (D.reductiveQuotientPoints C) = Nat.card 𝓀[F] ^ 2 - 1) ∧
      (IsRamifiedLocalQuadratic F E →
        ∀ (x : BuildingFacet D.base.toValuationBuildingData) (y : D.base.ReducedBuilding),
          D.base.IsVertex y → y ∈ x.val →
            ¬ IsConnectedReductive (D.models.facetModels.model x).neutral.specialFibre ∧
              Nat.card (D.reductiveQuotientPoints x) =
                Nat.card 𝓀[F] * (Nat.card 𝓀[F] ^ 2 - 1)) ∧
      (IsRamifiedLocalQuadratic F E →
        ∀ C : BuildingFacet D.base.toValuationBuildingData, D.base.IsChamber C.val →
          Nat.card (D.reductiveQuotientPoints C) = Nat.card 𝓀[F] - 1)

/-- The conjunction of the `SU_3` relative-root, affine-root, incidence and depth-zero
statements for KP building data. -/
def SU3BuildingRegressionStatement : Prop :=
  SU3RelativeRootsStatement.{u} ∧ SU3AffineRootsStatement.{u} ∧
    SU3ReducedBuildingStatement.{u} ∧ SU3DepthZeroQuotientsStatement.{u}

end Langlands.Geometry.Building

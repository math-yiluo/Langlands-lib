import Langlands.Geometry.Building.KPOptimalPoints
import Langlands.Geometry.Building.KPLieFiltrationDual

/-!
# The apartment restriction of Kaletha–Prasad Lemma 13.4.4

Given a fixed chamber and a choice of `x_S` optimal for each nonempty subset of its `Σ`,
each lattice at a point of the closed chamber is contained in the same-depth lattice at
one of the chosen points. The target uses nonempty actual affine roots and supplied Lie
filtration data on the apartment. It does not construct the choice or transport it to the building.
-/

universe u

open CategoryTheory AlgebraicGeometry Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-- A nonempty finite subset of `Σ` for the chamber represented by `c`. -/
abbrev OptimalPointSubset (Ψ : Set (A →ᵃ[ℝ] ℝ)) (c : A) :=
  {S : Finset (A →ᵃ[ℝ] ℝ) // S.Nonempty ∧ (↑S : Set (A →ᵃ[ℝ] ℝ)) ⊆ positiveRootsBelowPeriod Ψ c}

/-- A choice of `x_S` for each such subset, as in the paragraph before KP Example 13.4.3. -/
abbrev OptimalPointChoice (Ψ : Set (A →ᵃ[ℝ] ℝ)) (c : A) :=
  (S : OptimalPointSubset Ψ c) → {x : A // IsOptimalPointFor Ψ c S.val x}

end AffineRootSystem

open AffineRootSystem AffineRootSystem.GalleryGeometry

/-- KP Lemma 13.4.4 on the closed chamber `facetClosure P.affineRoots c` of the supplied
apartment and with the chosen `x_S` in place of their building-wide orbit set. Here `L` gives
the lattices, the root set is nonempty, and the choice of all `x_S` is supplied. Then for each
`z` in the closed chamber and each real `s`, `𝔤_{z,s} ⊆ 𝔤_{x_S,s}` for some nonempty `S ⊆ Σ`. -/
def ApartmentOptimalPointDominationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (L : P.LieFiltrationData) (c : P.Apartment),
    IsRegular P.affineRoots c → P.affineRoots.Nonempty →
    ∀ (choosePoint : OptimalPointChoice P.affineRoots c) (z : P.Apartment),
      z ∈ facetClosure P.affineRoots c → ∀ s : ℝ,
        ∃ S, L.lieFiltrationReal z s ≤ L.lieFiltrationReal (choosePoint S).val s

end Langlands.Geometry.Building

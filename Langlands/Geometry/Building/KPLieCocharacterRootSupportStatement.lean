import Langlands.Geometry.Building.KPLieFiltrationDual
import Langlands.Geometry.Building.KPNilpotentCoset

/-!
# Root support of an apartment Lie vector contracted by a cocharacter

The cocharacter is of the actual maximal split torus of the apartment. The target isolates the
weight-space argument in the proof of KP Proposition 13.6.7, for the relative-root Lie span of
§13.3.3 and the real-depth shift of §13.3.1. It does not assert that such a cocharacter can be
chosen after conjugation by a parahoric point.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel TensorProduct
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open ParahoricBuildingData.LieFiltrationData (indexShift shiftedIndex)

/-- If an element of the supplied real-depth lattice is contracted by `G_m → S → G` for the
apartment's torus `S`, its scaled vectors at the nonnegative depth `t = r + ⌈-r⌉₊` lie in the
span of the affine-root lattices with `ψ(x) ≥ t` whose derivatives are strictly positive
on the reduced apartment direction of the cocharacter. -/
def LieRootSupportOfApartmentCocharacterStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (L : P.LieFiltrationData)
    (x : P.Apartment) (ν : cocharacterLattice P.S) (r : ℝ) (X : GenericLie 𝒪[F] G),
    X ∈ L.lieFiltrationReal x r →
    GenericLie.equiv 𝒪[F] G X ∈ cocharacterPositiveLie (CommGroupScheme.groupHom ν ≫ P.i) →
    let v : TranslationSpace P.i := Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν)
    ∀ a ∈ 𝓂[F] ^ indexShift r,
      a • X ∈ ⨆ (ψ : P.affineRoots) (_ : (shiftedIndex r : ℝ) ≤ ψ.1 x)
        (_ : 0 < ψ.1.linear v), L.affineRootLie ψ

end Langlands.Geometry.Building

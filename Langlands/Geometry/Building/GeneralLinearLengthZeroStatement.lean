import Langlands.Geometry.Building.IwahoriWeyl
import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Langlands.Representation.Plancherel.LocalFieldUnits

/-! # The length-zero part of the Iwahori–Weyl group of `GL_N`

For a nonarchimedean local field `F`, `N ≥ 1`, `G = GL_N` over `F` and building data
`D : KPBuildingDatum G` satisfying the one-group axioms, with parahoric building data
`P = D.base`, the statement `GeneralLinearLengthZeroStatement` describes the length-zero part
`Ω = W̃^0_C` of the Iwahori–Weyl group `W̃^0 = N(F)/Z(F)^0` (`IwahoriWeylGroup`), the stabilizer
`chamberStabilizer C` of a chamber `C` of the apartment (Kaletha–Prasad, Theorem 7.8.1 and
7.8.2; Definition 2.6.23; 15.1.24 and 15.1.33):

* `G(F)/G(F)^0 ≅ ℤ` through `g ↦ ord_F(det g)`;
* `chamberStabilizer C` is infinite cyclic and `toComponents` maps it bijectively onto
  `G(F)/G(F)^0`;
* for `N ≥ 2`, every `n ∈ N(F)` stabilizing `C` whose class generates `chamberStabilizer C`
  permutes the `N` vertices of `C` as a cycle of length `N`;
* the pointwise fixer in `G(F)` of the chamber `C` of the reduced building is `F^× · P_C`
  (the centre of `G(F)` and the Iwahori subgroup `P_C = P.parahoric C`), and for `N ≥ 2` it is
  strictly smaller than the setwise stabilizer of `C`.

The affine Weyl group stays the separate subgroup `affinePart` (KP Theorem 7.8.1(1)); this
statement concerns its complement `chamberStabilizer C`. This definition states the
comparison and does not prove it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **The length-zero part of the Iwahori–Weyl group of `GL_N` is infinite cyclic.** For
building data `D` of `G = GL_N`, `N ≥ 1`, over a nonarchimedean local field `F` satisfying the
one-group axioms, with `P = D.base`, `ρ : G(F) → GL_N(F)` the matrix of a point and
`ord = Plancherel.fieldOrderUnits F` the normalized valuation on `Fˣ`:

* `Z(F)^0` is normal in `N(F)`, `G(F)^0` is normal in `G(F)`, and there is an isomorphism
  `G(F)/G(F)^0 ≃ ℤ` sending the class of `g` to `ord(det ρ(g))`;
* for every chamber `C` of the apartment, `chamberStabilizer C` is isomorphic to `ℤ`, and
  `toComponents` restricted to it is bijective onto `G(F)/G(F)^0`;
* for `N ≥ 2` and every `n ∈ N(F)` stabilizing `C` whose class generates `chamberStabilizer C`,
  there is a vertex `x₀` of `C` such that `x₀, n x₀, …, n^(N-1) x₀` are distinct, are all the
  vertices `x` of `C` (the points with `{x}` a face of `C`), and `n^N x₀ = x₀`; so `n` permutes
  the `N` vertices of `C` as a cycle of length `N`;
* the pointwise fixer in `G(F)` of the image of `C` in the reduced building is
  `Z(G(F)) ⊔ P_C`, the product `F^× · P_C` of the centre and the Iwahori subgroup
  `P_C = P.parahoric C`, and for `N ≥ 2` it is a proper subgroup of the setwise stabilizer of
  that image

(Kaletha–Prasad, Theorem 7.8.1(1), 7.8.2, Proposition 7.7.12, Definition 2.6.23, 15.1.24 and
15.1.33). -/
def GeneralLinearLengthZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (D : KPBuildingDatum (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))),
    D.SatisfiesGroupAxioms → 1 ≤ N →
      let P := D.base
      let ρ : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) →*
          GL (Fin N) F :=
        (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)).toMonoidHom
      ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
        (∃ e : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) ⧸
              P.zeroSubgroup ≃* Multiplicative ℤ,
          ∀ g, e (QuotientGroup.mk g) =
            Plancherel.fieldOrderUnits F (Matrix.GeneralLinearGroup.det (ρ g))) ∧
        ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
          Nonempty (P.chamberStabilizer C ≃* Multiplicative ℤ) ∧
          Function.Bijective (P.toComponents.comp (P.chamberStabilizer C).subtype) ∧
          (2 ≤ N → ∀ n ∈ P.normalizerStabilizer C,
            Subgroup.zpowers (QuotientGroup.mk n : P.IwahoriWeylGroup) =
                P.chamberStabilizer C →
              ∃ x₀ : P.Apartment,
                Function.Injective (fun k : Fin N => (n ^ (k : ℕ)) • x₀) ∧
                Set.range (fun k : Fin N => (n ^ (k : ℕ)) • x₀) =
                  {x | AffineRootSystem.IsFaceOf P.affineRoots {x} C} ∧
                (n ^ N) • x₀ = x₀) ∧
          P.pointwiseFixer (P.apartmentMap '' C) =
            Subgroup.center (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))
              ⊔ P.parahoric C ∧
          (2 ≤ N → P.pointwiseFixer (P.apartmentMap '' C) <
            MulAction.stabilizer
              (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))
              (P.apartmentMap '' C))

end Langlands.Geometry.Building

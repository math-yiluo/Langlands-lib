import Langlands.Geometry.Building.KPLieFiltrationDual
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Promotion of a root-supported Lie coset within an apartment

This is the affine translation step in the proof of KP Proposition 13.6.7, formulated for
supplied relative affine-root Lie lattices. The hypothesis on the representative at the
shifted depth is a root-support condition, not the existence of a contracting cocharacter.
The strict-depth denominator is required to be finitely generated so that there is one
deeper lattice containing the whole translate, not a depth depending on its element.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open ParahoricBuildingData.LieFiltrationData (indexShift shiftedIndex)

/-- Let `n = ⌈-r⌉₊` and `t = r + n`. Suppose that `𝔪^n X` is contained in the span of
those affine-root lattices with either `ψ(x) > t` or `ψ(x) = t` and `ψ̇(v) > 0`. If the
supplied family is periodic and `𝔤_{x,r+}` is finitely generated over `𝒪[F]`, then for
all sufficiently small `ε > 0` the entire coset `X + 𝔤_{x,r+}` is contained in a single
lattice `𝔤_{ε v +ᵥ x,s}` for some `s > r`. -/
def LieCosetPromotionOfPositiveRootSupportStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (L : P.LieFiltrationData),
    L.IsPeriodic →
    ∀ (x : P.Apartment) (v : TranslationSpace P.i) (r : ℝ) (X : GenericLie 𝒪[F] G),
      (L.lieFiltrationPlusReal x r).FG →
      (let t : ℝ := shiftedIndex r
       ∀ a ∈ 𝓂[F] ^ indexShift r,
         a • X ∈ ⨆ (ψ : P.affineRoots)
           (_ : t < ψ.1 x ∨ (t = ψ.1 x ∧ 0 < ψ.1.linear v)), L.affineRootLie ψ) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        ∃ s : ℝ, r < s ∧ ∀ Y : GenericLie 𝒪[F] G,
          Y - X ∈ L.lieFiltrationPlusReal x r → Y ∈ L.lieFiltrationReal (ε • v +ᵥ x) s

end Langlands.Geometry.Building

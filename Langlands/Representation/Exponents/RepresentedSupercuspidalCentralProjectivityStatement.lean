import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Supercuspidal representations are projective and injective with fixed central character

Renard 2026, VI.3.6, Proposition (printed p.148 / PDF p.154): an irreducible supercuspidal
representation of `G` with central character `χ` is projective and injective in the full
subcategory `M(G)_χ` of smooth representations admitting the central character `χ`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.3.6, Proposition, for all actual connected reductive groups: an irreducible
smooth representation `τ` of `G(F)` with central character `χ`, whose Jacquet modules along
all proper actual rational parabolics vanish, is projective and injective in the full
subcategory of smooth representations (carriers in universe `v`) on which the center of
`G(F)` acts through `χ`. -/
def RepresentedSupercuspidalCentralProjectivityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (χ : Subgroup.center (rationalPoints G) →* ℂˣ)
      (τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (hχ : τ.HasCentralCharacter χ),
      τ.IsIrreducible →
      (∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)),
        ¬ IsIso p → Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj τ)) →
      let C : ObjectProperty (SmoothRep.{0, u, v} ℂ (rationalPoints G)) :=
        fun A => A.HasCentralCharacter χ
      Projective (C := C.FullSubcategory) ⟨τ, hχ⟩ ∧
        Injective (C := C.FullSubcategory) ⟨τ, hχ⟩

end Langlands.Aubert.General.RepresentedParabolic

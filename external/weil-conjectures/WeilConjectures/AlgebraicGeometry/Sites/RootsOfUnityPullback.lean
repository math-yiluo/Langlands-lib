/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDelta

/-!
# Pullback of `μₙ` and of the Kummer sequence

For a morphism of schemes `g : X ⟶ Y` the comparison `g^* 𝔾ₘ ⟶ 𝔾ₘ` restricts to a comparison
`g^* μₙ ⟶ μₙ` of sheaves of `n`-th roots of unity, and together they form a morphism from the
pullback of the Kummer sequence of `Y` to the Kummer sequence of `X`. Hence the induced pullback
maps on the cohomology of `μₙ` and of `𝔾ₘ` commute with the inclusion `μₙ ⟶ 𝔾ₘ` and with the
Kummer boundary.

## Main definitions

- `AlgebraicGeometry.Scheme.gmCohomologyMap`, `AlgebraicGeometry.Scheme.rootsOfUnityCohomologyMap`:
  the pullback maps `Hᵠ(Y, 𝔾ₘ) → Hᵠ(X, 𝔾ₘ)` and `Hᵠ(Y, μₙ) → Hᵠ(X, μₙ)`.

## Main statements

- `AlgebraicGeometry.Scheme.rootsOfUnityCohomologyMap_kummerδ₁`: the Kummer boundary commutes
  with pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

section Pullback

variable (X : Scheme.{u}) (n : ℕ) in
/-- The inclusion `μₙ ⟶ 𝔾ₘ` of the sheaf of `n`-th roots of unity. -/
noncomputable abbrev rootsOfUnitySheafι : X.rootsOfUnitySheaf n ⟶ X.gmSheaf :=
  kernel.ι (n • 𝟙 X.gmSheaf)

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ)

/-- The comparison `g^* 𝔾ₘ ⟶ 𝔾ₘ` commutes with the `n`-th power maps. -/
@[reassoc]
lemma map_nsmul_comp_upperStarGmSheafToGmSheaf :
    (g)^*[AddCommGrpCat.{u + 1}].map (n • 𝟙 Y.gmSheaf) ≫ upperStarGmSheafToGmSheaf g =
      upperStarGmSheafToGmSheaf g ≫ (n • 𝟙 X.gmSheaf) := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

/-- The pullback of the Kummer sequence of `Y` maps to the Kummer sequence of `X`. -/
noncomputable def kummerSequenceUpperStarMap :
    (Y.kummerSequence n).map (g)^*[AddCommGrpCat.{u + 1}] ⟶ X.kummerSequence n where
  τ₁ := upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g
  τ₂ := upperStarGmSheafToGmSheaf g
  τ₃ := upperStarGmSheafToGmSheaf g
  comm₁₂ := upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι n g
  comm₂₃ := (map_nsmul_comp_upperStarGmSheafToGmSheaf g n).symm

/-- The pullback map `Hᵠ(Y, 𝔾ₘ) → Hᵠ(X, 𝔾ₘ)` along `g : X ⟶ Y`. -/
noncomputable def gmCohomologyMap (q : ℕ) : Sheaf.H Y.gmSheaf q →+ Sheaf.H X.gmSheaf q :=
  (Sheaf.H.map (upperStarGmSheafToGmSheaf g) q).comp (Etale.cohomologyMap g Y.gmSheaf q)

/-- The pullback map `Hᵠ(Y, μₙ) → Hᵠ(X, μₙ)` along `g : X ⟶ Y`. -/
noncomputable def rootsOfUnityCohomologyMap (q : ℕ) :
    Sheaf.H (Y.rootsOfUnitySheaf n) q →+ Sheaf.H (X.rootsOfUnitySheaf n) q :=
  (Sheaf.H.map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g) q).comp
    (Etale.cohomologyMap g (Y.rootsOfUnitySheaf n) q)

/-- The pullback maps on the cohomology of `μₙ` and of `𝔾ₘ` are compatible with the inclusion
`μₙ ⟶ 𝔾ₘ`. -/
lemma map_kernelι_rootsOfUnityCohomologyMap (q : ℕ) (x : Sheaf.H (Y.rootsOfUnitySheaf n) q) :
    Sheaf.H.map (X.rootsOfUnitySheafι n) q (rootsOfUnityCohomologyMap g n q x) =
      gmCohomologyMap g q (Sheaf.H.map (Y.rootsOfUnitySheafι n) q x) := by
  simp only [rootsOfUnityCohomologyMap, gmCohomologyMap, AddMonoidHom.comp_apply]
  rw [← Sheaf.H.map_comp_apply, upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι,
    Sheaf.H.map_comp_apply, Etale.cohomologyMap_map]

/-- **The Kummer boundary commutes with pullback.** For `g : X ⟶ Y` and `n` invertible on `Y`
and on `X`, the square

```
  H¹(Y, 𝔾ₘ) ──δ──▶ H²(Y, μₙ)
      │                 │
      ▼                 ▼
  H¹(X, 𝔾ₘ) ──δ──▶ H²(X, μₙ)
```

of Kummer boundaries (`AlgebraicGeometry.Scheme.kummerδ₁`) and pullback maps commutes. -/
lemma rootsOfUnityCohomologyMap_kummerδ₁ (hY : IsUnit (n : Γ(Y, ⊤))) (hX : IsUnit (n : Γ(X, ⊤)))
    (c : Y.CohomologicalPicardGroup) :
    rootsOfUnityCohomologyMap g n 2 (Y.kummerδ₁ n hY c) =
      X.kummerδ₁ n hX (gmCohomologyMap g 1 c) := by
  have h₁ := Etale.cohomologyMap_δSucc g (Y.kummerSequence_shortExact n hY) 1 c
  have h₂ := Sheaf.H.map_δSucc
    ((Y.kummerSequence_shortExact n hY).map_of_exact (g)^*[AddCommGrpCat.{u + 1}])
    (X.kummerSequence_shortExact n hX)
    (kummerSequenceUpperStarMap g n) 1 (Etale.cohomologyMap g Y.gmSheaf 1 c)
  exact (congrArg (Sheaf.H.map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g) 2) h₁).trans h₂

end Pullback

end AlgebraicGeometry.Scheme

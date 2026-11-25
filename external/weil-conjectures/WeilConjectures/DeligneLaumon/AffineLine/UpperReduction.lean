/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Exactness
public import WeilConjectures.WeilSheaf.CohomologyExact
public import WeilConjectures.WeilSheaf.FiniteLength
public import WeilConjectures.WeilSheaf.UpperStarExact
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
import WeilConjectures.AlgebraicGeometry.AffineSpace.GeometricallyConnected

/-!
# Reduction of the affine-line estimate to irreducible factors

Let `j : U₀ ↪ 𝔸¹` be a dense open immersion and let `F` be a lisse Weil sheaf on `U₀`, pure of
weight `w`, which is the restriction `j'^* G` of a lisse Weil sheaf `G` on a `k₀`-scheme `W`
with irreducible geometric fiber, along `j' : U₀ ⟶ W`. A composition series of `G` restricts to
a filtration of `F` whose graded pieces are restrictions of irreducible lisse sheaves on `W`.
Each step of it stays short exact after `j_*` (exactness of the middle extension at a fixed
pure weight), the long exact sequence of compactly supported cohomology gives an exact triple
in degree one, and the middle term inherits a common upper weight bound from its outer terms.
Hence the bound `w + 1` for `H_c^1(𝔸¹, j_*F)` follows from the same bound for the graded pieces.
This is Step 3 of the blueprint proof of `theorem-weight-bound-affine-line`.

## Main statements

- `…LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_one_of_upperStar`:
  the reduction to irreducible factors.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace FrobeniusModule

variable {K : Type*} [Field K]

/-- A zero Frobenius module has weights at most any `w`: it has no eigenvalue. -/
theorem hasWeightsAtMost_of_subsingleton {M : FrobeniusModule K} [Subsingleton M.carrier]
    (ι : K →+* ℂ) (q : ℕ) (w : ℝ) : M.HasWeightsAtMost ι q w := fun α hα ↦ by
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  exact (hx.2 (Subsingleton.elim x 0)).elim

end FrobeniusModule

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- A zero Weil complex has zero compactly supported cohomology. -/
theorem subsingleton_compactlySupportedCohomology_of_isZero {K : WeilComplex k₀ l X}
    (hK : IsZero K) (r : ℤ) : Subsingleton (K.compactlySupportedCohomology r).carrier :=
  ModuleCat.subsingleton_of_isZero <| (WeilCoefficients.toModuleCat l).map_isZero <|
    (WeilSheaf.globalSectionsFunctor k₀ l (Spec (.of k₀))).map_isZero <|
      (homologySheaf r).map_isZero <|
        (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).map_isZero hK

end WeilComplex

namespace WeilSheaf.LisseOnDenseOpen

/-- The datum `(U₀, j, G)` with the same dense open immersion as `D` and another lisse sheaf. -/
@[simps]
def withSheaf (D : LisseOnDenseOpen k₀ l) (G : WeilSheaf k₀ l D.U) (hG : G.IsLisse) :
    LisseOnDenseOpen k₀ l :=
  { D with sheaf := G, lisse := hG }

variable (ι : PadicAlgCl l →+* ℂ)

-- Instance search for the structures over `Spec k₀` of the affine line is slow.
/-- **Reduction to irreducible factors** (Step 3 of `theorem-weight-bound-affine-line`). Let
`F = D.sheaf` be punctually `ι`-pure of weight `w` on the dense open `U₀` of the affine line,
and let `F ≅ j'^* G` for a lisse Weil sheaf `G` on a `k₀`-scheme `W` with irreducible geometric
fiber. If `H_c^1(𝔸¹, j_*(j'^* M))` has weights at most `w + 1` for every irreducible lisse sheaf
`M` on `W` with `j'^* M` pure of weight `w`, then `H_c^1(𝔸¹, j_*F)` has weights at most `w + 1`:
along a composition series of `G` the middle extension is exact at the fixed weight `w`, and the
long exact sequence of compactly supported cohomology propagates the bound. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one_of_upperStar
    {W : Scheme.{u}} [W.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀))]
    [IrreducibleSpace (W ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (D : LisseOnDenseOpen k₀ l) (j' : D.U ⟶ W) [j'.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (D.U ↘ Spec (CommRingCat.of k₀))]
    {w : ℝ}
    (hirr : ∀ (M : WeilSheaf k₀ l W) (hM : M.IsIrreducibleLisse),
      ((upperStar j').obj M).IsPunctuallyPureOfWeight ι w →
      ((D.withSheaf ((upperStar j').obj M)
        (ProEtale.IsAdicLisseSheaf.upperStar _ hM.1)).directImage.compactlySupportedCohomology
          1).HasWeightsAtMostOver k₀ ι (w + 1))
    (G : WeilSheaf k₀ l W) (hG : G.IsLisse) (e : (upperStar j').obj G ≅ D.sheaf)
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  -- the bound for the restriction of a lisse sheaf on `W`
  let P : WeilSheaf k₀ l W → Prop := fun G ↦ ∀ hG : G.IsLisse,
    ((upperStar j').obj G).IsPunctuallyPureOfWeight ι w →
    ((D.withSheaf ((upperStar j').obj G)
      (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).directImage.compactlySupportedCohomology
        1).HasWeightsAtMostOver k₀ ι (w + 1)
  have key : P G := by
    refine IsLisse.induction_on_shortExact (P := P) ?_ ?_ ?_ hG
    · intro M hM hML _
      have : Subsingleton ((D.withSheaf ((upperStar j').obj M)
          (ProEtale.IsAdicLisseSheaf.upperStar _ hML)).directImage.compactlySupportedCohomology
            1).carrier :=
        WeilComplex.subsingleton_compactlySupportedCohomology_of_isZero
          (toComplex.map_isZero ((WeilSheaf.directImage D.j).map_isZero
            ((upperStar j').map_isZero hM))) 1
      exact FrobeniusModule.hasWeightsAtMost_of_subsingleton _ _ _
    · intro M hM _ hMw
      exact hirr M hM hMw
    · intro S hS h₁ h₂ h₃ hP₁ hP₃ _ hw₂
      have hS' := shortExact_map_upperStar j' hS
      have : Mono (S.map (upperStar j')).f := hS'.mono_f
      have : Epi (S.map (upperStar j')).g := hS'.epi_g
      have hw₁ := hw₂.of_mono (S.map (upperStar j')).f
      have hw₃ := hw₂.of_epi (S.map (upperStar j')).g
      have hS'' := shortExact_map_directImage ι D.j (S.map (upperStar j')) hS'
        (ProEtale.IsAdicLisseSheaf.upperStar _ h₁) (ProEtale.IsAdicLisseSheaf.upperStar _ h₂)
        (ProEtale.IsAdicLisseSheaf.upperStar _ h₃) hw₁ hw₃
      exact FrobeniusModule.HasWeightsAtMost.of_functionExact _ _
        (WeilComplex.compactlySupportedCohomologyMap_frobenius _ 1)
        (WeilComplex.compactlySupportedCohomologyMap_frobenius _ 1)
        (exact_compactlySupportedCohomologyMap hS'' 1) (hP₁ h₁ hw₁) (hP₃ h₃ hw₃)
  have hGw : ((upperStar j').obj G).IsPunctuallyPureOfWeight ι w := fun x ↦ by
    obtain ⟨E⟩ := nonempty_equiv_stalk_of_iso e x
    exact (hw x).of_equiv E
  exact FrobeniusModule.HasWeightsAtMost.of_equiv
    (compactlySupportedCohomologyEquivOfIso ((WeilSheaf.directImage D.j).mapIso e.symm) 1)
    (key hG hGw)

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry

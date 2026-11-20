import Langlands.Global.ArthurParabolicSpaces
import Langlands.GroupScheme.Rational.RelativeRealCorootStatements
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof

/-! # Comparison of `𝔞_P` and `𝔞_P^*` with the relative root data

Arthur 2005, §4–5, (5.1): for a standard parabolic subgroup `P` with `Δ_0^P = S`,
`𝔞_P^* = X(P)_F ⊗ ℝ` embeds in `𝔞_0^*` with image the annihilator of the coroots of `S`, and
`𝔞_P = Hom(X(P)_F, ℝ)` is the quotient of `𝔞_0` by `𝔞_0^P`, identified with the subspace
`{H ∈ 𝔞_0 : α(H) = 0, α ∈ S}`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.Global.ArthurParabolicSpaces

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints

/-- **Arthur 2005, (5.1) and p.26, for standard parabolic subgroups.** For a connected reductive
group `G` over a field `k`, a maximal split torus `i : T → G`, a generic cocharacter `ν`, integral
reflection data `D` and `S ⊆ Δ_0`:
* restriction `X(P_S) ⊗ ℝ → X(T) ⊗ ℝ` is injective with image the annihilator
  `corootAnnihilator i D S` of the coroots of `S` (`𝔞_P^* ⊆ 𝔞_0^*`);
* the transpose `𝔞_0 → Hom(X(P_S), ℝ)` is surjective with kernel the span of the coroots of `S`
  (`𝔞_0^P`), and its restriction to `{H : α(H) = 0, α ∈ S}` is bijective (`𝔞_P ⊆ 𝔞_0`). -/
def ParabolicSpacesComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
    ∀ D : RelativeRootReflectionData i, ∀ S : Set (characterLattice T),
      S ⊆ simpleRelativeRoots i ν →
        Function.Injective (restrictToTorus k i ν S) ∧
        LinearMap.range (restrictToTorus k i ν S) = corootAnnihilator i D S ∧
        Function.Surjective (toCharacterDual k i ν S) ∧
        LinearMap.ker (toCharacterDual k i ν S) = Submodule.span ℝ (D.realCorootsOf S) ∧
        Function.Bijective ((toCharacterDual k i ν S).domRestrict (rootAnnihilator T S))

/-- The comparison gives the bijectivity of restriction `X(P_0) ⊗ ℝ → X(T) ⊗ ℝ` used to read
heights in `𝔞_0`. -/
theorem bijective_restrictToTorus_empty (h : ParabolicSpacesComparisonStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : @IsGenericCocharacter k _ T G hG.isAffineHom i ν) :
    Function.Bijective (@restrictToTorus k _ G hG.isAffineHom T i ν ∅) := by
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  obtain ⟨D, -⟩ := relativeRootReflectionExistence k G hG T i hi
  obtain ⟨hinj, hrange, -⟩ := h k G hG T i hi ν hν D ∅ (Set.empty_subset _)
  refine ⟨hinj, ?_⟩
  rw [← LinearMap.range_eq_top, hrange]
  ext y
  simp

end Langlands.Global.ArthurParabolicSpaces

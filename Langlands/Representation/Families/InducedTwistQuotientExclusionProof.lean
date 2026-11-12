import Langlands.Representation.Families.InducedTwistQuotientExponentStatements
import Langlands.Representation.Families.InducedTwistExclusionGenericity
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Proof of exclusion of the inducing exponent from proper quotients -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- **Exclusion.** Away from a proper Zariski-closed set of unramified characters, no
`A_M`-exponent of `ρψ` is an `A_M`-exponent of the normalized Jacquet module of a quotient of
`i_P^G(ρψ)` by a nonzero invariant subspace. -/
theorem inducedTwistQuotientExclusion : InducedTwistQuotientExclusionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG _ _ P M U p l r hp hl hr hmul A a ha ρ hρ hadm
  classical
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  have := hG.smooth
  -- the represented geometric lemma for `r_P ∘ i_P`
  obtain ⟨m, c, z, hz, D, hglue⟩ := representedGeometricLemma k G hG P M U P M U
    p l r hp hl hr hmul p l r hp hl hr hmul
  -- a character of `M(k)` whose real part lies in the open chamber of `P`
  obtain ⟨pres⟩ := parabolicRootPresentationExistence k G hG P M A p l a hp hl ha
  have : Mono pres.data.i.hom.hom.left := pres.isCompatible.maximalSplit.isSplitSubtorus.mono
  obtain ⟨R, -⟩ := relativeRootReflectionExistence k G hG pres.data.T pres.data.i
    pres.isCompatible.maximalSplit
  obtain ⟨ζ, hζ⟩ := pres.exists_standardCocharacter
  have hfinite := IsSplitTorus.finite_relativeRoots pres.data.i
    pres.isCompatible.maximalSplit.isSplitSubtorus.1
  obtain ⟨x, hx⟩ := restrictedCorootChamber_nonempty pres.data.i pres.data.ν pres.data.J
    pres.data.f R hfinite ζ hζ
  let ψ₀ := leviPositiveUnramifiedCharacter l hl a pres.isCompatible.splitComponent x
  have hψ₀ : leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ₀ ∈
      restrictedCorootChamber pres.data.i pres.data.ν pres.data.J pres.data.f R := by
    rw [leviUnramifiedRealPart_positiveCharacter]
    exact hx
  -- one separating polynomial for every nonidentity piece
  have hpiece := fun i (hi : c i ≠ DoubleCoset.mk (pointImage p) (pointImage p) 1) =>
    exists_polynomial_pieceSeparation hG p l r hp hl hr hmul pres R ψ₀ hψ₀ ρ hρ hadm (D i)
      (by rw [hz i]; exact hi)
  choose F hF0 hF using hpiece
  let Fi : Fin m → MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ := fun i =>
    if h : c i ≠ DoubleCoset.mk (pointImage p) (pointImage p) 1 then F i h else 1
  refine ⟨∏ i, Fi i, Finset.prod_ne_zero_iff.mpr (fun i _ => ?_), ?_⟩
  · change Fi i ≠ 0
    unfold Fi
    split
    · exact hF0 i ‹_›
    · exact one_ne_zero
  intro ψ hψ χ hχ S hS
  refine not_isGeneralizedEigencharacter_jacquet_quotient_of_pieceSeparation hG p l r hp hl hr
    hmul ha _ ((SmoothRep.isIrreducible_twist_iff _ _ ρ).mpr hρ)
    ((SmoothRep.isAdmissible_twist_iff _ _ ρ).mpr hadm) c z hz D hglue χ hχ ?_ S hS
  intro i hi
  have hmem := (mem_rationalUnramifiedPrincipalOpen_prod l hl Finset.univ Fi ψ).mp hψ i
    (Finset.mem_univ _)
  have hmem' : ψ ∈ Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive
      (F i hi) := by
    unfold Fi at hmem
    split at hmem
    · exact hmem
    · exact absurd hi ‹_›
  exact hF i hi ψ hmem' χ hχ

end Langlands.Renard.AlgebraicFamily

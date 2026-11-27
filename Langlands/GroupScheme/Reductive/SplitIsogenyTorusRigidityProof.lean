import Langlands.GroupScheme.Reductive.SplitIsogenyTorusRigidityStatement
import Langlands.GroupScheme.Reductive.IsogenyRootDatumProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.GroupScheme.Reductive.FibrewiseCentralIsogenyReduction
import Langlands.GroupScheme.Torus.CharacterIsomorphism
import Langlands.LinearAlgebra.RootDatumIsogenyRigidity

/-! # Isogenies of split reductive groups with the same root characters agree on the torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, *Algebraic Groups* (2017), Proposition 23.8, in corrected form: two isogenies of
split reductive groups, one of the groups semisimple, whose restrictions to the split maximal
tori have character maps agreeing on every root of the target torus, agree on the source
torus. -/
theorem splitIsogenyTorusRigidity : SplitIsogenyTorusRigidityStatement.{u} := by
  intro k _ G G' hG hG' hss T T' i i' hT hi hT' hi' φ₁ φ₂ t₁ t₂ hs₁ hk₁ hc₁ hs₂ hk₂ hc₂
    hroots
  suffices h : t₁ = t₂ by rw [← hc₁, ← hc₂, h]
  let := hG.smooth
  let := hG.connectedSpace
  let := hG.isAffineHom
  let := hG'.smooth
  let := hG'.isAffineHom
  have hφ₁ : IsIsogeny φ₁ :=
    FibrewiseCentralIsogenyReduction.isogeny_of_surjective_of_finite_kernel φ₁ hs₁ hk₁
  have hφ₂ : IsIsogeny φ₂ :=
    FibrewiseCentralIsogenyReduction.isogeny_of_surjective_of_finite_kernel φ₂ hs₂ hk₂
  obtain ⟨J, _, P, hP, hPred⟩ := rootDatumExistence k G hG T hT i hi
  obtain ⟨J', _, P', hP', hP'red⟩ := rootDatumExistence k G' hG' T' hT' i' hi'
  let := hT.finite_characterLattice
  let := hT.finite_cocharacterLattice
  let := hT'.finite_characterLattice
  let := hT'.finite_cocharacterLattice
  obtain ⟨-, f₁, hf₁, -, -, -⟩ := isogenyRootDatum k G G' hG hG' T T' hT hT' i i' hi hi'
    φ₁ t₁ hφ₁ hc₁.symm J J' P P' hP hP'
  obtain ⟨-, f₂, hf₂, -, -, -⟩ := isogenyRootDatum k G G' hG hG' T T' hT hT' i i' hi hi'
    φ₂ t₂ hφ₂ hc₂.symm J J' P P' hP hP'
  have hagree : ∀ j, f₁.weightMap (P'.root j) = f₂.weightMap (P'.root j) := by
    intro j
    rw [hf₁, hf₂]
    apply hroots
    rw [← hP'.2.1]
    exact Set.mem_range_self j
  have hw : f₁.weightMap = f₂.weightMap := by
    rcases hss with hGs | hG's
    · have := (splitSemisimpleRootDatum k G hG T hT i hi J P hP).2.mp hGs
      exact LinearAlgebra.RootDatumIsogeny.weightMap_eq_of_finite_corootSpan f₁ f₂ hagree
    · have := (splitSemisimpleRootDatum k G' hG' T' hT' i' hi' J' P' hP').1.mp hG's
      exact LinearAlgebra.RootDatumIsogeny.weightMap_eq_of_finite_rootSpan f₁ f₂ hagree
  apply hT'.hom_ext_of_characters
  intro χ
  rw [← hf₁, ← hf₂, hw]

end Langlands.GroupScheme

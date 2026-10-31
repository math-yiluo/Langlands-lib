/-
Ported from `Theorems/Thm_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isPullback_glue_of_isPullback_of_isOpenImmersion
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {U₀ V₀ W₀ : Scheme.{u}} (u₀ : U₀ ⟶ Spec (CommRingCat.of R)) (v₀ : V₀ ⟶ Spec (CommRingCat.of R))
    (a : W₀ ⟶ U₀) (b : W₀ ⟶ V₀) [IsOpenImmersion a] [IsOpenImmersion b] (hab : a ≫ u₀ = b ≫ v₀)
    [QuasiCompact u₀] [QuasiSeparated u₀] [LocallyOfFinitePresentation u₀]
    [QuasiCompact v₀] [QuasiSeparated v₀] [LocallyOfFinitePresentation v₀] [QuasiCompact (a ≫ u₀)]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A))
    {U V W : Scheme.{u}} (jU : U ⟶ X) (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    (hcov : Set.range jU.base ∪ Set.range jV.base = Set.univ)
    (kU : W ⟶ U) (kV : W ⟶ V) (hW : IsPullback kU kV jU jV)
    (πU : U ⟶ U₀) (hU : IsPullback πU (jU ≫ g) u₀ (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (πV : V ⟶ V₀) (hV : IsPullback πV (jV ≫ g) v₀ (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (πW : W ⟶ W₀) (hWU : IsPullback kU πW πU a) (hWV : IsPullback kV πW πV b) :
    ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of R)) (π : X ⟶ X₀) (iU : U₀ ⟶ X₀) (iV : V₀ ⟶ X₀),
      IsOpenImmersion iU ∧ IsOpenImmersion iV ∧ iU ≫ f₀ = u₀ ∧ iV ≫ f₀ = v₀ ∧ a ≫ iU = b ≫ iV ∧
      Set.range iU.base ∪ Set.range iV.base = Set.univ ∧ IsPullback a b iU iV ∧
      πU ≫ iU = jU ≫ π ∧ πV ≫ iV = jV ≫ π ∧
      QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧ LocallyOfFinitePresentation f₀ ∧
      IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.solution u₀ v₀ a b hab g jU jV hcov kU kV hW πU hU πV hV πW hWU hWV

/-
Ported from `P2M/Sol/S_Module_Grassmannian_exists_scheme_represents_and_isClosedImmersion_toProjSpace.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; universe levels are generalized. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.RingTheory.Grassmannian.Representability
import Langlands.RingTheory.Grassmannian.ProjectiveEmbedding
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
namespace P2MW.S_Module_Grassmannian_exists_scheme_represents_and_isClosedImmersion_toProjSpace
attribute [-simp] CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (R : Type uz) [CommRing R] (M : Type uz) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ) :
    ∃ (Gr : Scheme.{uz}) (p : Gr ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (A : Type uz) [CommRing A] [Algebra R A],
        Module.Grassmannian A (A ⊗[R] M) k ≃
          {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      (∀ (A B : Type uz) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : Module.Grassmannian A (A ⊗[R] M) k),
        (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1) ∧
      ∃ (m : ℕ) (ι : Gr ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)),
        IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R m = p := by
  obtain ⟨Gr, p, pt, V, hnat, hV, hVaff, hVchart⟩ :=
    Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover R M k
  exact ⟨Gr, p, pt, hnat,
    Module.Grassmannian.exists_isClosedImmersion_toProjSpace_of_represents R M k Gr p pt hnat V hV hVaff hVchart⟩

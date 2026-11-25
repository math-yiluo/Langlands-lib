/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists
import WeilConjectures.AlgebraicGeometry.CoherentMapTorsionCompletionExt
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Lifting maps between torsion-controlled coherent arrows

Source: Stacks Project, Tags 0889(1) and 05EK.
(blueprint: lem-weil-pbc-torsion-controlled-completion-hom-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Completion and the arrow to H jointly determine a coherent comparison map.
There is no claim that completion alone is fully faithful.

Source: Stacks Project, Tag 0889(1), omitted uniqueness verification, using Tag 05EK.
(blueprint: lem-weil-pbc-torsion-controlled-completion-hom-lift).

Proof:
Work on an affine open Spec A and write I for the ideal of J. Coherence identifies
F, F' and H with finite A-modules. The finite-module tensor comparison identifies
completion with scalar extension to the flat ring A-hat, whose quotient by I is A/I.
Choose finitely many generators f_i of I. Both a and a' become isomorphisms after
localizing at f_i, since their kernels and cokernels are killed by powers of I.
Define the localized comparison by a followed by the inverse of a'. The given theta
is the completed comparison. The equation with the completed arrows shows that these
maps agree on completed localizations; they agree on double localizations because the
maps to H do. For each section x of F the images under these comparisons form an
element of the kernel of the gluing-complex differential for F'. Exactness of 05EK
produces a unique section of F'. Injectivity in 05EK proves additivity, A-linearity,
the equation with a', and the completion equation. It also proves uniqueness of this
module map. Tilde transfers it to a coherent-module morphism. On intersections refine
by affine opens; the same uniqueness identifies the restrictions. Glue the morphisms
with 00AL, and check both equations and uniqueness on that affine cover.
For I = A the arrows themselves are isomorphisms, so the same map is a followed by
the inverse of a'. For I = 0 completion is the constant system and theta is the map.
The empty scheme has unique morphisms; no nonempty-cover assumption is used.
-/
theorem torsionControlled_completion_hom_lift
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H F F' : CoherentModules X) (a : F ⟶ H) (a' : F' ⟶ H)
    (ha : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))))
    (ha' : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom))))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a) :
    ∃! g : F ⟶ F', g ≫ a' = a ∧ (completion X J).map g = θ := by
  obtain ⟨g, hg⟩ := torsionControlled_completion_hom_lift_exists J H F F' a a' ha ha' θ hθ
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  obtain ⟨s, hs, hk, hc⟩ := ha'
  symm
  apply coherentMap_torsion_completion_ext J F F' H a' ⟨s, hs, hk⟩ g g'
  · exact hg.1.trans hg'.1.symm
  · exact hg.2.trans hg'.2.symm

end AlgebraicGeometry

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.FiniteCyclic

/-!
# Cyclic Tate short complexes of isomorphic representations

Adapted by Worker 66 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

The fixed-field realization of an abstract extension changes both the
presentation of its cyclic group and the presentation of its coefficient
module.  This file records the second of the two functorial comparisons needed
to transport the local class-field-axiom theorem: replacing a representation by
an isomorphic one.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

open CategoryTheory

section RepresentationIso

variable {R Q : Type} [CommRing R] [CommGroup Q] [Fintype Q]

/-- Isomorphic representations have isomorphic cyclic `H⁰` short
complexes. -/
def normHomCompSubIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    Rep.FiniteCyclicGroup.normHomCompSub M g ≅
      Rep.FiniteCyclicGroup.normHomCompSub N g := by
  let i : ModuleCat.of R M.V ≅ ModuleCat.of R N.V :=
    (forget₂ (Rep R Q) (ModuleCat R)).mapIso e
  refine ShortComplex.isoMk i i i ?_ ?_
  · have h := congrArg
      (fun f : M ⟶ N => ModuleCat.ofHom f.hom.toLinearMap)
      (Rep.norm_comm e.hom)
    simpa [i, Rep.norm] using h
  · have hrep :
        e.hom ≫ (Rep.applyAsHom N g - 𝟙 N) =
          (Rep.applyAsHom M g - 𝟙 M) ≫ e.hom := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
        Category.id_comp, Rep.applyAsHom_comm]
    let F := forget₂ (Rep R Q) (ModuleCat R)
    change F.map e.hom ≫ F.map (Rep.applyAsHom N g - 𝟙 N) =
      F.map (Rep.applyAsHom M g - 𝟙 M) ≫ F.map e.hom
    rw [← F.map_comp, ← F.map_comp, hrep]

/-- Isomorphic representations have isomorphic cyclic `H⁻¹` short
complexes. -/
def subCompNormHomIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    Rep.FiniteCyclicGroup.subCompNormHom M g ≅
      Rep.FiniteCyclicGroup.subCompNormHom N g := by
  let i : ModuleCat.of R M.V ≅ ModuleCat.of R N.V :=
    (forget₂ (Rep R Q) (ModuleCat R)).mapIso e
  refine ShortComplex.isoMk i i i ?_ ?_
  · have hrep :
        e.hom ≫ (Rep.applyAsHom N g - 𝟙 N) =
          (Rep.applyAsHom M g - 𝟙 M) ≫ e.hom := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
        Category.id_comp, Rep.applyAsHom_comm]
    let F := forget₂ (Rep R Q) (ModuleCat R)
    change F.map e.hom ≫ F.map (Rep.applyAsHom N g - 𝟙 N) =
      F.map (Rep.applyAsHom M g - 𝟙 M) ≫ F.map e.hom
    rw [← F.map_comp, ← F.map_comp, hrep]
  · have h := congrArg
      (fun f : M ⟶ N => ModuleCat.ofHom f.hom.toLinearMap)
      (Rep.norm_comm e.hom)
    simpa [i, Rep.norm] using h

/-- Homology-level representation-isomorphism comparison in degree zero. -/
def normHomCompSubHomologyIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    (Rep.FiniteCyclicGroup.normHomCompSub M g).homology ≅
      (Rep.FiniteCyclicGroup.normHomCompSub N g).homology :=
  ShortComplex.homologyMapIso (normHomCompSubIsoOfRepIso e g)

/-- Homology-level representation-isomorphism comparison in degree
minus one. -/
def subCompNormHomHomologyIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    (Rep.FiniteCyclicGroup.subCompNormHom M g).homology ≅
      (Rep.FiniteCyclicGroup.subCompNormHom N g).homology :=
  ShortComplex.homologyMapIso (subCompNormHomIsoOfRepIso e g)

end RepresentationIso

end
end Langlands.NYLL.LocalClassFieldTheory

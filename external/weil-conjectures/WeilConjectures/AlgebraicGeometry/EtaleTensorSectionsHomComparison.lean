/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
import WeilConjectures.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality

/-!
# Comparing tensor-pullback sections with the presheaf of module homomorphisms

Source: Stacks Project, Descent, Tag 03DT, proof of Lemma 35.8.1, the identification
of a section with a morphism from the pulled-back structure sheaf; Tag 03DR,
equation (35.8.0.1) (blueprint: lem-sc-etale-tensor-sections-hom-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false


private theorem evaluation_bijective {X : Scheme.{u}} (F : X.Modules) (U : X.Etale) :
    Function.Bijective (etaleTensorHomEvaluation F U) := by
  constructor
  · intro φ ψ h
    have h' : (pullbackObjUnitIso U.hom).inv ≫ φ ≫
        (tensorSectionsPullbackComparison U.hom).inv.app F =
        (pullbackObjUnitIso U.hom).inv ≫ ψ ≫ (tensorSectionsPullbackComparison U.hom).inv.app F :=
      unit_hom_ext h
    simpa using h'
  · intro s
    refine ⟨(pullbackObjUnitIso U.hom).hom ≫
      homOfGlobalSection ((tensorPullback U.hom).obj F) s ≫
      (tensorSectionsPullbackComparison U.hom).hom.app F, ?_⟩
    dsimp only [etaleTensorHomEvaluation]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      Iso.inv_hom_id_assoc]
    rw [homOfGlobalSection_app_one, presheaf_map_id_apply]

/-- Sections of tensor pullbacks and homomorphisms from the pulled-back structure sheaf
are naturally isomorphic as presheaves of sets. No quasi-coherence assumption is needed.

Source: Stacks Project, Tag 03DT, proof of Lemma 35.8.1, the reinterpretation of sections
as module maps; Tag 03DR, equation (35.8.0.1).
(blueprint: lem-sc-etale-tensor-sections-hom-comparison).

Proof:
1. For `u : U → X`, compare `tensorPullback u` with Mathlib's `pullback u` by uniqueness
   of left adjoints to `pushforward u`. Use the adjunction selected in
   `exists_tensorPullbackAdjunction` and Mathlib's `pullbackPushforwardAdjunction`.
   The resulting comparison intertwines the two adjunction units.
2. Pullback of the structure sheaf is canonically the structure sheaf of `U`.
   A section of the pullback of `F` corresponds to the module map from that structure
   sheaf sending a local function `a` to `a` times the restricted section. Conversely,
   a module map is recovered from its value at `1`. Transport the target through the
   comparison in step 1 and the source through the structure-sheaf pullback isomorphism.
   These constructions are mutually inverse: linearity determines a map on every
   local function from its value at `1`, and the image of `1` under multiplication by
   the section is the section itself.
3. For `g : V → U` over `X`, pullback of the map in step 2 is multiplication by the
   pulled-back section. The comparison in step 1 respects composition because both
   comparison composites are the unique comparison of left adjoints intertwining
   the composite adjunction units. In particular, `tensorSectionsComp` is exactly the
   composition comparison normalized by those units. The equality `g ≫ u = v` gives
   the same equality transport on both sides. Hence the component bijections commute
   with `etaleTensorSectionsRestriction` and with the maps of `etaleHom`.
4. The component bijections and this naturality assemble into a natural isomorphism.
   This uses neither a covering nor a sheaf condition. -/
theorem nonempty_etaleTensorSectionsHomIso {X : Scheme.{u}} (F : X.Modules) :
    Nonempty ((etaleTensorSectionsPresheaf F ⋙ CategoryTheory.forget AddCommGrpCat) ≅
      etaleHom (unitObj X) F) := by
  classical
  let e : etaleHom (unitObj X) F ≅
      etaleTensorSectionsPresheaf F ⋙ CategoryTheory.forget AddCommGrpCat :=
    NatIso.ofComponents
      (fun U ↦ (Equiv.ofBijective (etaleTensorHomEvaluation F U.unop)
        (evaluation_bijective F U.unop)).toIso)
      (fun g ↦ etaleTensorHomEvaluation_naturality F g)
  exact ⟨e.symm⟩

end AlgebraicGeometry.Scheme.Modules

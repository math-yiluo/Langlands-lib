/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective

import WeilConjectures.AlgebraicGeometry.EtaleClosedSectionShrink
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageSectionDescription

/-! # Local representatives around a closed subscheme

Source: Stacks Project, Tag 09ZF, fourth proof paragraph, local shrinking argument.
(blueprint: lem-weil-pbc-etale-closed-section-local-family).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Local sections whose unit equations hold on the entire closed base changes.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph, through the equation
`t|_{U_j times_X Z} = i⁻¹s_j`.
(blueprint: lem-weil-pbc-etale-closed-section-local-family).

Proof: Identify the pullback of the identity X-object with the identity Z-object,
using the canonical pullback isomorphism. Apply the local inverse-image section
description to t transported along this isomorphism. This produces an étale cover
V_j of Z and maps a_j to the closed base changes of étale X-objects U_j, together
with sections s_j and equality after restriction to V_j. Each a_j is étale by
cancellation and has open image. The closed embedding of the base change into U_j
identifies this image with the intersection of an ambient open W_j with the closed
base change. Replace U_j by W_j and restrict s_j. Then V_j maps surjectively to
its whole closed base change. Separatedness for this singleton étale cover promotes
the equality to the whole base change. Unit naturality preserves the equation under
restriction. Since the V_j cover Z, the images of the shrunk U_j contain i(Z).
All operations preserve the original universe-u index set. If Z is empty, choose
the empty index set; both clauses are vacuous. No compactness or restriction-unit
injectivity is used. -/
theorem etale_closed_section_local_family
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X))))) :
    ∃ (J : Type u) (U : J → X.Etale) (s : ∀ j, F.obj.obj (op (U j))),
      Set.range i ⊆ ⋃ j, Set.range (U j).hom ∧
      ∀ j, etaleSetDescentUnit i F (U j) (s j) =
        ((Scheme.etaleSetPullback i).obj F).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ i).map
            (MorphismProperty.Over.homMk (U j).hom (Category.comp_id _) :
              U j ⟶ Scheme.Etale.mk (𝟙 X))).op t := by
  classical
  let B := MorphismProperty.Over.pullback @Etale ⊤ i
  let H := (Scheme.etaleSetPullback i).obj F
  let e : Scheme.Etale.mk (𝟙 Z) ≅ B.obj (Scheme.Etale.mk (𝟙 X)) :=
    (MorphismProperty.Over.mkIdTerminal @Etale Z).uniqueUpToIso
      ((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _)
  obtain ⟨J, V, π, hπ, hrep⟩ := etaleInverseImageSectionDescription X Z i F
    (H.obj.map e.hom.op t)
  have hlocal : ∀ j, ∃ (U : X.Etale) (s : F.obj.obj (op U)),
      Set.range ((V j).hom ≫ i) ⊆ Set.range U.hom ∧
      etaleSetDescentUnit i F U s = H.obj.map
        (B.map (MorphismProperty.Over.homMk U.hom (Category.comp_id _) :
          U ⟶ Scheme.Etale.mk (𝟙 X))).op t := by
    intro j
    obtain ⟨U, a, s, hs⟩ := hrep j
    have ht : H.obj.map
        (((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _).from (V j)).op t =
        H.obj.map a.op (etaleSetDescentUnit i F U s) := by
      rw [← Functor.map_comp_apply, ← op_comp] at hs
      have he : π j ≫ e.hom =
          ((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _).from (V j) :=
        ((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj B _).hom_ext _ _
      rw [he] at hs
      exact hs
    exact etale_closed_section_shrink i F t (V j) U a s ht
  choose U s hr he using hlocal
  refine ⟨J, U, s, ?_, he⟩
  rintro x ⟨z, rfl⟩
  have hc := (Scheme.ofArrows_mem_smallEtaleTopology_iff π).mp hπ
  have hz : z ∈ ⋃ j, Set.range (π j).left := by rw [hc]; trivial
  obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hz
  have hπhom : (π j).left = (V j).hom := by
    have h := MorphismProperty.Over.w (π j)
    change (π j).left ≫ 𝟙 Z = (V j).hom at h
    exact (Category.comp_id ((π j).left)).symm.trans h
  apply Set.mem_iUnion.mpr
  refine ⟨j, hr j ?_⟩
  refine ⟨y, ?_⟩
  change i ((V j).hom y) = i z
  rw [← hπhom]
  exact congrArg i hy

end AlgebraicGeometry

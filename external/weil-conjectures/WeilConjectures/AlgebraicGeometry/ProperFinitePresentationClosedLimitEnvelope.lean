/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ChowFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.EventuallyClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! The proper finitely presented closed envelope clause of Lemma 09ZR.
(blueprint: lem-weil-pbc-proper-closed-in-proper-fp-envelope-part)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A proper scheme over a qcqs base embeds as a closed subscheme of a proper
finitely presented scheme over that base.

Source: Stacks Project, Limits, Lemma 09ZR
(blueprint: lem-weil-pbc-proper-closed-in-proper-fp-envelope-part).

Proof:
1. Properness gives finite type and separatedness. By
   theorem-nagata-s-compactification-theorem--1 (01ZJ), embed X into a separated finitely
   presented S-scheme Y. Both X and Y are qcqs by
   lem-weil-pbc-qcqs-morphism-permanence.
2. Apply lem-weil-pbc-chow-finite-type (0202) to Y: obtain a proper surjective
   Y' → Y and an immersion Y' → projective space over S. The latter space is proper
   over S by lemma-nagata-projective-space-base-change-proper.
3. By lemma-nagata-closed-subscheme-fp-system (09ZP), express X as the inverse limit
   of the closed subschemes Xᵢ of Y defined by finite-type subideals of its ideal.
   Zero and sums make this a nonempty directed set. Every Xᵢ is finitely presented
   over S by lem-weil-pbc-proper-fp-permanence, and all transitions and projections
   are closed immersions. They are affine by lem-weil-pbc-closed-immersion-finite,
   so this is the limit of lem-weil-pbc-limit-affine-transition.
4. Pull back Xᵢ and X to Y', obtaining X'ᵢ and X'. Base change preserves closed
   immersions by lem-weil-pbc-proper-fp-permanence. Limits of sets commute with
   fibre products; directedness makes the constant factors stay constant. Thus
   the compatible maps X' → X'ᵢ form a limiting cone by Yoneda.
5. The scheme X' is proper over S by base change and composition. Its immersion
   into projective space is proper by lem-weil-pbc-proper-over-separated and hence
   closed by lem-weil-pbc-proper-immersion-closed.
6. Apply lem-weil-pbc-eventually-closed-immersion (0A0N) to X'ᵢ in projective space.
   The needed qcqs and finite-type properties follow from steps 1–4 and
   lem-weil-pbc-qcqs-morphism-permanence. From some stage onward these immersions
   are closed; closure under composition is lem-weil-pbc-closed-immersion-comp.
7. These X'ᵢ are proper over S. Their maps onto Xᵢ are surjective by
   lem-weil-pbc-surjective-base-change. By lem-weil-pbc-image-universally-closed
   (03GN), Xᵢ is universally closed over S. Its separatedness and finite type from
   step 3 therefore make it proper.
8. Choose a stage at or beyond the bound from step 6. Step 7 makes its structure
   map proper. Step 3 makes it finitely presented and gives a closed immersion
   from X, whose composition with the structure map is f. This is the envelope. -/
theorem exists_proper_finitePresentation_closedImmersion_envelope
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ S),
      IsClosedImmersion i ∧ IsProper g ∧ LocallyOfFinitePresentation g ∧
        QuasiCompact g ∧ QuasiSeparated g ∧ i ≫ g = f := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨Y, i, g, hi, hgfp, hgqc, hgsep, hif⟩ :=
    f.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  obtain ⟨n, Y', π, j, hπ, hπs, hj, hjover⟩ := exists_chow_finite_type g
  let P := ProjectiveSpace (ULift.{u} (Fin (n + 1))) S
  let p : P ⟶ S := P ↘ S
  let I := i.ker
  let D := I.fgSubDiagram
  let c := I.fgSubCone
  let q : D ⟶ (Functor.const (I.FGSub)ᵒᵖ).obj Y :=
    { app := fun a ↦ a.unop.1.subschemeι
      naturality := fun a b t ↦ by simp [D] }
  have hq (a : (I.FGSub)ᵒᵖ) : c.π.app a ≫ q.app a = I.subschemeι := by
    simp [c, q]
  let : IsConnected (I.FGSub)ᵒᵖ := IsCofiltered.isConnected _
  let E : (I.FGSub)ᵒᵖ ⥤ Scheme.{u} :=
    { obj := fun a ↦ pullback π (q.app a)
      map := fun {a b} t ↦ pullback.map _ _ _ _ (𝟙 Y') (D.map t) (𝟙 Y)
        (by simp) (by simp)
      map_id := fun a ↦ by apply pullback.hom_ext <;> simp
      map_comp := fun t t' ↦ by apply pullback.hom_ext <;> simp }
  let d : Cone E :=
    { pt := pullback π I.subschemeι
      π :=
        { app := fun a ↦ pullback.map _ _ _ _ (𝟙 Y') (c.π.app a) (𝟙 Y)
            (by simp) (by simp [hq])
          naturality := fun a b t ↦ by
            apply pullback.hom_ext
            · simp [E]
            · simpa [E, D, Category.assoc] using
                (congrArg (fun z ↦ pullback.snd π I.subschemeι ≫ z) (c.w t)).symm } }
  let β : E ⟶ D :=
    { app := fun a ↦ pullback.snd π (q.app a)
      naturality := fun a b t ↦ by simp [E] }
  have hd : IsLimit d :=
    isLimitOfIsPullbackOfIsConnected β d c
      { hom := pullback.snd π I.subschemeι
        w := fun a ↦ by simp [d, β] }
      (fun a ↦ isPullback_pullback_map π I.subschemeι (q.app a) (c.π.app a) (hq a))
      I.isLimitFgSubCone
  let h : E ⟶ (Functor.const (I.FGSub)ᵒᵖ).obj P :=
    { app := fun a ↦ pullback.fst π (q.app a) ≫ j
      naturality := fun a b t ↦ by simp [E] }
  let k : d.pt ⟶ P := pullback.fst π I.subschemeι ≫ j
  have hkover : k ≫ p = pullback.snd π I.subschemeι ≫ I.subschemeι ≫ g := by
    dsimp [k, p, P]
    rw [Category.assoc, hjover, pullback.condition_assoc]
  have : IsProper (I.subschemeι ≫ g) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) i.toImage]
    simpa [I, ← Category.assoc, hif] using (inferInstance : IsProper f)
  have : IsProper (k ≫ p) := by rw [hkover]; infer_instance
  have : IsProper k := IsProper.of_comp k p
  have : IsImmersion k := inferInstance
  have : IsClosedImmersion k := IsClosedImmersion.of_universallyClosed k
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated p
  have (a : (I.FGSub)ᵒᵖ) : CompactSpace (E.obj a) := by
    dsimp [E]
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd π (q.app a))
  have (a : (I.FGSub)ᵒᵖ) : QuasiSeparatedSpace (E.obj a) := by
    dsimp [E]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd π (q.app a))
  have {a b : (I.FGSub)ᵒᵖ} (t : a ⟶ b) : IsClosedImmersion (E.map t) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (isPullback_pullback_map π (q.app a) (q.app b) (D.map t)
        (by simp)).flip inferInstance
  have hover (a : (I.FGSub)ᵒᵖ) : h.app a ≫ p = β.app a ≫ q.app a ≫ g := by
    dsimp [h, β, p, P]
    rw [Category.assoc, hjover, pullback.condition_assoc]
  have (a : (I.FGSub)ᵒᵖ) : LocallyOfFiniteType (h.app a) := by
    dsimp [h, E]
    infer_instance
  obtain ⟨a, ha⟩ := eventually_isClosedImmersion_of_isLimit P E h d hd k
    (fun a ↦ by simp [d, h, k])
  have : IsClosedImmersion (h.app (op a)) := ha a le_rfl
  have : IsProper (h.app (op a) ≫ p) := inferInstance
  have : UniversallyClosed (β.app (op a) ≫ q.app (op a) ≫ g) := by
    rw [← hover]
    infer_instance
  have : Surjective (β.app (op a)) := by dsimp [β]; infer_instance
  have : UniversallyClosed (q.app (op a) ≫ g) :=
    UniversallyClosed.of_comp_surjective (β.app (op a)) (q.app (op a) ≫ g)
  have : IsProper (q.app (op a) ≫ g) := { }
  refine ⟨D.obj (op a), i.toImage ≫ c.π.app (op a), q.app (op a) ≫ g,
    inferInstance, inferInstance, ?_, inferInstance, inferInstance, ?_⟩
  · dsimp [q]
    infer_instance
  · rw [Category.assoc, ← Category.assoc (c.π.app (op a)), hq]
    simpa [I, ← Category.assoc] using hif

end AlgebraicGeometry

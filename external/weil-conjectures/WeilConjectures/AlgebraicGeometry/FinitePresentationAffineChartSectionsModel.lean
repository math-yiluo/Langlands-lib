/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.FinitePresentation

import WeilConjectures.AlgebraicGeometry.AffineChartSectionsColimitComparison
import WeilConjectures.Algebra.Homology.FinitePresentationPreorderColimitModel
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Algebraic models for affine chart sections
Source: Stacks Project, Tags 01ZR and 05N7. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The finite presentation of the restricted module descends as algebraic sections.
Source: Stacks Project, Algebra Tag 05N7 and Limits Tag 01ZR, affine object clause.
(blueprint: lem-pc-fp-affine-chart-sections-model).

Proof: On the upper tail above i the stage chart rings are base changes of the fixed
chart ring. Affine pullback identifies these with tensor products, which commute
with directed colimits. Uniqueness of the affine limit identifies the limit chart
ring with that colimit. The restriction of M has finitely presented sections since
it is finitely presented and the chart is affine. Apply the object clause of module
descent over a directed preorder: lift a finite relation matrix and form its range
quotient at a stage. Its scalar extension is the original sections module. The
pullback pasting isomorphism identifies the limit chart with the iterated chart
in the conclusion, and transports the section comparison. Zero rings and modules
are treated by the same relation quotient; no choice of unspecified sheaf data
is made. -/
theorem exists_finitePresentation_affine_chart_sections_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (M : (pullback f (c.π.app (op i))).Modules)
    (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent)
    (V : Xi.OpenCover.{u}) (a : V.I₀) (ha : IsAffine (V.X a)) :
    ∃ (j : I) (hij : i ≤ j),
      let U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u} :=
        V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE hij))))
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
      let Y := (U.pullback₁ p).X a
      let P := (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M
      ∃ Q : ModuleCat.{u} Γ(U.X a, ⊤),
        Module.FinitePresentation Γ(U.X a, ⊤) Q ∧
        Nonempty ((ModuleCat.extendScalars (U.pullbackHom p a).appTop.hom).obj Q ≅
          ModuleCat.of Γ(Y, ⊤) Γ(P, ⊤)) := by
  classical
  let J := {j : I // i ≤ j}
  have : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  have : IsDirected J (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let W := V.pullback₁ (pullback.fst f (c.π.app (op i)))
  let Z := W.X a
  let P₀ := (Scheme.Modules.pullback (W.f a)).obj M
  let N := ModuleCat.of Γ(Z, ⊤) Γ(P₀, ⊤)
  have : IsAffine (V.X a) := ha
  have : IsAffineHom (c.π.app (op i)) :=
    @isAffineHom_of_isAffine c.pt (Spec (R.obj i)) _ inferInstance inferInstance
  have : IsAffineHom (pullback.fst f (c.π.app (op i))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffine Z := by
    change IsAffine (pullback (pullback.fst f _) (V.f a))
    exact isAffine_of_isAffineHom (pullback.snd _ _)
  have : M.IsFinitePresentation := hM
  have : M.IsQuasicoherent := hMq
  have : P₀.IsFinitePresentation := inferInstance
  have hN : Module.FinitePresentation Γ(Z, ⊤) N :=
    Scheme.Modules.finitePresentation_sections_of_isFinitePresentation P₀ (isAffineOpen_top Z)
  obtain ⟨F, q, hcompare⟩ :=
    exists_affine_chart_sections_colimit_comparison R c hc i f M V a ha
  let X := (ModuleCat.extendScalars q.inv.hom).obj N
  let : Algebra Γ(Z, ⊤) (colimit F : CommRingCat.{u}) := q.inv.hom.toAlgebra
  have : Module.FinitePresentation Γ(Z, ⊤) N := hN
  have hX : Module.FinitePresentation (colimit F : CommRingCat.{u}) X := by
    change Module.FinitePresentation (colimit F : CommRingCat.{u})
      (TensorProduct Γ(Z, ⊤) (colimit F : CommRingCat.{u}) N)
    infer_instance
  obtain ⟨j, Q, hQ, ⟨eQ⟩⟩ :=
    ModuleCat.exists_finitePresentation_model_of_preorder_colimit F X hX
  obtain ⟨e, s, hmaps, ⟨t⟩⟩ := hcompare j
  let U : (pullback f (Spec.map (R.map (homOfLE j.property)))).OpenCover.{u} :=
    V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE j.property))))
  let p := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
    (T' := Over.mk (c.π.app (op i)))
    (Over.homMk (c.π.app (op j.val)) (c.w (homOfLE j.property).op))
  let g := U.pullbackHom p a
  let Q' := (ModuleCat.extendScalars e.hom.hom).obj Q
  have : Module.FinitePresentation (F.obj j) Q := hQ
  let : Algebra (F.obj j) Γ(U.X a, ⊤) := e.hom.hom.toAlgebra
  have hQ' : Module.FinitePresentation Γ(U.X a, ⊤) Q' := by
    change Module.FinitePresentation Γ(U.X a, ⊤) (TensorProduct (F.obj j) Γ(U.X a, ⊤) Q)
    infer_instance
  have hinv : q.hom.hom.comp q.inv.hom = RingHom.id Γ(Z, ⊤) :=
    congrArg CommRingCat.Hom.hom q.inv_hom_id
  let cancel : (ModuleCat.extendScalars q.hom.hom).obj X ≅ N :=
    ((ModuleCat.extendScalarsComp q.inv.hom q.hom.hom).app N).symm ≪≫
      eqToIso (congrArg (fun r ↦ (ModuleCat.extendScalars r).obj N) hinv) ≪≫
      (ModuleCat.extendScalarsId Γ(Z, ⊤)).app N
  have hr : s.hom.hom.comp (q.hom.hom.comp (colimit.ι F j).hom) =
      g.appTop.hom.comp e.hom.hom :=
    congrArg CommRingCat.Hom.hom hmaps
  refine ⟨j.val, j.property, Q', hQ', ⟨?_⟩⟩
  exact ((ModuleCat.extendScalarsComp e.hom.hom g.appTop.hom).app Q).symm ≪≫
    eqToIso (congrArg (fun r ↦ (ModuleCat.extendScalars r).obj Q) hr.symm) ≪≫
    (ModuleCat.extendScalarsComp (q.hom.hom.comp (colimit.ι F j).hom) s.hom.hom).app Q ≪≫
    (ModuleCat.extendScalars s.hom.hom).mapIso
      ((ModuleCat.extendScalarsComp (colimit.ι F j).hom q.hom.hom).app Q ≪≫
        (ModuleCat.extendScalars q.hom.hom).mapIso eQ ≪≫ cancel) ≪≫ t

end AlgebraicGeometry

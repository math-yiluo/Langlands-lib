/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearSliceScalarGeneratorsBasic
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.Algebra.Homology.Slice.SliceSystemExtensionConstruction

/-! # Finite evaluation of extension by zero on strict coefficient towers

Source: current blueprint theorem-sp-qbar, proof (2), open factor.
The coefficient diagram consists of actual ring sheaves. In particular it may be
formed from the pulled-back continuous condensed ell-power quotient rings. No
native-to-constant coefficient presentation or finiteOpenIso is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.sheafCompose

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r}) (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The ordinary evaluation comparison is the identity on the prescribed level
objects. Source: theorem-sp-qbar, proof (2), open evaluation
(blueprint: lem-pur-native-open-finite-evaluation). -/
def SliceSystemExtensionPresentation.evaluationIso
    (P : SliceSystemExtensionPresentation.{c, v, r} B U) (n : ℕ) :
    P.F ⋙ systemEvaluation.{c, v, max c v r} B n ≅
      systemEvaluation.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U) n ⋙
        localizedSystemExtension.{c, v, r} (B.obj (op n)) U :=
  NatIso.ofComponents (fun M ↦ eqToIso (P.obj_eq M n)) (by
    intro M N f
    change (P.F.map f).app n ≫ eqToHom (P.obj_eq N n) =
      eqToHom (P.obj_eq M n) ≫
        (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map (f.app n)
    rw [P.map_eq]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

private theorem sliceExtension_map_exact
    (P : SliceSystemExtensionPresentation.{c, v, r} B U)
    (S : ShortComplex (StrictRingSystem.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U)))
    (hS : S.Exact) : (S.map P.F).Exact := by
  let evs : JointlyReflectIsomorphisms (fun n : ℕ ↦ systemEvaluation.{c, v, max c v r} B n) :=
    ⟨fun f h ↦ (strictRingSystem_isIso_iff B f).2 h⟩
  apply (evs.exact_iff _).2
  intro n
  have := localizedSystemExtensionAdditive.{c, v, r} (B.obj (op n)) U
  have := localizedSystemExtensionLimits.{c, v, r} (B.obj (op n)) U
  have := localizedSystemExtensionColimits.{c, v, r} (B.obj (op n)) U
  have h : ((S.map (systemEvaluation.{max c v, v, max c v r}
      (sliceScalarRings.{c, v, r} B U) n)).map
        (localizedSystemExtension.{c, v, r} (B.obj (op n)) U)).Exact :=
    (hS.map (systemEvaluation.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U) n)).map
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U)
  exact ShortComplex.exact_of_iso
    (S.mapNatIso (P.evaluationIso B U n)).symm h

/-- Extension is exact on whole strict systems, as detected by ordinary evaluation.
Source: theorem-sp-qbar, proof (2), exact open factor
(blueprint: lem-pur-native-open-finite-evaluation).
Proof: the evaluation comparison identifies each component with exact slice
extension. Exact evaluation and the componentwise isomorphism criterion jointly
detect exact short complexes. The abelian exactness criterion gives both finite
limits and finite colimits. This uses ordinary evaluation, never faithfulness
of evaluation in the derived category. -/
theorem SliceSystemExtensionPresentation.exact
    (P : SliceSystemExtensionPresentation.{c, v, r} B U) :
    PreservesFiniteLimits P.F ∧ PreservesFiniteColimits P.F := by
  have : P.F.PreservesHomology :=
    Functor.preservesHomology_of_map_exact P.F (sliceExtension_map_exact B U P)
  exact ⟨Functor.preservesFiniteLimits_of_preservesHomology P.F,
    Functor.preservesFiniteColimits_of_preservesHomology P.F⟩

/-- Extension by zero on actual strict ring-sheaf towers commutes with each finite
evaluation after exact localization, with its canonical localization normalization. The ordinary
presentation fixes its action on every extension summand and every semilinear
transition, including equal levels. Thus this is a map of whole derived systems.
For the purity application B is the diagram of section rings of the pulled-back
continuous condensed O_E/ell^(n+1), and U is the open object of a compactification.
Source: current blueprint theorem-sp-qbar, proof (2), open factor;
Stacks 03DI and 03DJ (blueprint: lem-pur-native-open-finite-evaluation).

Proof: construct ordinary strict extension by direct sums and sheafification.
Its transitions extend the input transitions on each original summand, so their
identity and composition hold before localization. The prescribed level-object
and morphism equations give the ordinary evaluation isomorphism. It proves
exactness of extension by the componentwise exactness criterion. Localize the
ordinary square using the exact-functor comparison. Its canonical localization
fixes the comparison on every complex representative. No assertion that derived
evaluations detect equality is made. Empty opens, zero complexes and n=0 use the
same construction, without division by a coefficient or a ramification bound. -/
theorem nativeOpen_finiteEvaluation :
    ∃ P : SliceSystemExtensionPresentation.{c, v, r} B U,
      ∃ (_ : PreservesFiniteLimits P.F) (_ : PreservesFiniteColimits P.F),
      ∀ n : ℕ,
        letI : HasDerivedCategory (systemLevel.{c, v, max c v r} B n) :=
          HasDerivedCategory.standard _
        letI : HasDerivedCategory (systemLevel.{max c v, v, max c v r}
            (sliceScalarRings.{c, v, r} B U) n) := HasDerivedCategory.standard _
        letI : HasDerivedCategory (SheafOfModules.{max c v r}
            (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
              (B.obj (op n))).over U)) := HasDerivedCategory.standard _
        letI := localizedSystemExtensionAdditive.{c, v, r} (B.obj (op n)) U
        letI := localizedSystemExtensionLimits.{c, v, r} (B.obj (op n)) U
        letI := localizedSystemExtensionColimits.{c, v, r} (B.obj (op n)) U
        ∃ e :
        P.F.mapDerivedCategory ⋙ (systemEvaluation.{c, v, max c v r} B n).mapDerivedCategory ≅
          (systemEvaluation.{max c v, v, max c v r}
            (sliceScalarRings.{c, v, r} B U) n).mapDerivedCategory ⋙
            (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).mapDerivedCategory,
        e = Functor.mapDerivedCategorySquareIso (P.evaluationIso B U n) := by
  obtain ⟨P⟩ := exists_sliceSystemExtensionPresentation.{c, v, r} B U
  obtain ⟨hl, hc⟩ := P.exact B U
  exact ⟨P, hl, hc, fun n ↦ ⟨_, rfl⟩⟩

end SheafOfModules

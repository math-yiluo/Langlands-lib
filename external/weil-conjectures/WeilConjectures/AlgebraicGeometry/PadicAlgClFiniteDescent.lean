/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!
# Finite coefficient descent for algebraic-closure constructible complexes

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Lemma 7.9 and
Theorem 7.7 (blueprint: lem-fd-qbar-finite-descent).

The coefficients use the existing finite-subextension-valued condensed algebraic closure.
All scalar extensions are the existing derived extensions on ordinary module derived
categories. The finite model and every finite enlargement use bounded constructibility
with no derived completeness condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A bounded constructible complex over the finite-subextension-valued condensed
algebraic closure descends to one finite coefficient field, and the resulting model
remains bounded constructible and a model after every finite enlargement.

Source: Hemo--Richarz--Scholbach, Lemma 7.9 and Theorem 7.7
(blueprint: lem-fd-qbar-finite-descent).

Proof plan, following the four steps of the node:
1. The locally Noetherian and quasi-compact hypotheses packaged by `IsNoetherian`
make the underlying space Noetherian. Equivalently, the minimal-closed-subset result
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` rules out infinite strict
descending chains of closed subsets. No separation or finite-type hypothesis is used.
2. Apply `constructibleCocone_essSurjObj` (`proposition-dctf-x-qbar-2-colimit--2`) to `K`.
It produces a finite intermediate field `F`, a bounded constructible `K_F`, and an
isomorphism from `constructibleToPadicAlgCl` applied to `K_F` to `K`. Map that isomorphism
along the full-subcategory inclusion. The cocone functor is the restriction of
`derivedExtendScalarsToPadicAlgCl`, so this is the required ambient derived isomorphism.
3. For `h : F ≤ F'`, apply `boundedConstructible_derivedExtendScalarsSubfield_obj`
(`lemma-extension-scalars-preserves-dctf--1`) to `K_F`. This proves bounded constructibility
of the derived scalar extension to `F'`.
4. Evaluate `derivedExtendScalarsCompIso` (`definition-sp-scalar-extension--2`) at
`K_F.obj`, and compose with the isomorphism from step 2. This gives the second
displayed isomorphism, also when `F' = F` and `h` is reflexivity. -/
theorem exists_padicAlgCl_finite_descent
    (ℓ : ℕ) [Fact ℓ.Prime] (Z : Scheme.{u}) [IsNoetherian Z]
    (K : PadicAlgClConstructible Z ℓ) :
    ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (K_F : PadicSubfieldConstructible Z ℓ F),
      Nonempty ((derivedExtendScalarsToPadicAlgCl Z ℓ F).obj K_F.obj ≅ K.obj) ∧
      ∀ (F' : PadicAlgCl.FiniteIntermediateField ℓ) (h : F ≤ F'),
        boundedConstructible (padicSubfieldRingObj Z ℓ F')
          ((derivedExtendScalarsSubfield Z ℓ h).obj K_F.obj) ∧
        Nonempty ((derivedExtendScalarsToPadicAlgCl Z ℓ F').obj
          ((derivedExtendScalarsSubfield Z ℓ h).obj K_F.obj) ≅ K.obj) := by
  obtain ⟨F, K_F, ⟨e⟩⟩ := constructibleCocone_essSurjObj Z ℓ K
  let e' : (derivedExtendScalarsToPadicAlgCl Z ℓ F).obj K_F.obj ≅ K.obj :=
    (boundedConstructible (padicAlgClRingObj Z ℓ)).ι.mapIso e
  refine ⟨F, K_F, ⟨e'⟩, fun F' h ↦ ⟨?_, ?_⟩⟩
  · exact boundedConstructible_derivedExtendScalarsSubfield_obj Z ℓ h K_F
  · exact ⟨(derivedExtendScalarsCompIso Z ℓ h).app K_F.obj ≪≫ e'⟩

end AlgebraicGeometry.ProEtale

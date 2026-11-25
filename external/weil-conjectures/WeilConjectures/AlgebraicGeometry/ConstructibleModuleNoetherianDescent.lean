/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent

/-!
# Noetherian descent of constructible module sheaves

Source: Stacks Project, Etale Cohomology, Lemma 09Z7 (proof, first paragraph)
(blueprint: lem-weil-pbc-constructible-module-noetherian-descent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A constructible sheaf of modules on a quasi-compact, quasi-separated scheme descends
along a morphism to a constructible sheaf on a Noetherian scheme.
Source: Stacks Project, Etale Cohomology, Lemma 09Z7 (proof, first paragraph)
(blueprint: lem-weil-pbc-constructible-module-noetherian-descent).
Proof outline: (1) Noetherian approximation gives a cofiltered system of schemes of
finite type over `Spec ℤ` with affine transitions and limit `X`, using
`theorem-nagata-s-compactification-theorem--1` and `theorem-nagata-s-compactification-theorem--1`.
(2) Reindex it by a directed set using
`lem-weil-pbc-cofiltered-limit-directed-reindex`.
(3) Each stage is Noetherian, hence quasi-compact and quasi-separated, by
`pqf-lem-locnoeth-lft` and `lem-weil-pbc-locally-noetherian-quasi-separated`.
(4) `lem-weil-pbc-constructible-module-limit-descent` descends `F` to a
constructible `F'` at one stage and supplies the displayed inverse-image isomorphism.
(5) Taking that stage as `X'` gives the existential conclusion. -/
theorem exists_noetherian_descent
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (X' : Scheme.{u}), IsNoetherian X' ∧
      ∃ (ν : X ⟶ X') (F' : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        Scheme.IsConstructibleEtaleModuleSheaf F' ∧
          Nonempty (((ν)^*[ModuleCat.{u + 1} Λ]).obj F' ≅ F) := by
  obtain ⟨N⟩ := X.nonempty_noetherianApproximation
  obtain ⟨I, hI, hd, hn, G, hG⟩ := IsFiltered.exists_directed N.Iᵒᵖ
  let := hI
  let := hd
  let := hn
  let := hG
  let D := G.leftOp ⋙ N.D
  let c := (CategoryTheory.Limits.Cone.mk X N.π).whisker G.leftOp
  have hc : CategoryTheory.Limits.IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv G.leftOp _).symm N.isLimit
  let : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) :=
    fun {_ _} f ↦ N.isAffineHom_map (G.leftOp.map f)
  let : ∀ i : Iᵒᵖ, CompactSpace (D.obj i) :=
    fun i ↦ N.compactSpace_obj (G.leftOp.obj i)
  let : ∀ i : Iᵒᵖ, IsNoetherian (D.obj i) :=
    fun i ↦ N.isNoetherian_obj (G.leftOp.obj i)
  let : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i) :=
    fun i ↦ IsLocallyNoetherian.quasiSeparatedSpace
  obtain ⟨i, F', hF', e⟩ :=
    Scheme.exists_constructible_etaleModuleSheaf_descent D c hc Λ F hF
  exact ⟨D.obj (Opposite.op i), N.isNoetherian_obj _, c.π.app (Opposite.op i), F', hF', e⟩

end AlgebraicGeometry.Etale

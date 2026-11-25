/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Vanishing of cohomology along short exact sequences and finite coproducts

The functor `SheafOfModules.toSheaf` from `𝒪_X`-modules to abelian sheaves is exact, so a short
exact sequence of `𝒪_X`-modules has a long exact sequence in the cohomology
`AlgebraicGeometry.Scheme.Modules.H`, the covariant `Ext` sequence. We record the vanishing
statements that follow from it.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.toAb`: the exact forgetful functor from `𝒪_X`-modules to
  abelian sheaves.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_iso`: vanishing of `H^n` only depends on
  the isomorphism class of the module.
- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_isZero`: the cohomology of a zero module
  vanishes.
- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_shortExact`: for `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0`
  short exact, `H^n(M₂) = 0` and `H^{n+1}(M₁) = 0` imply `H^n(M₃) = 0`.
- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_sigma`: `H^n` of a finite coproduct vanishes
  if it vanishes on every summand.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

variable (X) in
/-- The forgetful functor from `𝒪_X`-modules to abelian sheaves on `X`. -/
noncomputable abbrev toAb : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf.{u} X.ringCatSheaf

instance : (toAb X).PreservesZeroMorphisms :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms

instance : PreservesFiniteLimits (toAb X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

instance : PreservesFiniteColimits (toAb X) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

/-- Vanishing of sheaf cohomology only depends on the isomorphism class of the module. -/
lemma subsingleton_H_of_iso {M N : X.Modules} (e : M ≅ N) (n : ℕ) [Subsingleton (M.H n)] :
    Subsingleton (N.H n) :=
  (H.mapLinearEquiv e n).symm.toEquiv.subsingleton

/-- The cohomology of a zero module vanishes. -/
lemma subsingleton_H_of_isZero {M : X.Modules} (h : IsZero M) (n : ℕ) : Subsingleton (M.H n) :=
  ⟨fun x y ↦ by rw [← H.map_id_apply M n x, ← H.map_id_apply M n y, h.eq_of_src (𝟙 M) 0,
    H.map_zero_apply, H.map_zero_apply]⟩

/-- **Vanishing from the long exact cohomology sequence.** For a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules, the long exact sequence contains
`H^n(M₂) ⟶ H^n(M₃) ⟶ H^{n+1}(M₁)`, so `H^n(M₃) = 0` as soon as `H^n(M₂) = 0` and
`H^{n+1}(M₁) = 0`.

The underlying sequence of abelian sheaves is again short exact, since `SheafOfModules.toSheaf`
is exact (`SheafOfModules.preservesFiniteColimits_toSheaf`). -/
lemma subsingleton_H_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (S.X₂.H n)] [Subsingleton (S.X₁.H (n + 1))] : Subsingleton (S.X₃.H n) := by
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : S.X₃.H n, z = 0 by rw [h x, h y]
  intro z
  obtain ⟨w, hw⟩ := Abelian.Ext.covariant_sequence_exact₃ _ (hS.map_of_exact (toAb X)) z
    (n₁ := n + 1) rfl (Subsingleton.elim (α := S.X₁.H (n + 1)) _ _)
  obtain rfl : w = 0 := Subsingleton.elim (α := S.X₂.H n) _ _
  rw [← hw]
  apply Abelian.Ext.zero_comp

/-- **Cohomology of a finite coproduct.** If `H^n(G i) = 0` for every member of a finite family
of sheaves of modules, then `H^n(∐ G) = 0`: the identity of the coproduct, which is a
biproduct, is the sum of the projections followed by the inclusions, and each of these factors
through some `H^n(G i)`. -/
lemma subsingleton_H_sigma {ι : Type*} [Finite ι] (G : ι → X.Modules) (n : ℕ)
    [∀ i, Subsingleton ((G i).H n)] : Subsingleton ((∐ G).H n) := by
  -- reindex by `Fin k`, since the biproduct API is stated for index types in `Type`
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  suffices ∀ G' : Fin k → X.Modules, (∀ i, Subsingleton ((G' i).H n)) →
      Subsingleton ((∐ G').H n) by
    have := this (G ∘ e.symm) fun i ↦ inferInstanceAs (Subsingleton ((G (e.symm i)).H n))
    exact subsingleton_H_of_iso (Sigma.reindex e.symm G) n
  intro G _
  have : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteCoproducts
  suffices Subsingleton ((⨁ G).H n) from subsingleton_H_of_iso (biproduct.isoCoproduct G) n
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : (⨁ G).H n, z = 0 by rw [h x, h y]
  intro z
  let φ : ((⨁ G) ⟶ (⨁ G)) →+ (⨁ G).H n :=
    { toFun := fun f ↦ H.map f n z
      map_zero' := H.map_zero_apply _ _
      map_add' := fun f g ↦ H.map_add_apply f g n z }
  have h1 : φ (∑ i, biproduct.π G i ≫ biproduct.ι G i) = z := by
    rw [biproduct.total]
    exact H.map_id_apply _ _ z
  rw [← h1, map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  change H.map (biproduct.π G i ≫ biproduct.ι G i) n z = 0
  rw [H.map_comp_apply, Subsingleton.elim (α := (G i).H n) (H.map (biproduct.π G i) n z) 0,
    map_zero]

end AlgebraicGeometry.Scheme.Modules

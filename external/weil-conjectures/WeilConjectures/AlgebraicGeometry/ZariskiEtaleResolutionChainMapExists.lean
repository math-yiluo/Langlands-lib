/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Resolution comparison bridge -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- An augmented comparison from a resolution to the pushed complex exists.

Source: Stacks Project, Derived Categories, Tag 013P (comparison of resolutions).
(blueprint: lem-zariski-etale-resolution-chain-map-exists)

Proof: The exact inverse image preserves monomorphisms. Its right adjoint therefore
preserves injectives, so every term of the pushed complex is injective. Extend the
pushed augmentation along the monic augmentation of R to obtain the degree-zero
component. Its composite with the next differential vanishes on the augmentation.
Exactness of R lets it factor through the first differential and injectivity extends
it to degree one. Inductively, commutativity at the preceding degree and the
square-zero identity show that the required composite vanishes on the preceding
differential. Factor and extend again. The inductive chain-map constructor assembles
these components. Its degree-zero component gives the asserted augmentation equality.
No exactness of the pushed complex is required. -/
theorem zariski_etale_resolution_comparison_chain_map_exists
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F)
    (R : InjectiveResolution ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F))
    :
    ∃ b : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex,
      R.ι.f 0 ≫ b.f 0 = (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map (I.ι.f 0) := by
  classical
  let G := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)
  have (n : ℕ) : Injective (K.X n) := G.injective_obj (I.cocomplex.X n)
  let b₀ : R.cocomplex.X 0 ⟶ K.X 0 := Injective.factorThru (G.map (I.ι.f 0)) (R.ι.f 0)
  have hb₀ : R.ι.f 0 ≫ b₀ = G.map (I.ι.f 0) := by
    simp [b₀]
  have hz : R.ι.f 0 ≫ (b₀ ≫ K.d 0 1) = 0 := by
    rw [← Category.assoc, hb₀]
    change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
    rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]
  let b₁ := R.exact₀.descToInjective (b₀ ≫ K.d 0 1) hz
  have hb₁ : b₀ ≫ K.d 0 1 = R.cocomplex.d 0 1 ≫ b₁ :=
    (R.exact₀.comp_descToInjective _ _).symm
  let b : R.cocomplex ⟶ K := CochainComplex.mkHom _ _ b₀ b₁ hb₁
    (fun n data ↦ by
      rcases data with ⟨g, g', w⟩
      have hz' : R.cocomplex.d n (n + 1) ≫ (g' ≫ K.d (n + 1) (n + 2)) = 0 := by
        rw [← Category.assoc, ← w, Category.assoc,
          HomologicalComplex.d_comp_d, comp_zero]
      exact ⟨(R.exact_succ n).descToInjective _ hz',
        ((R.exact_succ n).comp_descToInjective _ hz').symm⟩)
  exact ⟨b, hb₀⟩



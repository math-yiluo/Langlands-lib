/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.EtaleCoefficientInjectiveSystem

/-! # Compatible injective coefficient systems

Source: Stacks Project, Tags 0EXZ and 04JC.
(blueprint: lem-weil-pbc-etale-coefficient-injective-cokernel-system).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- A compatible coefficient system embeds in a stagewise injective system, with
compatible cokernels. Source: Stacks Project, Tag 0EXZ, product-of-direct-images
construction, and Tag 04JC for preservation of cokernels by inverse image.
(blueprint: lem-weil-pbc-etale-coefficient-injective-cokernel-system).

Proof: Choose the canonical monomorphism from F k to Injective.under (F k).
For each i take the product of the direct images of these injectives indexed by
pairs (k, f : i to k). The component of ai is adjoint to φ f followed by the
chosen embedding at k. The identity component is monic, so ai is monic.
Each factor is injective because its left adjoint is exact, and the product is
injective. For f : i to j, the k-component of ψ f is obtained by projecting to
the factor indexed by f followed by g : j to k, then applying the counit and the
composition comparison of direct images. Compare product projections and
transpose across the adjunction: the unit and associativity equations give the
identity and composition laws and the displayed compatibility with ai.
Put FR i equal to cokernel (ai i) and bi i equal to its projection. The sequence
is short exact since ai i is mono. Since inverse image preserves cokernels,
compatibility of ai induces φR f with the displayed compatibility with bi.
Cancel the epic inverse images of bi to prove the identity and composition laws
of φR; the equations reduce to those of ψ and naturality of the comparisons.
All choices here occur in an existential proof; no object is defined by an
arbitrary witness of an unproved existence theorem. -/
theorem etale_coefficient_injective_cokernel_system
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
 :
    ∃ (FR : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φR : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FR i) ⟶ FR j)
    (hidentityR : ∀ i : I, φR (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FR i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FR i))
    (hcompositionR : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φR (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φR f) ≫ φR g)
    (FI : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ψ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FI i) ⟶ FI j)
    (hidentityI : ∀ i : I, ψ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FI i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FI i))
    (hcompositionI : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ψ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FI i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ψ f) ≫ ψ g)
    (ai : ∀ i : I, F i ⟶ FI i) (bi : ∀ i : I, FI i ⟶ FR i)
    (wi : ∀ i : I, ai i ≫ bi i = 0)
    (hi : ∀ i : I, (ShortComplex.mk (ai i) (bi i) (wi i)).ShortExact),
      (∀ i : I, Injective (FI i)) ∧
      (∀ (i j : I) (f : i ⟶ j),
        φ f ≫ ai j = (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).map (ai i) ≫ ψ f) ∧
      (∀ (i j : I) (f : i ⟶ j),
        ψ f ≫ bi j = (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).map (bi i) ≫ φR f) := by
  obtain ⟨FI, ψ, hidentityI, hcompositionI, ai, hInjective, hMono, ha⟩ :=
    etale_coefficient_injective_system D F φ hidentity hcomposition
  let FR := fun i : I ↦ cokernel (ai i)
  let bi := fun i : I ↦ cokernel.π (ai i)
  have wi : ∀ i : I, ai i ≫ bi i = 0 := fun i ↦ cokernel.condition (ai i)
  let φR := fun {i j : I} (f : i ⟶ j) ↦
    (PreservesCokernel.iso (upperStar AddCommGrpCat.{u + 1} (D.map f.op)) (ai i)).hom ≫
      cokernel.map ((upperStar AddCommGrpCat.{u + 1} (D.map f.op)).map (ai i))
        (ai j) (φ f) (ψ f) (ha i j f).symm
  have hb : ∀ (i j : I) (f : i ⟶ j),
      ψ f ≫ bi j = (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).map (bi i) ≫ φR f := by
    intro i j f
    dsimp [φR, bi]
    simp only [PreservesCokernel.π_iso_hom_assoc, cokernel.π_desc]
  have hidentityR : ∀ i : I, φR (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FR i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FR i) := by
    intro i
    apply (cancel_epi ((upperStar AddCommGrpCat.{u + 1} (D.map (𝟙 (op i)))).map
      (bi i))).mp
    have hbId : ψ (𝟙 i) ≫ bi i =
        (upperStar AddCommGrpCat.{u + 1} (D.map (𝟙 (op i)))).map (bi i) ≫ φR (𝟙 i) :=
      hb i i (𝟙 i)
    rw [← hbId, hidentityI]
    have hn := (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1})
      (D.map_id (op i)))).hom.naturality (bi i)
    have hu := (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.naturality (bi i)
    simp only [Functor.id_map] at hu
    simp only [Category.assoc]
    rw [reassoc_of% hn, hu]
  have hcompositionR : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φR (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φR f) ≫ φR g := by
    intro i j k f g
    apply (cancel_epi ((upperStar AddCommGrpCat.{u + 1} (D.map (f ≫ g).op)).map
      (bi i))).mp
    rw [← hb, hcompositionI]
    have hn := (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
      (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.naturality (bi i)
    simp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    rw [reassoc_of% hn, ← Functor.map_comp_assoc, ← hb i j f, Functor.map_comp]
    simp only [Category.assoc]
    rw [← hb j k g]
  have hi : ∀ i : I, (ShortComplex.mk (ai i) (bi i) (wi i)).ShortExact := by
    intro i
    have : Mono (ai i) := hMono i
    exact ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (ai i))⟩
  exact ⟨FR, φR, hidentityR, hcompositionR, FI, ψ, hidentityI, hcompositionI,
    ai, bi, wi, hi, hInjective, ha, hb⟩

end AlgebraicGeometry.Etale

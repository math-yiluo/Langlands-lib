/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerTriangle
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerLocalComplexes
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientPreviousLocalComplexes

/-! # The controlled outer terms of the coefficient-filtration triangle

Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094I and 094H
(blueprint: lem-weil-pbc-finite-quotient-cohomology-filtration-triangle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Tensoring the coefficient-layer sequence gives a distinguished triangle
whose middle term is the actual successor reduction and whose outer terms have
bounded finite etale-local cohomology. No assertion is made about the homology of
the middle term.

Source: Stacks Project, sites-cohomology.tex, lemma-bounded (0942), first proof
paragraph, and lemma-locally-constant-bounded (094I), with lemma-locally-constant-tensor-product
(094H); proetale.tex, Tag 09C2.
(blueprint: lem-weil-pbc-finite-quotient-cohomology-filtration-triangle).

Proof: put B = A/I^(n+2) and Q = I^(n+1)/I^(n+2), and regard the exact sequence
0 -> Q -> B -> A/I^(n+1) -> 0 as a sequence of B-modules. Resolve M by a flat-term
K-flat complex over the completed ring. Extend to B and tensor the displayed
sequence with that complex. Exact constant realization and termwise flatness
give a short exact sequence of complexes, hence its distinguished triangle.
The unit tensor comparison and the specified universal scalar-extension counit
identify its middle term with the actual successor reduction. Balancing and the
coefficient compatibility squares identify its last term with the scalar restriction
of the previous reduction, and its first term with the scalar restriction of the
residue reduction tensored over A/I with Q. The ideal I kills Q and its finite ideal
generators give finite generators over A/I. Intersect the residue and previous
trivializing etale covers. On the residue cover the first term is computed by the
ordinary tensor of the finite-projective residue complex with Q. The last term is
computed by the previous finite-projective complex. Both are supported in [a,b]
and have finite terms, so their homology is finite over the finite Noetherian ring B.
Constant realization, exact restriction and coefficient isomorphisms identify the
cohomology sheaves with the constant finite algebraic homology modules on these
etale covers. Vanishing on the covers implies vanishing on V by sheaf
separatedness. Pull back and compose the covers for every W over V. On an empty
chart take zero modules, and for the zero ring all terms are zero. This uses only
outer-term homology, never the desired middle-term cohomology conclusion. -/
theorem finiteQuotient_cohomology_filtration_triangle
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (a b : ℤ) (hab : a ≤ b)
    (hresidue : FinitePerfectModelsOn X d φ M 0 V a b) (n : ℕ)
    (hprevious : FinitePerfectModelsOn X d φ M n V a b) :
    let B := A ⧸ d.ideal ^ (n + 1 + 1)
    let R₀ := completedAdicFiniteRing X d (n + 1)
    let K := (completedAdicQuotientReduction X d (n + 1)).obj M
    let P : ObjectProperty (SheafOfModules.{t + 1} R₀) := fun F ↦
      ∀ (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj F ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X (φ (n + 1))).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                      ModuleCat.restrictScalars.{t + 1}
                        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                      koszulConstantFunctor X B).obj N)))
    ∃ T : Triangle (DerivedCategory (SheafOfModules.{t + 1} R₀)),
      T ∈ distTriang _ ∧ Nonempty (T.obj₂ ≅ K) ∧
        (∀ q : ℤ, q < a ∨ b < q →
          IsZero ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj V)).obj
            ((DerivedCategory.homologyFunctor _ q).obj T.obj₁)) ∧
          IsZero ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj V)).obj
            ((DerivedCategory.homologyFunctor _ q).obj T.obj₃))) ∧
        DerivedCategory.homologyProperty P T.obj₁ ∧
        DerivedCategory.homologyProperty P T.obj₃ := by
  have : Finite (A ⧸ d.ideal ^ (n + 1 + 1)) := d.quotientFinite (n + 1)
  obtain ⟨T, hT, ⟨e₁⟩, e₂, ⟨e₃⟩⟩ :=
    finiteQuotient_coefficient_layer_triangle X d M n
  have h₁ := finiteCoefficient_local_homology_models X
    (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))
    (finiteQuotientLayerObject X d M n) V a b
    (finiteQuotient_layer_local_complexes X d φ hφ hcompat M V a b hab n hresidue)
  have h₃ := finiteCoefficient_local_homology_models X
    (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))
    (finiteQuotientPreviousObject X d M n) V a b
    (finiteQuotient_previous_local_complexes X d φ hφ hcompat M V a b hab n hprevious)
  refine ⟨T, hT, e₂, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨(h₁.1 q hq).of_iso
        ((SheafOfModules.overFunctor _ ((toProEt X).obj V)).mapIso
          ((DerivedCategory.homologyFunctor _ q).mapIso e₁)),
      (h₃.1 q hq).of_iso
        ((SheafOfModules.overFunctor _ ((toProEt X).obj V)).mapIso
          ((DerivedCategory.homologyFunctor _ q).mapIso e₃))⟩
  · intro q W g
    obtain ⟨S, hS, hs⟩ := h₁.2 q W g
    refine ⟨S, hS, ?_⟩
    intro Z f hf
    obtain ⟨N, hN, ⟨e⟩⟩ := hs Z f hf
    exact ⟨N, hN, ⟨(SheafOfModules.overFunctor _ ((toProEt X).obj Z)).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso e₁) ≪≫ e⟩⟩
  · intro q W g
    obtain ⟨S, hS, hs⟩ := h₃.2 q W g
    refine ⟨S, hS, ?_⟩
    intro Z f hf
    obtain ⟨N, hN, ⟨e⟩⟩ := hs Z f hf
    exact ⟨N, hN, ⟨(SheafOfModules.overFunctor _ ((toProEt X).obj Z)).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso e₃) ≪≫ e⟩⟩

end AlgebraicGeometry.Scheme

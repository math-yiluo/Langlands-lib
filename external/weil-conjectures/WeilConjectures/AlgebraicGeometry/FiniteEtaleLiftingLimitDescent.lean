/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore

/-!
# Reduction of finite étale lifting to henselian G-rings

Source: Stacks Project, Fundamental Groups, Lemma 0GS2, proof, "General case"
(blueprint: lem-weil-pbc-finite-etale-lifting-limit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Lifting finite étale covers of proper schemes over arbitrary henselian pairs follows
from lifting them over henselian G-ring pairs. Hypothesis `H` is the statement of
`exists_finiteEtale_lift_of_henselianPair_of_isGRing`.
Source: Stacks Project, Lemma 0GS2, proof, "General case"
(blueprint: lem-weil-pbc-finite-etale-lifting-limit-descent).

Proof (the eight steps of the blueprint node):
1. By lem-weil-pbc-proper-limit-noetherian and lem-weil-pbc-limit-affine-transition,
   approximate the proper morphism Y → Spec A by proper Yᵢ → Spec Aᵢ, with Aᵢ finitely
   generated over ℤ, affine transition maps, and A the filtered colimit of the Aᵢ.
2. Put Iᵢ = αᵢ⁻¹(I). These ideals form a directed system; every element of A comes from
   a stage by lem-weil-pbc-filtered-colimit-algebras-elementwise. Thus the pairs and their
   quotients have colimits (A,I) and A/I.
3. By lem-weil-pbc-spec-colimit-limit, the closed base spectra have limit Spec(A/I).
   The closed fibres Yᵢ,₀ have affine transitions: factor each through a closed immersion
   followed by an affine base change, using lem-weil-pbc-closed-immersion-base-change,
   pqf-def-affine-morphism and lem-weil-pbc-affine-morphism-permanence. Proper base change
   and lem-weil-pbc-qcqs-morphism-permanence make them qcqs. By
   lem-weil-pbc-limit-affine-transition their limit exists; the universal property of
   def-pc-fibre-product and commuting limits identify it with Y₀.
4. Descend V by proposition-jacobian-over-ground-field--1; increase the stage until its morphism is
finite
   and étale by lem-weil-pbc-descend-finite and lem-weil-pbc-descend-etale. The finite
   presentation hypotheses follow from def-weil-finite-integral-morphism,
   def-weil-etale-morphism and def-sbc-locally-finite-presentation.
5. Henselize (Aᵢ,Iᵢ), using lem-weil-pbc-pair-henselization. Its quotient is Aᵢ/Iᵢ.
   By lem-weil-pbc-finite-type-z-g-ring and lem-weil-pbc-henselization-pair-g-ring,
   the henselized ring is a Noetherian G-ring. By lem-weil-pbc-henselization-colimit
   there is a compatible pair map Aᵢʰ → A.
6. Base change Yᵢ to Spec Aᵢʰ; it remains proper by lem-weil-pbc-proper-base-change.
   Its closed fibre is Yᵢ,₀ by the quotient isomorphism and def-pc-fibre-product.
   Apply H to lift Vᵢ to a finite étale cover Uᵢ of this proper scheme.
7. The compatible maps Y → Yᵢ and Y → Spec Aᵢʰ give Y → Yᵢ × Spec Aᵢʰ by
   def-pc-fibre-product. Pull Uᵢ back to Y; it is finite étale by
   def-weil-pbc-finite-etale-category.
8. The resulting maps from Y₀ agree because their ring maps modulo I agree after
   precomposition with the stage quotient isomorphism. Paste the fibre squares by
   lem-weil-pbc-cartesian-square-pasting. The closed fibre of the resulting U is
   Vᵢ × Y₀, hence V, with all isomorphisms over Y₀. -/
theorem exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting
    (H : ∀ (B : Type u) [CommRing B], IsGRing B →
      ∀ (J : Ideal B) [HenselianRing B J] (Z : Scheme.{u})
        (g : Z ⟶ Spec (.of B)) [IsProper g]
        (W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
          (pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
        ∃ U' : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Z,
          Nonempty
            (Over.mk (pullback.snd U'.hom
              (pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))) ≅
              Over.mk W.hom))
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) := by
  obtain ⟨U, hU, _⟩ :=
    exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting_core H I f V
  exact ⟨U, hU⟩

end AlgebraicGeometry.Scheme

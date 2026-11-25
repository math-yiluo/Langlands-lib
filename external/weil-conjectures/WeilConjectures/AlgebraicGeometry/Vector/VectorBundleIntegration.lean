/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts

import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationLocalTraceCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.DerivedDegreeZeroNormalization
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSheafHomFamilyGluing

/-!
# Integration along a vector bundle

Source: blueprint sec-smooth-purity/sk-prop-an, order 1972
(blueprint: proposition-purity-vector-bundles).

The coefficient is expressed by the existing ordered tensor of shifted finite Tate lines:
its pullback to E is A_E(d)[2d]. The local map is the actual compact-support exchange for
the inverse frame, followed by the canonical Tate comparison and the existing affine trace.
The unique-gluing theorem determines a unique morphism, so the final definition postpones
only its construction's proof, without choosing an unconstrained map or orientation.

## Main definitions

- `vectorIntegrationCoefficient`, `vectorIntegrationSource`: A_E(d)[2d] and C_pi.
- `vectorIntegrationLocalTrace`: the prescribed trace on each linear trivialization.
- `VectorIntegrationNormalization`: the local characterization, for every frame.
- `vectorBundleIntegration`: the unique global map with those restrictions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem local_normalization_iff (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (ell : L ⟶ ordinaryFiniteConstant A S) :
    VectorIntegrationNormalization N hN A hA S hS d F
        (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell) ↔
      ∀ (t : OrdinaryFiniteTwistTransport A N hA)
        (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
          OrdinaryFiniteP1Datum A N hA t T hT)
        (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V),
        (localizationRestriction (ModuleCat.{u + 1} A) V.ι inferInstance).map ell =
          vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V e := by
  constructor
  · intro h t D V e
    exact (vectorIntegrationLocalSheafTrace_normalization_iff
      N hN A hA t D S hS d F α ell V e).1 (h t D V e)
  · intro h t D V e
    exact (vectorIntegrationLocalSheafTrace_normalization_iff
      N hN A hA t D S hS d F α ell V e).2 (h t D V e)

private theorem existsUnique_normalized_sheaf_trace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L) :
    ∃! ell : L ⟶ ordinaryFiniteConstant A S,
      VectorIntegrationNormalization N hN A hA S hS d F
        (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell) := by
  classical
  obtain ⟨t, D, _, _⟩ := exists_affineSpaceTopTrace N hN A hA
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
  let ψ := fun i : I ↦
    vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α (V i) (e i).some
  have hcover : ∀ x : S, ∃ (i : I) (y : (V i).toScheme), (V i).ι.base y = x := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ x) : x ∈ ⨆ i, V i)
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  obtain ⟨ell, hell, huniq⟩ := existsUnique_etaleSheafHom_of_family A
    (fun i : I ↦ (V i).ι) hcover L (ordinaryFiniteConstant A S) ψ
    (fun W i j q q' ↦ vectorIntegrationLocalSheafTrace_compatible N hN A hA
      S hS d F α t t D D (V i) (V j) (e i).some (e j).some W q q')
  have hnorm : VectorIntegrationNormalization N hN A hA S hS d F
      (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell) := by
    apply (local_normalization_iff N hN A hA S hS d F α ell).2
    intro t' D' V' e'
    apply etaleSheafHom_restriction_eq_of_compatible A
      (fun i : I ↦ (V i).ι) hcover L (ordinaryFiniteConstant A S) ψ
      (fun W i j q q' ↦ vectorIntegrationLocalSheafTrace_compatible N hN A hA
        S hS d F α t t D D (V i) (V j) (e i).some (e j).some W q q') ell hell V'.ι
    · intro W i q q'
      exact vectorIntegrationLocalSheafTrace_compatible N hN A hA
        S hS d F α t t' D D' (V i) V' (e i).some e' W q q'
    · intro W q q'
      exact descentComponent_eq_of_mono A V'.ι _ W q q'
  refine ⟨ell, hnorm, ?_⟩
  intro μ hμ
  exact huniq μ (fun i ↦
    (local_normalization_iff N hN A hA S hS d F α μ).1 hμ t D (V i) (e i).some)

/-- The unique sheaf-glued derived trace. This is the existence and uniqueness needed
by the definition, not a choice of a morphism from a mere nonempty Hom set.
Source: blueprint order 1972, full construction (blueprint: proposition-purity-vector-bundles).

Proof:
1. Use the finite locally free frames of proposition-purity-vector-bundles to cover S.
The coefficient is the ordered tensor of d Tate lines shifted by two, hence bounded below.
The geometry theorem and Nagata give compactifications between Noetherian schemes.
The canonical D+ comparisons of proposition-construction-independence-rf-shriek--7 and exchange of
proposition-composition-base-change-rf-shriek identify each restriction with the existing affine
trace source. lemma-integral-linear-character--1 gives its actual isomorphism to A[0]. Exact inverse
image (situation-conventions) commutes with cohomology; the cover detects
vanishing (lem-weil-pbc-etale-cover-detects-iso). Thus C_pi has only H^0 = L_pi.
2. For frames i,j on W, write a_g = phi_i phi_j^{-1}. If e_j = e_i G, then
phi_j = a_(G transpose) phi_i and g = (G transpose)^{-1}. Thus phi_j^{-1} = phi_i^{-1} a_g.
Horizontal pasting of the two inverse-coordinate squares and normalized Tate composition
give B_j = rho_g B_i, with rho_g exactly affineLinearTraceAction. Base-change compatibility
of the affine trace and proposition-purity-vector-bundles give t rho_g B_i = t B_i.
All hypotheses hold on the Noetherian overlap W, with N invertible and the same finite A.
3. Take H^0 of these maps. The resulting module-sheaf maps lambda_i agree on overlaps.
Use lem-pur-sheaf-hom-cover-gluing to obtain a unique lambda: L_pi → A_S. Its application
here uses the usual equivalence between constant A-module sheaves and sheaves of A_S-modules.
4. On a representative K form b: tau_le_0 K → K and c: tau_le_0 K → H^0(K)[0].
The degree-zero component of c is cycles → cohomology; it kills boundaries, hence is a
chain map. Both maps induce the identity in degree zero; every other cohomology vanishes
by lem-weil-pbc-truncation-cohomology. Thus they are quasi-isomorphisms and
alpha = Q(c) Q(b)^{-1} is an isomorphism. Theorem theorem-pbc-injective-acyclicity gives
the descended truncation and projection; naturality of b and c, also after inversion of
quasi-isomorphisms, proves independence of the representative and compatibility with
exact open restriction. H^0(alpha) is the identity under the standard single-H^0 comparison.
5. Set t_pi = lambda[0] alpha. On a trivializing open, composing a_i with alpha^{-1}
is a map between degree-zero complexes with H^0 equal to lambda_i. Full faithfulness
(lem-weil-pbc-derived-single-fully-faithful) gives equality with lambda_i[0]. Hence the
constructed map has exactly the displayed local restrictions. The Kummer generator and
projective counit normalizations in OrdinaryFiniteP1Datum show that this equation uses
the same affine traces for every normalized t,D, without an extra base-change assumption.
6. For two covers use their common refinement by intersections; step 2 and unique sheaf
gluing identify the maps. Any map with these restrictions, composed with alpha^{-1},
corresponds by degree-zero full faithfulness to a sheaf map with restrictions lambda_i.
Sheaf uniqueness proves uniqueness in the derived Hom set. In rank zero the affine
counit is the identity adjunction counit, including on the empty base.
-/
theorem existsUnique_vectorIntegrationGluing (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (∀ q : ℤ, q ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (vectorIntegrationSource A N hA S d F))) ∧
    ∃! p :
        (vectorIntegrationSource A N hA S d F ≅
          (_root_.DerivedCategory.singleFunctor _ 0).obj
            (vectorIntegrationSheaf A N hA S d F)) ×
        (vectorIntegrationSheaf A N hA S d F ⟶ ordinaryFiniteConstant A S),
      (_root_.DerivedCategory.homologyFunctor _ 0).map p.1.hom ≫
          (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
            (vectorIntegrationSheaf A N hA S d F) =
        𝟙 (vectorIntegrationSheaf A N hA S d F) ∧
      VectorIntegrationNormalization N hN A hA S hS d F
        (p.1.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map p.2) := by
  dsimp only [vectorIntegrationSheaf]
  have hz := vectorIntegration_cohomology_zero N hN A hA S hS d F
  refine ⟨hz, _root_.DerivedCategory.existsUnique_normalized_iso_and_map
    (vectorIntegrationSource A N hA S d F) (ordinaryFiniteConstant A S) hz
    (VectorIntegrationNormalization N hN A hA S hS d F) ?_⟩
  intro α
  exact existsUnique_normalized_sheaf_trace N hN A hA S hS d F α

/-- The canonical truncation identification alpha_pi and the glued sheaf map lambda.
The H^0 normalization determines alpha_pi, and all frame restrictions determine lambda.
Thus the theorem used here specifies the pair uniquely, rather than asserting bare existence.
Source: blueprint order 1972, alpha_pi and lambda (blueprint: proposition-purity-vector-bundles). -/
def vectorIntegrationGluing (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj (vectorIntegrationSheaf A N hA S d F)) ×
    (vectorIntegrationSheaf A N hA S d F ⟶ ordinaryFiniteConstant A S) :=
  (existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2.exists.choose

/-- Integration t_pi, the unique map restricting on each linear trivialization to the
specified affine-space trace. Its existence proof is precisely sheaf gluing followed by
the canonical truncation roof; uniqueness determines the data in this definition.
Source: blueprint order 1972, t_pi (blueprint: proposition-purity-vector-bundles). -/
def vectorBundleIntegration (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    vectorIntegrationSource A N hA S d F ⟶ ordinaryFiniteUnit A S :=
  (vectorIntegrationGluing N hN A hA S hS d F).1.hom ≫
    (_root_.DerivedCategory.singleFunctor _ 0).map
      (vectorIntegrationGluing N hN A hA S hS d F).2

end AlgebraicGeometry.Etale

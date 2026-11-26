import Langlands.Geometry.Building.DepthZero.Definitions

/-! # The depth-zero consumer for valid KP building data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

open BruhatTits.IntegralModels

/-- For each facet of a KP datum satisfying the one-group axioms, the neutral integral
points give the compact open zero-fixer. Reduction identifies its quotient by the
radical preimage with the finite group of points of the reductive quotient. Complex
representations of this quotient inflate through reduction and compactly induce
smoothly to `G(F)`. Between two such inductions from finite-dimensional representations,
the space of maps is linearly identified, by evaluation on the unit functions, with
the two-sided equivariant kernels of finite double-coset support. -/
def DepthZeroConsumerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (D : KPBuildingDatum G), D.SatisfiesGroupAxioms →
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : Smooth G.X.hom := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ x : BuildingFacet D.base.toValuationBuildingData,
      let P := D.parahoric x
      let N := D.parahoricRadical x
      let red := D.parahoricReduction x
      (P = BuildingModelFamily.zeroFixer D.base (BuildingModelIndex.ofFacet x) ∧
        IsCompact (P : Set (rationalPoints G)) ∧ IsOpen (P : Set (rationalPoints G))) ∧
      (∃ hN : N.Normal,
        letI : N.Normal := hN
        IsCompact (N : Set P) ∧ IsOpen (N : Set P) ∧
          Function.Surjective red ∧ red.ker = N ∧
          IsConnectedReductive (D.reductiveQuotient x) ∧ Finite (D.reductiveQuotientPoints x) ∧
          ∃ e : P ⧸ N ≃* D.reductiveQuotientPoints x, ∀ g : P, e (g : P ⧸ N) = red g) ∧
      (∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ (D.reductiveQuotientPoints x) V),
        D.depthZeroInflation x σ = σ.comp red ∧
          (∀ n : N, D.depthZeroInflation x σ (n : P) = 1) ∧
          IsSmooth (D.depthZeroCompactInduction x σ).representation) ∧
      (∀ (V W : Type u)
        [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
        (σ : Representation ℂ (D.reductiveQuotientPoints x) V)
        (τ : Representation ℂ (D.reductiveQuotientPoints x) W),
        let σP := D.depthZeroInflation x σ
        let τP := D.depthZeroInflation x τ
        let A := D.depthZeroCompactInduction x σ
        let B := D.depthZeroCompactInduction x τ
        let hσ := (D.quotients.quotient x).isSmooth_inflation
          (D.models.facetModels.model x).localField_isOpen_congruenceSubgroup σ
        ∃ kernel : (A ⟶ B) →ₗ[ℂ] (rationalPoints G → V →ₗ[ℂ] W),
          Function.Injective kernel ∧
          (∀ Φ, Φ ∈ LinearMap.range kernel ↔
            (∀ (p q : P) (g : rationalPoints G),
              Φ ((p : rationalPoints G) * g * (q : rationalPoints G)) =
                τP p ∘ₗ Φ g ∘ₗ σP q) ∧
              (DoubleCoset.mk P P '' Function.support Φ).Finite) ∧
          ∀ (T : A ⟶ B) (g : rationalPoints G) (v : V),
            kernel T g v = Induction.eval P τP
              (SmoothRep.hom T (Induction.unitFunction P (D.parahoricOpenSubgroup x).isOpen
                σP hσ v)).1 g)

end Langlands.Geometry.Building

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality

/-! # The natural cohomology sequence of a strict Roos complex

proof.md, first paragraph.
-/

@[expose] public section

set_option autoImplicit false

universe a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The natural short exact sequence from the long exact sequence of Cone(1-T)[-1].

proof.md, first paragraph
(auxiliary; not a blueprint node).

Proof: Apply the cone long exact cohomology sequence to the transition endomorphism
on the termwise product. Exact products identify its cohomology with the product
of the cohomology objects; the projection formulas conjugate the induced map to
1-T. Factor the incoming map through its cokernel and the outgoing map through
its kernel. Exactness at the three middle terms makes the first factor a mono,
the second an epi, and their image and kernel equal. The kernel of 1-T is the
limit of the tower: its projections are compatible and any compatible family
factors uniquely through the kernel. A tower morphism induces the diagonal map
on both cone summands. It commutes with the inclusion and negative projection,
so the kernel and cokernel universal properties give the two naturality squares.
This calculation applies in every integer degree and to unbounded complexes. -/
theorem roos_cohomology_sequence {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableLimits A] [HasExactLimitsOfShape (Discrete ℕ) A] :
    ∀ q : ℤ,
        ∃ (a : ∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            milnorTowerCokernel (milnorCohomologyTower K (q - 1)) ⟶
              (WeilConjectures.integralOperationsRoos K).homology q)
          (b : ∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            (WeilConjectures.integralOperationsRoos K).homology q ⟶
              limit (milnorCohomologyTower K q)),
          (∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            ∃ h : a K ≫ b K = 0, (ShortComplex.mk (a K) (b K) h).ShortExact) ∧
          (∀ (K L : ℕᵒᵖ ⥤ CochainComplex A ℤ) (f : K ⟶ L),
            milnorTowerCokernelMap
                (Functor.whiskerRight f
                  (HomologicalComplex.homologyFunctor A
                    (ComplexShape.up ℤ) (q - 1))) ≫ a L =
              a K ≫ HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ∧
            HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ≫ b L =
              b K ≫ limMap (Functor.whiskerRight f
                (HomologicalComplex.homologyFunctor
                  A (ComplexShape.up ℤ) q))) := by
  intro q
  refine ⟨fun K ↦ milnorInclusion K q, fun K ↦ milnorProjection K q,
    fun K ↦ milnor_shortExact K q, ?_⟩
  intro K L f
  exact roos_cohomology_naturality q f

end AlgebraicGeometry.Scheme.ProEt

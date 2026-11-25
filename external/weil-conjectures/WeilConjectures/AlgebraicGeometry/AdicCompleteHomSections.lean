/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.AdicCompleteReductionCone
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Milnor

/-! # Lifting compatible finite-reduction morphisms

Source: Stacks Project, Tags 09C6, 0940 and 0941.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

/-- The surjective half of the Milnor Hom sequence needs no finiteness condition. -/
private theorem milnor_surjective
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} (c : Cone F) (hc : Pretriangulated.IsHomotopyLimit c) (T : D) :
    Function.Surjective (Pretriangulated.milnorMap c T) := by
  obtain ⟨P, hP, δ, htriangle⟩ := hc
  intro x
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ htriangle
    (Fan.IsLimit.lift hP x.val) (by
      refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
      simp only [Pretriangulated.Triangle.mk_mor₂, Preadditive.comp_sub,
        Preadditive.sub_comp, Category.assoc, Pretriangulated.towerShift_proj,
        Fan.IsLimit.fac_assoc, zero_comp]
      erw [Category.id_comp, Fan.IsLimit.fac, x.property n, sub_self])
  refine ⟨g, Subtype.ext (funext fun n ↦ ?_)⟩
  have h := congrArg (fun k ↦ k ≫ P.proj n) hg
  simp only [Pretriangulated.Triangle.mk_mor₁, Fan.IsLimit.fac, Category.assoc] at h
  exact h.symm

/-- Compatible morphisms to the finite reductions lift to a morphism into a complete object.
Source: Stacks Project, proetale.tex, Tag 09C6, the inverse-limit morphism; Cohomology on
Sites, Tags 0940 and 0941.
(auxiliary; not a blueprint node).

Proof: the quotient-completion reflector identifies M, with its actual quotient unit,
with the derived inverse limit of its restricted finite reductions. The Roos triangle
and representability give a surjection from Hom(T,M) onto the kernel of 1-shift on
the product of Hom(T,Res M_n). The scalar-extension/restriction adjunction identifies
Hom(T,Res M_n) with Hom(T tensor^L B_n,M_n). Its unit is insertion of 1; its scalar
reassociation is the balancing map. Naturality of these adjunctions identifies the
transition on these groups with adicResidueHomStep, including its two conjugations.
The kernel is therefore precisely the sections of adicResidueHomTower. The surjection
is the displayed adicResidueHomSection, since its nth component is scalar extension
of the original morphism. This argument requires no boundedness or perfectness of T,
no Mittag-Leffler hypothesis, and no compatibility choice of object isomorphisms. -/
theorem adicResidueHomSection_surjective
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U)
    (_hM : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) M) :
    Function.Surjective (adicResidueHomSection.{u, v} X J U (T := T) (M := M)) := by
  classical
  obtain ⟨F, c, eM, e, adj, hc, hleg, hstep⟩ :=
    adicResidue_complete_reduction_cone.{u, v} X J U M _hM
  intro s
  let x : Pretriangulated.towerHomLimit F T :=
    ⟨fun n ↦ (adj n).homEquiv T _ (s.val (op n)) ≫ (e n).inv, by
      intro n
      apply (cancel_mono (e n).hom).mp
      rw [Category.assoc, Category.assoc, hstep]
      have hs := s.property (homOfLE (Nat.le_succ n)).op
      dsimp only [adicResidueHomTower] at hs
      rw [Functor.ofOpSequence_map_homOfLE_succ] at hs
      change adicResidueHomStep.{u, v} X J U T M n (s.val (op (n + 1))) = s.val (op n) at hs
      simp only [hs, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
  obtain ⟨g, hg⟩ := milnor_surjective c hc T x
  refine ⟨g ≫ eM.hom, ?_⟩
  apply Subtype.ext
  funext i
  obtain ⟨n⟩ := i
  change (adicResidueLocalReduction.{u, v} X J U n).map (g ≫ eM.hom) = s.val (op n)
  apply (adj n).homEquiv T _ |>.injective
  have hn := congrArg (fun t : Pretriangulated.towerHomLimit F T ↦ t.val n) hg
  change g ≫ c.π.app (op n) = (adj n).homEquiv T _ (s.val (op n)) ≫ (e n).inv at hn
  have h := congrArg (fun k ↦ k ≫ (e n).hom) hn
  simp only [Category.assoc, hleg, Iso.inv_hom_id, Category.comp_id] at h
  calc
    _ = (g ≫ eM.hom) ≫ (adj n).unit.app M := by
      rw [Adjunction.homEquiv_unit]
      exact ((adj n).unit.naturality (g ≫ eM.hom)).symm
    _ = _ := by simpa only [Category.assoc] using h

end AlgebraicGeometry.Scheme

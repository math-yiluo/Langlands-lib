/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
import WeilConjectures.AlgebraicGeometry.RingComplexCechConeFiltration
import WeilConjectures.AlgebraicGeometry.RingComplexCechLocalizedOrthogonality

/-! # Maps between augmented ordered localization models -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

/-- Composition with the augmentation of an ordered localization model induces a
bijection on derived maps from another model for the same finitely generated ideal.
Source: Stacks Project, dualizing.tex, Tag 0A6R, the local-cohomology adjunction.
(auxiliary; not a blueprint node)

Proof: choose a finite generating list f of I and use the two augmented derived
isomorphisms with its ordered localization complex C(f). Inverting any f_i contracts
C(f), by inserting or deleting index i with its ordered sign. Thus the source T has
zero derived localization at each f_i. The cone of C(f) to A[0] has a finite filtration
whose graded pieces are shifts of the positive-degree terms of C(f), each a finite
product of localization modules A[1/g], with g a nonempty product of generators.
For every integer shift, derived Hom from T to A[1/g] vanishes: flat localization and
restriction of scalars are adjoint on derived categories, and T localizes to zero
after inverting g, since a factor f_i is then invertible. Finite products and the
long exact Hom sequences of the filtration imply vanishing of Hom from T to the
cone and to its shift by -1. The triangle Hom sequence therefore says exactly that
composition with C(f) to A[0] is bijective. Transport across the augmented derived
isomorphism for K gives the displayed map. When the list is empty the augmentation
is an isomorphism; a zero generator has zero localization, so the argument includes
zero ideals, unit ideals, and the zero ring without extra hypotheses. -/
theorem ringComplex_cech_augmentation_hom_bijective
    (A : CommRingCat.{u}) [HasDerivedCategory.{w} (RingSiteModules A)]
    (I : {I : Ideal A // I.FG})
    (T K : CochainComplex (RingSiteModules A) ℤ)
    (εT : T ⟶ ringComplexSingle A) (εK : K ⟶ ringComplexSingle A)
    (hT : RingComplexHasCechModel A I.val T εT)
    (hK : RingComplexHasCechModel A I.val K εK) :
    Function.Bijective
      (fun f : DerivedCategory.Q.obj T ⟶ DerivedCategory.Q.obj K ↦
        f ≫ DerivedCategory.Q.map εK) := by
  let P := ((ObjectProperty.singleton (DerivedCategory.Q.obj T)).shiftClosure ℤ).rightOrthogonal
  have hcone : P (DerivedCategory.Q.obj (CochainComplex.mappingCone εK)) :=
    ringComplex_cech_cone_filtration A I K εK hK P
      (fun s hs M hM ↦ ringComplex_cech_localized_orthogonality A I T εT hT s hs M hM)
  have hTmem : (ObjectProperty.singleton (DerivedCategory.Q.obj T)).shiftClosure ℤ
      (DerivedCategory.Q.obj T) :=
    (ObjectProperty.singleton (DerivedCategory.Q.obj T)).le_shiftClosure _
      ((ObjectProperty.singleton_iff _ _).mpr rfl)
  let D := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle εK)
  have hD : D ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished εK
  constructor
  · intro f g hfg
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ D.invRotate
      (inv_rot_of_distTriang D hD) (f - g) (by
        change (f - g) ≫ DerivedCategory.Q.map εK = 0
        simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)
    have hq0 : q = 0 := (P.le_shift (-1 : ℤ) _ hcone) q hTmem
    rw [hq0, zero_comp] at hq
    exact sub_eq_zero.mp hq
  · intro g
    obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₂ D hD g (hcone _ hTmem)
    exact ⟨f, hf.symm⟩

end AlgebraicGeometry

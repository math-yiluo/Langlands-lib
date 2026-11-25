/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.Abelian.DerivedBottomUnitNormalizationFormula

/-! # Normalization of the bottom-cohomology comparison

Source: Stacks Project, Tag 05TC (2), and the degree-zero comparison for a left
exact derived functor, as used in Tags 08D4 and 0AVW.
(blueprint: lem-pc-derived-bottom-unit-normalization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The bottom comparison can be normalized by the actual right-derived unit.
This only compares with the lower truncation; it does not invert the image of
that truncation under the derived functor.

Source: Stacks Project, Tag 05TC (2), the double-truncation and degree-zero
calculation used in Tags 08D4 and 0AVW.
(blueprint: lem-pc-derived-bottom-unit-normalization).

Proof: Lift the lower truncation to the bounded-below derived category. Apply
05TC (2) to its upper truncation at n: the complementary term has cohomology
strictly above n, and its right derived image has the same lower bound. Thus
upper truncation induces an isomorphism in degree n. Double truncation is the
single object H^n(E) in degree n. Shift to zero and use the single-object
right-derived comparison followed by the inverse of the degree-zero unit of S.
Left exactness makes this last unit invertible. Compose these natural maps,
then transport from bounded-below to unbounded right derived functors and
identify H^n of the lower truncation with H^n(E). This constructs delta.

For the formula, represent E by K and the lower-truncation projection by the
smart truncation K -> tauGE K. Naturality of the right-derived unit compares
the two complexes. On a cycle of K, the smart truncation sends its class to
the degree-n kernel in the truncated complex; the double-truncation map sends
it to the same class in H^n(K). The degree-zero unit sends that class to its
class in an injective resolution, and the bottom comparison inverts that unit.
Consequently the displayed composite is S applied to the cycle quotient.
The relation S(T.i) = k followed by U.i identifies the cycle maps, since U.i
is monic. Precompose with the cycle inclusion into the resolution and use
kernel uniqueness and the cokernel quotient to obtain the formula for any
left homology data T and U, not only the chosen canonical data. These maps
are natural in K; localization and bounded-below compatibility preserve the
unit, so the formula uses the specified unbounded right-derived unit.
Zero objects and arbitrary integers require no exceptions. -/
theorem exists_rightDerivedFunctor_truncated_bottom_unit
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    [HasDerivedCategory.{wD} D]
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] (n : ℤ) :
    ∃ δ : DerivedCategory.TStructure.t.truncGE n ⋙ S.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ S,
      ∀ (K : CochainComplex C ℤ)
        (T : (K.sc n).LeftHomologyData)
        (U : (((S.mapHomologicalComplex (.up ℤ)).obj K).sc n).LeftHomologyData)
        (k : S.obj T.K ⟶ U.K),
        S.map T.i = k ≫ U.i →
        k ≫ U.π ≫ U.homologyIso.inv ≫
          ((DerivedCategory.homologyFunctorFactors D n).app
            ((S.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
          (DerivedCategory.homologyFunctor D n).map
            ((DerivedCategory.quotientCompQhIso D).inv.app
                ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
              S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
              S.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)) ≫
          (DerivedCategory.homologyFunctor D n).map
            (S.rightDerivedFunctor.map
              ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K))) ≫
          δ.hom.app (DerivedCategory.Q.obj K) =
        S.map (T.π ≫ T.homologyIso.inv ≫
          ((DerivedCategory.homologyFunctorFactors C n).app K).inv) := by
  refine ⟨S.rightDerivedFunctorTruncatedBottomIso n, ?_⟩
  intro K T U k hk
  let V := (((S.mapHomologicalComplex (.up ℤ)).obj K).sc n)
  let l : S.obj (K.sc n).cycles ⟶ V.cycles :=
    V.liftCycles (S.map (K.sc n).iCycles) (by
      change S.map (K.sc n).iCycles ≫ S.map (K.sc n).g = 0
      rw [← S.map_comp, (K.sc n).iCycles_g, S.map_zero])
  have hl : l ≫ V.iCycles = S.map (K.sc n).iCycles := V.liftCycles_i _ _
  have hcycles : k ≫ U.cyclesIso.inv = S.map T.cyclesIso.inv ≫ l := by
    apply (cancel_mono V.iCycles).1
    dsimp only [V] at hl ⊢
    simp only [Category.assoc, ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles,
      hl, ← S.map_comp, hk]
  rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv_assoc,
    ← Category.assoc k U.cyclesIso.inv, hcycles]
  simp only [Category.assoc]
  rw [normalized_bottom_unit_formula S n K]
  rw [← S.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv_assoc]

end CategoryTheory.Functor

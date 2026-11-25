/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormallyUnramifiedConormal
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenRestrictionCore
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenRestrictionConormal

/-!
# Universal thickenings and conormal sheaves on open subschemes

Source: Stacks Project, More on Morphisms, Lemma 04FA and Lemma 02HC
(blueprint: lem-weil-pbc-universal-thickening-open-restriction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Universal first order thickenings, formal unramifiedness, and conormal sheaves
restrict to compatible open subschemes.
Source: Stacks Project, More on Morphisms, Lemma 04FA and Lemma 02HC
(blueprint: lem-weil-pbc-universal-thickening-open-restriction).
Proof:
1. Factor `V.ι ≫ h` through `U.ι` using
   lem-weil-pbc-morphism-factors-through-open-subscheme. Two lifts into `V` give
   two lifts into `Z`, equal by formal unramifiedness of `h`; cancel `V.ι`.
   This is lem-weil-pbc-formally-unramified-open-restriction (Stacks 02HC).
2. The first order thickening `i` is a homeomorphism on points. Its image of `V`
   is the unique open `V'` with preimage `V`. The equation `i ≫ h' = h` puts
   `h'(V')` in `U`, so factor the restricted structure map through `U`.
   By lem-weil-pbc-thickening-open-restriction, the restricted immersion `iV`
   is closed and its ideal is the restriction of `i.ker`, still of square zero.
   Cancel `U.ι` to obtain `iV ≫ hV' = hV`.
3. Given a test first order thickening over `U` mapping to `V`, compose with
   the open inclusions to get a test over `X`. Apply
   def-weil-pbc-universal-first-order-thickening to obtain the extension into `Z'`.
   Every point of the test thickening comes from its closed subscheme, so the
   extension lands in `V'`. Factor it through `V'` and cancel the open inclusions
   to check both compatibility equations over `U`.
4. Two extensions into `V'` give extensions into `Z'`, equal by universal
   uniqueness. Cancel `V'.ι` to prove their equality. Together with Steps 2-3
   this proves that `iV` is universal over `U`, as in Stacks 04F3.
5. By def-weil-pbc-conormal-sheaf-formally-unramified, the conormal modules are
   the tensor pullbacks of the square-zero ideal sheaves. Use
   lem-weil-pbc-open-immersion-module-pullback-restriction to identify restriction
   with tensor pullback, and def-pc-module-pullback for composition. The equation
   `iV ≫ V'.ι = V.ι ≫ i` and the ideal restriction from Step 2 identify the two
   modules. Independence of the chosen universal thickening follows from
   lem-weil-pbc-universal-first-order-thickening-exists. -/
theorem universalFirstOrderThickening_open_restriction
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : IsUniversalFirstOrderThickening h i h')
    (hform : FormallyUnramified h)
    (V : Z.Opens) (U : X.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    ∃ (hV : V.toScheme ⟶ U.toScheme),
      V.ι ≫ h = hV ≫ U.ι ∧ FormallyUnramified hV ∧
        ∃ (V' : Z'.Opens) (iV : V.toScheme ⟶ V'.toScheme)
          (hV' : V'.toScheme ⟶ U.toScheme),
          i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
          iV ≫ V'.ι = V.ι ≫ i ∧
            hV' ≫ U.ι = V'.ι ≫ h' ∧
            iV ≫ hV' = hV ∧
            IsUniversalFirstOrderThickening hV iV hV' ∧
            ∃ (hVform : FormallyUnramified hV),
              ∃ (HV : IsUniversalFirstOrderThickening hV iV hV'),
                Nonempty
                  ((Scheme.Modules.restrictFunctor V.ι).obj
                      (@formallyUnramifiedConormal _ _ _ h hform i h' H) ≅
                    @formallyUnramifiedConormal _ _ _ hV hVform iV hV' HV) := by
  obtain ⟨hV, hVeq, V', iV, hV', hdata⟩ :=
    universalFirstOrderThickening_open_restriction_core h i h' H V U hVU
  obtain ⟨hVform, HV, hiso⟩ :=
    universalFirstOrderThickening_open_restriction_conormal
      h i h' H hform hdata
  exact ⟨hV, hVeq, hVform, V', iV, hV', hdata.1, hdata.2.1, hdata.2.2.1,
    hdata.2.2.2.1, hdata.2.2.2.2.1, hdata.2.2.2.2.2, ⟨hVform, HV, hiso⟩⟩

end AlgebraicGeometry

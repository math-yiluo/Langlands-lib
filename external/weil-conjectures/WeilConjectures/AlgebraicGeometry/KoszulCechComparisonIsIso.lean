/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.KoszulCechStageLifting
import WeilConjectures.AlgebraicGeometry.KoszulCechStageKernel
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Invertibility of the specified Koszul-to-Čech chain map

Source: Stacks, Tag 08D1 (blueprint: lem-sc-koszul-cech-comparison-is-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The explicit localization cocone induces an isomorphism of A-module complexes.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-koszul-cech-comparison-is-iso).

Proof:
1. Put M = Γ(Spec(A), F) degreewise. Affine quasi-coherence identifies the sections
of F.X q on D(g) with M.X q localized at g, naturally in q and restriction maps.
2. In Čech row p, the Koszul tail is finite free on the subsets J of size p+1.
Its Hom complex is a finite product of copies of M.X q. A transition multiplies
that coordinate by g_J = product of f_j over J. The colimit of this repeated
multiplication system is M.X q localized at g_J, by the fraction map m/g_J^(e+1).
There are finitely many rows and subsets, so these identifications commute with
formation of each total degree. The finite-stage statements
`koszulCechCocone_stage_lifting` and `koszulCechCocone_stage_kernel` supply
surjectivity and injectivity for the specified cocone via the colimit equations.
3. The formula defining koszulCechCocone gives precisely these fractions times
(-1)^(pq+p(p-1)/2). This sign converts the signed Hom differential into the
horizontal Čech differential plus (-1)^p times the vertical differential.
Thus the degreewise bijections are the components of koszulCechComparison.
Their inverses form a chain map, proving it is an isomorphism of complexes.
For r=0 there are no nonempty subsets and both complexes are zero. For r=1
this is the usual localization map from the multiplication colimit, and for
F=0 it is the unique isomorphism between zero complexes. -/
theorem koszulCechComparison_isIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) :
    IsIso (koszulCechComparison A r f F) := by
  have : Limits.PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    Limits.preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let D := koszulCechHomDiagram A r f
    (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
  have hι (e : ℕ) :
      Limits.colimit.ι D e ≫ koszulCechComparison A r f F =
      (koszulCechCocone A r f F).ι.app e ≫
        eqToHom (koszulCechCocone_exists A r f F).choose_spec.1 := by
    simp [koszulCechComparison, D]
  have (n : ℤ) : IsIso ((koszulCechComparison A r f F).f n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective ((koszulCechComparison A r f F).f n).hom
    constructor
    · apply (injective_iff_map_eq_zero _).2
      intro x hx
      let E : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} A :=
        HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n
      obtain ⟨e, z, hz⟩ := Limits.Concrete.isColimit_exists_rep (D ⋙ E)
        (Limits.isColimitOfPreserves E (Limits.colimit.isColimit D)) x
      change ((Limits.colimit.ι D e).f n) z = x at hz
      have hz' : (((koszulCechCocone A r f F).ι.app e ≫
          eqToHom (koszulCechCocone_exists A r f F).choose_spec.1).f n) z = 0 := by
        rw [← hι e]
        change ((koszulCechComparison A r f F).f n)
          (((Limits.colimit.ι D e).f n) z) = 0
        rw [hz]
        exact hx
      obtain ⟨b, h, hb⟩ := koszulCechCocone_stage_kernel A r f F hF n e z hz'
      have hw := congrArg (fun g ↦ (g.f n) z) (Limits.colimit.w D (homOfLE h))
      rw [← hz]
      calc
        ((Limits.colimit.ι D e).f n) z =
            ((Limits.colimit.ι D b).f n) (((D.map (homOfLE h)).f n) z) := hw.symm
        _ = 0 := by rw [hb]; exact map_zero _
    · intro y
      obtain ⟨e, z, hz⟩ := koszulCechCocone_stage_lifting A r f F hF n y
      refine ⟨((Limits.colimit.ι D e).f n).hom z, ?_⟩
      rw [← hι e] at hz
      exact hz
  exact HomologicalComplex.Hom.isIso_of_components _

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity

/-! # Hom continuity for locally finitely presented finite-field coefficients -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

noncomputable local instance hasZeroMorphisms_condensedRingObj_condensedLfpHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

local instance localInst_CondensedLfpHomContinuity_1
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) {I : Type (u + 1)} [SmallCategory I]
    (N : I ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) : HasColimit N := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : HasColimitsOfShape I C := inferInstance
  have (n : ℤ) : HasColimit (N ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval N⟩⟩⟩

/-- Continuity for a locally finitely presented module on the scheme itself.
Source: Hemo--Richarz--Scholbach, proof of Lemma 5.3(2), the locally free calculation.
(auxiliary; not a blueprint node)

Proof: local finite presentations over the finite continuous coefficient field are
pro-etale locally finite free. Identify internal module objects with sheaves of modules
for the same coefficient ring. The evaluation-normalized locally free derived Hom formula
identifies the functor below with H^n of derived sections after tensor by the finite
locally free dual. The dual tensor is exact and preserves filtered colimits, as is checked
on the finite free trivializations. It also preserves the common lower bound. The
noetherian scheme is qcqs, so apply qcqs global-sections continuity to the tensor diagram.
Good truncation at the common bound compares its cocone quasi-isomorphically with the
ordinary termwise colimit cocone, since filtered colimits of module sheaves are exact.
Naturality of evaluation identifies the induced arrow with the displayed colimit.desc.
Rank zero and the empty scheme give zero Hom groups; no nonempty-rank assumption is used. -/
theorem condensed_lfp_hom_continuity
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousMapRingObj E.val) X) P)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) X)) ℤ)
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (n : ℤ) :
    IsIso (colimit.desc _
      ((condensedShiftedHom (Profinite.continuousMapRingObj E.val) X
        ((DerivedCategory.singleFunctor _ 0).obj P) n).mapCocone (colimit.cocone N))) := by
  exact condensed_finite_free_hom_continuity X _ P (finite_lf ℓ E X P hP) N hN n

end AlgebraicGeometry.ProEtale

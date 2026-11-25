/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Filtered continuity after the finite locally free derived Hom calculation -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

noncomputable local instance hasZeroMorphisms_condensedRingObj_condensedFiniteFreeHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

private theorem isColimit_of_truncated_comparison
    {A : Type*} [Category A] [Abelian A]
    {I : Type (u + 1)} [SmallCategory I] (D : I ⥤ CochainComplex A ℤ)
    [HasColimitsOfShape I (CochainComplex A ℤ)]
    (a : ℤ) (ha : ∀ i : I, (D.obj i).IsStrictlyGE a)
    (T : CochainComplex A ℤ ⥤ Ab.{u + 1})
    (hT : IsIso (condensedContinuityComparison D a T)) :
    Nonempty (IsColimit (T.mapCocone (colimit.cocone D))) := by
  let α := Functor.whiskerLeft D ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
  have (i : I) : IsIso (α.app i) := (CochainComplex.isIso_πTruncGE_iff _ a).2 (ha i)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    infer_instance
  have hc : IsColimit (condensedContinuityCocone D a) :=
    (IsColimit.precomposeHomEquiv (asIso α) _).symm
      (colimit.isColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A))
  obtain ⟨ht⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 hT
  exact ⟨ht.ofIsoColimit ((Cocone.functoriality D T).mapIso
    (hc.uniqueUpToIso (colimit.isColimit D)))⟩

set_option backward.isDefEq.respectTransparency true in
-- Elaborating the exact dual tensor and derived sections requires extra heartbeats.
/-- Continuity for a pro-etale locally finite free internal module.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), locally free calculation.
(auxiliary; not a blueprint node)

Proof: finite free trivializations identify the dual tensor functor with finite powers.
Hence it is exact, preserves filtered colimits and preserves the common termwise bound.
The evaluation-normalized derived Hom formula identifies Hom(P[0],N[n]) with degree n
of derived global sections of the dual tensor of N. Use the equivalence between internal
module objects and sheaves of modules for the identical coefficient ring to apply that
formula. Noetherianity implies qcqs, so derived global sections commute with these
filtered colimits. Good truncation at the common bound compares the continuity cocone
with the termwise colimit cocone by a quasi-isomorphism. Naturality of evaluation and
shift identifies the comparison with the stated colimit.desc on the original legs.
Finite powers include the zero power, so empty schemes and rank zero need no exception. -/
theorem condensed_finite_free_hom_continuity
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (n : ℤ) :
    IsIso (colimit.desc _
      ((condensedShiftedHom Λ X
        ((DerivedCategory.singleFunctor _ 0).obj P) n).mapCocone (colimit.cocone N))) := by
  obtain ⟨H, hadd, hlim, hfin, hcolim, hformula⟩ :=
    condensed_finite_free_derived_hom X Λ P hP
  let : H.Additive := hadd
  let : PreservesColimitsOfSize.{u + 1, u + 1} H := hcolim
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let T := DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ n
  let M := N ⋙ Hc
  obtain ⟨a, ha⟩ := hN
  have hb (i : I) : CochainComplex.IsStrictlyGE (M.obj i) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro r hr
    exact H.map_isZero (ha i r hr)
  obtain ⟨hc⟩ : Nonempty (IsColimit (T.mapCocone (colimit.cocone M))) :=
    isColimit_of_truncated_comparison M a hb T
      (condensed_qcqs_globalSections_continuity Λ X M a (fun i r hr ↦ by
        let : CochainComplex.IsStrictlyGE (M.obj i) a := hb i
        exact CochainComplex.isZero_of_isGE _ a r hr) n)
  let : PreservesColimit M T :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit M) hc
  have hcomp : IsColimit ((Hc ⋙ T).mapCocone (colimit.cocone N)) :=
    (isColimitOfPreserves T (isColimitOfPreserves Hc (colimit.isColimit N))).ofIsoColimit
      (Functor.mapCoconeMapCocone (colimit.cocone N))
  obtain ⟨e⟩ := hformula n
  apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
  exact ⟨IsColimit.mapCoconeEquiv e.symm hcomp⟩

end AlgebraicGeometry.ProEtale

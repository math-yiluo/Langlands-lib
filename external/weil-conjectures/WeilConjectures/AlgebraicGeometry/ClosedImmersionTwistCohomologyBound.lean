/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.AlternatingCechComputes
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import Mathlib.Algebra.Category.Grp.Zero

/-! # A step in projective Serre vanishing -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private def opensSiteCech (X : Scheme.{u}) {n : Type u} (U : n → X.Opens) :
    SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)) where
  W p t := ⨅ k, U (t k)
  pr p t k := homOfLE (iInf_le _ k)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨homOfLE (le_iInf fun k ↦ (a k).le), ?_, ?_⟩
    · intro k
      apply Subsingleton.elim
    · intro b _
      apply Subsingleton.elim
  W_zero t := by simp
  pr_zero _ := Subsingleton.elim _ _
  indexMap t α := homOfLE (le_iInf fun k ↦ iInf_le _ (α k))
  indexMap_pr _ _ _ := Subsingleton.elim _ _

private noncomputable def opensSiteCechIso (X : Scheme.{u}) {n : Type u} (U : n → X.Opens)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (opensSiteCech X U).complex F ≅ (TopCat.Presheaf.cechComplex U).obj F :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro p q hpq
    obtain rfl : p + 1 = q := hpq
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply AddCommGrpCat.ext
    intro s
    funext t
    rw [TopCat.Presheaf.cechComplex_d_apply]
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    rfl)

/-- The standard N+1 affine opens bound cohomology of a closed projective subscheme.
Source: Stacks Project, Tags 01XT and 01YS (4).
(blueprint: lem-pc-j4-closed-immersion-twist-cohomology-bound)

Proof: Restrict the N+1 standard affine opens to X. A closed subscheme of an affine
scheme is affine. Their intersections are affine because X is separated. The twisted
module is quasi-coherent, so its higher cohomology on each intersection is zero.
The ordered Cech complex computes cohomology and its terms, indexed by strictly
increasing tuples of distinct cover indices, are zero in all degrees above N. Hence
cohomology is zero above N, for every twist, including
zero; no finite presentation is needed for this cover argument. -/
theorem isZero_closedImmersion_twist_above_dimension
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (q t : ℕ) (hq : N < q) :
    IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
      (tensorObj F (ProjectiveSpace.twistRestrict i t))) := by
  classical
  let n := ULift.{u} (Fin (N + 1))
  let : LinearOrder n := LinearOrder.lift' ULift.down ULift.down_injective
  let U : n → X.Opens := fun a ↦ i ⁻¹ᵁ ProjectiveSpace.standardOpen n (Spec (.of A)) a
  have hU : iSup U = ⊤ :=
    i.iSup_preimage_eq_top (ProjectiveSpace.iSup_standardOpen n _)
  let G := tensorObj F (ProjectiveSpace.twistRestrict i t)
  have : G.IsQuasicoherent := isQuasicoherent_tensorObj F _
  let P := G.presheafModuleCat ⋙ forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat
  obtain ⟨K, e, r, -, -, hr⟩ := Scheme.alternatingCechComputes X U hU P
    (opensSiteCech X U)
  have hempty : IsEmpty {a : Fin (q + 1) → n // StrictMono a} := by
    refine ⟨fun a ↦ ?_⟩
    have hc := Fintype.card_le_of_injective a.1 a.2.injective
    simp only [Fintype.card_fin, Fintype.card_ulift, n] at hc
    omega
  have hz : IsZero (K.X q) :=
    ((AddCommGrpCat.isZero_iff_subsingleton).mpr inferInstance).of_iso (e q)
  have hh : IsZero (K.homology q) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (K.sc q) hz
  have := hr q
  have hz' : IsZero (((opensSiteCech X U).complex P).homology q) :=
    hh.of_iso (asIso (HomologicalComplex.homologyMap r q))
  have hcech : IsZero (((TopCat.Presheaf.cechComplex U).obj P).homology q) :=
    hz'.of_iso (HomologicalComplex.homologyMapIso (opensSiteCechIso X U P) q).symm
  let ec := TopCat.Presheaf.cechComplexFunctorHomologyIso U G.presheafModuleCat q
  have : Subsingleton (((TopCat.Presheaf.cechComplex U).obj P).homology q) :=
    (AddCommGrpCat.isZero_iff_subsingleton).mp hcech
  have : Subsingleton (((cechComplexFunctor U).obj G.presheafModuleCat).homology q) :=
    ec.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  obtain ⟨el⟩ := nonempty_cechComplex_linearEquiv_H_of_isSeparated
    (i ≫ (ℙ(n; Spec (.of A)) ↘ Spec (.of A))) U
    (fun a ↦ (ProjectiveSpace.isAffineOpen_standardOpen n _ a).preimage i) hU G q
  have : Subsingleton (G.H q) := el.symm.toEquiv.subsingleton
  obtain ⟨c, _⟩ := exists_moduleCohomology_source_comparison X q
  exact (ModuleCat.isZero_iff_subsingleton).mpr (c G).toEquiv.subsingleton

end AlgebraicGeometry.Scheme.Modules

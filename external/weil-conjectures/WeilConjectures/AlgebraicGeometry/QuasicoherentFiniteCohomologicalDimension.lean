/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AlternatingCechComputes
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Finite cohomological dimension for quasi-coherent modules

Source: Stacks Project, Cohomology of Schemes, Lemma 30.4.2, Tag 01XI
(blueprint: lem-sc-picard-qcoh-finite-cd).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Actual intersections and inclusions realize the site Čech products (Stacks 01XI). -/
private def openCechProducts (X : Scheme.{u}) {I : Type u} (U : I → X.Opens) :
    SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)) where
  W p t := ⨅ k, U (t k)
  pr p t k := homOfLE (iInf_le _ k)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨homOfLE (le_iInf fun k ↦ leOfHom (a k)), ?_, ?_⟩
    · intro k
      exact Subsingleton.elim _ _
    · intro b _
      exact Subsingleton.elim _ _
  W_zero t := by simp
  pr_zero _ := Subsingleton.elim _ _
  indexMap t α := homOfLE (le_iInf fun k ↦ iInf_le _ (α k))
  indexMap_pr _ _ _ := Subsingleton.elim _ _

/-- The two full Čech complexes have identical section groups and face restrictions. -/
private noncomputable def openCechProductsIso (X : Scheme.{u}) {I : Type u}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((openCechProducts X U).complex F) ≅ (TopCat.Presheaf.cechComplex U).obj F :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro p q hpq
    have hq : p + 1 = q := hpq
    subst q
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply AddCommGrpCat.ext
    intro s
    funext t
    rw [TopCat.Presheaf.cechComplex_d_apply]
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    rfl)

/-- Stacks 01XI, second proof: increasing tuples disappear above the cover size. -/
private theorem finiteCech_isZero (X : Scheme.{u}) {I : Type u}
    [Fintype I] [LinearOrder I] (U : I → X.Opens) (hU : iSup U = ⊤)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (p : ℕ) (hp : Fintype.card I ≤ p) :
    IsZero (((TopCat.Presheaf.cechComplex U).obj F).homology p) := by
  obtain ⟨A, e, r, _, _, hr⟩ := alternatingCechComputes X U hU F (openCechProducts X U)
  have hempty : IsEmpty {t : Fin (p + 1) → I // StrictMono t} := ⟨by
    intro t
    have hcard := Fintype.card_le_of_injective t.1 t.2.injective
    simp only [Fintype.card_fin] at hcard
    omega⟩
  have hterm : IsZero (A.X p) := by
    apply IsZero.of_iso _ (e p)
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr inferInstance
  have hhom : IsZero (A.homology p) :=
    (A.sc p).isZero_homology_of_isZero_X₂ hterm
  have : IsIso (HomologicalComplex.homologyMap r p) := hr p
  have hsite : IsZero (((openCechProducts X U).complex F).homology p) :=
    hhom.of_iso (asIso (HomologicalComplex.homologyMap r p))
  exact hsite.of_iso (HomologicalComplex.homologyMapIso (openCechProductsIso X U F) p).symm

/-- A quasi-compact scheme over a field with affine diagonal has a uniform nonnegative
bound on the cohomology of all quasi-coherent modules.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.4.2, Tag 01XI
(blueprint: lem-sc-picard-qcoh-finite-cd).

Proof: By quasi-compactness choose a finite affine open cover with `N` members.
The affine diagonal makes pairwise intersections affine
(`lem-sc-picard-affine-diagonal-intersections`), hence all finite intersections affine
by induction. The alternating Cech complex computes Cech cohomology
(`lem-pc-alternating-cech-computes`). Its degree `p` term is indexed by strictly increasing
`(p + 1)`-tuples of cover indices, so it is zero when `p ≥ N`. Cech comparison
(`lem-pc-cech-computes`) identifies this cohomology with `H^p(X,F)` for every
quasi-coherent module `F`. The additive comparison
(`lem-sc-module-cohomology-source-comparison`) identifies this ordinary cohomology
with module right-derived global sections. Take `d = N`; the implication `d < p`
then gives `N ≤ p`, including the empty cover. The cover, and therefore the bound,
is independent of `F`. -/
theorem exists_quasicoherent_cohomology_bound (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (X ↘ Spec (.of k)))] :
    ∃ d : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), d < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) := by
  classical
  obtain ⟨s, hs, hcover⟩ :=
    isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (show IsCompact ((⊤ : X.Opens) : Set X) from isCompact_univ)
  let I := s
  let : Fintype I := hs.fintype
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  let U : I → X.Opens := fun i ↦ i.1.1
  have hU : iSup U = ⊤ := by
    simpa only [U, I, iSup_subtype] using hcover.symm
  have hAff : ∀ i, IsAffineOpen (U i) := fun i ↦ i.1.2
  have hinf : ∀ (V W : X.Opens), IsAffineOpen V → IsAffineOpen W →
      IsAffineOpen (V ⊓ W) := by
    intro V W hV hW
    exact (isAffineHom_diagonal_iff (f := X ↘ Spec (.of k))).mp inferInstance
      ⊤ (isAffineOpen_top _) V
      (by simp) W (by simp) hV hW
  have hAffFin : ∀ t : Finset I, t.Nonempty → IsAffineOpen (⨅ i ∈ t, U i) := by
    intro t ht
    exact InfClosed.biInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen)
      (fun _ h _ h' ↦ hinf _ _ h h') t.finite_toSet ht (fun i _ ↦ hAff i)
  refine ⟨Fintype.card I, ?_⟩
  intro F _ p hp
  have hzero := finiteCech_isZero X U hU
    (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj) p (by omega)
  let : Subsingleton ((TopCat.Sheaf.cechCohomologyFunctor U p).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hzero
  obtain ⟨e⟩ := Modules.nonempty_cechComplex_linearEquiv_H U hAffFin hU F p
  obtain ⟨a, _⟩ := Modules.exists_moduleCohomology_source_comparison X p
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ((a F).trans (e.symm.toAddEquiv.trans
    (Modules.cechComplexHomologyAddEquiv U F p))).injective.subsingleton

end AlgebraicGeometry.Scheme

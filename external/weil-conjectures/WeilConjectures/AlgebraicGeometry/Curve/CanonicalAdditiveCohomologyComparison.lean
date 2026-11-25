/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Cohomology.AffineCechInverseImage
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechInverseImage
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural
import WeilConjectures.AlgebraicGeometry.EtaleTensorUnitSectionsNatural

/-! # Canonical additive comparison and its inverse-image square

Source: Stacks Project, Tags 03P2 and 01FD.
(blueprint: lem-pbc-canonical-additive-cohomology-square)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Multiplication by a global function on the lifted additive structure sheaf.
This is a sectionwise construction, with naturality from structural pullback.
Source: Stacks Project, Tag 03P2, the associated abelian sheaf of the unit module.
(blueprint: lem-pbc-canonical-additive-cohomology-square) -/
noncomputable def etaleAdditiveSmul (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf := by
  refine ⟨{ app := ?_, naturality := ?_ }⟩
  · intro U
    exact AddCommGrpCat.ofHom
      { toFun := fun x ↦ ULift.up
          ((show Γ(U.unop.left, ⊤) from x.down) * (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r))
        map_zero' := by
          change ULift.up (0 * (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r)) = ULift.up 0
          rw [zero_mul]
        map_add' := fun x y ↦ by
          apply ULift.ext
          exact add_mul (show Γ(U.unop.left, ⊤) from x.down) y.down _ }
  · intro U V g
    ext x
    apply ULift.ext
    symm
    change g.unop.left.appTop ((show Γ(U.unop.left, ⊤) from x.down) *
        (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r)) =
      (show Γ(V.unop.left, ⊤) from g.unop.left.appTop x.down) *
        (show Γ(V.unop.left, ⊤) from V.unop.hom.appTop r)
    rw [map_mul]
    congr 1
    have hw := congrArg Scheme.Hom.appTop g.unop.w
    rw [Scheme.Hom.comp_appTop] at hw
    exact ConcreteCategory.congr_hom hw r

/-- The coefficient map adjoint to structural pullback on additive sections.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial.
(blueprint: lem-pbc-canonical-additive-cohomology-square) -/
noncomputable def etaleAdditivePullback {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj X.etaleAdditiveSheaf ⟶
      Y.etaleAdditiveSheaf :=
  ((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm
    (Scheme.etaleAdditiveSheafToLowerStar g)

private theorem exists_refined_affine_covers {X Y : Scheme.{u}} (g : Y ⟶ X)
    [CompactSpace X] [CompactSpace Y] [X.IsSeparated] [Y.IsSeparated] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens) (V : ι → Y.Opens),
      (∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) ∧
      (∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, V (y l))) ∧
      iSup U = ⊤ ∧ iSup V = ⊤ ∧
      ∀ (k : ℕ) (y : Fin (k + 1) → ι),
        (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)) := by
  classical
  let J := { p : X.affineOpens × Y.affineOpens // p.2.1 ≤ g ⁻¹ᵁ p.1.1 }
  let ι := X.affineOpens ⊕ J
  let U : ι → X.Opens := Sum.elim Subtype.val (fun p ↦ p.val.1.val)
  let V : ι → Y.Opens := Sum.elim (fun _ ↦ ⊥) (fun p ↦ p.val.2.val)
  have hu (i : ι) : IsAffineOpen (U i) := by
    cases i with
    | inl i => exact i.property
    | inr i => exact i.val.1.property
  have hv (i : ι) : IsAffineOpen (V i) := by
    cases i with
    | inl i => exact isAffineOpen_bot Y
    | inr i => exact i.val.2.property
  have hi (i : ι) : V i ≤ g ⁻¹ᵁ U i := by
    cases i with
    | inl i => exact bot_le
    | inr i => exact i.property
  have hcover : iSup U = ⊤ := by
    apply top_unique
    rw [← iSup_affineOpens_eq_top X]
    exact iSup_le fun i ↦ le_iSup_of_le (Sum.inl i) le_rfl
  have hcover' : iSup V = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨A, hA, hyA, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (x := g.base y) (U := ⊤) (by trivial)
    obtain ⟨B, hB, hyB, hBA⟩ := exists_isAffineOpen_mem_and_subset
      (X := Y) (x := y) (U := g ⁻¹ᵁ A) hyA
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨Sum.inr ⟨(⟨A, hA⟩, ⟨B, hB⟩), hBA⟩, hyB⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) (by
      intro x _
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (by trivial : x ∈ ⊤))
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ (V i : Set Y)) (fun i ↦ (V i).isOpen) (by
      intro x _
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover'.ge (by trivial : x ∈ ⊤))
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let S := s ∪ t
  let U' : S → X.Opens := fun i ↦ U i.val
  let V' : S → Y.Opens := fun i ↦ V i.val
  refine ⟨S, inferInstance, U', V',
    (fun k y ↦ IsAffineOpen.iInf (fun l ↦ hu (y l).val)),
    (fun k y ↦ IsAffineOpen.iInf (fun l ↦ hv (y l).val)), ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs (by trivial : x ∈ Set.univ))
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨i, Finset.mem_union_left t his⟩, hxi⟩
  · apply top_unique
    intro x _
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht (by trivial : x ∈ Set.univ))
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨i, Finset.mem_union_right s hit⟩, hxi⟩
  · intro k y x hx
    change g.base x ∈ (↑(⨅ l, U' (y l)) : Set _)
    rw [TopologicalSpace.Opens.coe_iInf]
    refine Set.mem_iInter.mpr fun l ↦ ?_
    exact hi (y l).val ((iInf_le (fun l ↦ V' (y l)) l) hx)

/-- The fixed additive structure sheaves admit comparisons compatible with global
multiplication and the canonical inverse-image coefficient map.
Source: Stacks Project, Tag 03P2, theorem
etale-cohomology-theorem-zariski-fpqc-quasi-coherent; Tag 01FD, inverse-image
naturality of the Cech comparison.
(blueprint: lem-pbc-canonical-additive-cohomology-square)

Proof: Choose finite affine open covers of X and Y, refining the target cover so
that each member lies over a source member. Separatedness makes their tuple
intersections affine. For the unit quasi-coherent modules, affine etale
acyclicity in each coefficient universe identifies etale cohomology with the
ordered Cech complex of structural functions. Lowering the finitely many lifted
coordinates identifies that complex with the ordinary unit-module Cech complex.
The natural etale/Zariski and ordinary-H comparisons give e and e'. Multiplication
by a global function acts componentwise on these complexes, so the comparison
intertwines etaleAdditiveSmul with H.map of smulHom. Structural pullback on each
intersection is both the adjoint section map of etaleAdditivePullback and the
underlying coefficient map of unitToPushforwardObjUnit. The inverse-image Cech
comparison identifies the induced cycle-class map with the Ext map using invImage
and constIso. Every class is represented by a cycle, which proves the square.
Refinement naturality makes the chosen comparisons compatible with both maps.
Degree zero is the section map. The empty scheme gives zero complexes and groups.
There is no affine, flat, proper, or invertibility hypothesis on g. -/
theorem exists_canonical_additive_cohomology_square
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    [CompactSpace X] [CompactSpace Y] [X.IsSeparated] [Y.IsSeparated] (n : ℕ) :
    ∃ e : Sheaf.H X.etaleAdditiveSheaf n ≃+
        H (SheafOfModules.unit X.ringCatSheaf) n,
    ∃ e' : Sheaf.H Y.etaleAdditiveSheaf n ≃+
        H (SheafOfModules.unit Y.ringCatSheaf) n,
      (∀ (r : Γ(X, ⊤)) x,
        e (Sheaf.H.map (etaleAdditiveSmul X r) n x) =
          H.map (smulHom (SheafOfModules.unit X.ringCatSheaf) r) n (e x)) ∧
      (∀ (r : Γ(Y, ⊤)) x,
        e' (Sheaf.H.map (etaleAdditiveSmul Y r) n x) =
          H.map (smulHom (SheafOfModules.unit Y.ringCatSheaf) r) n (e' x)) ∧
      ∀ x, e' (Sheaf.H.map (etaleAdditivePullback g) n
          (Etale.cohomologyMap g X.etaleAdditiveSheaf n x)) =
        Sheaf.H.map (coeff g (SheafOfModules.unitToPushforwardObjUnit
          g.toRingCatSheafHom)) n
          (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj
              (SheafOfModules.unit X.ringCatSheaf)) n (e x)) := by
  classical
  obtain ⟨ι, hfinite, U, V, hU, hV, hcover, hcover', hinter⟩ := exists_refined_affine_covers g
  have := hfinite
  obtain ⟨a, a', ha, ha', haa'⟩ := exists_etaleAdditive_cech_inverseImage g U V
    hU hV hcover hcover' hinter (etaleAdditiveSmul X) (etaleAdditiveSmul Y)
    (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) n
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
  obtain ⟨b, b', hbb'⟩ := exists_affineCech_inverseImage g X.toSpecΓ Y.toSpecΓ U V
    hU hV hcover hcover' (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit Y.ringCatSheaf)
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) n hinter
  let e := a.trans b.toLinearEquiv.toAddEquiv
  let e' := a'.trans b'.toLinearEquiv.toAddEquiv
  refine ⟨e, e', ?_, ?_, ?_⟩
  · intro r x
    change b.hom (a (Sheaf.H.map (etaleAdditiveSmul X r) n x)) = _
    rw [ha]
    rw [b.hom.hom.map_smul]
    change H.map (smulHom (SheafOfModules.unit X.ringCatSheaf)
        (((Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ X.toSpecΓ.appTop).hom r)) n _ = _
    simp only [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
    rfl
  · intro r x
    change b'.hom (a' (Sheaf.H.map (etaleAdditiveSmul Y r) n x)) = _
    rw [ha']
    rw [b'.hom.hom.map_smul]
    change H.map (smulHom (SheafOfModules.unit Y.ringCatSheaf)
        (((Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ Y.toSpecΓ.appTop).hom r)) n _ = _
    simp only [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
    rfl
  · intro x
    obtain ⟨z, z', hz, hz', hzz'⟩ := haa' x
    have hb := hbb' z z' hzz'
    rw [hz, hz'] at hb
    exact hb

end AlgebraicGeometry.Scheme.Modules

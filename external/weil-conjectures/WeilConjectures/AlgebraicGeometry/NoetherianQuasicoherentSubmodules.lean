/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Subobject.Basic
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentSubobjectAffineCoverExt
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Minimal

/-! # Ascending chains of quasi-coherent submodules

Source: Stacks Project, Cohomology of Schemes, Lemma 30.10.1 (Tag 01Y8), and the
maximal-element form used in Tags 088C and 088E
(blueprint: lem-weil-pbc-noetherian-acc-quasi-coherent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private noncomputable def subobjectSections {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) : Subobject F →o Submodule Γ(X, U) Γ(F, U) where
  toFun G := LinearMap.range (G.arrow.val.app (.op U)).hom
  monotone' := by
    intro G H hGH
    have h := congrArg (fun f ↦ (f.val.app (.op U)).hom) (Subobject.ofLE_arrow hGH)
    change LinearMap.range (G.arrow.val.app (.op U)).hom ≤
      LinearMap.range (H.arrow.val.app (.op U)).hom
    rw [← h]
    exact LinearMap.range_comp_le_range _ _

private theorem exists_finite_affine_cover (X : Scheme.{u}) [IsNoetherian X] :
    ∃ (I : Type u) (_ : Finite I) (U : I → X.affineOpens), ⨆ i, (U i).1 = ⊤ := by
  obtain ⟨S, hS, hfin, hcov⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact
      (U := ⊤) (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  let U : S → X.affineOpens := fun i ↦ ⟨i.1, hS i.2⟩
  exact ⟨S, hfin.to_subtype, U, by
    change (⨆ i : S, i.1) = ⊤
    rw [← sSup_eq_iSup' S]
    exact hcov.symm⟩

/-- On a Noetherian scheme, ascending sequences of quasi-coherent submodules of a coherent
module stabilize. Every nonempty set of these submodules, or of quasi-coherent ideal
sheaves (`X.IdealSheafData`), has a maximal element under inclusion.

Source: Stacks Project, Tag 01Y8; maximal-element form as used in Tags 088C and 088E
(blueprint: lem-weil-pbc-noetherian-acc-quasi-coherent).

Proof:
1. Choose a finite affine open cover using compactness and the affine-open basis.
   Local Noetherianness gives Noetherian section rings on these opens.
2. Coherence gives finite presentations by taking local generators and generators of
   their kernels. The proved source-library affine finite-presentation theorem makes
   the ambient sections finite. Evaluate subobject arrows and take their linear ranges;
   subobject factorization makes these maps monotone.
3. Apply finite-module ACC to each affine section chain and take the finite supremum of
   its stabilization indices. The section images then agree on the cover. An inclusion
   into a quasi-coherent subobject which is surjective on these affines is surjective on
   their basic opens: extend a power multiple of a section, lift on the affine, restrict,
   then divide by the defining unit. The sheaf basis test gives equality globally.
4. The chain condition on the subtype of quasi-coherent subobjects gives well-foundedness
   of strict inclusion in the increasing direction. Mathlib supplies maximal elements in
   every nonempty set of this subtype.
5. For ideal sheaves, finite-module ACC applies directly to the section ideals over the
   same cover. Mathlib's ideal-sheaf extensionality on an affine cover gives stabilization
   globally. Convert this to well-foundedness and apply the same maximal-element theorem.
   This does not require any coherence theorem for the structure sheaf. -/
theorem noetherian_quasicoherent_submodules (X : Scheme.{u}) [IsNoetherian X]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    (∀ (G : ℕ → Subobject F), Monotone G →
      (∀ n, (G n : SheafOfModules.{u} (moduleRings X.toRingedSpace)).IsQuasicoherent) →
      ∃ n, ∀ m, n ≤ m → G m = G n) ∧
    (∀ S : Set (Subobject F), S.Nonempty →
      (∀ G ∈ S, (G : SheafOfModules.{u} (moduleRings X.toRingedSpace)).IsQuasicoherent) →
      ∃ G ∈ S, ∀ H ∈ S, G ≤ H → H = G) ∧
    (∀ S : Set X.IdealSheafData, S.Nonempty →
      ∃ I ∈ S, ∀ J ∈ S, I ≤ J → J = I) := by
  classical
  obtain ⟨I, hI, U, hU⟩ := exists_finite_affine_cover X
  have : Finite I := hI
  have (i : I) : IsNoetherianRing Γ(X, (U i).1) :=
    IsLocallyNoetherian.component_noetherian (U i)
  have (i : I) : Module.Finite Γ(X, (U i).1) Γ(F, (U i).1) :=
    Scheme.Modules.coherent_affine_sections_finite X F hF _ (U i).2
  let Q := {G : Subobject F // (Subobject.underlying.obj G).IsQuasicoherent}
  have hchain : ∀ a : ℕ →o Q, ∃ n, ∀ m, n ≤ m → a n = a m := by
    intro a
    have hi (i : I) : ∃ n, ∀ m, n ≤ m →
        subobjectSections F (U i).1 (a n).1 = subobjectSections F (U i).1 (a m).1 :=
      monotone_stabilizes_iff_noetherian.mpr inferInstance
        ⟨fun n ↦ subobjectSections F (U i).1 (a n).1,
          fun n m h ↦ (subobjectSections F (U i).1).monotone (a.monotone h)⟩
    choose n hn using hi
    refine ⟨⨆ i, n i, ?_⟩
    intro m hm
    apply Subtype.ext
    exact Scheme.Modules.quasicoherent_subobject_eq_of_affine_cover X F _ _
      (a _).2 (a.monotone hm) I U hU (fun i ↦
        (hn i _ (le_ciSup (Set.Finite.bddAbove (Set.finite_range n)) i)).symm.trans
          (hn i m ((le_ciSup (Set.Finite.bddAbove (Set.finite_range n)) i).trans hm)))
  have : WellFoundedGT Q := wellFoundedGT_iff_monotone_chain_condition.mpr hchain
  refine ⟨?_, ?_, ?_⟩
  · intro G hG hqc
    obtain ⟨n, hn⟩ := hchain ⟨fun n ↦ ⟨G n, hqc n⟩, fun n m h ↦ hG h⟩
    exact ⟨n, fun m hm ↦ (congrArg Subtype.val (hn m hm)).symm⟩
  · intro S hS hqc
    obtain ⟨G, hG⟩ := exists_maximal_of_wellFoundedGT
      (fun G : Q ↦ G.1 ∈ S) (by
        obtain ⟨G, hG⟩ := hS
        exact ⟨⟨G, hqc G hG⟩, hG⟩)
    refine ⟨G.1, hG.1, ?_⟩
    intro H hH hGH
    exact le_antisymm (hG.2 (y := ⟨H, hqc H hH⟩) hH hGH) hGH
  · have hchainI : ∀ a : ℕ →o X.IdealSheafData,
        ∃ n, ∀ m, n ≤ m → a n = a m := by
      intro a
      have hi (i : I) : ∃ n, ∀ m, n ≤ m →
          (a n).ideal (U i) = (a m).ideal (U i) :=
        monotone_stabilizes_iff_noetherian.mpr inferInstance
          ⟨fun n ↦ (a n).ideal (U i), fun n m h ↦ a.monotone h (U i)⟩
      choose n hn using hi
      refine ⟨⨆ i, n i, ?_⟩
      intro m hm
      exact Scheme.IdealSheafData.ext_of_iSup_eq_top U hU (fun i ↦
        (hn i _ (le_ciSup (Set.Finite.bddAbove (Set.finite_range n)) i)).symm.trans
          (hn i m ((le_ciSup (Set.Finite.bddAbove (Set.finite_range n)) i).trans hm)))
    have : WellFoundedGT X.IdealSheafData :=
      wellFoundedGT_iff_monotone_chain_condition.mpr hchainI
    intro S hS
    obtain ⟨J, hJ⟩ := exists_maximal_of_wellFoundedGT (fun J ↦ J ∈ S) hS
    exact ⟨J, hJ.1, fun K hK hJK ↦ le_antisymm (hJ.2 hK hJK) hJK⟩

end AlgebraicGeometry

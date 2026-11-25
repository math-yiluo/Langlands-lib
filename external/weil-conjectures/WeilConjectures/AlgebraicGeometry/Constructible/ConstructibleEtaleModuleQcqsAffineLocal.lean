/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore

/-!
# Affine locality of constructible etale module sheaves on qcqs schemes

Source: Stacks Project, Tags 095E and 03RW(3)
(blueprint: lem-weil-pbc-constructible-qcqs-affine-local).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private noncomputable def transportStratification {X Y : Scheme.{u}}
    (e : X ≅ Y) (S : Stratification X) : Stratification Y where
  n := S.n
  stratum i := e.inv ⁻¹' S.stratum i
  isLocallyClosed_stratum i := (S.isLocallyClosed_stratum i).preimage e.inv.continuous
  isConstructible_stratum i := e.inv.isConstructible_preimage (S.isConstructible_stratum i)
  iUnion_stratum_eq_univ := by
    rw [← Set.preimage_iUnion, S.iUnion_stratum_eq_univ, Set.preimage_univ]
  pairwise_disjoint_stratum i j hij := (S.pairwise_disjoint_stratum hij).preimage _
  domain := S.domain
  immersion i := S.immersion i ≫ e.hom
  range_immersion i := by
    rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp, S.range_immersion]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e.inv (e.hom x) ∈ S.stratum i
      rw [← Hom.comp_apply, e.hom_inv_id]
      exact hx
    · intro hy
      refine ⟨e.inv y, hy, ?_⟩
      change (e.inv ≫ e.hom) y = y
      rw [e.inv_hom_id]
      rfl

private noncomputable def reducedStratification {X : Scheme.{u}}
    (S : Stratification X) : Stratification X :=
  { S with
    domain i := (S.domain i).nilradical.subscheme
    immersion i := (S.domain i).nilradical.subschemeι ≫ S.immersion i
    isImmersion i := by infer_instance
    range_immersion i := by
      rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        IdealSheafData.range_subschemeι, support_nilradical,
        TopologicalSpace.Closeds.coe_top, Set.image_univ, S.range_immersion] }

private theorem finiteLocallyConstant_comp
    {X Y Z : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)) :
    IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (g ≫ f)).obj F) := by
  have := h
  have := IsFiniteLocallyConstantSheaf.upperStar g
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)
  exact IsFiniteLocallyConstantSheaf.of_iso
    (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F))
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) g f).app F).symm

/-- For finite module coefficients, affine-local constructibility, its validity on an
open cover, and a global constructible immersed partition are equivalent.
Reduced immersed representatives encode the reduced induced structure on local strata.
Source: Stacks Project, Tags 095E and 03RW(3)
(blueprint: lem-weil-pbc-constructible-qcqs-affine-local).

Proof:
1. For (1) implies (2), take the cover consisting of the whole scheme. Transport the
   witnessing stratification across the isomorphism from an open in that member to
   its image in the original scheme. The domains stay the same, so reducedness stays.
2. Pullback preserves finite local constancy by `IsFiniteLocallyConstantSheaf.upperStar`.
   Its compatibility with composite morphisms follows from `Etale.upperStarComp` and
   `IsFiniteLocallyConstantSheaf.of_iso`, all directly in the category of modules.
3. Under (2), choose an affine neighbourhood in a covering member for each point.
   Transport its stratification to the corresponding affine open in the base, keeping
   the same domains and the same composite immersions. Compactness gives a finite
   subcover, which may be empty when the base is empty.
4. Apply `exists_global_stratification_factoring_local`. Pull back the finite local
   systems along its actual factorization maps and use step 2. On each global stratum,
   `finite_locally_constant_module_values_iff` gives the finite-value trivialization
   required by `IsConstructibleEtaleModuleSheaf`.
5. Under (3), base change the stratification to the given affine open using
   `Stratification.pullback`; constructibility of the preimages is already a field.
   Replace each domain by its explicit nilradical subscheme. These schemes are reduced
   and the reduction maps have full image, so the strata and their partition stay the
   same. Pull back the original finite local systems along the first projection and
   then along the reduction map; the pullback square and step 2 give (1).
6. Apply `List.tfae_of_cycle` to these three implications. -/
theorem constructible_etale_module_qcqs_affine_local
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    List.TFAE [
      (∀ U : T.Opens, IsAffineOpen U →
        ∃ S : Stratification U.toScheme,
          (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) ∧
          (∀ k : Fin S.n, IsReduced (S.domain k)) ∧
          ∀ k : Fin S.n,
            IsFiniteLocallyConstantSheaf
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k ≫ U.ι)).obj F)),
      (∃ 𝒱 : Set T.Opens,
        (∀ x : T, ∃ V ∈ 𝒱, x ∈ V) ∧
        ∀ V ∈ 𝒱, ∀ U : V.toScheme.Opens, IsAffineOpen U →
          ∃ S : Stratification U.toScheme,
            (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) ∧
            (∀ k : Fin S.n, IsReduced (S.domain k)) ∧
            ∀ k : Fin S.n,
              IsFiniteLocallyConstantSheaf
                ((Etale.upperStar (ModuleCat.{u + 1} Λ)
                  (S.immersion k ≫ U.ι ≫ V.ι)).obj F)),
      IsConstructibleEtaleModuleSheaf F] := by
  classical
  apply List.tfae_of_cycle
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    constructor
    · intro h
      refine ⟨{⊤}, ?_, ?_⟩
      · intro x
        exact ⟨⊤, Set.mem_singleton _, trivial⟩
      · intro V hV U hU
        obtain rfl := Set.mem_singleton_iff.mp hV
        let W : T.Opens := (⊤ : T.Opens).ι ''ᵁ U
        let e : U.toScheme ≅ W.toScheme := (⊤ : T.Opens).ι.isoImage U
        obtain ⟨S, hc, hr, hS⟩ := h W (hU.image_of_isOpenImmersion _)
        let R := transportStratification e.symm S
        refine ⟨R, R.isConstructible_stratum, hr, ?_⟩
        intro k
        simpa only [R, transportStratification, Iso.symm_hom, e, W, Category.assoc,
          Hom.isoImage_inv_ι] using hS k
    · rintro ⟨𝒱, hcover, hlocal⟩
      have charts (x : T) : ∃ (W : T.Opens), IsAffineOpen W ∧ x ∈ W ∧
          ∃ S : Stratification W.toScheme,
            (∀ k, Topology.IsConstructible (S.stratum k)) ∧
            ∀ k, IsFiniteLocallyConstantSheaf
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k ≫ W.ι)).obj F) := by
        obtain ⟨V, hV, hxV⟩ := hcover x
        obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
          (X := V.toScheme) (x := ⟨x, hxV⟩) (U := ⊤) trivial
        obtain ⟨S, hc, hr, hS⟩ := hlocal V hV U hU
        let W : T.Opens := V.ι ''ᵁ U
        let R := transportStratification (V.ι.isoImage U) S
        refine ⟨W, hU.image_of_isOpenImmersion _, ?_, R, R.isConstructible_stratum, ?_⟩
        · exact ⟨⟨x, hxV⟩, hxU, rfl⟩
        · intro k
          simpa only [R, transportStratification, W, Category.assoc, Hom.isoImage_hom_ι] using hS k
      choose W hW hxW S hc hS using charts
      obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
        (fun x : T ↦ (W x : Set T)) (fun x ↦ (W x).isOpen) (fun x _ ↦
          Set.mem_iUnion.mpr ⟨x, hxW x⟩)
      let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (by simp)).symm
      let w (a : Fin s.card) : T := (e a).1
      have coverW : (⋃ a : Fin s.card, (W (w a) : Set T)) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
        exact Set.mem_iUnion.mpr ⟨e.symm ⟨y, hy⟩, by simpa [w] using hxy⟩
      obtain ⟨R, hRc, hR⟩ := exists_global_stratification_factoring_local s.card
        (fun a ↦ W (w a)) (fun a ↦ hW (w a)) coverW
        (fun a ↦ S (w a)) (fun a b ↦ hc (w a) b)
      refine ⟨R, fun k ↦ (finite_locally_constant_module_values_iff _).1.mpr ?_⟩
      obtain ⟨a, b, q, hq⟩ := hR k
      have h := finiteLocallyConstant_comp F ((S (w a)).immersion b ≫ (W (w a)).ι)
        q (hS (w a) b)
      rwa [hq] at h
  · rintro ⟨S, hS⟩ U hU
    let P := S.pullback U.ι
    let R := reducedStratification P
    refine ⟨R, R.isConstructible_stratum,
      fun k ↦ (inferInstance : IsReduced (P.domain k).nilradical.subscheme), ?_⟩
    intro k
    have hk := (finite_locally_constant_module_values_iff _).1.mp (hS k)
    have hp := finiteLocallyConstant_comp F (S.immersion k)
      (CategoryTheory.Limits.pullback.fst (S.immersion k) U.ι) hk
    rw [CategoryTheory.Limits.pullback.condition] at hp
    exact finiteLocallyConstant_comp F (P.immersion k ≫ U.ι)
      (P.domain k).nilradical.subschemeι hp

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenSectionFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineSectionLocalization
import WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestriction
import WeilConjectures.AlgebraicGeometry.NonvanishingLocusRestrict

/-! # Section fractions on an affine open of an ambient scheme

Source: Stacks Project, Tags 01PW and 09MR, affine-open paragraph.
(blueprint: lem-sc-affine-open-section-fraction-localization).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem span_toAddSubgroup_eq_closure {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (A : Set M)
    (hA : ∀ (r : R) (x : M), x ∈ A → r • x ∈ A) :
    (Submodule.span R A).toAddSubgroup = AddSubgroup.closure A := by
  let P : Submodule R M :=
    { AddSubgroup.closure A with
      smul_mem' := by
        intro r x hx
        induction hx using AddSubgroup.closure_induction with
        | mem x hx => exact AddSubgroup.subset_closure (hA r x hx)
        | zero => simp
        | add x y hx hy ihx ihy =>
          change r • (x + y) ∈ AddSubgroup.closure A
          rw [smul_add]
          exact AddSubgroup.add_mem _ ihx ihy
        | neg x hx ih =>
          change r • (-x) ∈ AddSubgroup.closure A
          rw [smul_neg]
          exact AddSubgroup.neg_mem _ ih }
  apply le_antisymm
  · exact (Submodule.span_le (p := P)).mpr (fun x hx ↦ AddSubgroup.subset_closure hx)
  · exact (AddSubgroup.closure_le _).mpr (fun x hx ↦ Submodule.subset_span hx)

private theorem sectionFractionRelations_additive {Y : Scheme.{u}} (L F : Y.Modules)
    (s : Γ(L, ⊤)) :
    (sectionFractionRelations L F s).toAddSubgroup = openSectionFractionRelations L F s ⊤ := by
  apply span_toAddSubgroup_eq_closure
  rintro r x ⟨n, b, t, rfl⟩
  refine ⟨n, b, r • t, ?_⟩
  rw [smul_sub, ← DirectSum.of_smul, ← DirectSum.of_smul]
  rw [Hom.app_smul]

private theorem fraction_equiv_of_numerator_equiv {X Y : Scheme.{u}}
    (L F : X.Modules) (s : Γ(L, ⊤)) (U : X.Opens)
    (LY FY : Y.Modules) (sY : Γ(LY, ⊤))
    (N : ∀ n : ℕ, Γ(F ⊗ L.tensorPow n, U) ≃+ Γ(FY ⊗ LY.tensorPow n, ⊤))
    (hN : ∀ (n b : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)),
      N (n + b) ((mulTensorPowSection (homOfGlobalSection L s) F n b).app U t) =
        (mulTensorPowSection (homOfGlobalSection LY sY) FY n b).app ⊤ (N n t)) :
    ∃ Q : OpenSectionFractionPresentation L F s U ≃+ SectionFractionPresentation LY FY sY,
      ∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)),
        Q (openSectionFraction L F s U n t) = sectionFraction LY FY sY n (N n t) := by
  classical
  let E := DirectSum.congrAddEquiv N
  have hE (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)) :
      E.toAddMonoidHom (DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, U)) n t) =
        DirectSum.of (fun i : ℕ ↦ Γ(FY ⊗ LY.tensorPow i, ⊤)) n (N n t) := by
    exact DirectSum.map_of _ _ _
  have hrel : (openSectionFractionRelations L F s U).map E.toAddMonoidHom =
      (sectionFractionRelations LY FY sY).toAddSubgroup := by
    rw [sectionFractionRelations_additive]
    unfold openSectionFractionRelations
    rw [AddMonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨n, b, t, rfl⟩, rfl⟩
      exact ⟨n, b, N n t, by rw [map_sub, hE, hE, hN]⟩
    · rintro ⟨n, b, t, rfl⟩
      refine ⟨_, ⟨n, b, (N n).symm t, rfl⟩, ?_⟩
      rw [map_sub, hE, hE, hN, (N n).apply_symm_apply]
  refine ⟨QuotientAddGroup.congr _ _ E hrel, ?_⟩
  intro n t
  exact congrArg QuotientAddGroup.mk (hE n t)

/-- Localization of ordinary sections over an ambient affine open.
Source: Stacks Project, Properties, Tag 01PW, equation module-invert-s, and Cohomology
of Schemes, Tag 09MR, affine-open paragraph.
(blueprint: lem-sc-affine-open-section-fraction-localization).

Proof: Put Y = U.toScheme and restrict L and F along U.ι. Restriction agrees with
pullback, so the restricted L is invertible and the restricted F is quasi-coherent.
Restrict s to U and use restrictAppIso to regard it as a global section on Y.
Apply affine_section_localization on Y. The stalk criterion for nonvanishing identifies
its nonvanishing open with the preimage of S, whose image in X is U inf S.
Restriction preserves the tensor unit, tensor products, tensor powers, and the maps
mulTensorPowSection. Thus restrictAppIso in each numerator degree gives an additive
equivalence of direct sums which identifies all fraction relations.
The additive closure of the section relations equals the underlying additive subgroup
of their module span: multiplying the generator indexed by (n,b,t) by r gives the
generator indexed by (n,b,r smul t), by linearity of mulTensorPowSection. Consequently
the direct-sum equivalence descends from OpenSectionFractionPresentation to the
SectionFractionPresentation on Y. Compose with affine_section_localization and the
section comparison on U inf S. The tensor formula there is exactly the displayed
coefficient map: the inverse right unitor sends z to z tensor 1 and tensorPowSection
sends 1 to the section s to the power n. Naturality of restrictAppIso identifies the
other side with restriction from U. Empty U and zero s are included; no nonzero
or inhabited hypothesis occurs in the quotient construction or localization theorem. -/
theorem affineOpen_sectionFraction_localization (X : Scheme.{u})
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ e : OpenSectionFractionPresentation L F s U ≃+ Γ(F, U ⊓ S),
      ∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)),
        (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
            F ⟶ (F ⊗ L.tensorPow n : X.Modules)).app (U ⊓ S)
            (e (openSectionFraction L F s U n t)) =
          (F ⊗ L.tensorPow n).presheaf.map
            (homOfLE (inf_le_left : U ⊓ S ≤ U)).op t := by
  let LU := L.restrict U.ι
  let FU := F.restrict U.ι
  let sU : Γ(LU, ⊤) :=
    (L.restrictAppIso U.ι ⊤).inv (L.presheaf.map (homOfLE le_top).op s)
  have : IsAffine U.toScheme := hU
  have : LU.IsInvertible :=
    IsInvertible.of_iso ((restrictFunctorIsoPullback U.ι).app L).symm
  have : FU.IsQuasicoherent := inferInstance
  obtain ⟨N, hN, hT⟩ := exists_tensorPowSection_open_restriction X L F s U
  obtain ⟨Q, hQ⟩ := fraction_equiv_of_numerator_equiv L F s U LU FU sU N hN
  obtain ⟨V, hV, e, _, he⟩ := affine_section_localization U.toScheme LU sU FU
  have himage : U.ι ''ᵁ V = U ⊓ S := by
    have hpre : V = U.ι ⁻¹ᵁ S := by
      apply SetLike.coe_injective
      exact hV.trans ((nonvanishingLocus_restrict U.ι L s).trans
        (congrArg (U.ι ⁻¹' ·) hS.symm))
    rw [hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  obtain ⟨T, hT⟩ := hT V (U ⊓ S) himage inf_le_left
  refine ⟨(Q.trans e).trans T, ?_⟩
  intro n t
  apply (hT n t (e (Q (openSectionFraction L F s U n t)))).mp
  rw [hQ]
  exact he n (N n t)

end AlgebraicGeometry.Scheme.Modules

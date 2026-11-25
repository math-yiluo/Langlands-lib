/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement

import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Pro-étale and étale primary cohomological dimensions agree
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem torsion_iff_colimit.{v₁, w₁} {A : Type v₁} [Category.{w₁} A] [Abelian A]
    [HasColimitsOfShape ℕ A] (ℓ : ℕ) (hℓ : ℓ.Prime) (F : A) :
    IsEllPowerTorsion ℓ hℓ F ↔ Nonempty (IsColimit (ellPowerKernelCocone ℓ (F := F))) := by
  exact (IsColimit.nonempty_isColimit_iff_isIso_desc
    (colimit.isColimit (ellPowerKernelFunctor ℓ (F := F)))).symm

private theorem torsion_transport.{v₁, v₂, w₁, w₂} {A : Type v₁} [Category.{w₁} A] [Abelian A]
    {B : Type v₂} [Category.{w₂} B] [Abelian B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L]
    [PreservesColimitsOfShape ℕ L] [L.ReflectsIsomorphisms]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (F : A) (G : B) (e : L.obj F ≅ G) :
    IsEllPowerTorsion ℓ hℓ F ↔ IsEllPowerTorsion ℓ hℓ G := by
  let E (r : ℕ) : L.obj (ellPowerKernel ℓ (F := F) r) ≅
      ellPowerKernel ℓ (F := G) r :=
    PreservesKernel.iso L ((ℓ ^ r : ℕ) • 𝟙 F) ≪≫
      kernel.mapIso (L.map ((ℓ ^ r : ℕ) • 𝟙 F)) ((ℓ ^ r : ℕ) • 𝟙 G) e e (by simp)
  have hE (r : ℕ) : (E r).hom ≫ kernel.ι ((ℓ ^ r : ℕ) • 𝟙 G) =
      L.map (kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F)) ≫ e.hom := by
    simp [E, PreservesKernel.iso_hom]
  let α : ellPowerKernelFunctor ℓ (F := F) ⋙ L ≅ ellPowerKernelFunctor ℓ (F := G) :=
    NatIso.ofComponents E (by
      intro r s f
      apply (cancel_mono (kernel.ι ((ℓ ^ s : ℕ) • 𝟙 G))).1
      dsimp only [Functor.comp_map, ellPowerKernelFunctor]
      rw [Category.assoc, hE, ← Category.assoc, ← L.map_comp]
      rw [ellPowerKernelCocone_naturality ℓ f]
      rw [Category.assoc, ellPowerKernelCocone_naturality ℓ f, hE])
  let c := L.mapCocone (ellPowerKernelCocone ℓ (F := F))
  let d := ellPowerKernelCocone ℓ (F := G)
  have hc : (Cocone.precompose α.inv).obj c ≅ d :=
    Cocone.ext e (by
      intro r
      change ((E r).inv ≫ L.map (kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F))) ≫ e.hom = _
      rw [Category.assoc, ← hE, Iso.inv_hom_id_assoc]
      rfl)
  let equiv := IsColimit.equivOfNatIsoOfIso α c d hc
  have : ReflectsColimitsOfShape ℕ L :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  rw [torsion_iff_colimit, torsion_iff_colimit]
  constructor
  · rintro ⟨h⟩
    exact ⟨equiv (isColimitOfPreserves L h)⟩
  · rintro ⟨h⟩
    exact ⟨isColimitOfReflects L (equiv.symm h)⟩

private theorem ell_cocone_annihilates.{v₁, w₁} {A : Type v₁} [Category.{w₁} A] [Abelian A]
    (ℓ r : ℕ) (F : A) :
    (ellPowerKernelCocone ℓ (F := F)).ι.app r ≫ ((ℓ ^ r : ℕ) • 𝟙 F) = 0 := by
  exact kernel.condition _

private theorem additive_torsion.{v₁, v₂, w₁} {A : Type v₁} [Category.{w₁} A] [Abelian A]
    [HasColimitsOfShape ℕ A] (ℓ : ℕ) (hℓ : ℓ.Prime) (F : A)
    (L : A ⥤ AddCommGrpCat.{v₂}) [L.Additive] [PreservesColimitsOfShape ℕ L]
    (hF : IsEllPowerTorsion ℓ hℓ F) : IsAddTorsion (L.obj F) := by
  obtain ⟨hc⟩ := (torsion_iff_colimit ℓ hℓ F).mp hF
  have hLc := isColimitOfPreserves L hc
  have := preservesFilteredColimitsOfSize_shrink.{0, v₂, 0, v₂}
    (CategoryTheory.forget AddCommGrpCat.{v₂})
  intro x
  obtain ⟨r, y, rfl⟩ := Concrete.isColimit_exists_rep
    (ellPowerKernelFunctor ℓ (F := F) ⋙ L) hLc x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨ℓ ^ r, pow_pos hℓ.pos r, ?_⟩
  have hk := congrArg L.map (ell_cocone_annihilates ℓ r F)
  dsimp only [ellPowerKernelCocone, ellPowerKernelFunctor, ellPowerKernel,
    Functor.const_obj_obj, id] at hk
  simp only [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id,
    Functor.map_zero] at hk
  have he := ConcreteCategory.congr_hom hk y
  simpa [ellPowerKernelCocone, ellPowerKernelFunctor, ellPowerKernel,
    ConcreteCategory.comp_apply] using he

private theorem etale_torsion_of_ell {X : Scheme.{u}} (ℓ : ℕ) (hℓ : ℓ.Prime)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsEllPowerTorsion ℓ hℓ F) : F.IsTorsion := by
  apply Scheme.isTorsion_iff_isAddTorsion_sheafFiber F |>.mpr
  intro Ω _ _ t
  let L := (Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
  have : L.Additive := (Scheme.pointSmallEtale t).sheafFiber_additive
  exact additive_torsion ℓ hℓ F L hF

/-- Torsion transport, absolute and relative comparison, and the all-torsion bound. -/
theorem ellCohomologicalDimension_etale_comparison (ℓ : ℕ) (hℓ : ℓ.Prime)
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g] (c : ℕ) :
    (∀ (F₀ : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
      (F : Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}),
      IsClassical ((sheafCompose (Scheme.ProEt.topology S)
        (forget AddCommGrpCat.{u + 1})).obj F) →
      Nonempty (F ≅ (comparisonUpperStar AddCommGrpCat.{u + 1} S).obj F₀) →
      (IsEllPowerTorsion ℓ hℓ F ↔ IsEllPowerTorsion ℓ hℓ F₀)) ∧
    cohomologicalDimension ℓ hℓ S = etaleCohomologicalDimension ℓ hℓ S ∧
    relativeCohomologicalDimension ℓ hℓ g =
      sSup {q : WithTop ℕ |
        ∃ n : ℕ, q = n ∧ ∃ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
          IsEllPowerTorsion ℓ hℓ F ∧
            ¬ IsZero
              ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
                ((AlgebraicGeometry.Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
                  ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))} ∧
    (S.HasTorsionEtaleCohomologicalDimensionLE c →
      cohomologicalDimension ℓ hℓ S ≤ c) := by
  refine ⟨?_, cohomologicalDimension_eq_etaleCohomologicalDimension ℓ hℓ,
    relativeCohomologicalDimension_eq_etale ℓ hℓ g, ?_⟩
  · intro F₀ F _ he
    obtain ⟨e⟩ := he
    exact (torsion_transport (comparisonUpperStar AddCommGrpCat.{u + 1} S)
      ℓ hℓ F₀ F e.symm).symm
  · intro hS
    rw [cohomologicalDimension_eq_etaleCohomologicalDimension ℓ hℓ]
    apply sSup_le
    rintro q ⟨n, rfl, F, hF, hn⟩
    by_contra h
    have hcn : c < n := by exact_mod_cast (lt_of_not_ge h)
    exact hn (AddCommGrpCat.isZero_iff_subsingleton.mpr
      (hS F (etale_torsion_of_ell ℓ hℓ F hF) n hcn))

end AlgebraicGeometry.ProEtale

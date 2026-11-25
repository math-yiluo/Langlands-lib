/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.ConstructibleSheaf.MonoidalParts
import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTensorScalar
import Mathlib.CategoryTheory.Sites.Adjunction

set_option linter.privateModule false

/-! # Tensor products, scalar extension and stalks of lisse sheaves

Lisse sheaves of `Λ`-modules are the sheaves satisfying the source predicate
`Scheme.IsFiniteLocallyConstantSheaf` at `A = ModuleCat Λ`. Geometric points have
algebraically closed fields. Stalks are the fibres of the lifted point
`(pointSmallEtale y).ulift`.

## References

* Stacks Project, sites-modules, 093V, 03EL
* Stacks Project, Tags 095D, 04FM and 03PN
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

section Tensor

variable {R : Type (u + 1)} [CommRing R]

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
attribute [local instance] CategoryTheory.Sheaf.braidedCategory

private def constantTensorIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{u + 1} R)]
    (M N : ModuleCat.{u + 1} R) :
    (constantSheaf J _).obj M ⊗ (constantSheaf J _).obj N ≅
      (constantSheaf J _).obj (M ⊗ N) :=
  Functor.Monoidal.μIso (presheafToSheaf J _)
      ((Functor.const Cᵒᵖ).obj M) ((Functor.const Cᵒᵖ).obj N) ≪≫
    (presheafToSheaf J _).mapIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp))

end Tensor

section Scalars

variable {R S : Type (u + 1)} [Ring R] [Ring S]

private def scalarOverIso (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (U : Y.Etale) :
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F).over U ≅
      (Sheaf.ringExtendScalars.{u + 1, u + 1} (Y.smallEtaleTopology.over U) f).obj
        (F.over U) :=
  (((Over.forget U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} S) (Y.smallEtaleTopology.over U) Y.smallEtaleTopology).app
      (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).symm

private def scalarConstantIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{u + 1} R)]
    [HasWeakSheafify J (ModuleCat.{u + 1} S)] (f : R →+* S)
    (M : ModuleCat.{u + 1} R) :
    (Sheaf.ringExtendScalars.{u + 1, u + 1} J f).obj ((constantSheaf J _).obj M) ≅
      (constantSheaf J _).obj ((ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj M) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  exact (presheafToSheafCompComposeAndSheafifyIso J E).app
      ((Functor.const Cᵒᵖ).obj M) ≪≫
    (presheafToSheaf J _).mapIso (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (by intros; simp))

private theorem scalarFinite (f : R →+* S) (M : ModuleCat.{u + 1} R)
    (hM : ConcreteCategory.IsFinitelyGenerated M) :
    ConcreteCategory.IsFinitelyGenerated
      ((ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj M) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  let η := adj.unit.app M
  obtain ⟨s, hs, h⟩ := hM
  refine ⟨η '' s, hs.image _, ?_⟩
  intro N m hm hsm
  let mR := (ModuleCat.restrictScalars f).map m
  have : Mono mR := inferInstance
  have hi : IsIso (pullback.snd mR η) := h _ inferInstance fun x hx ↦ by
    obtain ⟨n, hn⟩ := hsm ⟨x, hx, rfl⟩
    exact ⟨Concrete.pullbackMk mR η n x hn, Concrete.pullbackMk_snd mR η n x hn⟩
  let ℓ := inv (pullback.snd mR η) ≫ pullback.fst mR η
  have hℓ : ℓ ≫ mR = η := by
    dsimp only [ℓ]
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  let k := (adj.homEquiv M N).symm ℓ
  have hk : k ≫ m = 𝟙 (E.obj M) := by
    apply (adj.homEquiv M (E.obj M)).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    simpa [Adjunction.homEquiv_unit] using! hℓ
  have : IsSplitEpi m := ⟨⟨⟨k, hk⟩⟩⟩
  exact isIso_of_mono_of_epi m

end Scalars

end AlgebraicGeometry.Scheme

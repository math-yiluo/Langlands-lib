/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-! # From finite constant models to local constancy in slice sites -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Finite constant models expressed by scheme pullbacks give local constancy in slices.
Source: Stacks Project, Tags 098K and 099Y.
(auxiliary; not a blueprint node).

Proof: view each weakly etale covering morphism as an object of the small site.
Its slice site is equivalent to the small pro-etale site of its source. Under this
equivalence localized restriction is the scheme inverse image, and constant sheaves
correspond by uniqueness of the left adjoint to sections. Transport each given
constant model back across the equivalence. Finiteness is not needed for this transport.
The empty covering and zero model require no separate choices.
-/
theorem finiteModels_over
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hF : ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (((g i)^*[ModuleCat.{u + 1} Λ]).obj F ≅
            (constantSheaf (ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 X)),
      Presieve.ofArrows U f ∈ ProEt.precoverage X (ProEt.mk (𝟙 X)) ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (F.over (U i) ≅
            (constantSheaf ((ProEt.topology X).over (U i)) (ModuleCat.{u + 1} Λ)).obj M) := by
  obtain ⟨ι, W, g, hg, h⟩ := hF
  have hg' (i : ι) : WeaklyEtale (g i) :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ hg ⟨i⟩
  let U (i : ι) : X.ProEt := @ProEt.mk X (W i) (g i) (hg' i)
  let f (i : ι) : U i ⟶ ProEt.mk (𝟙 X) :=
    MorphismProperty.Over.homMk (g i) (by exact Category.comp_id (g i))
  refine ⟨ι, U, f, ?_, fun i ↦ ?_⟩
  · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hg
  · obtain ⟨M, hM, ⟨e⟩⟩ := h i
    have : (ProEt.sliceEquiv X (U i)).inverse.IsDenseSubsite
        (ProEt.topology (W i)) ((ProEt.topology X).over (U i)) :=
      ProEt.sliceDense X (U i)
    let E := (ProEt.sliceEquiv X (U i)).sheafCongr
      ((ProEt.topology X).over (U i)) (ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)
    let r : E.functor.obj (F.over (U i)) ≅
        (localizationRestriction (ModuleCat.{u + 1} Λ) (g i) (hg' i)).obj F :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    let c := ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
      ((ProEt.topology X).over (U i)) (ProEt.topology (W i))
      (ModuleCat.{u + 1} Λ) (Over.mkIdTerminal (X := U i))).app M
    exact ⟨M, hM, ⟨E.functor.preimageIso (r ≪≫
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) (g i) (hg' i)).app F).symm
        ≪≫ e ≪≫ c.symm)⟩⟩

end AlgebraicGeometry.ProEtale

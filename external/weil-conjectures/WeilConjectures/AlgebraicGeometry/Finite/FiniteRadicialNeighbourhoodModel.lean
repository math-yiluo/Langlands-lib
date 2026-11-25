/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.Affine.AffineNeighbourhoodStalkLimit
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRadicialModelDescent

/-!
# Extending a finite radicial local model to an affine neighbourhood

Source: Stacks Project, Tag 0GK7, the generic radicial-extension step, using limit descent.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A specified finite-presentation radicial cover of a local stalk extends to a finite
radicial cover of an affine open neighbourhood. The displayed square realizes the original
cover, rather than just constructing an unrelated cover of the neighbourhood.

Source: Stacks Project, Tag 0GK7, radicial-extension step, using Tags 01ZM, 01ZO and 07RR.
(blueprint: lem-weil-pbc-finite-radicial-neighbourhood-model)

Proof: Express Spec of the stalk as the inverse limit of the affine neighbourhoods.
Apply finite radicial model descent and identify its resulting affine base with its
open subscheme in the original scheme. Transport the cartesian square through these
isomorphisms. Finiteness, surjectivity, universal injectivity and finite presentation
are invariant under the resulting isomorphism of the target. This uses no reducedness
assumption and works for any point, including a component generic point of a reduced base.
-/
theorem exists_finite_radicial_neighbourhood_model
    (S : Scheme.{u}) (s : S) {Z : Scheme.{u}}
    (g : Z ⟶ Spec (S.presheaf.stalk s))
    [LocallyOfFinitePresentation g] [IsFinite g] [Surjective g]
    [UniversallyInjective g] :
    ∃ (U : S.Opens) (_ : s ∈ U) (_ : IsAffineOpen U)
      (V : Scheme.{u}) (p : V ⟶ U.toScheme)
      (a : Spec (S.presheaf.stalk s) ⟶ U.toScheme),
      LocallyOfFinitePresentation p ∧ IsFinite p ∧ Surjective p ∧
      UniversallyInjective p ∧ a ≫ U.ι = S.fromSpecStalk s ∧
      ∃ h : Z ⟶ V, IsPullback h g p a := by
  obtain ⟨I, hI, hd, hn, D, c, e, ⟨hc⟩, haff, htrans, hopen⟩ :=
    exists_affine_neighbourhood_stalk_limit S s
  let := hI
  let := hd
  let := hn
  let := haff
  let : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun a ↦ htrans a
  have : ∀ i, CompactSpace (D.obj i) := fun i ↦ inferInstance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i ↦ inferInstance
  let q := g ≫ e.hom
  have : LocallyOfFinitePresentation q := by dsimp [q]; infer_instance
  have : IsFinite q := by dsimp [q]; infer_instance
  have : Surjective q := by dsimp [q]; infer_instance
  have : UniversallyInjective q :=
    (MorphismProperty.cancel_right_of_respectsIso @UniversallyInjective g e.hom).mpr
      inferInstance
  obtain ⟨i, V, p, hfp, hfin, hsurj, hrad, h, H⟩ :=
    exists_finite_radicial_model_stage D c hc q
  obtain ⟨U, hsU, hU, eU, heq⟩ := hopen i
  have := hfp
  have := hfin
  have := hsurj
  have := hrad
  let p' := p ≫ eU.hom
  let a := e.hom ≫ c.π.app (op i) ≫ eU.hom
  have hp' : UniversallyInjective p' :=
    (MorphismProperty.cancel_right_of_respectsIso @UniversallyInjective p eU.hom).mpr hrad
  refine ⟨U, hsU, hU, V, p', a, inferInstance, inferInstance, inferInstance,
    hp', ?_, h, ?_⟩
  · exact heq
  · exact H.of_iso (Iso.refl _) (Iso.refl _) e.symm eU
      (by simp) (by simp [q]) (by simp [p']) (by simp [a])

end AlgebraicGeometry

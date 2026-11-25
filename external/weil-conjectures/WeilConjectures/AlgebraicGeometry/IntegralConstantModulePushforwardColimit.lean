/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation
import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardLimit
import WeilConjectures.Compactification.Defs

/-!
# Integral constant module pushforwards are filtered colimits of finite pushforwards

Source: Stacks Project, Tag 09Z6, finite approximation paragraph, using Tag 09Z1.
(blueprint: lem-weil-pbc-integral-constant-module-pushforward-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- An integral direct image of a finite constant module sheaf on a Noetherian base is
a small filtered colimit of finite direct images of the same constant module.

Source: Stacks Project, Tag 09Z6, final paragraph of the proof of (1), transferred to (3),
using Tags 09YZ and 09Z1.
(blueprint: lem-weil-pbc-integral-constant-module-pushforward-colimit).

Proof: Present the integral morphism nu as a cofiltered limit of finite X-schemes with
an index category of size u, using its finite approximation. Each transition map is affine,
and each structure map and nu are affine, hence quasi-compact and quasi-separated. Reverse
the index category to form a filtered diagram D of direct images of the constant module M.
The transition map is obtained from the inverse-image unit and the canonical comparison
between the pullback of a constant sheaf and the constant sheaf with the same value.
Functoriality follows from naturality of the unit and the inverse-image composition
comparison. The limit projections define a compatible cocone into nu_* M. The pullbacks
of the constant sheaves to the limit are canonically constant, with all transition maps
identified with identities; their colimit is constant M since the index is nonempty and
connected. The relative colimit theorem 09Z1 in degree zero identifies the cocone as a
colimit on underlying abelian sheaves. Forgetting modules preserves and creates filtered
colimits of sheaves, computed by sheafifying sectionwise module colimits, so the cocone is
also a module-sheaf colimit. Take Z and f from the finite approximation and the stage
isomorphisms from the definition of D. This includes zero M and the empty scheme. -/
theorem exists_filtered_colimit_finite_lowerStar_constant
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    {Y : Scheme.{u}} (ν : Y ⟶ X) [IsIntegralHom ν]
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (Z : I → Scheme.{u}) (f : ∀ i : I, Z i ⟶ X), (∀ i : I, IsFinite (f i)) ∧
      ∃ (D : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        (∀ i : I, Nonempty (D.obj i ≅ (lowerStar (ModuleCat.{u + 1} Λ) (f i)).obj
          ((constantSheaf (Z i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) ∧
        ∃ (η : D ⟶ (Functor.const I).obj
          ((lowerStar (ModuleCat.{u + 1} Λ) ν).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))),
          Nonempty (IsColimit (Cocone.mk _ η)) := by
  obtain ⟨F⟩ := ν.nonempty_finiteApproximation_of_isIntegralHom
  let D := constantModulePushforwardDiagram Λ M F.D F.p F.map_p
  let c := constantModulePushforwardCocone Λ M F.D F.p F.map_p ν F.π F.π_p
  refine ⟨F.Iᵒᵖ, inferInstance, inferInstance,
    (fun i ↦ F.D.obj i.unop), (fun i ↦ F.p i.unop),
    (fun i ↦ F.isFinite_p i.unop), D, (fun i ↦ ⟨Iso.refl _⟩), c.ι, ?_⟩
  exact isColimit_constantModulePushforwardCocone Λ M F.D F.p F.map_p ν F.π F.π_p
    F.isLimit

end AlgebraicGeometry.Etale

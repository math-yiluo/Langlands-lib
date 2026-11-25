/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
public import Mathlib.CategoryTheory.Filtered.Small

/-!

# The strict localization is weakly étale

The strict localization `S_(s) ⟶ S` of an affine scheme `S` at a geometric point `s` is weakly
étale: it is the cofiltered limit of the affine pointed étale neighbourhoods of `s`
(`AlgebraicGeometry.Scheme.isLimitStrictLocalizationCone`), each affine and étale over `S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- **The strict localization of an affine scheme is weakly étale** over it: `S_(s)` is the
cofiltered limit of the affine pointed étale neighbourhoods of `s`, each affine and étale
over `S`. -/
instance weaklyEtale_strictLocalizationToBase [IsAffine S] :
    WeaklyEtale (strictLocalizationToBase s) := by
  let F₀ := fromInitialModel.{u} (AffinePointedEtaleNeighborhood s)
  have hF₀ (d : AffinePointedEtaleNeighborhood s) : ∃ c, Nonempty (F₀.obj c ⟶ d) := by
    obtain ⟨⟨c, _, f⟩⟩ := (inferInstance : IsConnected (CostructuredArrow F₀ d)).is_nonempty
    exact ⟨c, ⟨f⟩⟩
  have : Nonempty (InitialModel.{u} (AffinePointedEtaleNeighborhood s)) :=
    ⟨(hF₀ (AffinePointedEtaleNeighborhood.exists_hom s (PointedEtaleNeighborhood.base s)).choose
      ).choose⟩
  let F := IsCofiltered.SmallCofilteredIntermediate.inclusion F₀
  have : F.Initial := by
    refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful F fun d ↦ ?_
    obtain ⟨c, ⟨f⟩⟩ := hF₀ d
    exact ⟨(IsCofiltered.SmallCofilteredIntermediate.factoring F₀).obj c,
      ⟨((IsCofiltered.SmallCofilteredIntermediate.factoringCompInclusion F₀).app c).hom ≫ f⟩⟩
  have hc := (Functor.Initial.isLimitWhiskerEquiv F (strictLocalizationCone s)).symm
    (isLimitStrictLocalizationCone s)
  have : ∀ j, IsAffineHom (F.obj j).obj.1.hom := fun j ↦
    @isAffineHom_of_isAffine _ _ _ (F.obj j).2 (inferInstanceAs (IsAffine S))
  exact weaklyEtale_of_isLimit (F ⋙ affineNeighborhoodDiagram s) hc
    (fun j ↦ (F.obj j).obj.1.hom) (fun f ↦ Over.w (F.map f).hom.1.hom) (strictLocalizationToBase s)
    (fun j ↦ strictLocalizationCone_π_app_hom s (F.obj j))

end AlgebraicGeometry.Scheme

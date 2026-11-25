/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ResolutionOpenComparisonMap
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import WeilConjectures.AlgebraicGeometry.ResolutionOpenRestrictionNatural

/-! # The fixed comparison commutes with restriction to the scalar nonvanishing open.
Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-resolution-open-restriction-core). -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules

private theorem unit_nonvanishing_basicOpen (Y : Scheme.{u}) (b : Γ(Y, ⊤)) :
    nonvanishingLocus (𝟙_ Y.Modules) (unitSectionsEquiv ⊤ b) =
      (Y.basicOpen b : Set Y) := by
  ext x
  rw [mem_nonvanishingLocus_iff_generatesAt]
  have he : IsFreeGenerator (unitSectionsEquiv (X := Y) ⊤ 1) :=
    isFreeGenerator_one ⊤
  apply generatesAt_iff_mem_basicOpen he
  · rw [presheaf_map_unitSectionsEquiv]
    simp only [homOfLE_refl, op_id, Y.presheaf.map_id]
    change unitSectionsEquiv ⊤ b = b • unitSectionsEquiv ⊤ 1
    exact unitSectionsEquiv_eq_smul_one b
  · trivial

/-- The fixed comparison commutes with restriction to the scalar nonvanishing open.
Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-resolution-open-restriction-core).

Proof: Restrict the resolution again to the inverse image of D(a). For the tensor unit the stalk
generator identifies nonvanishing with the basic open of the pulled back scalar. Pullback of
basic opens identifies it with the inverse image of D(a). The degreewise restrictAppIso
comparisons commute with the restriction maps of the original resolution. Apply homology, and
use the naturality of isoRightDerivedObj for the derived restriction natural transformation.
Cancel the comparison inverses to give the displayed equality. This works also for the empty
open, a=0, invertible a, and q=0. -/
theorem resolution_open_restriction_core {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (a : Γ(T, W))
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let s : Γ(𝟙_ Y.Modules, ⊤) := unitSectionsEquiv ⊤ b
    let c := resolutionOpenComparison f F I q W R
    ∀ (U : Y.Opens), (U : Set Y) = nonvanishingLocus (𝟙_ Y.Modules) s →
      ∃ d : P.obj (op (T.basicOpen a)) ≃+
        (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G,
        ∀ x : P.obj (op W),
          (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
            (homOfLE (le_top : U ≤ ⊤))).app G (c x) =
              d ((P.map (homOfLE (T.basicOpen_le a)).op).hom x) := by
  dsimp only
  intro U hU
  have h : U = (f ⁻¹ᵁ W).toScheme.basicOpen
      (((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a) :=
    SetLike.coe_injective (hU.trans (unit_nonvanishing_basicOpen _ _))
  have hi : (f ⁻¹ᵁ W).ι ''ᵁ U = f ⁻¹ᵁ (T.basicOpen a) := by
    rw [h]
    change (f ⁻¹ᵁ W).ι ''ᵁ (f ⁻¹ᵁ W).toScheme.basicOpen
      ((f ⁻¹ᵁ W).topIso.inv ((f.app W).hom a)) = _
    rw [Scheme.Opens.ι_image_basicOpen_topIso_inv, Scheme.preimage_basicOpen]
  exact resolution_open_restriction_natural f F I q W R
    (T.basicOpen a) (T.basicOpen_le a) U hi

end AlgebraicGeometry.Scheme.Modules

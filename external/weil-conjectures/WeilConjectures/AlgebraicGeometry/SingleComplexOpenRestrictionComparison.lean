/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.StalkComparisonCoordinateInvariance
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCoordinateTransport
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeIdentity

/-! # Restriction of the single-complex base-change arrow

Source: Stacks Project, Tag 0DJ9, first paragraph; Tag 08HY, counit description.
(blueprint: lem-pc-single-complex-open-restriction-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting a single-complex base-change problem to compatible base opens gives
an arrow isomorphic to the restriction of the original arrow, and preserves its
stalk condition. No affineness, quasi-compactness, or invertibility is assumed.
The two restricted complexes are explicitly given by exact restriction.
Source: Stacks Project, perfect.tex, Tag 0DJ9, first paragraph; cohomology.tex,
Tag 08HY (derived base-change counit), and Tag 08FE (direct-image restriction).
(blueprint: lem-pc-single-complex-open-restriction-comparison).

Proof: Put U = f inverse-image V and U' = f' inverse-image V'. Choose a
coordinate presentation of phi using nonempty_coordinates. The open-coordinate
transport theorem restricts its K-flat complex and representing chain map,
producing coordinates of the explicitly constructed phi0 and an equivalence of
invertibility of the original and restricted stalk comparisons. The original
stalk condition gives invertibility in these coordinates. Apply coordinate
invariance to obtain it in every restricted coordinate presentation. No
K-injectivity assumption is needed on the supplied coordinate complex N.

The source comparison a is the composite of the pullback-open comparison for g
and the direct-image-open comparison for f; the target comparison b is the
direct-image-open comparison for f'. These identify the restricted derived
counit with the counit for f restricted to V. Transpose under the compatible
derived adjunction for f' restricted to V'. Naturality of the counit and the
composition comparisons in the definition of schemeDerivedBaseChangeMap give
the displayed arrow equality. Naturality of the direct-image comparison with
respect to phi supplies its final factor. These computations do not require
quasi-coherence, boundedness, nonempty opens, or affine bases. -/
theorem singleComplexBaseChange_openRestrictionComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV')) :
    let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
    let K₀' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.obj K'
    let R := (schemeOpenRestriction S' V').mapDerivedCategory
    let φ₀ := singleComplexRestrictedCoefficient g' K K' φ
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    SingleComplexBaseChange.StalkCondition
        (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ K₀ K₀' φ₀ ∧
      ∃ (a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj K)) ≅
          (derivedPullback (g.resLE V V' hV')).obj
            ((schemeDerivedDirectImage (f ∣_ V)).obj K₀))
        (b : R.obj ((schemeDerivedDirectImage f').obj K') ≅
          (schemeDerivedDirectImage (f' ∣_ V')).obj K₀'),
        R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
          (schemeDerivedDirectImage f').map φ) =
        a.hom ≫ (schemeDerivedBaseChangeMap
          (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀.w K₀ ≫
            (schemeDerivedDirectImage (f' ∣_ V')).map φ₀) ≫ b.inv := by
  classical
  dsimp only
  constructor
  · obtain ⟨c⟩ := SingleComplexBaseChange.nonempty_coordinates g' K K' φ
    obtain ⟨d, hd⟩ := singleComplexOpen_coordinates_transport
      f f' g g' sq K K' φ c V V' hV' j hj sq₀
    intro c₀ z i
    apply (SingleComplexBaseChange.isIso_stalkComparison_iff_coordinates
      (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ d c₀ z i).mp
    exact (hd z i).mpr (h_stalk c z.val i)
  · obtain ⟨a, b, hb⟩ := singleComplexOpen_baseChange_identity
      f f' g g' sq K V V' hV' j hj sq₀
    refine ⟨a, b.app K', ?_⟩
    let R := (schemeOpenRestriction S' V').mapDerivedCategory
    let R' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory
    let D := schemeDerivedDirectImage (f' ∣_ V')
    let δ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    have hφ : singleComplexRestrictedCoefficient g' K K' φ
        (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj = δ ≫ R'.map φ := by
      dsimp only [δ, singleComplexRestrictedCoefficient, R']
      simp only [(schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.map_id
        ((derivedPullback g').obj K), Category.comp_id, Category.assoc]
    simp only [Functor.map_comp, hb, hφ]
    have hn := b.inv.naturality φ
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc, Iso.app_inv]
    exact congrArg (fun t ↦ a.hom ≫ schemeDerivedBaseChangeMap
      (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀.w
      ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K) ≫ D.map δ ≫ t)
      hn.symm

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenAffine
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenUnion
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTop
import WeilConjectures.AlgebraicGeometry.SingleComplexTargetLocality

/-! # Quasi-compact quasi-separated base change for one complex

Source: Stacks Project, perfect.tex, Tag 0DJ9, lemma-single-complex-base-change
(blueprint: lem-pc-rf-single-complex-qcqs-induction).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- A stalkwise single-complex condition implies qcqs derived base change.
The hypothesis uses the canonical localized tensor-cohomology comparison followed
by the given phi, expressed in K-flat representative coordinates. The conclusion
is the canonical base-change morphism followed by Rf'_* of that same phi.

Proof (the four steps of the node):
1. Apply singleComplexBaseChange_targetLocal, supplying the affine-base criterion
   proved below. Its open restriction argument reduces to affine S and S'.
2. QuasiCompact f and QuasiSeparated f make X compact and quasi-separated over
   these affine bases. Define P(U) as invertibility of singleComplexOpenComparison.
   The affine case is singleComplexOpenComparison_affine, which transports the
   existing affine single-complex criterion to source-open coordinates.
3. For compact U and affine V, their intersection is compact by Mathlib's
   QuasiSeparatedSpace.inter_isCompact. singleComplexOpenComparison_union transports
   relative Mayer--Vietoris to U union V. Apply quasiCompactOpen_induction to obtain P(X).
4. singleComplexOpenComparison_top identifies this top-open comparison with the
   original comparison, completing the affine-base criterion of step 1.
Source: Stacks Project, perfect.tex, Tag 0DJ9
(blueprint: lem-pc-rf-single-complex-qcqs-induction). -/
theorem singleComplexBaseChangeQcqsInduction
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
      (schemeDerivedDirectImage f').map φ) := by
  apply singleComplexBaseChange_targetLocal (f := f) (f' := f') (g := g) (g' := g')
    (sq := sq) (K := K) (hK := hK) (K' := K') (hK' := hK') (φ := φ) (h_stalk := h_stalk)
  intro X₀ X₀' S₀ S₀' f₀ f₀' g₀ g₀' sq₀ _ _ _ _ K₀ hK₀ K₀' hK₀' φ₀ hstalk₀
  let : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  let : QuasiSeparatedSpace X₀ := quasiSeparatedSpace_of_quasiSeparated f₀
  let P : X₀.Opens → Prop := fun U ↦
    IsIso (singleComplexOpenComparison f₀ f₀' g₀ g₀' sq₀.w K₀ K₀' φ₀ U)
  have h_affine : ∀ U : X₀.Opens, IsAffineOpen U → P U := by
    intro U hU
    exact singleComplexOpenComparison_affine f₀ f₀' g₀ g₀' sq₀
      K₀ hK₀ K₀' hK₀' φ₀ hstalk₀ U hU
  have h_union : ∀ U V : X₀.Opens, IsCompact (U : Set X₀) → IsAffineOpen V →
      P U → P V → P (U ⊓ V) → P (U ⊔ V) := by
    intro U V hUqc hV hU hPV hUV
    have hVqc : IsCompact (V : Set X₀) := hV.isCompact
    exact singleComplexOpenComparison_union f₀ f₀' g₀ g₀' sq₀
      K₀ K₀' φ₀ U V hUqc hVqc hU hPV hUV
  have htop : P ⊤ := quasiCompactOpen_induction X₀ P h_affine h_union ⊤
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X₀)))
  exact singleComplexOpenComparison_top f₀ f₀' g₀ g₀' sq₀.w K₀ K₀' φ₀ htop

end AlgebraicGeometry

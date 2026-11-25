/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.AbelianDerivedHomologySections
import WeilConjectures.AlgebraicGeometry.CartesianHigherImageRawAffineDescent
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Descent of germs of relative higher direct images

Source: Stacks Project, Tag 0EYM, second proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Every germ of the limit higher image is the canonical image of a stage germ.
This is surjectivity of the relative higher-image continuity comparison, without
any invertibility hypothesis on stage exchanges.
Source: Stacks Project, Tag 0EYM, second proof, part (1).
(blueprint: lem-sc-cartesian-higher-image-germ-descent)

Proof: represent the germ by a section on an affine etale neighbourhood of s.
The higher-image sheaf is the sheafification of the pullback cohomology presheaf
(Tag 03Q8), so locally that section is represented by a cohomology class.
Descend the affine etale neighbourhood and the chosen point neighbourhood to a stage
(Tag 0EYL). The cartesian pullbacks of the later neighbourhoods form an affine
inverse system, with qcqs terms and limit the original pullback of f. The
coefficients are pulled back from F on X. Cohomology continuity (Tag 09YQ) gives
this class as the image of a class at some later stage. The presheaf-to-higher-image
map sends that stage class to a stage section. Its germ, transported by the exact
inverse-image/homology isomorphism, is the required element. Naturality of these
maps and the resolution formula for exchange identify its canonical leg image
with the starting germ. The argument includes q=0, zero coefficients, empty
schemes, and a nonempty cofiltered index, reindexed by a directed set if needed. -/
theorem exists_cartesianHigherImage_germ_rep
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (s : c.pt.left)
    (y : ((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
      (cartesianHigherImageLimit D c f F q)) :
    ∃ (i : I) (x : ((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
        (cartesianHigherImageStage D c f F q i)),
      (((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map
        (cartesianHigherImageLeg D c f F q i)) x = y := by
  classical
  let S := c.pt.left
  let K := cartesianDerivedImage f c.pt.hom
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  let Φ := S.uliftPointSmallEtale s
  let P := (abelianComparisonFree S ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
    preadditiveYoneda.obj (K⟦(q : ℤ)⟧)
  obtain ⟨τ, hτ, hτformula⟩ := exists_abelianDerivedHomology_sections_comparison S (q : ℤ) K
  have : LocallySmall.{u + 1} S.Etale := locallySmall_max.{u + 1, u, u + 1}
  have := hτ
  obtain ⟨y', hy'⟩ := Φ.toPresheafFiber_map_surjective τ y
  obtain ⟨U, u, z, hz⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) y'
  let A := Scheme.AffineEtale.Spec S
  obtain ⟨V, a, ⟨b⟩, v, hv⟩ := Φ.jointly_surjective (Sieve.coverByImage A U)
    (A.is_cover_of_isCoverDense S.smallEtaleTopology U) u
  let W := A.obj b.obj
  let w := Φ.fiber.map b.lift v
  let z' := P.map b.map.op z
  have : IsAffine W.left := by
    dsimp only [W, A]
    rw [Scheme.AffineEtale.Spec_obj_left]
    infer_instance
  obtain ⟨i, t, ht⟩ := exists_cartesianHigherImage_raw_affine_factorization
    D c hc f F q W z'
  let Kᵢ := (Functor.mapDerivedCategoryPlus
    (upperStar AddCommGrpCat.{u + 1} (c.π.app i).left)).obj
    (cartesianDerivedImage f (D.obj i).hom ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  obtain ⟨τᵢ, _, hτᵢformula⟩ :=
    exists_abelianDerivedHomology_sections_comparison S (q : ℤ) Kᵢ
  let t' := τᵢ.app (Opposite.op W) t
  have hsection : (cartesianHigherImageLeg D c f F q i).hom.app (Opposite.op W) t' =
      τ.app (Opposite.op W) z' := by
    let m := cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
      (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
    let H₀ := DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
    let Hq := DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    let σ := H₀.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero (q : ℤ))
    have hn := σ.hom.naturality m
    change H₀.map ((shiftFunctor _ (q : ℤ)).map m) ≫ σ.hom.app K =
      σ.hom.app Kᵢ ≫ Hq.map m at hn
    have he :
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
          H₀.map t ≫ σ.hom.app Kᵢ) ≫ Hq.map m =
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
          H₀.map z' ≫ σ.hom.app K := by
      rw [Category.assoc, Category.assoc, ← hn, ← H₀.map_comp_assoc, ht]
    dsimp only [t']
    rw [hτᵢformula, hτformula]
    exact congrArg (fun g ↦ (g.hom.app (Opposite.op W))
      (((toSheafify S.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free)).app (Opposite.op W))
          (FreeAbelianGroup.of (ULift.up (𝟙 W))))) he
  refine ⟨i, Φ.toPresheafFiber W w (cartesianHigherImageStage D c f F q i).obj t', ?_⟩
  change Φ.presheafFiber.map (cartesianHigherImageLeg D c f F q i).hom
    (Φ.toPresheafFiber W w (cartesianHigherImageStage D c f F q i).obj t') = y
  rw [Φ.toPresheafFiber_naturality_apply, hsection]
  rw [← Φ.toPresheafFiber_naturality_apply τ W w]
  have hw : Φ.toPresheafFiber W w P z' = y' := by
    dsimp only [z']
    rw [Φ.toPresheafFiber_w_apply]
    have hb : Φ.fiber.map b.map w = u := by
      dsimp only [w]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, b.fac]
      exact hv
    rw [hb]
    exact hz
  rw [hw]
  exact hy' 

end AlgebraicGeometry.Etale

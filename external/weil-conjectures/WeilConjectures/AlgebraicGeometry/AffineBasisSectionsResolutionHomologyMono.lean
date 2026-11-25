/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ShortComplexSectionComparison
import WeilConjectures.AlgebraicGeometry.IntegerSectionAcyclicIncomingKernelImage
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Mono part of affine-basis section resolution comparison

Source: Stacks Project, Tag 08C2, singleton cover; Tag 071B, compatible resolution tower.
(blueprint: lem-sc-affine-basis-sections-resolution-homology-mono).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def shortComplexTheta {X : Scheme.{u}}
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)) :
    (S.map (SheafOfModules.forget.{u} X.ringCatSheaf)).homology ⟶
      (SheafOfModules.forget.{u} X.ringCatSheaf).obj S.homology :=
  (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).homEquiv _ _
    (((S.map (SheafOfModules.forget.{u} X.ringCatSheaf)).mapHomologyIso
      (PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj))).inv ≫
        ShortComplex.homologyMap (S.mapNatTrans
          (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).counit))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adjointHomologyComparison_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) (U : D ⥤ C) [L.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [L.PreservesHomology] (a : L ⊣ U) {S T : ShortComplex D} (φ : S ⟶ T) :
    ShortComplex.homologyMap (U.mapShortComplex.map φ) ≫ a.homEquiv _ _
        (((T.map U).mapHomologyIso L).inv ≫
          ShortComplex.homologyMap (T.mapNatTrans a.counit)) =
      a.homEquiv _ _ (((S.map U).mapHomologyIso L).inv ≫
        ShortComplex.homologyMap (S.mapNatTrans a.counit)) ≫
          U.map (ShortComplex.homologyMap φ) := by
  have hn : L.mapShortComplex.map (U.mapShortComplex.map φ) ≫
      T.mapNatTrans a.counit = S.mapNatTrans a.counit ≫ φ := by
    ext <;> exact a.counit.naturality _
  apply a.homEquiv_naturality_left_square
  erw [ShortComplex.mapHomologyIso_inv_naturality_assoc
    (U.mapShortComplex.map φ) L]
  rw [← ShortComplex.homologyMap_comp, hn, ShortComplex.homologyMap_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem shortComplexTheta_naturality {X : Scheme.{u}}
    {S T : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (φ : S ⟶ T) :
    ShortComplex.homologyMap ((SheafOfModules.forget.{u} X.ringCatSheaf).mapShortComplex.map φ) ≫
        shortComplexTheta T =
      shortComplexTheta S ≫ (SheafOfModules.forget.{u} X.ringCatSheaf).map
        (ShortComplex.homologyMap φ) :=
  adjointHomologyComparison_naturality
    (PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj))
    (SheafOfModules.forget.{u} X.ringCatSheaf)
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)) φ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The section resolution map induces a monomorphism on homology in each degree.
Source: Stacks Project, Tag 08C2, lemma-alternating-cech-complex-complex-ss,
and Tag 071B, lemma-K-injective.
(blueprint: lem-sc-affine-basis-sections-resolution-homology-mono).

Proof: Use the cokernel and homology vanishing assumptions at W = V. The opcycle
sequence 0 -> H^j(F) -> coker(d^(j-1)) -> im(d^j) -> 0 and its long exact
cohomology sequence give positive-cohomology vanishing of the boundaries.
The cycle sequence 0 -> im(d^(j-1)) -> ker(d^j) -> H^j(F) -> 0 then gives
positive-cohomology vanishing of the cycles. In particular the incoming kernel
and image at degree n have zero first module cohomology on V, using the
ordinary/module cohomology comparison and exact open restriction.
Apply the short-complex section comparison to F.sc n: the adjunction-normalized
comparison from presheaf homology to underlying sheaf homology is invertible
at V. Its naturality follows from naturality of the sheafification homology
isomorphism and of the adjunction counit. Since i is a quasi-isomorphism, the
map on sheaf homology is invertible. Thus the naturality square identifies the
section homology map followed by the target comparison with a composite of
isomorphisms. Cancellation gives monicity without requiring invertibility of
the target comparison. Finally exact presheaf evaluation commutes naturally
with homology, giving the asserted native module-valued map. The module-to-group
forgetful functor reflects invertibility in the source comparison. No tower,
boundedness, termwise acyclicity, or K-injectivity is needed for this mono proof;
the original hypotheses are retained. Empty opens and all integer degrees are
included. -/
theorem affineBasisSections_resolution_homology_mono
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    (F J : CochainComplex X.Modules ℤ) [J.IsKInjective]
    (i : F ⟶ J) [QuasiIso i]
    (hterms : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.X n).restrict W.ι).H (q + 1)))
    (hcokernels : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((cokernel (F.d (n - 1) n)).restrict W.ι).H (q + 1)))
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1))) (n : ℤ) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    Mono (HomologicalComplex.homologyMap
      ((S.mapHomologicalComplex (ComplexShape.up ℤ)).map i) n) := by
  dsimp
  cases hterms V hV le_rfl n 0
  let U := SheafOfModules.forget.{u} X.ringCatSheaf
  let : U.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} X.ringCatSheaf).Additive)
  let E := PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)
  let P : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) := F.sc n
  let T : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) := J.sc n
  let φ : P ⟶ T := (HomologicalComplex.shortComplexFunctor X.Modules (.up ℤ) n).map i
  change Mono (ShortComplex.homologyMap
    (E.mapShortComplex.map (U.mapShortComplex.map φ)))
  obtain ⟨hk, hb⟩ := Scheme.Modules.integer_section_acyclic_incoming_kernel_image F V
    (hcokernels V hV le_rfl) (hhomology V hV le_rfl) n
  have hθ : IsIso (E.map (shortComplexTheta P)) := by
    have h := Scheme.Modules.shortComplex_sectionComparison_isIso P V hk hb
    let G := forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u}
    change IsIso (G.map (E.map (shortComplexTheta P))) at h
    exact isIso_of_reflects_iso (E.map (shortComplexTheta P)) G
  have hH : IsIso (ShortComplex.homologyMap φ) := by
    change IsIso (HomologicalComplex.homologyMap i n)
    infer_instance
  have hnat := E.congr_map (shortComplexTheta_naturality φ)
  simp only [Functor.map_comp] at hnat
  have hm : Mono (E.map (shortComplexTheta P) ≫
      E.map (U.map (ShortComplex.homologyMap φ))) := inferInstance
  rw [← hnat] at hm
  have hmono : Mono (E.map (ShortComplex.homologyMap (U.mapShortComplex.map φ))) :=
    mono_of_mono _ (E.map (shortComplexTheta T))
  have hE := ShortComplex.mapHomologyIso_hom_naturality (U.mapShortComplex.map φ) E
  have hcomp : Mono (ShortComplex.homologyMap
      (E.mapShortComplex.map (U.mapShortComplex.map φ)) ≫
      ((T.map U).mapHomologyIso E).hom) := by
    erw [hE]
    infer_instance
  exact mono_of_mono _ ((T.map U).mapHomologyIso E).hom

end AlgebraicGeometry

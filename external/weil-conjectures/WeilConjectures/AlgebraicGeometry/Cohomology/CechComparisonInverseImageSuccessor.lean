/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
public import WeilConjectures.AlgebraicGeometry.Cohomology.CechInverseImageCochainMap

/-! # Successor step for inverse-image Čech comparison

Source: Stacks Project, Tags 01FD and 01EQ, applied to abelian sheaves.
(blueprint: lem-pc-cech-comparison-inverse-image-unit-succ-step)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

private noncomputable abbrev unitCechMap
    {X Y : Scheme.{u}} {ι : Type u} (g : Y ⟶ X)
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  cechInverseImageCochainMap g U V hinter F ((invImage g).obj F)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app F).hom
private theorem unitCechMap_naturality
    {X Y : Scheme.{u}} {ι : Type u} (g : Y ⟶ X)
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (TopCat.Sheaf.cechComplexFunctor U).map φ ≫ unitCechMap g U V hinter G =
      unitCechMap g U V hinter F ≫
        (TopCat.Sheaf.cechComplexFunctor V).map ((invImage g).map φ) := by
  ext k x
  funext y
  change ((invImage g).obj G).obj.map (homOfLE (hinter k y)).op
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app G).hom.app
        (op (⨅ l, U (y l))) (φ.hom.app _ (x y))) =
    ((invImage g).map φ).hom.app _
      (((invImage g).obj F).obj.map (homOfLE (hinter k y)).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app F).hom.app
          (op (⨅ l, U (y l))) (x y)))
  rw [NatTrans.naturality_apply ((invImage g).map φ).hom]
  congr 1
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.naturality φ
  exact congrArg (fun t ↦ t.hom.app (op (⨅ l, U (y l))) (x y)) h

private theorem exactFunctor_Hδ
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    (G : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : (constantSheaf K AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ≅
      G.obj ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))))
    (T : ShortComplex (Sheaf J AddCommGrpCat.{u}))
    (hT : T.ShortExact) (q : ℕ) (x : Sheaf.H T.X₃ q) :
    Sheaf.H.mapFunctor G e T.X₁ (q + 1) (Sheaf.functorHδ hT q x) =
      Sheaf.functorHδ (hT.map_of_exact G) q
        (Sheaf.H.mapFunctor G e T.X₃ q x) := by
  simp only [Sheaf.functorHδ_apply, Sheaf.H.δSucc_apply, Sheaf.H.mapFunctor_apply,
    CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_extClass]
  exact (CategoryTheory.Abelian.Ext.comp_assoc
    (CategoryTheory.Abelian.Ext.mk₀ e.hom) (x.mapExactFunctor G)
    (hT.map_of_exact G).extClass (zero_add q) rfl (by omega)).symm


/-- The inverse-image comparison equality passes through a Čech connecting map.

Source: Stacks Project, Tags 01FD and 01EQ, connecting-map compatibility of the
comparison; the elementary diagram chase is written here for normalized systems.
(blueprint: lem-pc-cech-comparison-inverse-image-unit-succ-step)

Proof: Naturality of the adjunction unit and of restriction makes its cochain maps
into a morphism between the two short exact Čech complexes. Naturality of the
homology connecting map sends the U-boundary of y to the V-boundary of its image.
Apply the connecting laws of c′ and c. Between them substitute the assumed equality
on y. Exact inverse image maps the extension class of T to that of its image;
Ext associativity then identifies the two sheaf-cohomology boundaries. -/
theorem cechComparison_inverseImage_succ_step
    {X Y : Scheme.{u}} {ι : Type u} (g : Y ⟶ X)
    (U : ι → X.Opens) (V : ι → Y.Opens) (hcover : iSup U = ⊤)
    (hcover' : iSup V = ⊤)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (c : CechComparisonSystem U hcover) (c' : CechComparisonSystem V hcover')
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l)))))
    (hg' : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (((invImage g).map T.g).hom.app (op (⨅ l, V (y l)))))
    (q : ℕ) (y : (TopCat.Sheaf.cechCohomologyFunctor U q).obj T.X₃)
    (hih : (c'.comparison q).app ((invImage g).obj T.X₃)
        (HomologicalComplex.homologyMap
          (cechInverseImageCochainMap g U V hinter T.X₃ ((invImage g).obj T.X₃)
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
              T.X₃).hom) q y) =
      Sheaf.H.mapFunctor (invImage g) (constIso g).symm T.X₃ q
        ((c.comparison q).app T.X₃ y)) :
    (c'.comparison (q + 1)).app ((invImage g).obj T.X₁)
        (HomologicalComplex.homologyMap
          (cechInverseImageCochainMap g U V hinter T.X₁ ((invImage g).obj T.X₁)
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
              T.X₁).hom) (q + 1)
          (TopCat.Sheaf.cechδ U hT hg q y)) =
      Sheaf.H.mapFunctor (invImage g) (constIso g).symm T.X₁ (q + 1)
        ((c.comparison (q + 1)).app T.X₁
          (TopCat.Sheaf.cechδ U hT hg q y)) := by
  let φ : T.map (TopCat.Sheaf.cechComplexFunctor U) ⟶
      (T.map (invImage g)).map (TopCat.Sheaf.cechComplexFunctor V) :=
    { τ₁ := unitCechMap g U V hinter T.X₁
      τ₂ := unitCechMap g U V hinter T.X₂
      τ₃ := unitCechMap g U V hinter T.X₃
      comm₁₂ := (unitCechMap_naturality g U V hinter T.f).symm
      comm₂₃ := (unitCechMap_naturality g U V hinter T.g).symm }
  have hδ := HomologicalComplex.HomologySequence.δ_naturality φ
    (TopCat.Sheaf.shortExact_cechComplex hT hg)
    (TopCat.Sheaf.shortExact_cechComplex (hT.map_of_exact (invImage g)) hg')
    q (q + 1) rfl
  have hδy := congrArg (fun f ↦ f y) hδ
  change HomologicalComplex.homologyMap (unitCechMap g U V hinter T.X₁) (q + 1)
      (TopCat.Sheaf.cechδ U hT hg q y) =
    TopCat.Sheaf.cechδ V (hT.map_of_exact (invImage g)) hg' q
      (HomologicalComplex.homologyMap (unitCechMap g U V hinter T.X₃) q y) at hδy
  rw [hδy]
  have hc := congrArg (fun f ↦ f y) (c.connecting T hT hg q)
  have hc' := congrArg (fun f ↦ f
    (HomologicalComplex.homologyMap (unitCechMap g U V hinter T.X₃) q y))
    (c'.connecting (T.map (invImage g)) (hT.map_of_exact (invImage g)) hg' q)
  change (c.comparison (q + 1)).app T.X₁ (TopCat.Sheaf.cechδ U hT hg q y) =
    Sheaf.functorHδ hT q ((c.comparison q).app T.X₃ y) at hc
  change (c'.comparison (q + 1)).app ((invImage g).obj T.X₁)
      (TopCat.Sheaf.cechδ V (hT.map_of_exact (invImage g)) hg' q
        (HomologicalComplex.homologyMap (unitCechMap g U V hinter T.X₃) q y)) =
    Sheaf.functorHδ (hT.map_of_exact (invImage g)) q
      ((c'.comparison q).app ((invImage g).obj T.X₃)
        (HomologicalComplex.homologyMap (unitCechMap g U V hinter T.X₃) q y)) at hc'
  rw [hc', hih, hc]
  exact (exactFunctor_Hδ (invImage g) (constIso g).symm T hT q
    ((c.comparison q).app T.X₃ y)).symm

end AlgebraicGeometry.Scheme.Modules

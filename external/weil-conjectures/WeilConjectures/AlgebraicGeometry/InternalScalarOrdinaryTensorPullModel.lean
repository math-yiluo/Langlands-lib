/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorPullModels
import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorNormalization

/-! # The native ordinary tensorator in the scalar pullback square -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v u'
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace CategoryTheory.Mod.ResidueOrdinary
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {D : Type u'} [Category.{v} D] [Abelian D] [IsGrothendieckAbelian.{v} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {R : C} [MonObj R] [IsCommMonObj R] {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided] (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair G]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]
private theorem native_map_comap_tensorator (M N : Mod C R) :
    Functor.OplaxMonoidal.δ (G.mapMod R ⋙ Mod.comap ρ) M N =
      (tensorComparison ρ M N).hom := by
  have hm : G.map (Mod.tensorObjπ M N) ≫
      (Functor.OplaxMonoidal.δ (G.mapMod R) M N).hom =
      Functor.OplaxMonoidal.δ G M.X N.X ≫
        Mod.tensorObjπ ((G.mapMod R).obj M) ((G.mapMod R).obj N) := by
    change G.map (Mod.tensorObjπ M N) ≫ (G.mapModTensorIsoX M N).inv = _
    exact Cofork.IsColimit.π_desc' (G.isColimitMapTensorπ M N) _ _
  have hc : Mod.tensorObjπ ((G.mapMod R).obj M) ((G.mapMod R).obj N) ≫
      (Functor.OplaxMonoidal.δ (Mod.comap ρ)
        ((G.mapMod R).obj M) ((G.mapMod R).obj N)).hom =
      Mod.tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N) := by
    exact Mod.tensorObjπ_tensorObjDesc _ _ _ _
  apply Mod.hom_ext
  apply Cofork.IsColimit.hom_ext (G.isColimitMapTensorπ M N)
  change G.map (Mod.tensorObjπ M N) ≫
    ((Functor.OplaxMonoidal.δ (G.mapMod R) M N).hom ≫ _) = _
  rw [← Category.assoc, hm, Category.assoc, hc]
  change _ = G.map (Mod.tensorObjπ M N) ≫ (tensorComparison ρ M N).hom.hom
  rw [tensorComparison_π, Functor.Monoidal.inv_μ]
end CategoryTheory.Mod.ResidueOrdinary

namespace AlgebraicGeometry.ProEtale.QuotientChange
attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
private theorem native_pull_tensorator
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Functor.OplaxMonoidal.δ (CondensedRing.upperStar Λ f) M N =
      (by
        letI := CondensedRing.residueOrdinaryUpperStarMonoidal Λ f
        exact Functor.OplaxMonoidal.δ (CondensedRing.upperStar Λ f) M N) := by
  let U := ProEtale.upperStar Ab.{u + 1} f
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  let e := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)
  let i := Functor.isoWhiskerLeft (U.mapMod (condensedRingObj Λ Y)) e
  have h := Mod.ResidueOrdinary.native_map_comap_tensorator (G := U) ρ M N
  have ht : (by
        letI := CondensedRing.residueOrdinaryUpperStarMonoidal Λ f
        exact Functor.OplaxMonoidal.δ (CondensedRing.upperStar Λ f) M N) =
      i.hom.app (M ⊗ N) ≫ (Mod.ResidueOrdinary.tensorComparison ρ M N).hom ≫
        (i.inv.app M ⊗ₘ i.inv.app N) := by
    let : U.Braided :=
      { toMonoidal := inferInstance
        braided X Y := Functor.LaxBraided.braided (F := U) X Y }
    let := Mod.ResidueOrdinary.mapModComapMonoidal ρ
    exact Functor.Monoidal.transport_δ i.symm M N
  have he := Functor.Monoidal.transport_δ e.symm
    ((U.mapMod (condensedRingObj Λ Y)).obj M)
    ((U.mapMod (condensedRingObj Λ Y)).obj N)
  erw [ht, ← h]
  change (Mod.extendScalars (condensedPullbackHom Λ f)).map
      (Functor.OplaxMonoidal.δ (U.mapMod (condensedRingObj Λ Y)) M N) ≫ _ = _
  erw [he]
  simp only [Iso.symm_hom, Iso.symm_inv]
  erw [reassoc_of% e.hom.naturality
    (Functor.OplaxMonoidal.δ (U.mapMod (condensedRingObj Λ Y)) M N)]
  rfl
end AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale.QuotientChange
attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
private theorem native_pull_oplax
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal =
      (CondensedRing.residueOrdinaryUpperStarMonoidal Λ f).toOplaxMonoidal := by
  apply Functor.OplaxMonoidal.ext
  · change (Mod.extendScalars (condensedPullbackHom Λ f)).map (𝟙 _) ≫ _ = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  · funext M N
    exact native_pull_tensorator Λ f M N

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
/-- The ordinary balanced scalar square uses the native pullback tensorator.

Source: Bhatt--Scholze, Remark 6.8.15 and Lemma 6.5.9(5); Stacks 06YY,
0G7E; the ordinary tensor comparison in integral proper base change (1), (3).
(auxiliary; not a blueprint node).

Proof. Apply residueOrdinaryTensorPull_homotopy for the coefficient map a.
Its transported ordinary monoidal structure agrees with native module pullback
on tensorators. To check this equality forget module actions and precompose with
pullback of the balanced tensor coprojection. The native structure is the
composite of mapMod and extension along the coefficient pullback isomorphism.
The transported structure first combines mapMod with restriction along the
inverse coefficient isomorphism and then transports along extendScalarsIsoComapInv.
For both structures the resulting underlying map is the ambient sheaf pullback
tensorator followed by the two coefficient identifications and the balanced
tensor coprojection on X. Cancel the coprojection epimorphism and use faithfulness
of forgetting actions. This equality in each degree identifies the induced
homotopy tensorators; substitution in the cited ordinary homotopy square gives
the formula. This statement involves only ordinary functors and homotopy
complexes, with no derived scalar comparison or tensor normalization. -/
theorem scalar_ordinary_tensor_pull_model (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    let F := CondensedRing.upperStar Λ f
    let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
    let e := CondensedRing.residueOrdinaryRestrictedRegularPullIso Λ Λ' a f
    let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj (B₀ a Y)) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app (B₀ a Y) ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    let TP := ((extension a Y).mapHomotopyCategory (.up ℤ)).obj P
    (NatTrans.mapHomotopyCategory (CondensedRing.comapUpperStarIso a f).inv
        (.up ℤ)).app TP ≫
      ((V₀ a X).mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).inv (.up ℤ)).app P) ≫
      (Mod.tensorPresentationHomotopyIso (coefficientMap a X)).hom.app FP ≫
      (homotopyTensorSingleIso (B₀ a X)).inv.app FP ≫ eH.inv ▷ FP =
    (F.mapHomotopyCategory (.up ℤ)).map
        ((Mod.tensorPresentationHomotopyIso (coefficientMap a Y)).hom.app P ≫
          (homotopyTensorSingleIso (B₀ a Y)).inv.app P) ≫
      ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
        (Functor.tensorModelCoefficient (B₀ a Y))).app P := by
  have h := CondensedRing.residueOrdinaryTensorPull_homotopy Λ Λ' a f P
  dsimp only at h ⊢
  rw [← native_pull_oplax Λ f] at h
  exact h

end AlgebraicGeometry.ProEtale.QuotientChange

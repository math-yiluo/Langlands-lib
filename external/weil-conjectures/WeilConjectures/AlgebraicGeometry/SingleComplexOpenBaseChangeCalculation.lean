/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCounitCompatibility
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCube

/-! # Residual calculation for explicit open base-change comparisons

Source: Stacks Project, Tags 08FE, 08HY and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Use the constructed functors through their interfaces during the mate calculation.
attribute [local irreducible] singleComplexOpenDirectImageIso singleComplexOpenPullbackIso
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  singleComplexRestrictedCoefficient singleComplexOpenBaseChangeSourceIso
  singleComplexOpenPullbackSquareIso schemeDerivedBaseChangeMap singleComplexOpenSquareComparison


private theorem compose_of_equal
    {C : Type*} [Category* C] {A B D E H : C}
    {x x' : A ⟶ H} {u u' : A ⟶ B} {v v' : B ⟶ D}
    {w w' : D ⟶ E} {z : E ⟶ H}
    (hx : x = x') (hu : u = u') (hv : v = v') (hw : w = w')
    (h : x' = u' ≫ v' ≫ w' ≫ z) : x = u ≫ v ≫ w ≫ z := by
  rw [hx, hu, hv, hw]
  exact h

private theorem comp_map_identity
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    (M : C) {N : D} (x : N ⟶ F.obj M) : x ≫ F.map (𝟙 M) = x := by
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem restrict_homEquiv
    {C D C₀ D₀ : Type*}
    [Category* C] [Category* D] [Category* C₀] [Category* D₀]
    {L : C ⥤ D} {R : D ⥤ C} {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
    (a : L ⊣ R) (a₀ : L₀ ⊣ R₀) (S : C ⥤ C₀) (T : D ⥤ D₀)
    (d : S ⋙ L₀ ≅ L ⋙ T) (b : R ⋙ S ≅ T ⋙ R₀)
    (hb : ∀ N : D, L₀.map (b.hom.app N) ≫ a₀.counit.app (T.obj N) =
      d.hom.app (R.obj N) ≫ T.map (a.counit.app N))
    (M : C) (N : D) (x : L.obj M ⟶ N) :
    S.map (a.homEquiv M N x) ≫ b.hom.app N =
      a₀.homEquiv (S.obj M) (T.obj N) (d.hom.app M ≫ T.map x) := by
  apply (a₀.homEquiv (S.obj M) (T.obj N)).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, hb]
  rw [← Category.assoc]
  erw [d.hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← T.map_comp]
  exact congrArg (fun z ↦ d.hom.app M ≫ T.map z)
    ((a.homEquiv M N).symm_apply_apply x)

private theorem open_baseChange_mate
    {C D C' D' C₀ D₀ C₀' D₀' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    [Category* C₀] [Category* D₀] [Category* C₀'] [Category* D₀']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₀' : C₀' ⥤ D₀'} {R₀' : D₀' ⥤ C₀'}
    (a : L ⊣ R) (a' : L' ⊣ R') (a₀ : L₀ ⊣ R₀) (a₀' : L₀' ⊣ R₀')
    (G : C ⥤ C') (B : D ⥤ D') (G₀ : C₀ ⥤ C₀') (B₀ : D₀ ⥤ D₀')
    (S : C ⥤ C₀) (T : D ⥤ D₀) (S' : C' ⥤ C₀') (T' : D' ⥤ D₀')
    (q : G ⋙ L' ⟶ L ⋙ B) (q₀ : G₀ ⋙ L₀' ⟶ L₀ ⋙ B₀)
    (d : S ⋙ L₀ ≅ L ⋙ T) (d' : S' ⋙ L₀' ≅ L' ⋙ T')
    (e : S ⋙ G₀ ≅ G ⋙ S') (e' : T ⋙ B₀ ≅ B ⋙ T')
    (b : R ⋙ S ≅ T ⋙ R₀) (b' : R' ⋙ S' ≅ T' ⋙ R₀')
    (hb : ∀ N : D, L₀.map (b.hom.app N) ≫ a₀.counit.app (T.obj N) =
      d.hom.app (R.obj N) ≫ T.map (a.counit.app N))
    (hb' : ∀ N : D', L₀'.map (b'.hom.app N) ≫ a₀'.counit.app (T'.obj N) =
      d'.hom.app (R'.obj N) ≫ T'.map (a'.counit.app N))
    (hq : ∀ M : C,
      q₀.app (S.obj M) ≫ B₀.map (d.hom.app M) ≫ e'.hom.app (L.obj M) =
        L₀'.map (e.hom.app M) ≫ d'.hom.app (G.obj M) ≫ T'.map (q.app M))
    (K : D) :
    S'.map (a'.homEquiv (G.obj (R.obj K)) (B.obj K)
        (q.app (R.obj K) ≫ B.map (a.counit.app K))) =
      (e.inv.app (R.obj K) ≫ G₀.map (b.hom.app K)) ≫
        a₀'.homEquiv (G₀.obj (R₀.obj (T.obj K))) (B₀.obj (T.obj K))
          (q₀.app (R₀.obj (T.obj K)) ≫ B₀.map (a₀.counit.app (T.obj K))) ≫
        R₀'.map (e'.hom.app K) ≫ b'.inv.app (B.obj K) := by
  apply (cancel_mono (b'.hom.app (B.obj K))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [restrict_homEquiv a' a₀' S' T' d' b' hb']
  erw [← a₀'.homEquiv_naturality_right]
  erw [← a₀'.homEquiv_naturality_left]
  erw [← a₀'.homEquiv_naturality_left]
  apply congrArg (a₀'.homEquiv (S'.obj (G.obj (R.obj K))) (T'.obj (B.obj K)))
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% q₀.naturality (b.hom.app K)]
  rw [← B₀.map_comp_assoc, hb]
  simp only [Functor.map_comp, Category.assoc]
  erw [e'.hom.naturality (a.counit.app K)]
  erw [reassoc_of% hq (R.obj K)]
  rw [← L₀'.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem baseChange_homEquiv
    [instDerived : ∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (K : schemeDerivedCategory X) :
    schemeDerivedBaseChangeMap f f' g g' h K =
      (singleComplexOpenPinnedAdjunction f').homEquiv
        ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj K))
        ((derivedPullback g').obj K)
        ((singleComplexOpenSquareComparison f f' g g' h).app
            ((schemeDerivedDirectImage f).obj K) ≫
          (derivedPullback g').map ((singleComplexOpenPinnedAdjunction f).counit.app K)) := by
  unfold schemeDerivedBaseChangeMap singleComplexOpenSquareComparison
  dsimp only [singleComplexOpenPinnedComposition, singleComplexOpenPinnedAdjunction]
  simp only [Category.assoc]

attribute [local irreducible] CategoryTheory.Adjunction.homEquiv

/-- Compatibility of the pinned base-change arrow with the explicitly constructed
open comparisons. All comparison data are already constructed; this statement
is only the remaining mate calculation, with no existence claim.
Source: Stacks Project, cohomology.tex, Tags 08HY and 08FE; perfect.tex,
Tag 0DJ9, first paragraph.
(blueprint: lem-pc-n3-open-base-change-calculation).

Proof: Work on K-flat representatives for pullback and K-injective representatives
for direct image. Open restriction preserves K-injectives (Tag 08BS). The
underived direct-image comparison in singleComplexOpenDirectImageIso is the
sectionwise identity on inverse-image opens. It therefore identifies restriction
of the tensor-pullback adjunction counit with the restricted counit. The derived
comparison has the same equation by the factorization identities of
rightDerivedFunctorCompMapDerivedCategoryIso, rightDerivedFunctorNatIso,
rightDerivedFunctorCompIso and rightDerivedFunctorIsoMapDerivedCategory.
The adjunctions in schemeDerivedBaseChangeMap are pinned to the underived
adjunctions and the same derived counits, so this equation descends to their
counits. Explicitly, write L₀=L(f|V)*, R_X=restriction to U and
R_S=restriction to V. If c_f:L₀ R_S ≅ R_X Lf* is the comparison formed
from open pullback and the composition comparisons, and b_f is the constructed
direct-image comparison, the equation is
L₀(b_f.hom.app E) ≫ ε_f₀.app(R_X E) = c_f.hom.app(Rf*E) ≫ R_X(ε_f.app E).
Both sides are evaluation of the same restricted tensor-pullback counit on the
representatives. Apply the same equation for f'. Transpose both sides of the
claimed identity under the pinned adjunction for f' restricted to V'.
Tag 08HY identifies each transpose as pullback of the counit. Substitute the
restriction-counit equation and the explicit source comparison. Associativity
of the pinned pullback composition comparisons, the restricted square equation,
and hj identify the two pullback paths. Cancel inverse comparison factors.
The remaining factors are exactly singleComplexRestrictedCoefficient with
identity coefficient: inverse open pullback on X, composition along j and U.ι,
hj, inverse composition along U'.ι and g', and open pullback on X'. Transposing
back gives the equality. Every operation is a natural transformation identity,
so the proof also applies to zero coefficients, empty opens and unbounded
complexes. -/
theorem singleComplexOpen_baseChange_calculation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV')) :
    let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
    let R := (schemeOpenRestriction S' V').mapDerivedCategory
    let δ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K) =
      (singleComplexOpenBaseChangeSourceIso f g K V V' hV').hom ≫
        schemeDerivedBaseChangeMap
          (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀.w K₀ ≫
        (schemeDerivedDirectImage (f' ∣_ V')).map δ ≫
        (singleComplexOpenDirectImageIso f' V').inv.app ((derivedPullback g').obj K)
    := by
  classical
  rename_i instDerived
  dsimp only
  let a := @singleComplexOpenPinnedAdjunction.{u, w} instDerived
  let f₀ := f ∣_ V
  let f₀' := f' ∣_ V'
  let g₀ := g.resLE V V' hV'
  let RS : schemeDerivedCategory.{u, w} S ⥤ schemeDerivedCategory.{u, w} V.toScheme :=
    (schemeOpenRestriction S V).mapDerivedCategory
  let RX : schemeDerivedCategory.{u, w} X ⥤
      schemeDerivedCategory.{u, w} (f ⁻¹ᵁ V).toScheme :=
    (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory
  let RS' : schemeDerivedCategory.{u, w} S' ⥤ schemeDerivedCategory.{u, w} V'.toScheme :=
    (schemeOpenRestriction S' V').mapDerivedCategory
  let RX' : schemeDerivedCategory.{u, w} X' ⥤
      schemeDerivedCategory.{u, w} (f' ⁻¹ᵁ V').toScheme :=
    (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory
  let q := singleComplexOpenSquareComparison f f' g g' sq.w
  let q₀ := singleComplexOpenSquareComparison f₀ f₀' g₀ j sq₀.w
  let d := singleComplexOpenPullbackSquareIso f V (f ⁻¹ᵁ V) f₀
    (morphismRestrict_ι f V)
  let d' := singleComplexOpenPullbackSquareIso f' V' (f' ⁻¹ᵁ V') f₀'
    (morphismRestrict_ι f' V')
  let e := singleComplexOpenPullbackSquareIso g V V' g₀
    (Scheme.Hom.resLE_comp_ι g hV')
  let e' := singleComplexOpenPullbackSquareIso g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
  have hb (N : schemeDerivedCategory X) :
      (derivedPullback f₀).map ((singleComplexOpenDirectImageIso f V).hom.app N) ≫
          (a f₀).counit.app (RX.obj N) =
        d.hom.app ((schemeDerivedDirectImage f).obj N) ≫ RX.map ((a f).counit.app N) :=
    singleComplexOpen_counit_compatibility f V N
  have hb' (N : schemeDerivedCategory X') :
      (derivedPullback f₀').map ((singleComplexOpenDirectImageIso f' V').hom.app N) ≫
          (a f₀').counit.app (RX'.obj N) =
        d'.hom.app ((schemeDerivedDirectImage f').obj N) ≫ RX'.map ((a f').counit.app N) :=
    singleComplexOpen_counit_compatibility f' V' N
  have hq (M : schemeDerivedCategory S) :
      q₀.app (RS.obj M) ≫ (derivedPullback j).map (d.hom.app M) ≫
          e'.hom.app ((derivedPullback f).obj M) =
        (derivedPullback f₀').map (e.hom.app M) ≫
          d'.hom.app ((derivedPullback g).obj M) ≫ RX'.map (q.app M) :=
    singleComplexOpen_pullback_cube f f' g g' sq.w V V' hV' j hj sq₀.w M
  have hs : (singleComplexOpenBaseChangeSourceIso f g K V V' hV').hom =
      e.inv.app ((schemeDerivedDirectImage f).obj K) ≫
        (derivedPullback g₀).map ((singleComplexOpenDirectImageIso f V).hom.app K) := by
    simp only [singleComplexOpenBaseChangeSourceIso, e, singleComplexOpenPullbackSquareIso,
      NatIso.ofComponents_inv_app, Functor.mapIso_inv, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.app_hom,
      eqToIso.inv, eqToIso.hom, Functor.comp_obj, Functor.mapIso_hom, Category.assoc]
    rfl
  have hd : singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj = e'.hom.app K := by
    have hi := comp_map_identity RX' ((derivedPullback g').obj K) (e'.hom.app K)
    simpa only [singleComplexRestrictedCoefficient, e', singleComplexOpenPullbackSquareIso,
      NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Functor.mapIso_hom, eqToIso.hom, Category.assoc,
      singleComplexOpenPinnedComposition] using hi
  have hm := open_baseChange_mate
    (C := schemeDerivedCategory S) (D := schemeDerivedCategory X)
    (C' := schemeDerivedCategory S') (D' := schemeDerivedCategory X')
    (C₀ := schemeDerivedCategory V.toScheme)
    (D₀ := schemeDerivedCategory (f ⁻¹ᵁ V).toScheme)
    (C₀' := schemeDerivedCategory V'.toScheme)
    (D₀' := schemeDerivedCategory (f' ⁻¹ᵁ V').toScheme)
    (L := derivedPullback f) (R := schemeDerivedDirectImage f)
    (L' := derivedPullback f') (R' := schemeDerivedDirectImage f')
    (L₀ := derivedPullback f₀) (R₀ := schemeDerivedDirectImage f₀)
    (L₀' := derivedPullback f₀') (R₀' := schemeDerivedDirectImage f₀')
    (a f) (a f') (a f₀) (a f₀')
    (derivedPullback g) (derivedPullback g') (derivedPullback g₀) (derivedPullback j)
    RS RX RS' RX' q q₀ d d' e e'
    (singleComplexOpenDirectImageIso f V) (singleComplexOpenDirectImageIso f' V')
    hb hb' hq K
  have hdMap := congrArg (schemeDerivedDirectImage f₀').map hd
  have hBC : schemeDerivedBaseChangeMap f f' g g' sq.w K =
      (a f').homEquiv ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj K))
        ((derivedPullback g').obj K)
        (q.app ((schemeDerivedDirectImage f).obj K) ≫
          (derivedPullback g').map ((a f).counit.app K)) :=
    baseChange_homEquiv f f' g g' sq.w K
  have hBCMap := congrArg RS'.map hBC
  have hBC₀ : schemeDerivedBaseChangeMap f₀ f₀' g₀ j sq₀.w (RX.obj K) =
      (a f₀').homEquiv
        ((derivedPullback g₀).obj ((schemeDerivedDirectImage f₀).obj (RX.obj K)))
        ((derivedPullback j).obj (RX.obj K))
        (q₀.app ((schemeDerivedDirectImage f₀).obj (RX.obj K)) ≫
          (derivedPullback j).map ((a f₀).counit.app (RX.obj K))) :=
    baseChange_homEquiv f₀ f₀' g₀ j sq₀.w (RX.obj K)
  exact compose_of_equal
    (C := schemeDerivedCategory V'.toScheme)
    (A := RS'.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj K)))
    (B := (derivedPullback g₀).obj ((schemeDerivedDirectImage f₀).obj (RX.obj K)))
    (D := (schemeDerivedDirectImage f₀').obj ((derivedPullback j).obj (RX.obj K)))
    (E := (schemeDerivedDirectImage f₀').obj (RX'.obj ((derivedPullback g').obj K)))
    (H := RS'.obj ((schemeDerivedDirectImage f').obj ((derivedPullback g').obj K)))
    hBCMap hs hBC₀ hdMap hm

end AlgebraicGeometry

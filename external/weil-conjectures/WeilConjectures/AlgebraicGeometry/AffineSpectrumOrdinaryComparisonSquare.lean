/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRingIsoNaturality
import WeilConjectures.AlgebraicGeometry.AffineSpectrumTensorCoordinateTransport

/-! # The ordinary affine spectrum stalk comparison square

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098.
(blueprint: lem-pc-affine-spectrum-ordinary-comparison-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem homology_inverse_square
    {C : Type*} [Category* C] {K H K0 H0 : C}
    (c : K ≅ H) (d : K0 ≅ H0) (m : K ⟶ K0) (n : H ⟶ H0)
    (h : m ≫ d.hom = c.hom ≫ n) : n ≫ d.inv = c.inv ≫ m := by
  apply (cancel_epi c.hom).mp
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id]

private theorem assemble_comparison_square
    {C : Type*} [Category* C]
    {L L0 V V0 V0r H H0 HE K K0 KE D : C}
    {l : L ⟶ L0} {b : L ⟶ V} {b0 : L0 ⟶ V0} {a : V0r ≅ V0}
    {t : V ⟶ V0r} {s : V ⟶ H} {s0 : V0 ⟶ H0}
    {u : H ⟶ HE} {v : HE ⟶ H0}
    {c : K ≅ H} {c0 : K0 ≅ H0} {cE : KE ≅ HE}
    {j : K ⟶ D} {epsilon : D ⟶ KE} {alpha : KE ⟶ K0}
    (hl : l ≫ b0 ≫ a.inv = b ≫ t)
    (ht : t ≫ a.hom ≫ s0 = s ≫ u ≫ v)
    (hv : v ≫ c0.inv = cE.inv ≫ alpha)
    (hj : c.hom ≫ u ≫ cE.inv = j ≫ epsilon) :
    l ≫ b0 ≫ s0 ≫ c0.inv = b ≫ s ≫ c.inv ≫ j ≫ epsilon ≫ alpha := by
  have h := congrArg (fun k ↦ k ≫ a.hom ≫ s0 ≫ c0.inv) hl
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  rw [reassoc_of% ht, hv] at h
  have hc : u ≫ cE.inv = c.inv ≫ j ≫ epsilon := by
    apply (cancel_epi c.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hj
  simpa only [Category.assoc, reassoc_of% hc] using h

private theorem compose_maps_square
    {C C0 E D : Type*} [Category* C] [Category* C0] [Category* E] [Category* D]
    (F : C ⥤ D) (F0 : C0 ⥤ D) (H0 : E ⥤ C0)
    {L V S K : C} {L0 V0 S0 : C0} {E0 E1 E2 : E}
    (l : F.obj L ⟶ F0.obj L0)
    (b : L ⟶ V) (s : V ⟶ S) (c : S ⟶ K)
    (b0 : L0 ⟶ V0) (s0 : V0 ⟶ S0) (c0 : S0 ⟶ H0.obj E2)
    (j : F.obj K ⟶ F0.obj (H0.obj E0)) (epsilon : E0 ⟶ E1) (delta : E1 ⟶ E2)
    (h : l ≫ F0.map b0 ≫ F0.map s0 ≫ F0.map c0 =
      F.map b ≫ F.map s ≫ F.map c ≫ j ≫
        F0.map (H0.map epsilon) ≫ F0.map (H0.map delta)) :
    l ≫ F0.map (b0 ≫ s0 ≫ c0) =
      F.map (b ≫ s ≫ c) ≫ j ≫ F0.map (H0.map (epsilon ≫ delta)) := by
  simpa only [Functor.map_comp, Category.assoc] using h

private theorem cancel_transport_factors
    {C C0 D : Type*} [Category* C] [Category* C0] [Category* D]
    (F : C ⥤ D) (F0 : C0 ⥤ D) {A B : C} {A0 B0 : C0} {U : D}
    (c : A ≅ B) (cE : A0 ≅ B0) (e : F.obj A ≅ F0.obj A0)
    (d : U ≅ F0.obj A0) :
    F.map c.hom ≫ (F.mapIso c.symm ≪≫ e ≪≫ F0.mapIso cE).hom ≫ F0.map cE.inv =
      (e.hom ≫ d.inv) ≫ d.hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    ← F.map_comp_assoc, ← F0.map_comp, Iso.hom_inv_id]
  simp only [F.map_id, F0.map_id, Category.id_comp, Category.comp_id, d.inv_hom_id]

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The comparison before applying the inverse derived pullback counit.
Source: Stacks Project, Tag 0DJ8, equation-bc; Tag 0098, stalk pullback formula.
(blueprint: lem-pc-affine-spectrum-ordinary-comparison-square). -/
def comparisonIntoTensorPullback {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (i : ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
    HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
    (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv

/-- The actual chain isomorphism between the two successive ordinary pullbacks.
It is the adjunction mate of pushforward composition, with isoSpec naturality.
Source: Stacks Project, Tags 0096 and 0D5S, pullback composition.
(blueprint: lem-pc-affine-spectrum-ordinary-comparison-square). -/
def affineSpectrumTensorComplexIso {X X' : Scheme.{u}}
    [IsAffine X] [IsAffine X'] (g' : X' ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    ((Scheme.Modules.tensorPullback (Spec.map g'.appTop)).mapHomologicalComplex
      (.up ℤ)).obj
        (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
          (.up ℤ)).obj P) ≅
    ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatIso.mapHomologicalComplex
    ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
    Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
    (.up ℤ)).app P

-- Evaluating the localization lift includes the exact stalk and pullback factors.
private theorem ordinary_stalk_transport_eq {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (y : Y) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
    let E := Scheme.Modules.tensorPullback j
    let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
    F.map (comparisonStalkHomologyIso Z (j y) P i).hom ≫
        (ordinaryIsoPullbackStalkHomologyIso j y i P).hom ≫
        F0.map (comparisonStalkHomologyIso Y y
          ((E.mapHomologicalComplex (.up ℤ)).obj P) i).inv =
      (isoPullbackStalkCohomologyIso j y i).hom.app (DerivedCategory.Q.obj P) ≫
        F0.map ((comparisonStalkCohomology Y y i).map
          ((isoPullbackComplexCounitIso j).hom.app P)) := by
  dsimp only
  let : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
  let : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive :=
    comparisonStalkAdditive Y y
  let E := Scheme.Modules.tensorPullback j
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙
    forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
  let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let H0 := comparisonStalkCohomology Y y i
  let c := comparisonStalkHomologyIso Z (j y) P i
  let cE := comparisonStalkHomologyIso Y y ((E.mapHomologicalComplex (.up ℤ)).obj P) i
  let e := (additiveStalkCohomologyFactors Z (j y) i).app P ≪≫
    H.mapIso ((NatIso.mapHomologicalComplex (isoPullbackAdditiveStalkIso j y)
      (.up ℤ)).app P) ≪≫
    H.mapIso ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ S))
      (.up ℤ)).symm.app P) ≪≫
    (additiveStalkCohomologyFactors Y y i).symm.app
      ((E.mapHomologicalComplex (.up ℤ)).obj P)
  have h : (isoPullbackStalkCohomologyIso j y i).hom.app (DerivedCategory.Q.obj P) =
      e.hom ≫ F0.map (H0.map ((isoPullbackComplexCounitIso j).inv.app P)) := by
    simp only [isoPullbackStalkCohomologyIso, Localization.liftNatIso_hom,
      Localization.liftNatTrans_app]
    rfl
  rw [h]
  exact cancel_transport_factors F F0 c cE e
    (F0.mapIso (H0.mapIso ((isoPullbackComplexCounitIso j).app P)))


-- Unifying the two stalk-ring diagrams and their tensor models.
/-- The base-derived tensor comparison is invariant under affine spectrum coordinates
before introducing either inverse counit for g'. No K-flatness is needed here.

Proof: isoSpec naturality and stalkMap_comp identify R, A, B and C and their
structural maps in the original and spectrum squares. The map on A tensor_R B
is the tensor of the stalk ring isomorphisms; its inverse is the tensor of their
inverses. On the two tensor inclusions these maps intertwine tensorMap, including
its stalkCongr factor. The germ formula of Tag 0098 identifies the stalk complex
of the termwise pullback P0 with extension of the stalk complex of P along the
A-isomorphism. Restriction along its inverse is exact and inverse to this extension.
Transport the left-derived R-to-B extension through these exact equivalences.
Uniqueness of a left-derived lift identifies the transported functor and its
counit with the spectrum model. Apply homology, use cohomologyIso_smul for each
A-element, and tensor induction to lift the B-linear cohomology isomorphism to
an isomorphism over A tensor_R B. Extend scalars to C and forget scalars to get l.
The equations comparison_eq and localized_eq identify the model comparisons with
the transported counits. The tensorStalkIso germ formulas identify the ordinary
pullback factors with affineSpectrumTensorComplexIso. Restriction-stalk naturality
identifies the remaining stalk change with isoPullbackStalkCohomologyIso followed
by the exact iso-pullback complex counit. These equalities give the displayed
square. This uses only exact coordinate equivalences, with no flatness over R,
no invertibility of the comparisons, and no derived pullback composition along g'.
Zero complexes and empty schemes satisfy the same tensor and counit equations.
Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098,
lemma-stalk-pullback-modules; Tag 0096, pullback adjunction.
(blueprint: lem-pc-affine-spectrum-ordinary-comparison-square). -/
theorem exists_affineSpectrum_ordinaryComparison_square
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    ∃ l : F.obj (Arrow.mk (comparisonIntoTensorPullback f f' g g' sq z P i)).left ≅
        F0.obj (Arrow.mk
          (comparisonIntoTensorPullback (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0 i)).left,
      l.hom ≫ F0.map
        (comparisonIntoTensorPullback (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0 i) =
      F.map (comparisonIntoTensorPullback f f' g g' sq z P i) ≫
        (isoPullbackStalkCohomologyIso X'.isoSpec.inv z0 i).hom.app
          (DerivedCategory.Q.obj Pg) ≫
        F0.map (H0.map ((isoPullbackComplexCounitIso X'.isoSpec.inv).hom.app Pg ≫
          DerivedCategory.Q.map (affineSpectrumTensorComplexIso g' P).inv)) := by
  have hcoordinates := exists_affineSpectrum_tensor_coordinates f f' g g' sq sq0 z0 i P
  rcases hcoordinates with ⟨eR, eA, eB, eD, q, t, hA, hB, hD, ht, hcoord⟩
  let z := X'.isoSpec.inv z0
  let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
    (.up ℤ)).obj P
  let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0)) AddCommGrpCat.{u}
  let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
  let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  let := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
  let := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
  let := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
  let M := cohomologyModel f f' g g' sq z P
  let M0 := cohomologyModel (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
  let V0 := tensorComplex (Spec.map f.appTop) (Spec.map f'.appTop)
    (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
  have hlocalized := ModuleCat.exists_baseDerivedTensor_ringIso_square.{u, u + 1}
    (R := R f g' z) (A := A g' z) (B := B f' z) (D := C z)
    (R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0)
    (A0 := A (Spec.map g'.appTop) z0) (B0 := B (Spec.map f'.appTop) z0) (D0 := C z0)
    eR eA eB eD hA hB hD (stalkComplex g' z P)
    (stalkComplex (Spec.map g'.appTop) z0 P0) q M M0 t ht i
  rcases hlocalized with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  let T := ModuleCat.restrictScalars.{u} eD.toRingHom
  let alpha := affineSpectrumTensorComplexIso g' P
  let c := comparisonStalkHomologyIso X' z Pg i
  let cE := comparisonStalkHomologyIso (Spec Γ(X', ⊤)) z0
    (((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj Pg) i
  let c0 := comparisonStalkHomologyIso (Spec Γ(X', ⊤)) z0
    (((Scheme.Modules.tensorPullback (Spec.map g'.appTop)).mapHomologicalComplex
      (.up ℤ)).obj P0) i
  have hv : HomologicalComplex.homologyMap
      ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) i ≫ c0.inv =
      cE.inv ≫ H0.map (DerivedCategory.Q.map alpha.inv) :=
    homology_inverse_square cE c0 _ _
      (comparisonStalkHomologyIso_naturality (Spec Γ(X', ⊤)) z0 alpha.inv i)
  have hJ := ordinary_stalk_transport_eq X'.isoSpec.inv z0 i Pg
  have hvF : F0.map (HomologicalComplex.homologyMap
      ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) i) ≫ F0.map c0.inv =
      F0.map cE.inv ≫ F0.map (H0.map (DerivedCategory.Q.map alpha.inv)) :=
    (F0.map_comp _ _).symm.trans ((congrArg F0.map hv).trans (F0.map_comp _ _))
  have h := assemble_comparison_square
    (a := F.mapIso ((V0.sc i).mapHomologyIso T))
    (c := F.mapIso c) (c0 := F0.mapIso c0) (cE := F0.mapIso cE)
    hl hcoord hvF hJ
  let b := M.localizedComparison i
  let b0 := M0.localizedComparison i
  let s := HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i
  let s0 := HomologicalComplex.homologyMap
    (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom i
  let j := (isoPullbackStalkCohomologyIso X'.isoSpec.inv z0 i).hom.app
    (DerivedCategory.Q.obj Pg)
  let epsilon := (isoPullbackComplexCounitIso X'.isoSpec.inv).hom.app Pg
  let : HasDerivedCategory.{w} (Spec Γ(X', ⊤)).Modules := inferInstanceAs
    (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec Γ(X', ⊤)).toRingedSpace)))
  let delta := DerivedCategory.Q.map alpha.inv
  change l.hom ≫ F0.map (b0 ≫ s0 ≫ c0.inv) =
    F.map (b ≫ s ≫ c.inv) ≫ j ≫ F0.map (H0.map (epsilon ≫ delta))
  exact compose_maps_square F F0 H0 l.hom b s c.inv b0 s0 c0.inv j epsilon delta h

end AlgebraicGeometry.SingleComplexBaseChange

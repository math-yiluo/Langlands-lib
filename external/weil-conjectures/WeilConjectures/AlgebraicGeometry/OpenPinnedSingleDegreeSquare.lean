/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroSquare
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # The geometric restriction square for the pinned single-complex counits
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-open-pinned-single-degree-square). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- The component of the composition-pinned tensor counit in degree n.
This is constructed from the counit fixed by the composition structure; its
universal property determines that counit up to the natural isomorphism used
in downstream comparisons. No arbitrary module or complex is chosen.
Source: Stacks Project, Tag 08HY
(blueprint: lem-pc-open-pinned-single-degree-square). -/
def pinnedSingleDegreeTensorComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (k : X ⟶ Y) [(Scheme.Modules.tensorPullback k).Additive]
    (M : Y.Modules) (n : ℤ) :
    (derivedPullback k).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj M) ⟶
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
        ((Scheme.Modules.tensorPullback k).obj M) :=
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor _ n).obj M) ≫
    DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback k) (ComplexShape.up ℤ) n).hom.app M)))

private theorem transport_square
    {C : Type*} [Category C] {A A₀ B B₀ C₁ C₀ D D₀ : C}
    (eA : A ≅ A₀) (eB : B ≅ B₀) (eC : C₁ ≅ C₀) (eD : D ≅ D₀)
    (a : A₀ ≅ C₀) (b : B₀ ≅ D₀)
    (x : A ⟶ B) (x₀ : A₀ ⟶ B₀) (y : C₁ ⟶ D) (y₀ : C₀ ⟶ D₀)
    (hx : x ≫ eB.hom = eA.hom ≫ x₀)
    (hy : y ≫ eD.hom = eC.hom ≫ y₀)
    (h₀ : x₀ ≫ b.hom = a.hom ≫ y₀) :
    x ≫ (eB ≪≫ b ≪≫ eD.symm).hom =
      (eA ≪≫ a ≪≫ eC.symm).hom ≫ y := by
  apply (cancel_mono eD.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc x eB.hom, hx]
  simp only [Category.assoc]
  rw [← Category.assoc x₀ b.hom, h₀, hy]
  simp only [Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- Transport a pointwise square through compatible comparisons with a common functor. -/
private theorem transport_functor_square
    {A B C : Type*} [Category A] [Category B] [Category C]
    (r : A ⥤ B) (J : C ⥤ C)
    {F G F₀ G₀ : A ⥤ C} {F' G' F₀' G₀' : B ⥤ C}
    (x : ∀ M, F.obj M ⟶ G.obj M) (x₀ : ∀ M, F₀.obj M ⟶ G₀.obj M)
    (y : ∀ M, F'.obj M ⟶ G'.obj M) (y₀ : ∀ M, F₀'.obj M ⟶ G₀'.obj M)
    (h₀ : ∃ a₀ : F₀ ≅ r ⋙ F₀', ∃ b₀ : G₀ ≅ r ⋙ G₀',
      ∀ M, x₀ M ≫ b₀.hom.app M = a₀.hom.app M ≫ y₀ (r.obj M))
    (h₁ : ∃ a₁ : F ≅ F₀ ⋙ J, ∃ b₁ : G ≅ G₀ ⋙ J,
      ∀ M, x M ≫ b₁.hom.app M = a₁.hom.app M ≫ J.map (x₀ M))
    (h₂ : ∃ a₂ : F' ⋙ 𝟭 C ≅ (F₀' ⋙ 𝟭 C) ⋙ J,
      ∃ b₂ : G' ⋙ 𝟭 C ≅ (G₀' ⋙ 𝟭 C) ⋙ J,
      ∀ M, (𝟭 C).map (y M) ≫ b₂.hom.app M =
        a₂.hom.app M ≫ J.map ((𝟭 C).map (y₀ M))) :
    ∃ a : F ≅ r ⋙ F', ∃ b : G ≅ r ⋙ G',
      ∀ M, x M ≫ b.hom.app M = a.hom.app M ≫ y (r.obj M) := by
  obtain ⟨a₀, b₀, h₀⟩ := h₀
  obtain ⟨a₁, b₁, h₁⟩ := h₁
  obtain ⟨a₂, b₂, h₂⟩ := h₂
  simp only [Functor.comp_id, Functor.id_map] at a₂ b₂ h₂
  let a₂' := Functor.isoWhiskerLeft r a₂
  let b₂' := Functor.isoWhiskerLeft r b₂
  refine ⟨a₁ ≪≫ Functor.isoWhiskerRight a₀ J ≪≫ a₂'.symm,
    b₁ ≪≫ Functor.isoWhiskerRight b₀ J ≪≫ b₂'.symm, ?_⟩
  intro M
  have hshift := congrArg J.map (h₀ M)
  simp only [Functor.map_comp] at hshift
  exact transport_square (a₁.app M) (b₁.app M) (a₂'.app M) (b₂'.app M)
    ((Functor.isoWhiskerRight a₀ J).app M) ((Functor.isoWhiskerRight b₀ J).app M)
    (x M) (J.map (x₀ M)) (y (r.obj M)) (J.map (y₀ (r.obj M)))
    (h₁ M) (h₂ (r.obj M)) hshift

set_option backward.isDefEq.respectTransparency.types false in
/-- Natural restriction isomorphisms commute with the base-change mate for the
single components of the pinned counits. This contains only the geometric part
of open compatibility: neither arbitrary witnessing counits nor truncation or
comparison automorphisms occur in this statement.
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U; Steps 1, 2 and the
reference-counit part of Step 3 of stage3-open-fixed-counits-compatibility.
(blueprint: lem-pc-open-pinned-single-degree-square).

Proof: Write Z = f' inverse-image W. A cone over U and W composes to a cone
over X and S'. The original pullback property gives its unique lift to X',
which factors through Z. Hence Z is the pullback P of fA and gA, with the
same projections. Use this identification throughout. Restriction has exact
extension by zero as a left adjoint, so preserves K-injectives. Computing
Rf and Rf' on K-injective resolutions gives their natural restriction
isomorphisms (08FE). Restriction preserves K-flat complexes as well: extend
an acyclic test complex by zero, apply the extension-by-zero tensor projection
formula, and use exactness. Thus the pullback computations on K-flat
resolutions give the natural restriction isomorphisms for Lg and Lg'.
Combine the Lg and Rf comparisons with exact single-complex restriction to
obtain a. Combine the Rf' comparison with ordinary tensor restriction along
Z = P and the exact single-complex identification to obtain b.

Transpose both sides of the displayed square under the derived adjunctions
pinned to the composition counits. On the K-flat and K-injective representatives,
both transposes are tensor reassociation followed by the pullback of the
same direct-image counit. The underived restriction square commutes, including
units, counits and reassociations. Apply it termwise to the resolutions, then
localize. This proves equality of the transposes and hence of their mates
(08HY). The termwise single-complex identification identifies the last maps
with pinnedSingleDegreeTensorComparison. All comparisons are natural in G,
so the same functor isomorphisms a and b work for every G. This works in any
integer degree, with empty opens, and with zero modules. It uses no flatness,
properness, or affineness hypothesis on G or the schemes. -/
theorem open_pinned_single_degree_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (n : ℤ) (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    let U := f ⁻¹ᵁ V
    let fA := f ∣_ V
    let gA := g.resLE V W hWV
    let p := pullback.fst fA gA
    let q := pullback.snd fA gA
    let T := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n
    let T0 := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n
    let T' := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n
    let TP := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) n
    let R := (schemeOpenRestriction S' W).mapDerivedCategory
    ∃ a : ((T ⋙ schemeDerivedDirectImage f) ⋙ derivedPullback g) ⋙ R ≅
        ((schemeOpenRestriction X U ⋙ T0) ⋙ schemeDerivedDirectImage fA) ⋙
          derivedPullback gA,
    ∃ b : ((Scheme.Modules.tensorPullback g' ⋙ T') ⋙ schemeDerivedDirectImage f') ⋙ R ≅
        ((schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback p) ⋙ TP) ⋙
          schemeDerivedDirectImage q,
    ∀ G : X.Modules,
      R.map (schemeDerivedBaseChangeMap f f' g g' sq.w (T.obj G) ≫
          (schemeDerivedDirectImage f').map (pinnedSingleDegreeTensorComparison g' G n)) ≫
        b.hom.app G =
      a.hom.app G ≫
        (schemeDerivedBaseChangeMap fA q gA p pullback.condition
            (T0.obj ((schemeOpenRestriction X U).obj G)) ≫
          (schemeDerivedDirectImage q).map
            (pinnedSingleDegreeTensorComparison p ((schemeOpenRestriction X U).obj G) n))
    := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let U := f ⁻¹ᵁ V
  let fA := f ∣_ V
  let gA := g.resLE V W hWV
  let p := pullback.fst fA gA
  let q := pullback.snd fA gA
  let r := schemeOpenRestriction X U
  let R := (schemeOpenRestriction S' W).mapDerivedCategory
  let J := shiftFunctor (schemeDerivedCategory.{u, w} W.toScheme) (-n)
  exact transport_functor_square r J
    (F := singleDegreeBaseChangeSource.{u, w} f g n ⋙ R)
    (G := singleDegreeBaseChangeTarget.{u, w} g' f' n ⋙ R)
    (F₀ := singleDegreeBaseChangeSource.{u, w} f g 0 ⋙ R)
    (G₀ := singleDegreeBaseChangeTarget.{u, w} g' f' 0 ⋙ R)
    (F' := singleDegreeBaseChangeSource.{u, w} fA gA n)
    (G' := singleDegreeBaseChangeTarget.{u, w} p q n)
    (F₀' := singleDegreeBaseChangeSource.{u, w} fA gA 0)
    (G₀' := singleDegreeBaseChangeTarget.{u, w} p q 0)
    (fun G ↦ R.map (singleDegreeBaseChangeComposite.{u, w} f g g' f' sq.w n G))
    (fun G ↦ R.map (singleDegreeBaseChangeComposite.{u, w} f g g' f' sq.w 0 G))
    (fun G ↦ singleDegreeBaseChangeComposite.{u, w} fA gA p q pullback.condition n G)
    (fun G ↦ singleDegreeBaseChangeComposite.{u, w} fA gA p q pullback.condition 0 G)
    (open_pinned_single_degree_zero_square.{u, w} f g g' f' sq V W hWV)
    (pinned_single_base_change_shift.{u, w} f g g' f' sq.w R n)
    (pinned_single_base_change_shift.{u, w} fA gA p q pullback.condition
      (𝟭 (schemeDerivedCategory.{u, w} W.toScheme)) n)

end AlgebraicGeometry

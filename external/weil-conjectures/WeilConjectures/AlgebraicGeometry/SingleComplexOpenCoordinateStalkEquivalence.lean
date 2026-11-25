/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData

/-! # Stalkwise conjugacy for transported open coordinates.

Source: Stacks Project, perfect.tex, Tag 0DJ9, localization calculation.
(blueprint: lem-pc-single-complex-open-coordinate-stalk-equivalence)

The proof is the termwise stalk calculation: open-immersion stalk isomorphisms
identify the four local rings and complexes, and naturality of tensor extension,
homology, and the representing map conjugates the two comparison arrows.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

open SingleComplexBaseChange in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalkComparison_normalized
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c : Coordinates g' K K' φ) (z : X') (i : ℤ) :
    stalkComparison f f' g g' sq c z i ≫
        ((comparisonStalkHomologyIso X' z c.N i).inv ≫
          (comparisonStalkCohomology X' z i).map c.e'.hom) =
      comparisonIntoPullback f f' g g' sq z c.P c.counit_isIso i ≫
        (comparisonStalkCohomology X' z i).map ((derivedPullback g').map c.e.hom ≫ φ) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  have := c.counit_isIso
  have ht := comparisonStalkHomologyIso_naturality X' z c.t i
  have ht' : HomologicalComplex.homologyMap
      (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).map c.t) i ≫ (comparisonStalkHomologyIso X' z c.N i).inv =
      (comparisonStalkHomologyIso X' z
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).inv ≫
          (comparisonStalkCohomology X' z i).map (DerivedCategory.Q.map c.t) := by
    apply (cancel_epi (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).hom).mp
    rw [← Category.assoc, ← ht]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ht'' := congrArg (fun a => a ≫ (comparisonStalkCohomology X' z i).map c.e'.hom) ht'
  simp only [Category.assoc] at ht''
  simp only [stalkComparison, comparisonIntoPullback, Category.assoc, Functor.map_comp, cast_eq]
  rw [← Functor.map_comp, ← Functor.map_comp, ← c.represents]
  simp only [Functor.map_comp, cast_eq, IsIso.inv_hom_id_assoc]
  rw [ht'']

private theorem normalized_square
    {D : Type*} [Category D] {A₀ A B₀ B L₀ L M₀ M : D}
    (a : A₀ ⟶ B₀) (b : A ⟶ B) (l : A₀ ≅ A)
    (td : B₀ ≅ M₀) (tc : B ≅ M) (ν : M₀ ≅ M) (v : L₀ ≅ L)
    (p : A₀ ⟶ L₀) (q : A ⟶ L) (μ : L₀ ⟶ M₀) (η : L ⟶ M)
    (hd : a ≫ td.hom = p ≫ μ) (hc : b ≫ tc.hom = q ≫ η)
    (hl : p ≫ v.hom = l.hom ≫ q) (hn : μ ≫ ν.hom = v.hom ≫ η) :
    l.hom ≫ b = a ≫ (td ≪≫ ν ≪≫ tc.symm).hom := by
  apply (cancel_mono tc.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [hc, ← Category.assoc, ← hl, Category.assoc, ← hn, ← Category.assoc, ← hd]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Elaborating the mapped normalization equations unfolds nested derived tensor sources.
/-- The restricted and original stalk comparison arrows are isomorphic after
forgetting scalars, for any coordinates of the canonical restricted coefficient.
No invertibility of either comparison is assumed.

Proof: Write U=f⁻¹V and U'=f'⁻¹V'. At z the four open-immersion stalk maps
for U, U', V, V' are invertible. The point equalities follow from hj and the
restriction squares. Transport the four local rings along these stalk maps.
The stalkMap_comp identity and sq.w identify the maps R→A, R→B, A→C and B→C.
The two restrictions of tensorMap then agree, so its tensor-product universal
property identifies both the tensor algebra A⊗_R B and its action on C.

Exact stalks applied to c.e and d.e, together with the restriction-stalk
extension comparison, identify the derived stalks of c.P and d.P after this
ring transport: both represent the stalk of K at g'(z.val). Restriction and
extension along the stalk ring isomorphisms are inverse exact equivalences.
They transport the left-derived scalar-extension universal property. Its unique
counit-compatible isomorphism, followed by the model cohomologyIso, identifies
the base-derived tensor cohomology objects. The cohomologyIso_smul equations
identify multiplication by A; tensor-product induction lifts this identification
from B-linearity to A⊗_R B-linearity. Extend it to C and forget scalars to obtain
the source additive isomorphism. Exact stalks applied to c.e' and d.e' similarly
identify both target homologies with H^i(K') at z.val, giving the target isomorphism.

For commutativity, normalize both comparisons by these target identifications.
The represents equations replace each homology map of the chain map by the map
of the corresponding derived coefficient, after cancellation of its invertible
pullback counit. K-flatness of the stalk representatives follows from the stalk
criterion, so ordinary A→C extension computes their derived pullback. The
comparison_eq and localized_eq equations express the preceding tensor comparisons
by the universal derived counits and their extension/restriction transposes.
Naturality under the ring isomorphisms and derived representative isomorphisms
therefore identifies these normalized comparisons. The coefficient is exactly
singleComplexRestrictedCoefficient: its composition factors identify derived
pullback of the original coefficient with restricted pullback, and the
leftDerivedUnique factorization identity for singleComplexOpenPullbackIso makes
this identification compatible with the pinned counits. Consequently the source
and target isomorphisms give a commuting square for the two complete comparison
maps. Apply Arrow.isoMk. This argument constructs no extra coordinate system and
uses no flatness over R. Empty opens have no z; top opens, zero complexes, zero
rings and unbounded complexes obey the same identities.

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8 and
Tag 0DJ9, first paragraph; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-coordinate-stalk-equivalence). -/
theorem nonempty_singleComplexOpen_stalk_arrow_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (c : SingleComplexBaseChange.Coordinates g' K K' φ)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (d : SingleComplexBaseChange.Coordinates j
      ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K)
      ((schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.obj K')
      (singleComplexRestrictedCoefficient g' K K' φ
        (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj)) :
    ∀ (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ),
      Nonempty
        (Arrow.mk ((forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z))
            AddCommGrpCat.{u}).map
              (SingleComplexBaseChange.stalkComparison
                (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ d z i)) ≅
          Arrow.mk ((forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val))
            AddCommGrpCat.{u}).map
              (SingleComplexBaseChange.stalkComparison f f' g g' sq c z.val i))) :=
  open SingleComplexBaseChange in by
    intro z i
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let H := comparisonStalkCohomology X' z.val i
    let R := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    obtain ⟨ν, l, hl⟩ := exists_singleComplexOpen_normalized_transport
      f f' g g' sq K V V' hV' j hj sq₀ c.P d.P c.e d.e
      c.isKFlat d.isKFlat c.counit_isIso d.counit_isIso z i
    let td := F₀.mapIso ((comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z d.N i).symm ≪≫
      H₀.mapIso d.e')
    let tc := F.mapIso ((comparisonStalkHomologyIso X' z.val c.N i).symm ≪≫ H.mapIso c.e')
    let r := td ≪≫ ν.app K' ≪≫ tc.symm
    refine ⟨Arrow.isoMk l r ?_⟩
    have hφ : singleComplexRestrictedCoefficient g' K K' φ
        (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj = θ ≫ R.map φ := by
      simp [θ, R, singleComplexRestrictedCoefficient, Category.assoc]
    have hd : F₀.map (stalkComparison (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ d z i) ≫ td.hom =
        F₀.map (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
            (g.resLE V V' hV') j sq₀ z d.P d.counit_isIso i ≫
          H₀.map ((derivedPullback j).map d.e.hom ≫ θ)) ≫
            (R ⋙ H₀ ⋙ F₀).map φ := by
      have hd₀ := congrArg F₀.map (stalkComparison_normalized (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ d z i)
      have hp := congrArg (fun t ↦ F₀.map
        (comparisonIntoPullback (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀
          z d.P d.counit_isIso i ≫ H₀.map ((derivedPullback j).map d.e.hom ≫ t))) hφ
      simpa only [td, H₀, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Functor.map_comp, Functor.comp_map] using hd₀.trans hp
    have hc : F.map (stalkComparison f f' g g' sq c z.val i) ≫ tc.hom =
        F.map (comparisonIntoPullback f f' g g' sq z.val c.P c.counit_isIso i ≫
          H.map ((derivedPullback g').map c.e.hom)) ≫ (H ⋙ F).map φ := by
      simpa only [tc, H, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Functor.map_comp, Functor.comp_map] using
        congrArg F.map (stalkComparison_normalized f f' g g' sq c z.val i)
    have hn := ν.hom.naturality φ
    exact normalized_square _ _ l td tc (ν.app K') (ν.app ((derivedPullback g').obj K))
      _ _ _ _ hd hc hl hn

end AlgebraicGeometry

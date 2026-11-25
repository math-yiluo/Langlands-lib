/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Sites.Ga
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.EtaleTensorUnitSectionsNatural
import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
import WeilConjectures.AlgebraicGeometry.Sites.GaGmLowerStar
import WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FibreDimension
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentCohomologyULift
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Vanishing of the étale higher direct images of `𝔾ₐ` above the fibre dimension

Let `f : C ⟶ S` be proper and smooth, with fibres of dimension at most `d`. Then the étale
higher direct images `Rᵠf_* 𝔾ₐ` vanish for `q > d`.

The sheaf `Rᵠf_* 𝔾ₐ` is the sheafification of `V ↦ Hᵠ((C ×_S V)_ét, 𝔾ₐ)` (Stacks, Tag 072W). For
affine `V` étale over `S`, this is the Zariski cohomology `Hᵠ(C ×_S V, 𝒪)` (Stacks, Tag 03DW),
which is `Γ(V, Rᵠ(f_V)_* 𝒪)` for the base change `f_V : C ×_S V ⟶ V`, and vanishes above the
fibre dimension of `f_V`, which is that of `f` (Stacks, Tag 0E0L / Grothendieck vanishing on the
fibres).

## Main statements

- `AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctorAt_of_subsingleton_H`: derived
  sections over an étale object are the cohomology of the restriction.
- `AlgebraicGeometry.Scheme.subsingleton_H_gaSheaf_of_subsingleton_H_unit`: the étale cohomology
  of `𝔾ₐ` on a quasi-compact separated scheme vanishes where the Zariski cohomology of `𝒪` does.
- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedFunctor_lowerStar_gaSheaf`: `Rᵠf_* 𝔾ₐ = 0`
  for `q` larger than the fibre dimension of a proper smooth `f`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

local instance (X : Scheme.{u}) : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)

namespace Etale

/-- **Derived sections over an étale object.** For an étale `X`-scheme `W` and an abelian étale
sheaf `F` on `X`, the derived sections of `F` over `W` are the étale cohomology of the
restriction `F|_W`: if `Hᵠ(W_ét, F|_W) = 0`, then `Rᵠ Γ(W, -)(F) = 0`.

Restriction to `W` is exact and preserves injectives (it has the exact left adjoint `W_!`), and
`Γ(W, -)` is `Γ(W, -|_W)` (Stacks, Tag 03F3). -/
lemma isZero_rightDerived_sectionsFunctorAt_of_subsingleton_H {X : Scheme.{u}} (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj F) q)) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op W)).rightDerived q).obj F) := by
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf W.left.smallEtaleTopology AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  have hW : Etale W.hom := W.prop
  let ρ := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom hW
  let j := Etale.localizationRestriction AddCommGrpCat.{u + 1} W.hom hW
  let b : W.left.Etale :=
    MorphismProperty.Over.mk ⊤ (𝟙 W.left) (MorphismProperty.id_mem _ _)
  let ΓW : Sheaf W.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.sectionsFunctorAt _ b
  let e : (MorphismProperty.Over.map ⊤ hW).obj b ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.id_comp]
      exact (Category.id_comp _).symm)
  let eΓ : (Sheaf.sectionsFunctorAt X.smallEtaleTopology W :
      Sheaf _ AddCommGrpCat.{u + 1} ⥤ _) ≅ j ⋙ ΓW :=
    NatIso.ofComponents (fun G ↦ G.obj.mapIso e.op) (fun φ ↦ (φ.hom.naturality e.op.hom).symm)
  have : j.Additive := { }
  have : PreservesFiniteColimits j := preservesFiniteColimits_of_natIso ρ
  have : PreservesFiniteLimits j := preservesFiniteLimits_of_natIso ρ
  have : j.PreservesInjectiveObjects :=
    ⟨fun {I} _ ↦ Injective.of_iso (ρ.app I) (injective_upperStar_obj_of_etale_addCommGrp W.hom I)⟩
  refine IsZero.of_iso ?_ ((NatIso.rightDerived eΓ q).app F ≪≫
    (Functor.rightDerivedCompIsoOfExact j ΓW q).app F)
  refine IsZero.of_iso ?_ (ΓW.rightDerived q |>.mapIso (ρ.app F).symm)
  exact (Sheaf.subsingleton_H_iff_isZero_rightDerived W.left.smallEtaleTopology
    (Scheme.isTerminalEtaleMkId W.left) q _).1 h

/-- An abelian presheaf on the small étale site of `X` which vanishes on all étale `X`-schemes
with affine source has zero sheafification: the affine étale `X`-schemes cover every étale
`X`-scheme, so every section is locally zero. -/
theorem isZero_presheafToSheaf_of_isZero_of_isAffine {X : Scheme.{u}}
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hP : ∀ V : X.Etale, IsAffine V.left → IsZero (P.obj (op V))) :
    IsZero ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj P) := by
  have hz (W : X.Etale) (ξ : P.obj (op W)) :
      Presheaf.equalizerSieve ξ (0 : P.obj (op W)) ∈ X.smallEtaleTopology W := by
    rw [Scheme.mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨j, y, hy⟩ := W.left.affineCover.exists_eq x
    let A : X.Etale := Scheme.Etale.mk (W.left.affineCover.f j ≫ W.hom)
    let a : A ⟶ W := MorphismProperty.Over.homMk (W.left.affineCover.f j) rfl
    have hA : IsAffine A.left := inferInstanceAs (IsAffine (W.left.affineCover.X j))
    exact ⟨A, a, (AddCommGrpCat.isZero_iff_subsingleton.mp (hP A hA)).elim _ _, y, hy⟩
  have hzero : Presheaf.IsLocallySurjective X.smallEtaleTopology (0 : P ⟶ P) := by
    constructor
    intro W ξ
    apply X.smallEtaleTopology.superset_covering _ (hz W ξ)
    intro V v hv
    refine ⟨0, ?_⟩
    simpa only [Presheaf.equalizerSieve_apply, map_zero] using hv.symm
  let S := (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj P
  have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : Sheaf.IsLocallySurjective (0 : S ⟶ S) := by
    have hh := (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      X.smallEtaleTopology (0 : P ⟶ P)).2 hzero
    simpa only [Functor.map_zero] using hh
  have : Epi (0 : S ⟶ S) :=
    (Sheaf.isLocallySurjective_iff_epi' (J := X.smallEtaleTopology)
      AddCommGrpCat.{u + 1} (0 : S ⟶ S)).1 inferInstance
  exact IsZero.of_epi_zero S S

end Etale

namespace Scheme

namespace Modules

/-- The sections of a zero sheaf of modules are zero. -/
lemma subsingleton_sections_of_isZero {X : Scheme.{u}} {M : X.Modules} (hM : IsZero M)
    (U : X.Opens) : Subsingleton Γ(M, U) := by
  have h (z : Γ(M, U)) : z = 0 := by
    simpa using congrArg (fun φ : M ⟶ M ↦ φ.app U z) (hM.eq_of_src (𝟙 M) 0)
  exact ⟨fun x y ↦ (h x).trans (h y).symm⟩

/-- **Cohomology of `𝒪` vanishes above the fibre dimension.** For a proper flat morphism
`f : X ⟶ T` of finite presentation to an affine scheme whose fibres have dimension at most `d`,
`Hᵠ(X, 𝒪_X) = 0` for `q > d`: it is `Γ(T, Rᵠf_* 𝒪_X)`, and `Rᵠf_* 𝒪_X = 0` by Grothendieck
vanishing on the fibres (Stacks, Tags 02UZ and 0E0L). -/
theorem subsingleton_H_unit_of_topologicalKrullDim_fiber_le {X T : Scheme.{u}} (f : X ⟶ T)
    [IsAffine T] [IsProper f] [Flat f] [LocallyOfFinitePresentation f] {d : ℕ}
    (hd : ∀ t, topologicalKrullDim (f.fiber t) ≤ d) {q : ℕ} (hq : d < q) :
    Subsingleton (Scheme.Modules.H (X := X) (SheafOfModules.unit X.ringCatSheaf) q) := by
  have := isGrothendieckAbelian X
  have : SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : SheafOfModules.IsFinitePresentation.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hz := isZero_higherDirectImage_of_hFiber_eq_zero f _
    (isFlatOver_of_isInvertible f (SheafOfModules.unit X.ringCatSheaf)) (d := d)
    (fun t q' hq' ↦ ?_) hq
  · obtain ⟨e⟩ := nonempty_sections_higherDirectImage_iso_H f
      (SheafOfModules.unit X.ringCatSheaf) q
    have := subsingleton_sections_of_isZero hz ⊤
    exact e.symm.injective.subsingleton
  · have : LocallyOfFiniteType (f.fiberToSpecResidueField t) := by
      unfold Scheme.Hom.fiberToSpecResidueField
      infer_instance
    have := LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField t)
    have : IsNoetherian (f.fiber t) := ⟨⟩
    have : Subsingleton (((Modules.pullback (f.fiberι t)).obj
        (SheafOfModules.unit X.ringCatSheaf)).H q') :=
      Modules.subsingleton_H_of_topologicalKrullDim_lt _
        ((hd t).trans_lt (by exact_mod_cast hq'))
    let := f.fiberOverSpecResidueField t
    exact Module.finrank_zero_of_subsingleton

end Modules

/-- An abelian étale sheaf whose sections are identified with the global functions, compatibly
with restriction, is `𝔾ₐ`. -/
noncomputable def isoGaSheafOfSectionsAddEquiv {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ V : X.Etaleᵒᵖ, G.obj.obj V ≃+ Γ(V.unop.left, ⊤))
    (ha : ∀ (V W : X.Etaleᵒᵖ) (g : V ⟶ W) (x : G.obj.obj V),
      a W (G.obj.map g x) = g.unop.left.appTop (a V x)) :
    G ≅ X.gaSheaf :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun V ↦ ((a V).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun g ↦ by
      ext x
      apply ULift.ext
      exact ha _ _ g x))

/-- The universe lift of an abelian étale sheaf whose sections are identified with the global
functions, compatibly with restriction, is `𝔾ₐ`. -/
noncomputable def uliftIsoGaSheafOfSectionsAddEquiv {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ V : X.Etaleᵒᵖ, G.obj.obj V ≃+ Γ(V.unop.left, ⊤))
    (ha : ∀ (V W : X.Etaleᵒᵖ) (g : V ⟶ W) (x : G.obj.obj V),
      a W (G.obj.map g x) = g.unop.left.appTop (a V x)) :
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj G ≅
      X.gaSheaf :=
  isoGaSheafOfSectionsAddEquiv _ (fun V ↦ AddEquiv.ulift.trans (a V))
    (fun V W g x ↦ ha V W g x.down)

/-- The étale sheaf `𝔾ₐ` is the universe lift of the étale sheaf of `𝒪_X`
(Stacks, Tag 03DU). -/
theorem nonempty_gaSheaf_iso_uLift_etaleTensorSectionsSheaf (X : Scheme.{u}) :
    Nonempty (X.gaSheaf ≅
      (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf))) := by
  obtain ⟨b, hb, -⟩ := Modules.exists_etaleTensorUnit_sections_natural X
  exact ⟨(uliftIsoGaSheafOfSectionsAddEquiv _ b hb).symm⟩

/-- **Étale cohomology of `𝔾ₐ` and Zariski cohomology of `𝒪`.** On a quasi-compact separated
scheme `Y`, if `Hᵠ(Y, 𝒪_Y) = 0`, then `Hᵠ(Y_ét, 𝔾ₐ) = 0` (Stacks, Tag 03DW). -/
theorem subsingleton_H_gaSheaf_of_subsingleton_H_unit (Y : Scheme.{u}) [CompactSpace Y]
    [Y.IsSeparated] (q : ℕ)
    (h : Subsingleton (Scheme.Modules.H (X := Y) (SheafOfModules.unit Y.ringCatSheaf) q)) :
    Subsingleton (Sheaf.H Y.gaSheaf q) := by
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
  obtain ⟨e₁, -⟩ := Modules.exists_moduleCohomology_source_comparison Y q
  obtain ⟨_, _, c, _, _⟩ := Modules.etale_zariski_qcoh_comparison Y
  obtain ⟨e₃⟩ := Modules.nonempty_etaleTensorSectionsSheaf_cohomology_ulift Y
    (SheafOfModules.unit Y.ringCatSheaf) q
  obtain ⟨i₄⟩ := nonempty_gaSheaf_iso_uLift_etaleTensorSectionsSheaf Y
  let e₄ := ((Sheaf.functorH Y.smallEtaleTopology q).mapIso i₄).addCommGroupIsoToAddEquiv
  let : HasDerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
    HasDerivedCategory.standard _
  let : HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
    HasExt.standard _
  let e₂ := (Abelian.Ext.homAddEquiv.{u + 1, u}.trans
    Abelian.Ext.homAddEquiv.{u + 1, u + 1}.symm).trans
      (c (SheafOfModules.unit Y.ringCatSheaf) q).symm
  exact (e₄.trans (e₃.trans (e₂.trans
    (e₁ (SheafOfModules.unit Y.ringCatSheaf))))).injective.subsingleton

end Scheme

namespace Etale

/-- For a proper smooth `f : C ⟶ S` with fibres of dimension at most `d` and an étale
`S`-scheme `V` with affine source, `Hᵠ((C ×_S V)_ét, 𝔾ₐ) = 0` for `q > d`. -/
theorem isZero_rightDerived_sectionsFunctorAt_gaSheaf_pullback {C S : Scheme.{u}}
    (f : C ⟶ S) [IsProper f] [Smooth f] (V : S.Etale) [IsAffine V.left] {d : ℕ}
    (hd : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ d) {q : ℕ} (hq : d < q) :
    IsZero (((sheafToPresheaf C.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation C.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))).rightDerived q).obj
          C.gaSheaf) := by
  apply isZero_rightDerived_sectionsFunctorAt_of_subsingleton_H
  let W := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  have : Etale W.hom := W.prop
  let e := ((Sheaf.functorH _ q).mapIso
    (Scheme.upperStarGaSheafIso W.hom)).addCommGroupIsoToAddEquiv
  have : IsAffine ((𝟭 Scheme).obj V.left) := ‹IsAffine V.left›
  have : CompactSpace W.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom f : W.left ⟶ V.left)
  have : W.left.IsSeparated := by
    have h : IsSeparated ((pullback.fst V.hom f : W.left ⟶ V.left) ≫ terminal.from V.left) :=
      inferInstance
    exact ⟨(terminal.hom_ext (C := Scheme.{u})
      ((pullback.fst V.hom f : W.left ⟶ V.left) ≫ terminal.from V.left)
      (terminal.from W.left)) ▸ h⟩
  have : Subsingleton (Sheaf.H W.left.gaSheaf q) := by
    refine Scheme.subsingleton_H_gaSheaf_of_subsingleton_H_unit _ q
      (Scheme.Modules.subsingleton_H_unit_of_topologicalKrullDim_fiber_le
        (pullback.fst V.hom f) (fun v ↦ ?_) hq)
    have H := isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback V.hom f).flip v
    refine (IsHomeomorph.topologicalKrullDim_eq _
      H.isoPullback.hom.homeomorph.isHomeomorph).le.trans ?_
    have : LocallyOfFiniteType (f.fiberToSpecResidueField (V.hom v)) := by
      unfold Scheme.Hom.fiberToSpecResidueField
      infer_instance
    exact (topologicalKrullDim_pullback_le_of_field _ _).trans (hd _)
  exact @Function.Injective.subsingleton _ _ _ e.injective this

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The bounded below and unbounded models of the higher direct images of an abelian sheaf
agree: `Hᵠ` of `Rf_*⁺ G` and of `Rf_* G` are isomorphic. -/
@[irreducible]
noncomputable def homologyRightDerivedLowerStarPlusIso {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≅
    (DerivedCategory.homologyFunctor _ q).obj
      ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) :=
  (DerivedCategory.homologyFunctor _ q).mapIso
    ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlusCompatibility.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G))

/-- **Vanishing of `Rᵠf_* 𝔾ₐ` above the fibre dimension.** For a proper smooth morphism
`f : C ⟶ S` whose fibres have dimension at most `d`, the étale higher direct images
`Rᵠf_* 𝔾ₐ` vanish for `q > d`.

`Rᵠf_* 𝔾ₐ` is the sheafification of `V ↦ Hᵠ((C ×_S V)_ét, 𝔾ₐ)` (Stacks, Tag 072W), which
vanishes on affine `V` (`isZero_rightDerived_sectionsFunctorAt_gaSheaf_pullback`). -/
theorem isZero_homology_rightDerivedFunctor_lowerStar_gaSheaf {C S : Scheme.{u}}
    (f : C ⟶ S) [IsProper f] [Smooth f] {d : ℕ}
    (hd : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ d) {q : ℕ} (hq : d < q) :
    IsZero ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
      ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj C.gaSheaf))) := by
  refine IsZero.of_iso ?_ (homologyRightDerivedLowerStarPlusIso f C.gaSheaf q).symm
  refine IsZero.of_iso ?_ (higherDirectImageSheafifiedPresheaf f C.gaSheaf q).symm
  refine isZero_presheafToSheaf_of_isZero_of_isAffine _ fun V hV ↦ ?_
  exact isZero_rightDerived_sectionsFunctorAt_gaSheaf_pullback f V hd hq
/-- The universe lift of the étale sheaf of a zero module is zero. -/
lemma isZero_sheafCompose_uliftFunctor_etaleTensorSectionsSheaf {X : Scheme.{u}}
    (E : X.Modules) [E.IsQuasicoherent] (hE : IsZero E) :
    IsZero ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Scheme.Modules.etaleTensorSectionsSheaf E)) := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  apply ULift.ext
  have : (Scheme.Modules.tensorPullback U.unop.hom).IsLeftAdjoint :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.unop.hom)).isLeftAdjoint
  exact (Scheme.Modules.subsingleton_sections_of_isZero
    ((Scheme.Modules.tensorPullback U.unop.hom).map_isZero hE) ⊤).elim _ _

/-- If the degree-`q` étale higher direct image of `𝔾ₐ` vanishes, it is the universe lift of the
étale sheaf of the zero module, with the zero Frobenius-linear endomorphism. -/
theorem exists_frobeniusLinear_of_isZero_homology {C S : Scheme.{u}} (f : C ⟶ S) (p : ℕ)
    [Fact p.Prime] (hpC : (p : Γ(C, ⊤)) = 0) (q : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj C.gaSheaf)))) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteLocallyFree)
      (F : Scheme.Modules.etaleTensorSectionsSheaf E ⟶
        Scheme.Modules.etaleTensorSectionsSheaf E),
      (∀ (U : S.Etale) (a : Γ(U.left, ⊤))
        (e : Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)),
        F.hom.app (op U)
            ((((Scheme.Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
          (((Scheme.Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
            (F.hom.app (op U) e)) ∧
      ∃ e : (DerivedCategory.homologyFunctor _ q).obj
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj C.gaSheaf)) ≅
          (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
            (Scheme.Modules.etaleTensorSectionsSheaf E),
        (DerivedCategory.homologyFunctor _ q).map
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.map
              ((DerivedCategory.singleFunctor _ 0).map (C.gaArtinSchreier p hpC))) ≫ e.hom =
          e.hom ≫ (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
            (F - 𝟙 _) := by
  let E : S.Modules := SheafOfModules.free (ULift.{u} (Fin 0))
  have hE : IsZero E :=
    (IsZero.iff_id_eq_zero E).mpr (SheafOfModules.free_hom_ext fun i ↦ isEmptyElim i)
  refine ⟨E, inferInstance,
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0, 0, fun U a e ↦ ?_,
    h.iso (isZero_sheafCompose_uliftFunctor_etaleTensorSectionsSheaf E hE), h.eq_of_src _ _⟩
  have : (Scheme.Modules.tensorPullback U.hom).IsLeftAdjoint :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.hom)).isLeftAdjoint
  exact (Scheme.Modules.subsingleton_sections_of_isZero
    ((Scheme.Modules.tensorPullback U.hom).map_isZero hE) ⊤).elim _ _

end Etale

end AlgebraicGeometry

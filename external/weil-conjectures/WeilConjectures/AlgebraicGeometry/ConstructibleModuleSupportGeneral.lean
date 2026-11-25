/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSupport
import WeilConjectures.AlgebraicGeometry.GeometricStalkSupport
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Support of a constructible etale module sheaf

Source: Stacks Project, Etale Cohomology, Tags 09YS(3), 04FS and 04FN
(blueprint: new-constructible-module-support-general).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem constructible_image_clopen {Y : Type u} [TopologicalSpace Y]
    {X : Type u} [TopologicalSpace X] [SpectralSpace X] {f : Y → X}
    (hf : Topology.IsEmbedding f) (hE : Topology.IsConstructible (Set.range f))
    {t : Set Y} (ht : IsClopen t) : Topology.IsConstructible (f '' t) := by
  have hEc : IsCompact (Set.range f) := by
    have h := isCompact_iInter_of_isConstructible
      (s := fun _ : Unit ↦ Set.range f) (fun _ ↦ hE)
    simpa only [Set.iInter_const] using h
  have hY : IsCompact (Set.univ : Set Y) := by
    apply hf.isCompact_iff.mpr
    simpa using hEc
  have htc : IsCompact (f '' t) := by
    simpa using (hY.inter_right ht.1).image hf.continuous
  obtain ⟨U, hU, htU⟩ := hf.isInducing.image_eq_isOpen_inter_range ht.2
  obtain ⟨W, hWc, hWo, htW, hWU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between htc hU
      (by rw [htU]; exact Set.inter_subset_left)
  have heq : f '' t = Set.range f ∩ W := by
    rw [htU] at htW ⊢
    exact Set.Subset.antisymm (fun x hx ↦ ⟨hx.2, htW hx⟩)
      (fun x hx ↦ ⟨hWU hx.2, hx.1⟩)
  rw [heq]
  exact hE.inter (hWc.isConstructible hWo)

/-- Constant values on a trivializing cover detect the underlying abelian support.
Compare the stalk with its cover value, then forget coefficients. Independence of
zero stalks over one point proves both implications. Source: Stacks 09YS(3), 03Q1, 04FN. -/
private theorem etaleModuleSupport_on_trivializing_cover
    {X Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (f : Y ⟶ X)
    (d : LocallyConstantDatum ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G))
    (M : d.cover.I₀ → ModuleCat.{u + 1} Λ)
    (hM : ∀ i : d.cover.I₀, Nonempty ((((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G).over
          (d.cover.etalePrecoverageToEtale i)) ≅
        (constantSheaf (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} Λ)).obj (M i))) :
    ∀ (i : d.cover.I₀) (y : d.cover.X i),
      f (d.cover.f i y) ∈ etaleSheafSupport
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) ↔
        ¬ IsZero (M i) := by
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro i y
  let K := (d.cover.X i).residueField y
  let Ω := AlgebraicClosure K
  let s : Spec (.of Ω) ⟶ d.cover.X i :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ (d.cover.X i).fromSpecResidueField y
  let t := (s ≫ d.cover.f i) ≫ f
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
  have ht : t default = f (d.cover.f i y) := by
    change f (d.cover.f i ((d.cover.X i).fromSpecResidueField y
      ((Spec.map (CommRingCat.ofHom (algebraMap K Ω))) default))) = _
    rw [Scheme.fromSpecResidueField_apply]
  let H := (Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj G
  let W := d.cover.etalePrecoverageToEtale i
  let eH : (Etale.upperStar (ModuleCat.{u + 1} Λ) W.hom).obj H ≅
      (constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i) :=
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) W H).symm ≪≫
      (Etale.overSheafEquiv W (ModuleCat.{u + 1} Λ)).functor.mapIso (hM i).some ≪≫
      ((Etale.overEquiv W).constantSheafSheafCongrIso
        (Y.smallEtaleTopology.over W) W.left.smallEtaleTopology
        (ModuleCat.{u + 1} Λ) CategoryTheory.Over.mkIdTerminal).app (M i)
  let e : ((pointSmallEtale (s ≫ d.cover.f i)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj H ≅ M i :=
    ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) W.hom s).app H).symm ≪≫
      (pointSmallEtale s).sheafFiber.mapIso eH ≪≫
      (pointSmallEtale s).sheafFiberConstantSheafIso (M i)
  let e' := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ)
    f (s ≫ d.cover.f i)).app G
  let E : sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
          (pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ) ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
    (pointSmallEtale t).sheafFiberCompIso.{u, u, u + 1, u + 1, u + 1, u + 2, u + 2}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let eF := E.app G
  let eM := eF ≪≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
    (e'.symm ≪≫ e)
  have hz : IsZero ((pointSmallEtale t).sheafFiber.obj F) ↔ IsZero (M i) := by
    refine eM.isZero_iff.trans ?_
    rw [AddCommGrpCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
    rfl
  constructor
  · rintro ⟨Ω', hfield, hclosed, t', ht', hn⟩ hzM
    exact hn ((isZero_sheafFiber_iff_of_same_image t t' (ht.trans ht'.symm) F).mp
      (hz.mpr hzM))
  · intro hn
    exact ⟨Ω, inferInstance, inferInstance, t, ht, fun h ↦ hn (hz.mp h)⟩


/-- The underlying abelian support of a constructible module sheaf is constructible.

Source: Stacks Project, Tag 09YS(3), proof using Tags 03Q1 and 04FN.
(blueprint: new-constructible-module-support-general).

Proof: zero stalks are independent of the chosen geometric point. On each constructible
stratum, choose the constant values of a trivializing etale cover. The support and its
complement are unions of the open images of the cover members with respectively nonzero
and zero value. Hence the support is clopen on each stratum. An embedded constructible
stratum is compact, and a clopen subset of it is constructible in the spectral base:
choose finitely many compact open basis members between that subset and an ambient open.
Take the finite union over the strata. Empty strata and the zero sheaf are included.
No finiteness of the coefficient ring is used. -/
theorem constructibleModuleSupport_general {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {Λ : Type (u + 1)}
    [CommRing Λ] (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf G] :
    let F := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
    (∀ (x : X) (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
      (s : Spec (.of Ω) ⟶ X) (s' : Spec (.of Ω') ⟶ X),
      s default = x → s' default = x →
        (IsZero (((pointSmallEtale s).sheafFiber).obj F) ↔
          IsZero (((pointSmallEtale s').sheafFiber).obj F))) ∧
    (∀ (x : X) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      s default = x → IsZero (((pointSmallEtale s).sheafFiber).obj F) →
        x ∉ etaleSheafSupport F) ∧
    Topology.IsConstructible (etaleSheafSupport F) := by
  dsimp only
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
  have hind (x : X) (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω]
      [Field Ω'] [IsAlgClosed Ω'] (s : Spec (.of Ω) ⟶ X) (s' : Spec (.of Ω') ⟶ X)
      (hs : s default = x) (hs' : s' default = x) :
      IsZero ((pointSmallEtale s).sheafFiber.obj F) ↔
        IsZero ((pointSmallEtale s').sheafFiber.obj F) :=
    isZero_sheafFiber_iff_of_same_image s s' (hs.trans hs'.symm) F
  refine ⟨hind, ?_, ?_⟩
  · intro x Ω _ _ s hs hz hmem
    obtain ⟨Ω', hfield, hclosed, s', hs', hnz⟩ := hmem
    exact hnz ((hind x Ω Ω' s s' hs hs').mp hz)
  · classical
    obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
      (FA := fun A B : ModuleCat.{u + 1} Λ ↦ A →ₗ[Λ] B)
      (CA := fun A : ModuleCat.{u + 1} Λ ↦ A) (F := G)
    have hpart (k : Fin S.n) :
        Topology.IsConstructible (etaleSheafSupport F ∩ S.stratum k) := by
      have := hS k
      obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum
        (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj G)
      choose M hM using fun i ↦ (d.isConstant i).mem_essImage
      have hvalue := etaleModuleSupport_on_trivializing_cover G (S.immersion k) d M
        (fun i ↦ ⟨(hM i).some.symm⟩)
      let A : Set (S.domain k) := (S.immersion k) ⁻¹' etaleSheafSupport F
      have hrange (i : d.cover.I₀) : IsOpen (Set.range (d.cover.f i)) := by
        let : Etale (d.cover.f i) := d.cover.map_prop i
        simpa only [Set.image_univ] using (d.cover.f i).isOpenMap _ isOpen_univ
      have hpos : A = ⋃ (i : d.cover.I₀) (_ : ¬ IsZero (M i)),
          Set.range (d.cover.f i) := by
        ext y
        constructor
        · intro hy
          obtain ⟨i, z, rfl⟩ := d.cover.exists_eq y
          exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
            ⟨(hvalue i z).mp hy, ⟨z, rfl⟩⟩⟩
        · intro hy
          simp only [Set.mem_iUnion, Set.mem_range] at hy
          obtain ⟨i, hi, z, rfl⟩ := hy
          exact (hvalue i z).mpr hi
      have hneg : Aᶜ = ⋃ (i : d.cover.I₀) (_ : IsZero (M i)),
          Set.range (d.cover.f i) := by
        ext y
        constructor
        · intro hy
          obtain ⟨i, z, rfl⟩ := d.cover.exists_eq y
          have hz : IsZero (M i) := by
            by_contra hn
            exact hy ((hvalue i z).mpr hn)
          exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hz, ⟨z, rfl⟩⟩⟩
        · intro hy
          simp only [Set.mem_iUnion, Set.mem_range] at hy
          obtain ⟨i, hi, z, rfl⟩ := hy
          exact fun hz ↦ (hvalue i z).mp hz hi
      have hcl : IsClopen A := by
        constructor
        · rw [← isOpen_compl_iff, hneg]
          exact isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hrange i
        · rw [hpos]
          exact isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hrange i
      let := S.isImmersion k
      let : SpectralSpace X := {}
      have hc := constructible_image_clopen (S.immersion k).isEmbedding
        (by rw [S.range_immersion k]; exact S.isConstructible_stratum k) hcl
      simpa only [A, Set.image_preimage_eq_range_inter, S.range_immersion k,
        Set.inter_comm] using hc
    have heq : etaleSheafSupport F =
        ⋃ k : Fin S.n, etaleSheafSupport F ∩ S.stratum k := by
      rw [← Set.inter_iUnion, S.iUnion_stratum_eq_univ, Set.inter_univ]
    rw [heq]
    exact Topology.IsConstructible.iUnion hpart

end AlgebraicGeometry.Scheme

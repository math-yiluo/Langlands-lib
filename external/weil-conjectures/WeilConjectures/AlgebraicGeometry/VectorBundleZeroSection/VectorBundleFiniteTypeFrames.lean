/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Finite-type affine frames for a vector bundle

Source: blueprint sec-smooth-purity/sk-prop-sp-orientation,
preparation for sk-prop-sp-orientation-vector-bundle, Steps 1–3;
Stacks Project, Tags 01T6, 01T2, 01IT, 01C6, 01M1, 01S8 and 02G2.
(blueprint: lem-pur-vector-bundle-finite-type-frames).

The Noetherian base is a conclusion, supplied as an existential witness before using the
existing bundle construction. No separatedness assumption is imposed on the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.VectorBundleZeroSection

open Scheme.Modules

private noncomputable def restrictFrame (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    {U V : S.Opens} (h : V ≤ U) (e : Trivialization S d F U) :
    Trivialization S d F V := by
  have : (restrictFunctor (S.homOfLE h)).IsLeftAdjoint :=
    (restrictAdjunction (S.homOfLE h)).isLeftAdjoint
  exact restrictCompIso F U.ι (S.homOfLE h) V.ι (Scheme.homOfLE_ι S h) ≪≫
    (restrictFunctor (S.homOfLE h)).mapIso e ≪≫
      (SheafOfModules.mapFreeIso (restrictFunctor (S.homOfLE h))
        (ULift.{u} (Fin d)) (restrictUnitIso (S.homOfLE h)).symm).symm

private theorem exists_affine_frame (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (x : S) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧ Nonempty (Trivialization S d F U.1) := by
  classical
  obtain ⟨I, W, hW, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hW.ge (Set.mem_univ x))
  obtain ⟨V, hV, hx, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hi
  exact ⟨⟨V, hV⟩, hx, ⟨restrictFrame S d F hVU (e i).some⟩⟩

private theorem finite_affine_frames (S : Scheme.{u}) [CompactSpace S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    ∃ (n : ℕ) (U : Fin n → S.affineOpens)
      (_e : ∀ i, Trivialization S d F (U i).1),
      (⨆ i, (U i).1) = ⊤ ∧ (IsEmpty S → n = 0) := by
  classical
  by_cases h : IsEmpty S
  · let U : Fin 0 → S.affineOpens := Fin.elim0
    refine ⟨0, U, fun i ↦ Fin.elim0 i, ?_, fun _ ↦ rfl⟩
    let := h
    exact Subsingleton.elim _ _
  · choose U hx e using exists_affine_frame S d F
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
      (fun x : S ↦ ((U x).1 : Set S)) (fun x ↦ (U x).1.isOpen)
      (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
    let a : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
    refine ⟨Fintype.card t, fun i ↦ U (a i).1, fun i ↦ (e (a i).1).some, ?_, ?_⟩
    · apply top_unique
      intro x _
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact Opens.mem_iSup.mpr ⟨a.symm ⟨y, hy⟩, by simpa using hxy⟩
    · exact fun h' ↦ False.elim (h h')

private theorem bundle_smooth (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    SmoothOfRelativeDimension d (π S d F) := by
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension d) U hU
  intro i
  let E := (e i).some
  have := (trivializationMap_spec S d F (U i) E).1
  rw [← (trivializationMap_spec S d F (U i) E).2.1]
  have : SmoothOfRelativeDimension d
      (AffineSpace (ULift.{u} (Fin d)) (U i).toScheme ↘ (U i).toScheme) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over
      (ULift.{u} (Fin d)) (U i).toScheme
  exact MorphismProperty.RespectsIso.precomp _ _ _ this

private theorem bundle_zero_isIso (S : Scheme.{u}) [IsNoetherian S]
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank 0] : IsIso (π S 0 F) := by
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := 0)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU
  intro i
  have := (trivializationMap_spec S 0 F (U i) (e i).some).1
  rw [← (trivializationMap_spec S 0 F (U i) (e i).some).2.1]
  infer_instance

private theorem affine_finiteType (k : Type u) [Field k] {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.FiniteType := by
  rw [CommRingCat.hom_comp]
  exact RingHom.FiniteType.comp (HasRingHomProperty.iff_of_isAffine.mp ‹_›)
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)

set_option backward.isDefEq.respectTransparency false in
private theorem restrictFrame_section (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    {U V : S.Opens} (h : V ≤ U) (e : Trivialization S d F U) (i : Fin d) :
    frameSection S d F V (restrictFrame S d F h e) i =
      F.presheaf.map (homOfLE h).op (frameSection S d F U e i) := by
  have : (restrictFunctor (S.homOfLE h)).IsLeftAdjoint :=
    (restrictAdjunction (S.homOfLE h)).isLeftAdjoint
  have hg : (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) (ULift.up i)) ≫
      (restrictFrame S d F h e).inv =
      (restrictUnitIso (S.homOfLE h)).inv ≫
        (restrictFunctor (S.homOfLE h)).map
          (SheafOfModules.ιFree (ULift.up i) ≫ e.inv) ≫
        (restrictCompIso F U.ι (S.homOfLE h) V.ι (Scheme.homOfLE_ι S h)).inv := by
    dsimp only [restrictFrame, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
    simpa only [Category.assoc, Functor.map_comp, Iso.symm_hom] using
      congrArg (fun m ↦ m ≫ (restrictFunctor (S.homOfLE h)).map e.inv ≫
        (restrictCompIso F U.ι (S.homOfLE h) V.ι (Scheme.homOfLE_ι S h)).inv)
        (SheafOfModules.ιFree_mapFreeIso_hom (restrictFunctor (S.homOfLE h))
          (ULift.{u} (Fin d)) (restrictUnitIso (S.homOfLE h)).symm (ULift.up i))
  have hg' := congrArg (fun (m : SheafOfModules.unit V.toScheme.ringCatSheaf ⟶
      F.restrict V.ι) ↦ Scheme.Modules.Hom.app m ⊤
    (1 : Γ(V.toScheme, ⊤))) hg
  change (restrictFrame S d F h e).inv.val.app (op ⊤)
      ((SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) (ULift.up i)).val.app
        (op ⊤) (1 : Γ(V.toScheme, ⊤))) =
    (restrictCompIso F U.ι (S.homOfLE h) V.ι (Scheme.homOfLE_ι S h)).inv.val.app
      (op ⊤) (((restrictFunctor (S.homOfLE h)).map
        (SheafOfModules.ιFree (ULift.up i) ≫ e.inv)).val.app (op ⊤)
          ((restrictUnitIso (S.homOfLE h)).inv.val.app (op ⊤)
            (1 : Γ(V.toScheme, ⊤)))) at hg'
  unfold frameSection
  rw [hg']
  have h1 : (restrictUnitIso (S.homOfLE h)).inv.val.app (op ⊤)
      (1 : Γ(V.toScheme, ⊤)) =
      (1 : Γ(U.toScheme, (S.homOfLE h) ''ᵁ ⊤)) := by
    change ((S.homOfLE h).appIso ⊤).inv 1 = 1
    exact map_one _
  rw [h1]
  dsimp only [restrictCompIso, Iso.trans_inv, Iso.app_inv, Iso.symm_inv]
  change F.presheaf.map (eqToHom V.ι_image_top.symm).op
      (Hom.app ((restrictFunctorCongr (Scheme.homOfLE_ι S h)).hom.app F) ⊤
        (Hom.app ((restrictFunctorComp (S.homOfLE h) U.ι).inv.app F) ⊤
          (((restrictFunctor (S.homOfLE h)).map
            (SheafOfModules.ιFree (ULift.up i) ≫ e.inv)).val.app (op ⊤)
              (1 : Γ(U.toScheme, (S.homOfLE h) ''ᵁ ⊤))))) = _
  erw [restrictFunctorCongr_hom_app_app, restrictFunctorComp_inv_app_app]
  let W : U.toScheme.Opens := (S.homOfLE h) ''ᵁ ⊤
  let σ : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ F.restrict U.ι :=
    SheafOfModules.ιFree (ULift.up i) ≫ e.inv
  have hn := PresheafOfModules.naturality_apply σ.val
    (homOfLE (le_top : W ≤ ⊤)).op (1 : Γ(U.toScheme, ⊤))
  change σ.val.app (op W)
    (U.toScheme.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op 1) = _ at hn
  rw [map_one] at hn
  change F.presheaf.map (eqToHom V.ι_image_top.symm).op
    (F.presheaf.map _ (F.presheaf.map _
      (σ.val.app (op W) (1 : Γ(U.toScheme, W))))) = _
  rw [hn]
  change F.presheaf.map _ (F.presheaf.map _ (F.presheaf.map _
    (F.presheaf.map _ (σ.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤)))))) =
      F.presheaf.map _ (F.presheaf.map _
        (σ.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))))
  simp only [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  congr 1

set_option linter.unusedVariables false in
/-- A finite-type scheme over a field has finite affine module frames for every bundle
of constant finite rank. Their induced bundle charts have separated finite-type total
spaces, and frames compare on affine refinements of overlaps.

Source: blueprint sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-vector-bundle, geometric preparation for Steps 1–3;
Stacks Tags 01T6, 01T2, 01IT, 01C6, 01M1, 01S8, 01S7 and 02G2.
(blueprint: lem-pur-vector-bundle-finite-type-frames).

Proof:
1. The field is Noetherian. Finite type over its spectrum makes S Noetherian by
lem-weil-pbc-finite-type-over-noetherian. Choose local module frames by
 def-amb-finite-locally-free-module, shrink them to affine opens using
lem-weil-pbc-affine-opens-basis, and take a finite subcover by quasi-compactness.
The rings of these opens are finitely generated over k by lem-weil-pbc-lft-affine-pairs.
2. The quasi-coherent symmetric algebra restricts to the symmetric algebra of sections
by lem-weil-pbc-quasi-coherent-symmetric-algebra-affine. Relative Spec and its restriction
compatibility (lem-weil-pbc-affine-morphism-relative-spec) identify each inverse image
with the corresponding symmetric-algebra spectrum. The basis-to-polynomial equivalence
lem-weil-pbc-symmetric-algebra-free-module-polynomial identifies the frame generators
with variables. Scalars give the polynomial projection; augmentation kills the variables,
so the canonical trivializationMap carries the zero section to the coordinate origin.
3. The affine charts show that the projection is affine by pqf-lem-affine-local-target,
hence quasi-compact and separated by lem-weil-pbc-affine-morphism-permanence.
Polynomial algebras have the d variables as algebra generators, so the pointwise criterion
lem-weil-pbc-lft-pointwise-criterion proves local finite type. Finite type over the
Noetherian base then makes the total space Noetherian.
4. Adjoin the d variables to finite generators of each base ring over k. Each chart is
therefore finite type over k and is separated because its source is affine, using
lem-weil-pbc-affine-source-morphism-separated.
5. The affine-space projections are smooth of relative dimension d by
sbc-lem-affine-space-smooth. Transport across the frame isomorphisms using
lem-weil-pbc-smooth-restrict-open-subschemes, and descend through the covering using
lem-weil-pbc-smooth-local-on-source. A fibre over a point of a base chart is the entire
corresponding affine-space fibre, so its dimension everywhere is d.
6. Refine each overlap by affine neighbourhoods using lem-weil-pbc-affine-opens-basis.
Their coordinate rings are finitely generated by lem-weil-pbc-lft-affine-pairs. Restrict
both frames. The change of basis and its inverse give matrices G and H with GH = HG = I.
Linearity of the symmetric-algebra generator map gives the same substitution on coordinates,
as in proposition-purity-vector-bundles. No overlap itself needs to be affine.
7. On the empty scheme take the empty cover. At rank zero the symmetric algebra of the
zero module is the base ring; its structural inclusion and augmentation are identities.
Relative-Spec restriction compatibility glues these identifications. The projection is
therefore the canonical rank-zero isomorphism, inverse to its zero section. Empty sums
and empty matrices give all the formulas also in rank zero. -/
theorem finite_type_frames (k : Type u) [Field k] (S : Scheme.{u})
    (f : S ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    ∃ (hS : IsNoetherian S),
      IsNoetherian (scheme S d F) ∧
      IsAffineHom (π S d F) ∧ QuasiCompact (π S d F) ∧ IsSeparated (π S d F) ∧
      LocallyOfFiniteType (π S d F) ∧ SmoothOfRelativeDimension d (π S d F) ∧
      (d = 0 → ∃ e : scheme S d F ≅ S, e.hom = π S d F ∧ e.inv = zero S d F) ∧
      ∃ (n : ℕ) (U : Fin n → S.affineOpens)
        (e : ∀ i : Fin n, Trivialization S d F (U i).1),
        (⨆ i : Fin n, (U i).1) = ⊤ ∧
        (IsEmpty S → n = 0) ∧
        (⨆ i : Fin n, (π S d F) ⁻¹ᵁ (U i).1) = ⊤ ∧
        (∀ i : Fin n,
          ((Scheme.ΓSpecIso (.of k)).inv ≫ ((U i).1.ι ≫ f).appTop).hom.FiniteType ∧
          IsAffine (((π S d F) ⁻¹ᵁ (U i).1).toScheme) ∧
          IsSeparated (((π S d F) ⁻¹ᵁ (U i).1).ι ≫ π S d F ≫ f) ∧
          LocallyOfFiniteType (((π S d F) ⁻¹ᵁ (U i).1).ι ≫ π S d F ≫ f) ∧
          QuasiCompact (((π S d F) ⁻¹ᵁ (U i).1).ι ≫ π S d F ≫ f) ∧
          IsIso (trivializationMap S d F (U i).1 (e i)) ∧
          (trivializationMap S d F (U i).1 (e i) ≫
            AffineSpace (ULift.{u} (Fin d)) (U i).1.toScheme ↘ (U i).1.toScheme =
              (π S d F) ∣_ (U i).1) ∧
          (zeroRestricted S d F (U i).1 ≫ trivializationMap S d F (U i).1 (e i) =
            AffineSpace.zeroSection (ULift.{u} (Fin d)) (U i).1.toScheme) ∧
          ∃ φ : ((π S d F) ⁻¹ᵁ (U i).1).toScheme ≅
              Spec (.of (MvPolynomial (ULift.{u} (Fin d)) Γ((U i).1.toScheme, ⊤))),
            φ.hom = trivializationMap S d F (U i).1 (e i) ≫
              (AffineSpace.isoOfIsAffine (ULift.{u} (Fin d)) (U i).1.toScheme).hom) ∧
        (∀ (i j : Fin n) (x : S), x ∈ (U i).1 ⊓ (U j).1 →
          ∃ (T : S.affineOpens) (hi : T.1 ≤ (U i).1) (hj : T.1 ≤ (U j).1),
            x ∈ T.1 ∧
            ((Scheme.ΓSpecIso (.of k)).inv ≫ (T.1.ι ≫ f).appTop).hom.FiniteType ∧
            ∃ ei ej : Trivialization S d F T.1,
              (∀ a : Fin d, frameSection S d F T.1 ei a =
                F.presheaf.map (homOfLE hi).op (frameSection S d F (U i).1 (e i) a)) ∧
              (∀ a : Fin d, frameSection S d F T.1 ej a =
                F.presheaf.map (homOfLE hj).op (frameSection S d F (U j).1 (e j) a)) ∧
              ∃ G H : Matrix (Fin d) (Fin d) (S.presheaf.obj (op T.1)),
                G * H = 1 ∧ H * G = 1 ∧
                (∀ b : Fin d, frameSection S d F T.1 ej b =
                  ∑ a : Fin d, G a b • frameSection S d F T.1 ei a) ∧
                (∀ b : Fin d, coordinate S d F T.1 ej b = ∑ a : Fin d,
                  ((π S d F) ∣_ T.1).appTop (T.1.topIso.inv (G a b)) *
                    coordinate S d F T.1 ei a)) := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have hS : IsNoetherian S := ⟨⟩
  refine ⟨hS, ?_⟩
  have : IsAffineHom (π S d F) := (over S d F).property
  have := bundle_smooth S d F
  have := SmoothOfRelativeDimension.smooth (n := d) (f := π S d F)
  have := LocallyOfFiniteType.isLocallyNoetherian (π S d F)
  have := QuasiCompact.compactSpace_of_compactSpace (π S d F)
  refine ⟨⟨⟩, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ?_, ?_⟩
  · intro hd
    subst d
    have := bundle_zero_isIso S F
    refine ⟨asIso (π S 0 F), rfl, ?_⟩
    apply (cancel_mono (π S 0 F)).mp
    simp only [asIso_inv, IsIso.inv_hom_id, (zero_spec S 0 F).1]
  · obtain ⟨n, U, e, hU, he⟩ := finite_affine_frames S d F
    refine ⟨n, U, e, hU, he, (π S d F).iSup_preimage_eq_top hU, ?_, ?_⟩
    · intro i
      have := (U i).2
      obtain ⟨ht, hp, hz⟩ := trivializationMap_spec S d F (U i).1 (e i)
      have : IsAffine (((π S d F) ⁻¹ᵁ (U i).1).toScheme) :=
        IsAffine.of_isIso (trivializationMap S d F (U i).1 (e i))
      refine ⟨affine_finiteType k _, inferInstance, inferInstance, inferInstance,
        inferInstance, ht, hp, hz, ?_⟩
      exact ⟨(asIso (trivializationMap S d F (U i).1 (e i))).trans
        (AffineSpace.isoOfIsAffine (ULift.{u} (Fin d)) (U i).1.toScheme), rfl⟩
    · intro i j x hx
      obtain ⟨T, hT, hxT, hTU⟩ :=
        Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hx
      let hi : T ≤ (U i).1 := hTU.trans inf_le_left
      let hj : T ≤ (U j).1 := hTU.trans inf_le_right
      have : IsAffine (Scheme.Opens.toScheme T) := hT
      refine ⟨⟨T, hT⟩, hi, hj, hxT, affine_finiteType k _,
        restrictFrame S d F hi (e i), restrictFrame S d F hj (e j),
        fun a ↦ restrictFrame_section S d F hi (e i) a,
        fun a ↦ restrictFrame_section S d F hj (e j) a, ?_⟩
      exact transition_spec S d F T _ _

end AlgebraicGeometry.VectorBundleZeroSection

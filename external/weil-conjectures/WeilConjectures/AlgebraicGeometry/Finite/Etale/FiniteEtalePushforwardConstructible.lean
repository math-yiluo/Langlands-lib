/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.Sites.EtaleQcqsCofinalFiniteCoverings
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.DirectImageSplitCoverProduct
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSurjectivePullback

/-!
# Finite etale pushforward preserves constructibility of module sheaves

Source: Stacks Project, Etale Cohomology, Tag 095H, lemma-pushforward-constructible,
module clause for finite coefficient rings
(blueprint: lem-weil-pbc-finite-etale-pushforward-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem constructible_product
    {X : Scheme.{u}} {J : Type u} [Finite J]
    {Λ : Type (u + 1)} [CommRing Λ]
    (F : J → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ j, IsConstructibleSheaf (F j)] :
    IsConstructibleSheaf (CategoryTheory.Limits.piObj F) :=
  open CategoryTheory.Limits in by
  let : Zero (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := HasZeroObject.zero' _
  let P : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun G ↦ IsConstructibleSheaf G
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    have : IsConstructibleSheaf _ := h
    exact IsConstructibleSheaf.of_iso e⟩
  have : P.ContainsZero :=
    ⟨⟨0, isZero_zero _, IsConstructibleSheaf.of_isZero (isZero_zero _)⟩⟩
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨G, hG⟩
    have : IsConstructibleSheaf (G.obj ⟨.left⟩) := hG _
    have : IsConstructibleSheaf (G.obj ⟨.right⟩) := hG _
    have := IsConstructibleSheaf.biprod (G.obj ⟨.left⟩) (G.obj ⟨.right⟩)
    exact IsConstructibleSheaf.of_iso ((biprod.isoProd _ _) ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair G)).symm))
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product fun j ↦ (inferInstance : IsConstructibleSheaf (F j))

private theorem constructible_lowerStar_split
    {X Y : Scheme.{u}} {J : Type u} [Finite J]
    {Λ : Type (u + 1)} [CommRing Λ]
    (f : Y ⟶ X) (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ Y)
    (e : ∀ j, V j ≅ X) (he : ∀ j, (e j).hom = i j ≫ f)
    (hc : CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk Y i))
    (hi : ∀ j, IsOpenImmersion (i j) ∧ IsClosedImmersion (i j))
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    IsConstructibleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) :=
  open CategoryTheory.Limits in by
  let t := fun j ↦ (e j).inv
  have hinv₁ (j : J) : t j ≫ i j ≫ f = 𝟙 X := by
    rw [← he j]
    exact (e j).inv_hom_id
  have hinv₂ (j : J) : i j ≫ f ≫ t j = 𝟙 (V j) := by
    rw [← Category.assoc, ← he j]
    exact (e j).hom_inv_id
  obtain ⟨q, -⟩ := directImage_splitCover_product f V i t hc hinv₁ hinv₂
    (fun j ↦ (hi j).1) (fun j ↦ (hi j).2) F
  let (j : J) : IsOpenImmersion (i j) := (hi j).1
  let s := fun j ↦ t j ≫ i j
  let R := fun j ↦
    (Etale.localizationRestriction (ModuleCat.{u + 1} Λ) (s j) inferInstance).obj F
  have hR (j : J) : IsConstructibleSheaf (R j) := by
    have := IsConstructibleSheaf.upperStar (s j) F
    exact IsConstructibleSheaf.of_iso
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ)
        (s j) inferInstance).app F)
  let := hR
  have := constructible_product R
  exact IsConstructibleSheaf.of_iso q.symm

private theorem constructible_of_finite_affine_open_cover
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {J : Type u} [Finite J] (W : J → Scheme.{u}) [∀ j, IsAffine (W j)]
    (i : ∀ j, W j ⟶ X) [∀ j, IsOpenImmersion (i j)]
    (hcover : ∀ x : X, ∃ j, ∃ y : W j, i j y = x)
    {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ j, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (i j)).obj F)) :
    IsConstructibleSheaf F := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let e := (Fintype.equivFin J).symm
  let O : Fin (Fintype.card J) → X.Opens := fun a ↦ (i (e a)).opensRange
  have hO (a) : IsAffineOpen (O a) := by
    change IsAffine (O a).toScheme
    exact IsAffine.of_isIso (i (e a)).isoOpensRange.inv
  have hFO (a) : IsConstructibleSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (O a).ι).obj F) := by
    have := hF (e a)
    have := IsConstructibleSheaf.upperStar (i (e a)).isoOpensRange.inv
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (i (e a))).obj F)
    exact IsConstructibleSheaf.of_iso
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) (i (e a)).isoOpensRange.inv).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (i (e a))).obj F))
      (((Etale.upperStarComp (ModuleCat.{u + 1} Λ)
        (i (e a)).isoOpensRange.inv (i (e a))).app F).symm ≪≫
        eqToIso (by rw [Hom.isoOpensRange_inv_comp]))
  choose T hT using fun a ↦ (hFO a).exists_stratification
  obtain ⟨S, _, hS⟩ := exists_global_stratification_factoring_local
    (Fintype.card J) O hO (by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨j, y, rfl⟩ := hcover x
      refine Set.mem_iUnion.mpr ⟨e.symm j, ?_⟩
      change i j y ∈ Set.range (i (e (e.symm j)))
      rw [e.apply_symm_apply]
      exact ⟨y, rfl⟩)
    T (fun a ↦ (T a).isConstructible_stratum)
  refine ⟨S, fun k ↦ ?_⟩
  obtain ⟨a, b, q, hq⟩ := hS k
  have := hT a b
  have := IsFiniteLocallyConstantSheaf.upperStar q
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((T a).immersion b)).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (O a).ι).obj F))
  exact IsFiniteLocallyConstantSheaf.of_iso
    (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((T a).immersion b)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (O a).ι).obj F)))
    (((Etale.upperStar (ModuleCat.{u + 1} Λ) q).mapIso
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) ((T a).immersion b) (O a).ι).app F).symm) ≪≫
      ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) q
        ((T a).immersion b ≫ (O a).ι)).app F).symm ≪≫
      eqToIso (by rw [hq]))

/-- Direct image along a finite etale morphism of qcqs schemes preserves the finite
constructible-stratification predicate for sheaves over a finite commutative ring.

Source: Stacks Project, Tag 095H, lemma-pushforward-constructible, module clause
(blueprint: lem-weil-pbc-finite-etale-pushforward-constructible).

Proof:
1. By lem-weil-pbc-constructible-qcqs-affine-local, work on an affine open A of U.
   Use lem-weil-pbc-etale-inverse-image-restriction and
   lemma-weil-pbc-etale-pullback-forget-modules to identify restriction with inverse
   image. Naturality for multiplication by every scalar makes these identifications
   module-linear; sections of the constant ring are locally constant scalars.
2. Apply lem-weil-pbc-finite-etale-etale-local-split at each point of A and pull the
   splitting back to A. By lem-weil-pbc-etale-qcqs-cofinal-finite-coverings choose a
   finite affine etale cover B_b of A subordinate to these neighbourhoods. Base change
   preserves etaleness and each splitting. Form B as their finite disjoint union using
   lem-weil-pbc-scheme-coproduct-family. Its map to A is surjective and etale by
   lem-weil-pbc-etale-local-on-source. Each component is affine and hence qcqs by
   lem-weil-pbc-affine-scheme-qcqs; intersections are a component or empty, so B is
   qcqs by lem-weil-pbc-quasi-separated-affine-cover-criterion. Sheet numbers may vary.
3. On B_b, evaluate direct image on an etale W: the fibre products W ×_U V and
   W ×_{B_b} (B_b ×_U V) are canonically isomorphic, naturally in W and compatibly
   with scalars. Thus restriction commutes with direct image. The splitting gives
   a finite product of restrictions of G by lem-weil-pbc-direct-image-split-cover-product.
   The sheet composites are etale by lem-weil-pbc-etale-scheme-base-change and
   definition-torsion-sheaves--3. Each factor is constructible by
   prop-constructible-pullback and lem-weil-pbc-constructible-etale-module-sheaf-comparison.
4. A finite product is constructible by induction using clause (2) of
   thm-constructible-serre. The empty product is the zero module sheaf with finite
   constant value zero. The induction step uses the split exact sequence
   0 → P → P × H → H → 0. Transport the finite-stratum witnesses along the module
   isomorphisms in step 3.
5. The affine-local criterion makes the pullback to B constructible. Descend along
   B → A using lem-weil-pbc-etale-constructible-surjective-pullback, since B and A
   are qcqs. Apply the affine-local criterion on U to finish with precisely the
   global finite constructible-stratification predicate. -/
theorem isConstructibleEtaleModuleSheaf_lowerStar_of_finite_etale
    {V U : Scheme.{u}} [CompactSpace V] [QuasiSeparatedSpace V]
    [CompactSpace U] [QuasiSeparatedSpace U] (h : V ⟶ U) [IsFinite h] [Etale h]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleEtaleModuleSheaf G) :
    IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) h).obj G) := by
  classical
  let : IsConstructibleSheaf G := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mp hG
  let F := (Etale.lowerStar (ModuleCat.{u + 1} Λ) h).obj G
  choose W g a hg ha J C i hJ hc hi e he using
    fun x : U ↦ finite_etale_etale_local_split h x
  let (x : U) : Etale (g x) := hg x
  let (x : U) : Finite (J x) := hJ x
  have hlocal (x : U) :
      IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (g x)).obj F) := by
    let H := (Etale.upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.fst h (g x))).obj G
    have : IsConstructibleSheaf H := IsConstructibleSheaf.upperStar _ G
    have hsplit := constructible_lowerStar_split (Limits.pullback.snd h (g x))
      (C x) (i x) (e x) (he x) (hc x).some (hi x) H
    have := Etale.isIso_baseChangeMap_flip_of_isPullback (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback h (g x)).flip
    have : IsConstructibleSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (Limits.pullback.fst h (g x)) ⋙
          Etale.lowerStar (ModuleCat.{u + 1} Λ) (Limits.pullback.snd h (g x))).obj G) := hsplit
    exact IsConstructibleSheaf.of_iso
      (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback h (g x)).toCommSq).app G)).symm
  let T : U → U.Etale := fun x ↦ Scheme.Etale.mk (g x)
  let t : ∀ x, T x ⟶ Scheme.Etale.mk (𝟙 U) :=
    fun x ↦ MorphismProperty.Over.homMk (g x)
  have ht : Sieve.ofArrows T t ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U)) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff t).mpr
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, a x, ha x⟩
  obtain ⟨B, hB, b, D, v, hD, hv, hcov, _⟩ :=
    etale_qcqs_cofinal_finite_affine_coverings.{u, u, u} T t ht
  let : Finite B := hB
  let d : B → Scheme.{u} := fun j ↦ (D j).left
  let (j : B) : IsAffine (d j) := hD j
  choose k _ using hv
  have hfactor (j : B) : (k j).left ≫ g (b j) = (D j).hom :=
    MorphismProperty.Over.w (k j)
  have hDlocal (j : B) :
      IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D j).hom).obj F) := by
    have := hlocal (b j)
    have := IsConstructibleSheaf.upperStar (k j).left
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (g (b j))).obj F)
    exact IsConstructibleSheaf.of_iso
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) (k j).left).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (g (b j))).obj F))
      (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (k j).left (g (b j))).app F).symm ≪≫
        eqToIso (by rw [hfactor j]))
  let q : (∐ d) ⟶ U := Limits.Sigma.desc (fun j ↦ (D j).hom)
  have hvleft (j : B) : (v j).left = (D j).hom := by
    have hw := MorphismProperty.Over.w (v j)
    change (v j).left ≫ 𝟙 U = (D j).hom at hw
    change (v j).left = (D j).hom
    exact (Category.comp_id (v j).left).symm.trans hw
  have hsurj : (⋃ j : B, Set.range (α := U) (D j).hom) = Set.univ := by
    have hh := (Scheme.ofArrows_mem_smallEtaleTopology_iff v).mp hcov
    change (⋃ j : B, Set.range (α := U) (v j).left) = Set.univ at hh
    convert hh using 1
    ext x
    constructor <;> intro hx
    · rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      rcases hj with ⟨y, hy⟩
      exact ⟨y, (hvleft j).symm ▸ hy⟩
    · rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      rcases hj with ⟨y, hy⟩
      exact ⟨y, (hvleft j) ▸ hy⟩
  let : Surjective q := Surjective.sigmaDesc_of_union_range_eq_univ hsurj
  have hq : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj F) := by
    apply constructible_of_finite_affine_open_cover d (Limits.Sigma.ι d)
    · intro y
      obtain ⟨⟨j, z⟩, rfl⟩ := (sigmaMk d).surjective y
      exact ⟨j, z, sigmaMk_mk d j z |>.symm⟩
    · intro j
      have hcomp : Limits.Sigma.ι d j ≫ q = (D j).hom := by simp [q]
      have : IsConstructibleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (Limits.Sigma.ι d j ≫ q)).obj F) := by
        rw [hcomp]
        exact hDlocal j
      exact IsConstructibleSheaf.of_iso
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (Limits.Sigma.ι d j) q).app F)
  apply (isConstructibleEtaleModuleSheaf_iff_surjective_pullback q F).mpr
  exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr hq

end AlgebraicGeometry.Scheme

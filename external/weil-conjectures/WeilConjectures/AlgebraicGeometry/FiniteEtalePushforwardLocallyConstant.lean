/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.DirectImageSplitCoverProduct
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.ConstructibleSheaf.Biproduct
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.SixFunctors.BaseChange.Etale
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite etale pushforward of finite locally constant module sheaves

Source: Stacks Project, Tag 095B, Lemma 59.64.3, module clause
(blueprint: lem-weil-pbc-etale-finite-pushforward-locally-constant).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem finiteLocallyConstant_product
    {X : Scheme.{u}} {J : Type u} [Finite J]
    {Λ : Type (u + 1)} [CommRing Λ]
    (F : J → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ j, IsFiniteLocallyConstantSheaf (F j)] :
    IsFiniteLocallyConstantSheaf (CategoryTheory.Limits.piObj F) :=
  open CategoryTheory.Limits in
  by
  let : Zero (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := HasZeroObject.zero' _
  let P : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun G ↦ IsFiniteLocallyConstantSheaf G
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    have : IsFiniteLocallyConstantSheaf _ := h
    exact IsFiniteLocallyConstantSheaf.of_iso e⟩
  have : P.ContainsZero :=
    ⟨⟨0, isZero_zero _, IsFiniteLocallyConstantSheaf.of_isZero (isZero_zero _)⟩⟩
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨G, hG⟩
    have : IsFiniteLocallyConstantSheaf (G.obj ⟨.left⟩) := hG _
    have : IsFiniteLocallyConstantSheaf (G.obj ⟨.right⟩) := hG _
    have := IsFiniteLocallyConstantSheaf.biprod (G.obj ⟨.left⟩) (G.obj ⟨.right⟩)
    exact IsFiniteLocallyConstantSheaf.of_iso ((biprod.isoProd _ _) ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair G)).symm))
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product fun j ↦ (inferInstance : IsFiniteLocallyConstantSheaf (F j))

private theorem finiteLocallyConstant_lowerStar_split
    {X Y : Scheme.{u}} {J : Type u} [Finite J]
    {Λ : Type (u + 1)} [CommRing Λ]
    (f : Y ⟶ X) (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ Y)
    (e : ∀ j, V j ≅ X) (he : ∀ j, (e j).hom = i j ≫ f)
    (hc : CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk Y i))
    (hi : ∀ j, IsOpenImmersion (i j) ∧ IsClosedImmersion (i j))
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) :=
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
  have hR (j : J) : IsFiniteLocallyConstantSheaf (R j) := by
    have := IsFiniteLocallyConstantSheaf.upperStar (s j) F
    exact IsFiniteLocallyConstantSheaf.of_iso
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ)
        (s j) inferInstance).app F)
  let := hR
  have := finiteLocallyConstant_product R
  exact IsFiniteLocallyConstantSheaf.of_iso q.symm

/-- Direct image along a finite etale morphism preserves finite locally constant sheaves
of modules over a finite commutative ring. The finite-local-constancy predicate agrees
with local trivializations by finite modules by `finite_locally_constant_module_values_iff`.

Proof, following Stacks 095B and the node's six steps:
1. Finite local constancy is invariant under isomorphism and local for etale coverings:
   transport trivializations through an isomorphism, or compose the trivializing covers
   with the given cover (`lem-weil-pbc-finite-locally-constant-module-values`).
2. Etale restriction preserves finite local constancy: inverse image preserves local
   constancy (`lemma-constructible-pullback-locally-constant`), and its geometric stalk is
   the original stalk (`lem-weil-pbc-inverse-image-stalk-germ`). Restriction agrees with
   inverse image (`lem-weil-pbc-etale-inverse-image-restriction`); naturality at scalar
   multiplication makes this identification module-linear.
3. Direct image commutes with etale localization. On each test object, cartesian-square
   pasting (`lem-weil-pbc-cartesian-square-pasting`) identifies the two iterated fibre
   products naturally, hence gives an isomorphism of module sheaves.
4. A finite etale morphism splits over an etale cover into finitely many sheets, each
   isomorphic to the base (`lem-weil-pbc-finite-etale-etale-local-split`, Stacks 04HN).
5. On that cover, direct image is the product of restrictions to the sheets
   (`lem-weil-pbc-direct-image-split-cover-product`). Each restriction is finite locally
   constant by step 2. A finite nonempty product is a finite biproduct, hence finite
   locally constant (`lemma-constructible-flc-biproduct`). For no sheets it is the zero
   sheaf, trivialized by the identity cover with the finite zero module.
6. Apply step 3 and isomorphism invariance to obtain finite local constancy on the cover,
   then descend by the locality in step 1.

Source: Stacks Project, Tag 095B, Lemma 59.64.3, module clause and proof
(blueprint: lem-weil-pbc-etale-finite-pushforward-locally-constant). -/
theorem finiteLocallyConstant_lowerStar_of_finite_etale
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] :
    IsFiniteLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) :=
  open CategoryTheory.Limits in by
  classical
  choose U g a hg ha J V i hJ hc hi e he using
    fun x : X ↦ finite_etale_etale_local_split f x
  let (x : X) : Etale (g x) := hg x
  let (x : X) : Finite (J x) := hJ x
  let 𝒰 : Cover.{u} etalePrecoverage X :=
    Cover.mkOfCovers X U g (fun x ↦ ⟨x, a x, ha x⟩) hg
  let G := (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  have hG (x : X) :
      IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (g x)).obj G) := by
    let H := (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f (g x))).obj F
    have : IsFiniteLocallyConstantSheaf H := IsFiniteLocallyConstantSheaf.upperStar _ F
    have hsplit := finiteLocallyConstant_lowerStar_split (pullback.snd f (g x))
      (V x) (i x) (e x) (he x) (hc x).some (hi x) H
    have := Etale.isIso_baseChangeMap_flip_of_isPullback (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback f (g x)).flip
    have : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f (g x)) ⋙
          Etale.lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd f (g x))).obj F) := hsplit
    exact IsFiniteLocallyConstantSheaf.of_iso
      (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback f (g x)).toCommSq).app F)).symm
  have hlocal (x : 𝒰.I₀) :
      IsLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f x)).obj G) :=
    (hG x).toIsLocallyConstantSheaf
  have hfinite (x : 𝒰.I₀) :
      IsFiniteSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f x)).obj G) :=
    (hG x).toIsFiniteSheaf
  refine { toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_cover 𝒰 G
           toIsFiniteSheaf := ?_ }
  constructor
  intro Ω _ _ s
  obtain ⟨x, b, hb⟩ := 𝒰.exists_eq (s default)
  have : Etale (𝒰.f x) := 𝒰.map_prop x
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f x) s b hb
  have hfin := IsFiniteSheaf.isFinitelyGenerated_sheafFiber
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f x)).obj G) Ω t
  have hstalk := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (𝒰.f x) t).app G
  rw [ht] at hstalk
  exact hfin.of_iso hstalk

end AlgebraicGeometry.Scheme

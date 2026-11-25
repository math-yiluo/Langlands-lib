/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Tensor products of quasi-coherent modules on affine opens

Source: Stacks Project, Schemes, Lemma 01I8 and Section 01LA; Modules, Lemma 01CE
(blueprint: lem-weil-pbc-quasi-coherent-tensor-product-affine-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules


private instance ringIsoInvPair {R S : CommRingCat.{u}} (e : R ≅ S) :
    RingHomInvPair e.inv.hom e.hom.hom :=
  RingHomInvPair.of_ringEquiv e.symm.commRingCatIsoToRingEquiv

private instance ringIsoHomPair {R S : CommRingCat.{u}} (e : R ≅ S) :
    RingHomInvPair e.hom.hom e.inv.hom :=
  RingHomInvPair.of_ringEquiv e.commRingCatIsoToRingEquiv

private noncomputable def tildeSectionsEquiv (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    M ≃ₛₗ[(Scheme.ΓSpecIso R).inv.hom]
      Γ(tilde M, ⊤) :=
  { toFun := fun m ↦ tilde.toOpen M ⊤ m
    invFun := fun m ↦ (tilde.isoTop M).inv m
    left_inv := (tilde.isoTop M).toLinearEquiv.left_inv
    right_inv := (tilde.isoTop M).toLinearEquiv.right_inv
    map_add' := (tilde.toOpen M ⊤).hom.map_add
    map_smul' r m := by
      have h : (tilde.toOpen M ⊤) (r • m) = r • (tilde.toOpen M ⊤ m : Γ(tilde M, ⊤)) :=
        (tilde.toOpen M ⊤).hom.map_smul r m
      exact h.trans (smul_top_eq (tilde M) r (tilde.toOpen M ⊤ m)) }


set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
private theorem affine_tensor (R : CommRingCat.{u}) (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (F ⊗ G).IsQuasicoherent ∧ Function.Bijective (tensorSectionsMap F G ⊤) := by
  let M := (moduleSpecΓFunctor (R := R)).obj F
  let N := (moduleSpecΓFunctor (R := R)).obj G
  have : IsIso F.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent F
  have : IsIso G.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent G
  let eF : tilde M ≅ F := asIso F.fromTildeΓ
  let eG : tilde N ≅ G := asIso G.fromTildeΓ
  obtain ⟨β, hβ, hb, α, hα, hi, hu⟩ := affine_tilde_tensor R M N
  have := hi
  have hq : (tilde M ⊗ tilde N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (asIso α) inferInstance
  have hq' : (F ⊗ G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (show tilde M ⊗ tilde N ≅ F ⊗ G from eF ⊗ᵢ eG) hq
  refine ⟨hq', ?_⟩
  let t := TensorProduct.congr (tildeSectionsEquiv R M) (tildeSectionsEquiv R N)
  have ht : ∀ z, tensorSectionsMap (tilde M) (tilde N) ⊤ (t z) = β z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m n => exact (hβ m n).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  have hb' : Function.Bijective (tensorSectionsMap (tilde M) (tilde N) ⊤) := by
    have heq : (tensorSectionsMap (tilde M) (tilde N) ⊤) ∘ t = β := funext ht
    exact (Function.Bijective.of_comp_iff _ t.bijective).mp (heq ▸ hb)
  let f := appLinearEquivOfIso eF ⊤
  let g := appLinearEquivOfIso eG ⊤
  let e : tilde M ⊗ tilde N ≅ F ⊗ G := eF ⊗ᵢ eG
  have he : Function.Bijective (e.hom.app ⊤) :=
    (appLinearEquivOfIso e ⊤).bijective
  have hn : (tensorSectionsMap F G ⊤) ∘ TensorProduct.congr f g =
      (e.hom.app ⊤) ∘ tensorSectionsMap (tilde M) (tilde N) ⊤ := by
    apply funext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m n => exact (tensorHom_app_tmulSection eF.hom eG.hom m n).symm
    | add x y hx hy =>
      change tensorSectionsMap F G ⊤ ((TensorProduct.congr f g) (x + y)) = (e.hom.app ⊤)
        (tensorSectionsMap (tilde M) (tilde N) ⊤ (x + y))
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy
  exact (Function.Bijective.of_comp_iff _ (TensorProduct.congr f g).bijective).mp
    (hn ▸ he.comp hb')


private noncomputable def restrictionSectionsEquiv {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F : X.Modules) (V : Y.Opens) :
    Γ(F.restrict j, V) ≃ₛₗ[(j.appIso V).inv.hom] Γ(F, j ''ᵁ V) :=
  { (F.restrictAppIso j V).addCommGroupIsoToAddEquiv with
    map_smul' r s := smul_restrictAppIso_hom_apply j F V r s }

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
private theorem restriction_tensor_bijective {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) (V : Y.Opens)
    (h : Function.Bijective (tensorSectionsMap (F.restrict j) (G.restrict j) V)) :
    Function.Bijective (tensorSectionsMap F G (j ''ᵁ V)) := by
  obtain ⟨e, he⟩ := exists_restriction_tensor_comparison j F G
  let t := TensorProduct.congr (restrictionSectionsEquiv j F V)
    (restrictionSectionsEquiv j G V)
  let c := ((F ⊗ G).restrictAppIso j V).addCommGroupIsoToAddEquiv
  let d := appLinearEquivOfIso e.symm V
  have hn : ∀ z, tensorSectionsMap F G (j ''ᵁ V) (t z) =
      c (d (tensorSectionsMap (F.restrict j) (G.restrict j) V z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s t => exact (he V s t).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  have hh : Function.Bijective ((tensorSectionsMap F G (j ''ᵁ V)) ∘ t) := by
    have heq : (tensorSectionsMap F G (j ''ᵁ V)) ∘ t =
        c ∘ d ∘ tensorSectionsMap (F.restrict j) (G.restrict j) V := funext hn
    rw [heq]
    exact c.bijective.comp (d.bijective.comp h)
  exact (Function.Bijective.of_comp_iff _ t.bijective).mp hh

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
private theorem affine_tensor_restriction {X : Scheme.{u}} (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) :
    ((F ⊗ G).restrict hU.fromSpec).IsQuasicoherent ∧
      Function.Bijective (tensorSectionsMap F G U) := by
  have : (F.restrict hU.fromSpec).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor hU.fromSpec F
  have : (G.restrict hU.fromSpec).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor hU.fromSpec G
  obtain ⟨hq, hb⟩ := affine_tensor Γ(X, U) (F.restrict hU.fromSpec)
    (G.restrict hU.fromSpec)
  obtain ⟨e, he⟩ := exists_restriction_tensor_comparison hU.fromSpec F G
  refine ⟨(SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
    e.symm hq, ?_⟩
  have hi : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have hh := restriction_tensor_bijective hU.fromSpec F G ⊤ hb
  rw [hi] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem presentation_on_affine {X : Scheme.{u}} (H : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U)
    (h : (H.restrict hU.fromSpec).IsQuasicoherent) :
    Nonempty (H.restrict U.ι).Presentation := by
  let N := H.restrict hU.fromSpec
  have : N.IsQuasicoherent := h
  have : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  let M := (moduleSpecΓFunctor (R := Γ(X, U))).obj N
  let P := presentationTilde M Set.univ (by simp) _ (Submodule.span_eq _)
  let Q := SheafOfModules.Presentation.ofIsIso N.fromTildeΓ P
  have hp : Nonempty (H.restrict hU.fromSpec.opensRange.ι).Presentation :=
    ⟨presentationRestrictOpensRange hU.fromSpec Q⟩
  rw [hU.opensRange_fromSpec] at hp
  exact hp

/-- The tensor product of quasi-coherent modules is quasi-coherent, and its canonical
section map on every affine open is bijective. Source: Stacks Project, Schemes, Lemma 01I8(1)
and Section 01LA(1),(2),(8); Modules, Lemma 01CE(3)
(blueprint: lem-weil-pbc-quasi-coherent-tensor-product-affine-sections).

Proof:
1. Fix an affine open `U`, put `R = Γ(X, U)`, and use its canonical affine chart.
   Restriction preserves quasi-coherence. The affine tilde/global-sections equivalence
   identifies the restrictions of `F` and `G` with the tilde sheaves of their sections
   (`lem-weil-pbc-module-restriction-open-immersion-colimits`,
   `lem-weil-pbc-affine-tilde-gamma-adjunction`, `lem-weil-pbc-spec-module-tilde-sections`).
2. The sectionwise tensor presheaf restricts to the tensor presheaf on `U`. For the open
   immersion `j : U ⟶ X`, its tensor presheaf `P`, and any module sheaf `H` on `U`, identify
   Hom((Pᵟ)|U, H) with Hom(Pᵟ, j_*H), then Hom(P, j_*H), then Hom(P|U, H).
   Here `Pᵟ` denotes sheafification. The outer identifications use the restriction/direct-
   image adjunction (`lem-weil-pbc-module-restriction-open-immersion-colimits`); the middle
   uses sheafification (`def-weil-presheaf-modules-sheafification`). Direct image is a sheaf
   (`lem-weil-pbc-site-continuous-pushforward-sheaf`, `def-weil-pbc-direct-image`). Thus
   restriction commutes with sheafification and with the sheaf tensor product
   (`def-pur-sheaf-tensor-product`). Apply `lem-weil-pbc-affine-tilde-tensor` to identify this
   restriction with the tilde sheaf of `Γ(F, U) ⊗[R] Γ(G, U)`. Track pure tensors through
   the comparison: the original sheafification component sends `s ⊗ t` to
   `tmulSection s t` (`tensorSectionsMap_tmul`), so its map on sections is exactly
   `tensorSectionsMap F G U` and is bijective.
3. Every point has an affine open neighbourhood (`def-pc-scheme`). Step 2 identifies the
   tensor product there with a tilde module. The affine-local criterion (`pqf-def-coherent`)
   gives quasi-coherence; Step 2 already gives the second clause for every affine open.
-/
theorem quasiCoherent_tensor_product_affine_sections {X : Scheme.{u}} (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (tensorObj F G).IsQuasicoherent ∧
      ∀ (U : X.Opens), IsAffineOpen U → Function.Bijective (tensorSectionsMap F G U) := by
  set_option backward.isDefEq.respectTransparency false in
    have hlocal (U : X.Opens) (hU : IsAffineOpen U) :=
      affine_tensor_restriction F G U hU
    refine ⟨?_, fun U hU ↦ (hlocal U hU).2⟩
    let V := fun i : X.affineCover.I₀ ↦ (X.affineCover.f i).opensRange
    have hV (i : X.affineCover.I₀) : IsAffineOpen (V i) :=
      isAffineOpen_opensRange (X.affineCover.f i)
    have hp (i : X.affineCover.I₀) : Nonempty ((tensorObj F G).restrict (V i).ι).Presentation :=
      presentation_on_affine (tensorObj F G) (V i) (hV i) (hlocal (V i) (hV i)).1
    have (i : X.affineCover.I₀) : ((tensorObj F G).over (V i)).IsQuasicoherent :=
      (presentationOverOfRestrict (V i) (hp i).some).isQuasicoherent
    exact SheafOfModules.IsQuasicoherent.of_coversTop (tensorObj F G) V
      ((Opens.coversTop_iff _ V).mpr X.affineCover.isOpenCover_opensRange)

end AlgebraicGeometry.Scheme.Modules

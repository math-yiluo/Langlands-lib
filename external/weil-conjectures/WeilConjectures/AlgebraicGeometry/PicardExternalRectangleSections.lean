/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardScalarAffineSectionsExact
public import WeilConjectures.AlgebraicGeometry.ExternalSectionsComponents
import WeilConjectures.AlgebraicGeometry.AffineRectangleProjectionSectionsTensor
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The canonical external section map on a rectangle

Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-rectangle-sections-bijective).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Pull a section back and restrict it to an open lying above its domain.
Source: Stacks Project, Tag 0096
(blueprint: lem-sc-picard-external-rectangle-sections-bijective). -/
def picardPullbackScalarSection
    (f : X ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (F : X.Modules)
    (U : X.Opens) (W : Y.Opens) (hWU : W ≤ a ⁻¹ᵁ U) :
    scalarObj f F (op U) →ₗ[k] scalarObj (a ≫ f) ((tensorPullback a).obj F) (op W) :=
  (scalarRestriction (a ≫ f) ((tensorPullback a).obj F)
    (homOfLE hWU).op).hom.comp (scalarUnitSection f a F U)

/-- Tensor the two projection pullbacks of sections, restricted to their rectangle.
Source: Stacks Project, Tag 0BED
(blueprint: lem-sc-picard-external-rectangle-sections-bijective). -/
def picardExternalRectangleBilinear
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (V : Y.Opens) (F : X.Modules) (G : Y.Modules) :
    scalarObj f F (op U) →ₗ[k] scalarObj g G (op V) →ₗ[k]
      scalarObj (pullback.fst f g ≫ f)
        (tensorObj ((tensorPullback (pullback.fst f g)).obj F)
          ((tensorPullback (pullback.snd f g)).obj G))
        (op (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) := by
  let W := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V
  let L := picardPullbackScalarSection f (pullback.fst f g) F U W inf_le_left
  let R := picardPullbackScalarSection g (pullback.snd f g) G V W inf_le_right
  exact LinearMap.mk₂ k (fun s t ↦ tmulSection (L s) (R t))
    (by intros; rw [map_add, add_tmulSection])
    (by
      intro r s t
      rw [LinearMap.map_smul]
      exact smul_tmulSection _ _ _)
    (by intros; rw [map_add, tmulSection_add])
    (by
      intro r s t
      rw [LinearMap.map_smul]
      change tmulSection (L s) ((scalarMap (pullback.snd f g ≫ g) W r) • _) = _
      rw [show scalarMap (pullback.snd f g ≫ g) W r =
        scalarMap (pullback.fst f g ≫ f) W r from
        congrArg (fun a ↦ scalarMap a W r) pullback.condition.symm]
      exact tmulSection_smul _ _ _)

/-- The explicit external product map from tensor products of scalar section modules.
Source: Stacks Project, Tag 0BED
(blueprint: lem-sc-picard-external-rectangle-sections-bijective). -/
def picardExternalRectangleSectionsMap
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (V : Y.Opens) (F : X.Modules) (G : Y.Modules) :
    (tensorRight ((picardScalarSectionsFunctor g V).obj G)).obj
        ((picardScalarSectionsFunctor f U).obj F) ⟶
      (picardScalarSectionsFunctor (pullback.fst f g ≫ f)
        (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)).obj
        (tensorObj ((tensorPullback (pullback.fst f g)).obj F)
          ((tensorPullback (pullback.snd f g)).obj G)) :=
  ModuleCat.ofHom
    (X := scalarObj f F (op U) ⊗[k] scalarObj g G (op V))
    (Y := scalarObj (pullback.fst f g ≫ f)
      (tensorObj ((tensorPullback (pullback.fst f g)).obj F)
        ((tensorPullback (pullback.snd f g)).obj G))
      (op (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)))
    (TensorProduct.lift (picardExternalRectangleBilinear f g U V F G))

/-- The canonical rectangle map commutes with coefficient morphisms on the first factor.
Source: Stacks Project, Tag 0BED
(blueprint: lem-sc-picard-external-rectangle-sections-bijective).

Proof: On pure tensors the left projection unit is natural in F, its restriction
commutes with the pulled-back morphism, and tensoring sections is natural. These
identities extend to the entire tensor product by linearity. -/
theorem picardExternalRectangleSectionsMap_naturality
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (V : Y.Opens) {F F' : X.Modules} (a : F ⟶ F') (G : Y.Modules) :
    (tensorRight ((picardScalarSectionsFunctor g V).obj G)).map
        ((picardScalarSectionsFunctor f U).map a) ≫
        picardExternalRectangleSectionsMap f g U V F' G =
      picardExternalRectangleSectionsMap f g U V F G ≫
        (picardScalarSectionsFunctor (pullback.fst f g ≫ f)
          (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)).map
          ((tensorPullback (pullback.fst f g)).map a ▷
            (tensorPullback (pullback.snd f g)).obj G) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s t
  change (TensorProduct.lift (picardExternalRectangleBilinear f g U V F' G))
      ((a.app U s) ⊗ₜ[k] t) =
    (((tensorPullback (pullback.fst f g)).map a) ▷
      (tensorPullback (pullback.snd f g)).obj G).app
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
      ((TensorProduct.lift (picardExternalRectangleBilinear f g U V F G)) (s ⊗ₜ[k] t))
  simp only [TensorProduct.lift.tmul]
  dsimp only [picardExternalRectangleBilinear, LinearMap.mk₂_apply]
  rw [whiskerRight_app_tmulSection]
  congr 1
  dsimp only [picardPullbackScalarSection, scalarUnitSection, scalarRestriction,
    LinearMap.comp_apply]
  have hn := (Classical.choose
    (exists_tensorPullbackAdjunction (pullback.fst f g))).unit_naturality a
  have hv := congrArg (fun q ↦ q.val.app (op U) s) hn
  have hr := ((tensorPullback (pullback.fst f g)).map a).val.naturality
    (homOfLE (inf_le_left :
      pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ U)).op
  have hr' := congrArg (fun q ↦ q
    (((Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).unit.app F)
      |>.val.app (op U) s)) hr
  exact (hr'.trans (congrArg (fun z ↦
    ((tensorPullback (pullback.fst f g)).obj F').presheaf.map
      (homOfLE (inf_le_left :
        pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ U)).op z)
      hv)).symm

/-- On an affine rectangle the canonical external section map is bijective.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; Schemes, Tags 01I4,
01JQ, 01IA; Modules, Tag 01BG.
(blueprint: lem-sc-picard-external-rectangle-sections-bijective).

Proof: Set A = Gamma(X,U), B = Gamma(Y,V), M = Gamma(F,U), N = Gamma(G,V).
The rectangle is affine, with ring C = A tensor_k B, by the affine fibre-product
formula applied to the open subschemes U and V. Affine pullback sections identify
the two projection-pullback section modules with M tensor_A C and N tensor_B C.
These pullbacks are quasi-coherent, so the affine tensor-sections comparison is
bijective. The algebraic identity (M tensor_A C) tensor_C (N tensor_B C)
is M tensor_k N: its inverse sends m tensor n to (m tensor 1) tensor (n tensor 1).
The balancing relations and tensor induction verify both inverse identities.
Compose this inverse with the affine pullback comparisons and the tensor-sections
map. Their pure-tensor formulas identify the composite with the displayed canonical
map, which therefore is bijective. Restrict scalars to k throughout. Empty opens
have zero coordinate rings and section modules, so the identities also prove the
claim for empty rectangles. Zero coefficients give zero on both sides. -/
theorem picardExternalRectangleSectionsMap_bijective
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (picardExternalRectangleSectionsMap f g U V F G) := by
  classical
  let W := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V
  let P := (tensorPullback (pullback.fst f g)).obj F
  let Q := (tensorPullback (pullback.snd f g)).obj G
  have hP : P.IsQuasicoherent := by
    let e := (nonempty_tensorPullbackAdjunction (pullback.fst f g)).some.leftAdjointUniq
      (pullbackPushforwardAdjunction (pullback.fst f g))
    exact (SheafOfModules.isQuasicoherent (Limits.pullback f g).ringCatSheaf).prop_of_iso
      (e.app F).symm (by infer_instance)
  have hQ : Q.IsQuasicoherent := by
    let e := (nonempty_tensorPullbackAdjunction (pullback.snd f g)).some.leftAdjointUniq
      (pullbackPushforwardAdjunction (pullback.snd f g))
    exact (SheafOfModules.isQuasicoherent (Limits.pullback f g).ringCatSheaf).prop_of_iso
      (e.app G).symm (by infer_instance)
  let := hP
  let := hQ
  have ht := (quasiCoherent_tensor_product_affine_sections P Q).2
    W (isAffineOpen_preimage_inf_preimage_pullback f g hU hV)
  obtain ⟨e, he⟩ := exists_affine_rectangle_projection_sections_tensor k X Y f g U V hU hV F G
  have hc (z : scalarObj f F (op U) ⊗[k] scalarObj g G (op V)) :
      tensorSectionsMap P Q W (e z) = picardExternalRectangleSectionsMap f g U V F G z := by
    induction z using TensorProduct.inductionOn with
    | tmul s t =>
      rw [he, tensorSectionsMap_tmul]
      rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have hc' : (tensorSectionsMap P Q W) ∘ e =
      picardExternalRectangleSectionsMap f g U V F G := funext hc
  rw [← hc']
  exact ht.comp e.bijective

end
end AlgebraicGeometry.Scheme.Modules

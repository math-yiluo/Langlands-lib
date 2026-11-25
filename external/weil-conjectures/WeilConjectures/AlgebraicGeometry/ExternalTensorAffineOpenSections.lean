/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.AffineRectangleProjectionSectionsTensor
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.IsTensorProduct
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # External tensor sections on one affine product open

Source: Stacks Project, Tag 0BED, varieties-lemma-kunneth, affine-open paragraph.
(blueprint: lem-sc-external-tensor-affine-open-sections).
-/

@[expose] public section

set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type w} [Field k] {X Y : Scheme.{w}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
variable (F : X.Modules) (G : Y.Modules) (A : X.Opens) (V : Y.Opens)

/-- The external product of two sections, on a specified open of the product.
Source: Stacks Project, Tag 0BED, maps preceding equation-kunneth-on-cech.
(blueprint: lem-sc-external-tensor-affine-open-sections). -/
def externalTensorOpenPureSection
    (J : ((pullback.snd f g) ⁻¹ᵁ V).toScheme.Opens)
    (hK : ((pullback.snd f g) ⁻¹ᵁ V).ι ''ᵁ J ≤ (pullback.fst f g) ⁻¹ᵁ A)
    (hKV : ((pullback.snd f g) ⁻¹ᵁ V).ι ''ᵁ J ≤ (pullback.snd f g) ⁻¹ᵁ V)
    (s : Γ(F, A)) (t : scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤)) :
    Γ((externalCupCoefficients f g F G).restrict
      ((pullback.snd f g) ⁻¹ᵁ V).ι, J) := by
  let W := (pullback.snd f g) ⁻¹ᵁ V
  let E := externalCupCoefficients f g F G
  let K : (Limits.pullback f g).Opens := W.ι ''ᵁ J
  let t' : Γ(G, V) := G.presheaf.map (eqToHom V.ι_image_top.symm).op
    ((G.restrictAppIso V.ι ⊤).hom t)
  let ηF := (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).unit.app F
  let ηG := (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app G
  let s' : Γ((tensorPullback (pullback.fst f g)).obj F, K) :=
    ((tensorPullback (pullback.fst f g)).obj F).presheaf.map (homOfLE hK).op
      (ηF.val.app (op A) s)
  let t'' : Γ((tensorPullback (pullback.snd f g)).obj G, K) :=
    ((tensorPullback (pullback.snd f g)).obj G).presheaf.map (homOfLE hKV).op
      (ηG.val.app (op V) t')
  exact (E.restrictAppIso W.ι J).inv (tmulSection s' t'')

set_option backward.isDefEq.respectTransparency.types false in
/-- The external tensor identity over a pushout of commutative rings. -/
private noncomputable def externalTensorAlgebraEquiv
    (R A B C M N : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.IsPushout R A B C]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] :
    (C ⊗[A] M) ⊗[C] (C ⊗[B] N) ≃ₗ[R] M ⊗[R] N := by
  let e₁ := (TensorProduct.comm C (C ⊗[A] M) (C ⊗[B] N)).restrictScalars R
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A C C (C ⊗[B] N) M
  let e₃ := TensorProduct.congr (Algebra.IsPushout.cancelBaseChange R A B C N)
    (LinearEquiv.refl A M)
  let e₄ := TensorProduct.comm A (A ⊗[R] N) M
  let e₅ := TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M N
  exact e₁ ≪≫ₗ e₂.restrictScalars R ≪≫ₗ e₃.restrictScalars R ≪≫ₗ
    e₄.restrictScalars R ≪≫ₗ e₅.restrictScalars R

set_option backward.isDefEq.respectTransparency.types false in
private theorem externalTensorAlgebraEquiv_tmul
    (R A B C M N : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.IsPushout R A B C]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] (m : M) (n : N) :
    externalTensorAlgebraEquiv R A B C M N ((1 ⊗ₜ[A] m) ⊗ₜ[C] (1 ⊗ₜ[B] n)) =
      m ⊗ₜ[R] n := by
  simp only [externalTensorAlgebraEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.congr_tmul, Algebra.IsPushout.cancelBaseChange_tmul, one_smul,
    LinearEquiv.refl_apply]

private def globalScalarSectionEquiv :
    (ModuleCat.restrictScalars (scalarMap f ⊤)).obj
      (F.presheafModuleCat.obj (op A)) ≃ₗ[k] scalarObj f F (op A) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r s := by
    change (X.presheaf.map (homOfLE (le_top (a := A))).op).hom (scalarMap f ⊤ r) •
      (show Γ(F, A) from s) =
      scalarMap f A r • (show Γ(F, A) from s)
    congr 1
    simp only [scalarMap, RingHom.comp_apply]
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl

private theorem scalarMap_appLE {T : Scheme.{w}} (a : T ⟶ X) (B : T.Opens)
    (h : B ≤ a ⁻¹ᵁ A) :
    (a.appLE A B h).hom.comp (scalarMap f A) = scalarMap (a ≫ f) B := by
  ext r
  change (T.presheaf.map (homOfLE h).op).hom
    ((a.app A).hom (scalarMap f A r)) = _
  have hn := congrArg (fun q : Γ(X, ⊤) ⟶ Γ(T, a ⁻¹ᵁ A) ↦
    q.hom (((ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom r))
    (a.naturality (homOfLE (le_top (a := A))).op)
  have hp : (a.app A).hom (scalarMap f A r) = scalarMap (a ≫ f) (a ⁻¹ᵁ A) r := by
    simp only [scalarMap, RingHom.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp]
    convert hn using 1; rfl
  rw [hp]
  simp only [scalarMap, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← T.presheaf.map_comp]
  rfl

private def rightSectionEquiv :
    scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤) ≃ₗ[k] scalarObj g G (op V) := by
  let e := ((G.restrictAppIso V.ι ⊤) ≪≫
    G.presheaf.mapIso (eqToIso V.ι_image_top.symm).op).addCommGroupIsoToAddEquiv
  refine { e with map_smul' := ?_ }
  intro r t
  change G.presheaf.map (eqToHom V.ι_image_top.symm).op
    ((G.restrictAppIso V.ι ⊤).hom ((scalarMap (V.ι ≫ g) ⊤ r) •
      (show Γ(G.restrict V.ι, ⊤) from t))) =
      (scalarMap g V r) • (show Γ(G, V) from e t)
  rw [smul_restrictAppIso_hom_apply, Scheme.Modules.map_smul]
  congr 1
  have hs : scalarMap (V.ι ≫ g) ⊤ r =
      (V.ι.appLE ⊤ ⊤ (by simp)).hom (scalarMap g ⊤ r) :=
    congrArg (fun q : k →+* Γ(V.toScheme, ⊤) ↦ q r)
      (scalarMap_appLE g ⊤ V.ι ⊤ (by simp)).symm
  rw [hs]
  have hb := ConcreteCategory.congr_hom
    (V.ι.appLE_appIso_inv (U := ⊤) (V := ⊤) (by simp)) (scalarMap g ⊤ r)
  simp only [ConcreteCategory.comp_apply] at hb
  rw [hb]
  simp only [scalarMap, RingHom.comp_apply]
  simp only [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
  rfl

private theorem exists_external_open_raw [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hA : IsAffineOpen A) (hV : IsAffineOpen V)
    (K : (Limits.pullback f g).Opens)
    (hK : K ≤ (pullback.fst f g) ⁻¹ᵁ A)
    (hKV : K ≤ (pullback.snd f g) ⁻¹ᵁ V)
    (hKeq : K = (pullback.fst f g) ⁻¹ᵁ A ⊓ (pullback.snd f g) ⁻¹ᵁ V) :
    ∃ e : (scalarObj f F (op A) ⊗[k] scalarObj g G (op V)) ≃+
        Γ(externalCupCoefficients f g F G, K),
      ∀ (s : scalarObj f F (op A)) (t : scalarObj g G (op V)),
        e (s ⊗ₜ[k] t) = tmulSection
          (((tensorPullback (pullback.fst f g)).obj F).presheaf.map (homOfLE hK).op
            (((Classical.choose (exists_tensorPullbackAdjunction
              (pullback.fst f g))).unit.app F).val.app (op A) s))
          (((tensorPullback (pullback.snd f g)).obj G).presheaf.map (homOfLE hKV).op
            (((Classical.choose (exists_tensorPullbackAdjunction
              (pullback.snd f g))).unit.app G).val.app (op V) t)) := by
  classical
  subst K
  let K := (pullback.fst f g) ⁻¹ᵁ A ⊓ (pullback.snd f g) ⁻¹ᵁ V
  let Z := Limits.pullback f g
  have hAffineK : IsAffineOpen K :=
    isAffineOpen_preimage_inf_preimage_pullback f g hA hV
  obtain ⟨e, he⟩ := exists_affine_rectangle_projection_sections_tensor
    k X Y f g A V hA hV F G
  let P' := (tensorPullback (pullback.fst f g)).obj F
  let Q' := (tensorPullback (pullback.snd f g)).obj G
  have hP : P'.IsQuasicoherent := by
    let a := (nonempty_tensorPullbackAdjunction (pullback.fst f g)).some.leftAdjointUniq
      (pullbackPushforwardAdjunction (pullback.fst f g))
    exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      (a.app F).symm (by infer_instance)
  have hQ : Q'.IsQuasicoherent := by
    let a := (nonempty_tensorPullbackAdjunction (pullback.snd f g)).some.leftAdjointUniq
      (pullbackPushforwardAdjunction (pullback.snd f g))
    exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      (a.app G).symm (by infer_instance)
  let := hP
  let := hQ
  let b := LinearEquiv.ofBijective (tensorSectionsMap P' Q' K)
    ((quasiCoherent_tensor_product_affine_sections P' Q').2 K hAffineK)
  refine ⟨e.trans b.toAddEquiv, ?_⟩
  intro s t
  change tensorSectionsMap P' Q' K (e (s ⊗ₜ[k] t)) = _
  rw [he, tensorSectionsMap_tmul]
  rfl

/-- On one affine product open, the external tensor-section map is an additive
isomorphism, normalized by the original projection adjunction units.
Source: Stacks Project, Tag 0BED, varieties-lemma-kunneth, affine-open paragraph;
Tags 01I9 and 01CD for pullback and tensor sections.
(blueprint: lem-sc-external-tensor-affine-open-sections).

Proof: Put W = pr2 inverse V and K = W.ι(J). The image-preimage formula
identifies K with pr1 inverse A intersect pr2 inverse V. The affine product-open
lemma makes K affine. Apply the affine pushout-section comparison to the product
square and A,V, then transport its base from Gamma(Spec k,top) to k via GammaSpecIso.
The resulting pushout has projection ring maps appLE. Naturality of the structure
sheaf shows that they commute with the scalar maps from k.
Apply exists_tensorPullback_affine_sections to each projection, with source open K
and target open A or V. Its bijectivity, linearity and pure-tensor clauses give
C-linear equivalences C tensor_R M with the first projection sections and
C tensor_S N with the second, for R=Gamma(X,A), S=Gamma(Y,V), C=Gamma(Z,K),
M=Gamma(F,A), N=Gamma(G,V). Algebra.IsPushout.cancelBaseChange, tensor commutativity
and AlgebraTensorModule.cancelBaseChange identify their tensor product over C
with M tensor_k N. Its inverse sends s tensor t to (1 tensor s) tensor (1 tensor t).
Both projection pullbacks are quasi-coherent, since tensorPullback agrees with the
usual pullback by uniqueness of left adjoints. The affine tensor-section theorem
therefore makes tensorSectionsMap on K bijective. Compose its additive equivalence
with the preceding tensor equivalence; its pure-tensor formula is precisely the
tensor section of the two original projection-unit sections restricted to K.
The identity on F(A) identifies global-ring scalar restriction with the local
k action. The restriction-section isomorphism identifies the right factor with
G(V) k-linearly; its scalar compatibility follows from the appLE/appIso identity.
The inverse restriction-section isomorphism for W.ι gives the asserted sections
on J. These comparisons and their formulas prove the normalization. Empty A or V
gives zero section modules; no step excludes them. No finite family, Cech complex,
covering, or differential is involved. -/
theorem externalTensor_affine_open_sections [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hA : IsAffineOpen A) (hV : IsAffineOpen V)
    (J : ((pullback.snd f g) ⁻¹ᵁ V).toScheme.Opens)
    (hJ : J = ((pullback.snd f g) ⁻¹ᵁ V).ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ A))
    (hK : ((pullback.snd f g) ⁻¹ᵁ V).ι ''ᵁ J ≤ (pullback.fst f g) ⁻¹ᵁ A)
    (hKV : ((pullback.snd f g) ⁻¹ᵁ V).ι ''ᵁ J ≤ (pullback.snd f g) ⁻¹ᵁ V) :
    ∃ e : ((ModuleCat.restrictScalars (scalarMap f ⊤)).obj
        (F.presheafModuleCat.obj (op A)) ⊗[k]
          scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤)) ≃+
        Γ((externalCupCoefficients f g F G).restrict
          ((pullback.snd f g) ⁻¹ᵁ V).ι, J),
      ∀ (s : (ModuleCat.restrictScalars (scalarMap f ⊤)).obj
          (F.presheafModuleCat.obj (op A)))
        (t : scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤)),
        e (s ⊗ₜ[k] t) = externalTensorOpenPureSection f g F G A V J hK hKV s t := by
  classical
  let W := (pullback.snd f g) ⁻¹ᵁ V
  let K : (Limits.pullback f g).Opens := W.ι ''ᵁ J
  have hKeq : K = (pullback.fst f g) ⁻¹ᵁ A ⊓ (pullback.snd f g) ⁻¹ᵁ V := by
    dsimp only [K]
    rw [hJ, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_comm _ _
  obtain ⟨e, he⟩ := exists_external_open_raw f g F G A V hA hV K hK hKV hKeq
  let b := TensorProduct.congr (globalScalarSectionEquiv f F A) (rightSectionEquiv g G V)
  let d := ((externalCupCoefficients f g F G).restrictAppIso W.ι J).addCommGroupIsoToAddEquiv
  refine ⟨b.toAddEquiv.trans (e.trans d.symm), ?_⟩
  intro s t
  change d.symm (e (b (s ⊗ₜ[k] t))) = _
  rw [TensorProduct.congr_tmul, he]
  dsimp [globalScalarSectionEquiv, rightSectionEquiv, d, externalTensorOpenPureSection]
  rfl

end
end AlgebraicGeometry.Scheme.Modules

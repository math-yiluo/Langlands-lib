/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Images

import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Comparing extended ideal tensor products with categorical images

Source: Stacks Project, Varieties Remark 09NW and Lemma 09NX, displayed conductor equality;
Modules Tag 01CD. The general image identification below is the representation step.
(blueprint: lem-sc-ideal-tensor-image-comparison).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- The image of an adjoint ideal inclusion, multiplied by an invertible module, agrees
with the extended ideal tensor product, compatibly with any linear comparison of the
ambient modules and any change of pullback adjunction.

Source: Stacks Project, Varieties Remark 09NW and Lemma 09NX, displayed conductor equality;
Modules Tag 01CD, pullback of tensor products.
(blueprint: lem-sc-ideal-tensor-image-comparison).

Proof: write a₀ for the canonical adjunction and c for its comparison with adj.
For the canonical adjoint ideal map φ₀, on affine opens U = Spec B contained in the
preimage of V = Spec A the pullback sections are B ⊗[A] I(V), since I is quasi-coherent.
The adjunction equation sends b ⊗ a to b f♯(a). Its image is precisely I(V)B, the ideal
of I.comap f on U (ideal_comap_appLE). Changing the adjunction gives
φ = c_I.hom ≫ φ₀, hence the same image because c_I is an isomorphism. These affine
calculations commute with restriction and identify image φ with (I.comap f).toModules
compatibly with their inclusions into the unit module. No flatness is needed: this
computes an image, without asserting that B ⊗[A] I(V) maps injectively to B.
Write K = I.comap f. Tensoring either ideal inclusion with an invertible module is
monic (mono_whiskerRight). In particular multiplication μP is monic, so its source
maps isomorphically onto image μP. The module N₁ is invertible via e. Under the ideal
image identification, tensor the identity of K.toModules with the linear isomorphism
h = e.inv ≫ (c.app N).hom. Naturality of the left unitor shows that this tensor map
commutes with multiplication into P and N₁, with ambient map h. Compose it with the
inverse of the monic image corestriction to μP. This is an isomorphism of sheaves;
evaluation on the top open gives q and the displayed equality. Monicity of μ₁ also
shows that this equality uniquely determines q. -/
theorem ideal_tensor_image_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (N : Y.Modules) (P : X.Modules) [P.IsInvertible]
    (adj : tensorPullback f ⊣ pushforward f)
    (e : (tensorPullback f).obj N ≅ P) :
    let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
      (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    let μP := image.ι φ ▷ P ≫ (λ_ P).hom
    let N₁ := (tensorPullback f).obj N
    let μ₁ := (I.comap f).toModulesι ▷ N₁ ≫ (λ_ N₁).hom
    let c := adj.leftAdjointUniq (Classical.choose (exists_tensorPullbackAdjunction f))
    ∃ q : Γ(image μP, ⊤) ≃+ Γ((I.comap f).toModules ⊗ N₁, ⊤),
      ∀ t, μ₁.app ⊤ (q t) =
        (c.app N).hom.app ⊤ (e.inv.app ⊤ ((image.ι μP).app ⊤ t)) := by
  classical
  dsimp only
  let T := tensorPullback f
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let a₀ := Classical.choice (nonempty_tensorPullbackAdjunction f)
  let j := I.subschemeι
  let v := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let φ := (adj.homEquiv I.toModules O).symm (I.toModulesι ≫ v)
  let φ₀ := (a₀.homEquiv I.toModules O).symm (I.toModulesι ≫ v)
  let d := adj.leftAdjointUniq a₀
  have hφ : φ = (d.app I.toModules).hom ≫ φ₀ := by
    dsimp [φ, φ₀]
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    rw [← d.hom.naturality_assoc, Adjunction.leftAdjointUniq_hom_app_counit]
  have hker : (pullback.snd j f).ker = I.comap f := by
    calc
      _ = (pullback.fst f j).ker := by
        rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry j f).hom
          (pullback.fst f j), pullbackSymmetry_hom_comp_fst]
      _ = j.ker.comap f := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion j f
      _ = I.comap f := congrArg (fun K ↦ K.comap f) I.ker_subschemeι
  have himg₀ : Subobject.mk (I.comap f).toModulesι = imageSubobject φ₀ := by
    have h := (closedSubscheme_baseChange_ideal_image j f).2
    rw [hker, I.ker_subschemeι] at h
    simpa only [φ₀, a₀, Adjunction.homEquiv_naturality_left_symm] using h
  have himg : Subobject.mk (image.ι φ) = Subobject.mk (I.comap f).toModulesι := by
    change imageSubobject φ = _
    rw [hφ, imageSubobject_iso_comp]
    exact himg₀.symm
  let k : image φ ≅ (I.comap f).toModules :=
    Subobject.isoOfMkEqMk (image.ι φ) (I.comap f).toModulesι himg
  have hk : k.hom ≫ (I.comap f).toModulesι = image.ι φ := by
    simp [k]
  let μP := image.ι φ ▷ P ≫ (λ_ P).hom
  have : Mono μP := inferInstance
  let N₁ := T.obj N
  let c := adj.leftAdjointUniq (Classical.choose (exists_tensorPullbackAdjunction f))
  let h : P ≅ N₁ := e.symm ≪≫ c.app N
  let b : image φ ⊗ P ≅ (I.comap f).toModules ⊗ N₁ := k ⊗ᵢ h
  let q₀ : image μP ≅ (I.comap f).toModules ⊗ N₁ := imageMonoIsoSource μP ≪≫ b
  let μ₁ := (I.comap f).toModulesι ▷ N₁ ≫ (λ_ N₁).hom
  have hb : b.hom ≫ μ₁ = μP ≫ h.hom := by
    change (k.hom ⊗ₘ h.hom) ≫ (I.comap f).toModulesι ▷ N₁ ≫ (λ_ N₁).hom =
      (image.ι φ ▷ P ≫ (λ_ P).hom) ≫ h.hom
    rw [tensorHom_def, Category.assoc, whisker_exchange_assoc,
      ← comp_whiskerRight_assoc, hk]
    change image.ι φ ▷ P ≫ (𝟙_ X.Modules) ◁ h.hom ≫ (λ_ N₁).hom = _
    rw [leftUnitor_naturality]
    simp only [Category.assoc]
  have hq : q₀.hom ≫ μ₁ = image.ι μP ≫ h.hom := by
    dsimp only [q₀, Iso.trans_hom]
    rw [Category.assoc, hb, imageMonoIsoSource_hom_self_assoc]
  let q := ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso q₀).toLinearEquiv
    |>.toAddEquiv
  refine ⟨q, ?_⟩
  intro t
  exact congrArg (fun a ↦ a.app ⊤ t) hq


end AlgebraicGeometry.Scheme.Modules

import Langlands.GroupScheme.IdentityJetAffineGenerators
import Langlands.RingTheory.Smooth.SectionJetBaseChange

/-! # Actual base-changed identity jets in fixed affine coordinates -/

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.GroupScheme.IdentityJet

open AffineCoordinates Corepresented
open Langlands.AlgebraicGeometry.Picard.LineHom
open Langlands.AlgebraicGeometry.FiniteLinearEquations

variable {R : CommRingCat.{u}} {S : Scheme.{u}}
  (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- Fixed affine coordinates are all actual global functions on the original group. -/
def globalCoordinateEquiv :
    letI : Algebra R Γ(G.X.left, ⊤) := sectionsAlgebra (Over.mk G.X.hom)
    algebra G ≃ₐ[R] Γ(G.X.left, ⊤) := by
  letI : Algebra R Γ(G.X.left, ⊤) := sectionsAlgebra (Over.mk G.X.hom)
  refine AlgEquiv.ofBijective
    { toRingHom := ((Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv ≫
        (groupSchemeIso G).inv.hom.hom.left.appTop).hom
      commutes' := ?_ } ?_
  · intro r
    dsimp only [sectionsAlgebra, sectionScalars, RingHom.algebraMap_toAlgebra]
    change ((CommRingCat.ofHom (algebraMap R (algebra G)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv) ≫
          (groupSchemeIso G).inv.hom.hom.left.appTop) r =
      ((Scheme.ΓSpecIso R).inv ≫ G.X.hom.appTop) r
    rw [Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop]
    change ((Scheme.ΓSpecIso R).inv ≫
      ((groupSchemeIso G).inv.hom.hom.left ≫
        (groupScheme (functor G) (corepresentation G)).X.hom).appTop) r = _
    rw [Over.w]
  · exact (ConcreteCategory.bijective_of_isIso
      (groupSchemeIso G).inv.hom.hom.left.appTop).comp
        (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv)

variable (b : S ⟶ Spec R)

attribute [local instance] sectionAlgebra

/-- The actual base-change structure morphism is affine. -/
private theorem baseChange_affine : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  have : IsAffineHom G.X.hom := inferInstance
  change IsAffineHom (pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance

attribute [local instance] baseChange_affine

/-- Actual ambient coordinate pullback respects the coefficient algebra. -/
def baseChangeCoordinateAlgHom (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    letI : Algebra R Γ(((GroupScheme.baseChange b).obj G).X.left, ((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U) :=
      ((((GroupScheme.baseChange b).obj G).X.hom.app U).hom.comp (algebraMap R Γ(S, U))).toAlgebra
    algebra G →ₐ[R] Γ(((GroupScheme.baseChange b).obj G).X.left, ((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  letI : Algebra R Γ(((GroupScheme.baseChange b).obj G).X.left, ((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U) :=
    ((((GroupScheme.baseChange b).obj G).X.hom.app U).hom.comp (algebraMap R Γ(S, U))).toAlgebra
  exact
    { toRingHom := coordinateMap ((GroupScheme.baseChange b).obj G) (ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G))) U
      commutes' := ambient_coordinateMap_algebraMap G b (𝟙 ((GroupScheme.baseChange b).obj G)) U }

/-- The tensor coordinate map to actual functions on the base-changed group. -/
def baseChangeCoordinateTensor (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Γ(S, U) ⊗[R] algebra G →ₐ[Γ(S, U)] Γ(((GroupScheme.baseChange b).obj G).X.left, ((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  letI : Algebra R Γ(((GroupScheme.baseChange b).obj G).X.left, ((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U) :=
    ((((GroupScheme.baseChange b).obj G).X.hom.app U).hom.comp (algebraMap R Γ(S, U))).toAlgebra
  letI : IsScalarTower R Γ(S, U) Γ(((GroupScheme.baseChange b).obj G).X.left, ((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  exact AlgHom.liftEquiv R Γ(S, U) (algebra G) _ (baseChangeCoordinateAlgHom G b U)

@[simp]
theorem baseChangeCoordinateTensor_tmul (U : S.affineOpens)
    (a : Γ(S, U)) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    baseChangeCoordinateTensor G b U (a ⊗ₜ[R] c) =
      ((GroupScheme.baseChange b).obj G).X.hom.app U a * coordinateMap ((GroupScheme.baseChange b).obj G) (ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G))) U c := rfl

private theorem baseChange_coordinateMap (U : S.affineOpens) (c : algebra G) :
    letI : Algebra R Γ(G.X.left, ⊤) := sectionsAlgebra (Over.mk G.X.hom)
    coordinateMap ((GroupScheme.baseChange b).obj G) (ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G))) U c =
      (pullback.fst G.X.hom b).appLE ⊤ (((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U)
        (le_preimage_top _ _) (globalCoordinateEquiv G c) := by
  have hh := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE (pullback.fst G.X.hom b)
      (groupSchemeIso G).inv.hom.hom.left ⊤ ⊤ (((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U)
      (le_preimage_top _ _) (le_preimage_top _ _))
    ((Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv c)
  change
    ((groupSchemeIso G).inv.hom.hom.left.appLE ⊤
      ((groupSchemeIso G).inv.hom.hom.left ⁻¹ᵁ ⊤) le_rfl ≫
      (pullback.fst G.X.hom b).appLE ⊤ (((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U)
        (le_preimage_top _ _))
      ((Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv c) = _ at hh
  rw [Scheme.Hom.appLE_eq_app] at hh
  have hj : ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G)) =
      pullback.fst G.X.hom b ≫ (groupSchemeIso G).inv.hom.hom.left := by
    change (𝟙 (pullback G.X.hom b)) ≫ pullback.fst G.X.hom b ≫ _ = _
    rw [Category.id_comp]
  rw [hj]
  exact hh.symm

/-- The tensor coordinate map is bijective over every affine base open. -/
theorem baseChangeCoordinateTensor_bijective (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Function.Bijective (baseChangeCoordinateTensor G b U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let : Algebra R Γ(G.X.left, ⊤) := sectionsAlgebra (Over.mk G.X.hom)
  let : Algebra R Γ((Over.mk G.X.hom).left, ⊤) := sectionsAlgebra (Over.mk G.X.hom)
  have : IsAffine (Over.mk G.X.hom).left := inferInstanceAs (IsAffine G.X.left)
  let e : (Γ(S, U) ⊗[R] algebra G) ≃ₗ[R] (Γ(G.X.left, ⊤) ⊗[R] Γ(S, U)) :=
    (TensorProduct.comm R Γ(S, U) (algebra G)).trans
      (TensorProduct.congr (globalCoordinateEquiv G).toLinearEquiv
        (LinearEquiv.refl R Γ(S, U)))
  have hfac : ∀ z, baseChangeCoordinateTensor G b U z =
      sectionsTensorHom b (Over.mk G.X.hom) U (e z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a c =>
      change ((GroupScheme.baseChange b).obj G).X.hom.app U a * coordinateMap ((GroupScheme.baseChange b).obj G)
          (ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G))) U c =
        sectionsTensorHom b (Over.mk G.X.hom) U
          (globalCoordinateEquiv G c ⊗ₜ[R] a)
      rw [sectionsTensorHom_tmul, baseChange_coordinateMap, mul_comm]
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  rw [show ⇑(baseChangeCoordinateTensor G b U) =
    sectionsTensorHom b (Over.mk G.X.hom) U ∘ e from funext hfac]
  exact (sectionsTensorHom_bijective b (Over.mk G.X.hom) U.2).comp e.bijective

/-- The actual affine base-change coordinate algebra in its fixed coordinates. -/
def baseChangeCoordinateEquiv (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Γ(S, U) ⊗[R] algebra G ≃ₐ[Γ(S, U)] Γ(((GroupScheme.baseChange b).obj G).X.left, ((GroupScheme.baseChange b).obj G).X.hom ⁻¹ᵁ U) :=
  AlgEquiv.ofBijective (baseChangeCoordinateTensor G b U)
    (baseChangeCoordinateTensor_bijective G b U)

/-- Ambient evaluation agrees with evaluation at the actual base-changed identity. -/
theorem baseChange_augmentation_coordinateMap (U : S.affineOpens) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    augmentation ((GroupScheme.baseChange b).obj G) U
      (coordinateMap ((GroupScheme.baseChange b).obj G)
        (ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G))) U c) =
      algebraMap R Γ(S, U) ((LinearEmbedding.counit (corepresentation G)).hom c) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let ε := (LinearEmbedding.counit (corepresentation G)).hom
  have hc : c - algebraMap R (algebra G) (ε c) ∈ augIdeal (corepresentation G) := by
    change ε (c - algebraMap R (algebra G) (ε c)) = 0
    rw [map_sub, ε.commutes]
    change ε c - ε c = 0
    exact sub_self _
  have hh := augmentation_coordinateMap_eq_zero ((GroupScheme.baseChange b).obj G)
    (ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G)))
    (augIdeal (corepresentation G))
    (ambientProjection_vanishesAtIdentity G b (𝟙 ((GroupScheme.baseChange b).obj G))) U hc
  have hsc : augmentation ((GroupScheme.baseChange b).obj G) U
      (coordinateMap ((GroupScheme.baseChange b).obj G)
        (ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G))) U
          (algebraMap R (algebra G) (ε c))) = algebraMap R Γ(S, U) (ε c) := by
    rw [ambient_coordinateMap_algebraMap]
    exact (augmentation ((GroupScheme.baseChange b).obj G) U).commutes _
  exact sub_eq_zero.mp (by simpa only [map_sub, hsc] using hh)

/-- The actual coordinate equivalence respects the actual identity augmentation. -/
theorem augmentation_baseChangeCoordinateTensor (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    (augmentation ((GroupScheme.baseChange b).obj G) U).comp
        (baseChangeCoordinateTensor G b U) =
      Algebra.SectionJet.baseChangeAugmentation
        (LinearEmbedding.counit (corepresentation G)).hom Γ(S, U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    simp only [AlgHom.comp_apply, baseChangeCoordinateTensor_tmul, map_mul,
      Algebra.SectionJet.baseChangeAugmentation_tmul]
    rw [show augmentation ((GroupScheme.baseChange b).obj G) U
        (((GroupScheme.baseChange b).obj G).X.hom.app U a) = a from
      (augmentation ((GroupScheme.baseChange b).obj G) U).commutes a]
    exact congrArg (a * ·) (baseChange_augmentation_coordinateMap G b U c)
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem augmentedEquiv_ker
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C)
    (ε : C →ₐ[A] A) (δ : B →ₐ[A] A) (h : ε.comp e.toAlgHom = δ) :
    RingHom.ker ε = (RingHom.ker δ).map (e : B →+* C) := by
  have hk : (RingHom.ker ε).comap (e : B →+* C) = RingHom.ker δ := by
    ext z
    change ε (e z) = 0 ↔ δ z = 0
    have hh := AlgHom.congr_fun h z
    change ε (e z) = δ z at hh
    rw [hh]
  calc
    _ = ((RingHom.ker ε).comap (e : B →+* C)).map (e : B →+* C) :=
      (Ideal.map_comap_of_surjective (e : B →+* C) e.surjective _).symm
    _ = _ := by rw [hk]

private theorem baseChangeCoordinateEquiv_ker (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    RingHom.ker (augmentation ((GroupScheme.baseChange b).obj G) U) =
      (RingHom.ker (Algebra.SectionJet.baseChangeAugmentation
        (LinearEmbedding.counit (corepresentation G)).hom Γ(S, U))).map
          (baseChangeCoordinateEquiv G b U : _ →+* _) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  exact augmentedEquiv_ker (baseChangeCoordinateEquiv G b U)
    (augmentation ((GroupScheme.baseChange b).obj G) U)
    (Algebra.SectionJet.baseChangeAugmentation
      (LinearEmbedding.counit (corepresentation G)).hom Γ(S, U))
    (augmentation_baseChangeCoordinateTensor G b U)

/-- Fixed ambient truncated coordinates identify the actual base-changed jet sections. -/
def baseChangeJetEquiv (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Γ(S, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1))
      ≃ₗ[Γ(S, U)] Γ(module ((GroupScheme.baseChange b).obj G) n, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  exact
    ((Algebra.SectionJet.baseChangeEquiv
      (LinearEmbedding.counit (corepresentation G)).hom Γ(S, U) n).trans
        (Ideal.quotientEquivAlg _ _ (baseChangeCoordinateEquiv G b U)
          (by
            simpa only [Ideal.map_pow, AlgEquiv.toRingEquiv_toRingHom] using
              congrArg (fun I => I ^ (n + 1)) (baseChangeCoordinateEquiv_ker G b U)))).toLinearEquiv.trans
      (sectionsEquiv ((GroupScheme.baseChange b).obj G) n U).symm

/-- The actual jet comparison sends a pure tensor to the prescribed coordinate section. -/
theorem baseChangeJetEquiv_tmul_mk (n : ℕ) (U : S.affineOpens)
    (a : Γ(S, U)) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    baseChangeJetEquiv G b n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • (module ((GroupScheme.baseChange b).obj G) n).presheaf.map
        (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (ambientQuotientCoordinates G b (𝟙 ((GroupScheme.baseChange b).obj G)) n
            (Ideal.Quotient.mk _ c)) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let H := (GroupScheme.baseChange b).obj G
  let I := RingHom.ker (augmentation H U) ^ (n + 1)
  let cU := coordinateMap H (ambientProjection G b (𝟙 H)) U c
  have hq : (sectionsEquiv H n U).symm (Ideal.Quotient.mk I cU) =
      (module H n).presheaf.map
        (homOfLE (show (U : S.Opens) ≤ ⊤ from le_top)).op
          (ambientQuotientCoordinates G b (𝟙 H) n (Ideal.Quotient.mk _ c)) := by
    apply (sectionsEquiv H n U).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (sectionsEquiv_restrict_quotientCoordinates H
      (ambientProjection G b (𝟙 H)) (augIdeal (corepresentation G))
      (ambientProjection_vanishesAtIdentity G b (𝟙 H)) n U c).symm
  calc
    _ = a • (sectionsEquiv H n U).symm (Ideal.Quotient.mk I cU) := by
      apply (sectionsEquiv H n U).injective
      rw [(sectionsEquiv H n U).map_smul, LinearEquiv.apply_symm_apply]
      simp only [baseChangeJetEquiv, LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply,
        AlgEquiv.trans_apply]
      change (sectionsEquiv H n U) ((sectionsEquiv H n U).symm _) = _
      rw [LinearEquiv.apply_symm_apply]
      change Ideal.Quotient.mk I (baseChangeCoordinateTensor G b U (a ⊗ₜ[R] c)) =
        a • Ideal.Quotient.mk I cU
      rw [baseChangeCoordinateTensor_tmul]
      rfl
    _ = _ := congrArg (a • ·) hq

/-- The base-change equivalence is exactly the previously specified actual tensor map. -/
theorem baseChangeJetEquiv_toLinearMap (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    (baseChangeJetEquiv G b n U).toLinearMap =
      ambientTensorCoordinates G b (𝟙 ((GroupScheme.baseChange b).obj G)) n U := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact baseChangeJetEquiv_tmul_mk G b n U a c
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Langlands.GroupScheme.IdentityJet

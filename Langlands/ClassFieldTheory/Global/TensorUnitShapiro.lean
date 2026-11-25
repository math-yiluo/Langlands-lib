import Langlands.ClassFieldTheory.Global.IdeleSemilocal
import Langlands.GroupScheme.Torus.WeilRestrictionSeparable

/-! # Shapiro comparison for units of a split coefficient tensor product -/

noncomputable section

universe u

open CategoryTheory groupCohomology
open scoped TensorProduct

namespace Langlands.ClassFieldTheory.Global.TensorUnitShapiro

open ClassFieldTheory.Local GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F B L : Type u) [Field F] [Field B] [Field L]
  [Algebra F B] [Algebra F L]

/-- Automorphisms of the coefficient field act on the right tensor factor. -/
def tensorAction (σ : Gal(L/F)) : (B ⊗[F] L)ˣ →* (B ⊗[F] L)ˣ :=
  Units.map (Algebra.TensorProduct.lTensor (S := B) B σ.toAlgHom).toMonoidHom

/-- Tensor units, with the indicated actual coefficient action. -/
def tensorUnitRepresentation : Rep.{u} IntegerScalars.{u} Gal(L/F) :=
  Rep.of
    { toFun := fun σ => (tensorAction F B L σ).toAdditive.toIntLinearMap.restrictScalars IntegerScalars
      map_one' := by
        ext x
        change Algebra.TensorProduct.lTensor (S := B) B (AlgHom.id F L) (x.toMul : B ⊗[F] L) = _
        exact DFunLike.congr_fun
          (Algebra.TensorProduct.map_id (R := F) (S := B) (A := B) (B := L)) _
      map_mul' := by
        intro σ τ
        ext x
        change Algebra.TensorProduct.lTensor (S := B) B (σ * τ).toAlgHom (x.toMul : B ⊗[F] L) =
          Algebra.TensorProduct.lTensor (S := B) B σ.toAlgHom
            (Algebra.TensorProduct.lTensor (S := B) B τ.toAlgHom (x.toMul : B ⊗[F] L))
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp]
        rfl }

variable [Algebra B L] [IsScalarTower F B L] [FiniteDimensional F B] [Algebra.IsSeparable F B]
  [Normal F L]

omit [FiniteDimensional F B] [Algebra.IsSeparable F B] in
private theorem minpoly_splits (x : B) : ((minpoly F x).map (algebraMap F L)).Splits := by
  rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom F B L) (algebraMap B L).injective x]
  exact (inferInstance : Normal F L).splits (algebraMap B L x)

/-- The tensor coordinates given by all `F`-embeddings of `B` into `L`. -/
def tensorEmbeddingEquiv : (B ⊗[F] L) ≃ₐ[F] ((B →ₐ[F] L) → L) :=
  (Algebra.TensorProduct.comm F B L).trans <|
    (separableEmbeddingDecomposition F B L (minpoly_splits F B L)).restrictScalars F

@[simp] theorem tensorEmbeddingEquiv_tmul (b : B) (x : L) (j : B →ₐ[F] L) :
    tensorEmbeddingEquiv F B L (b ⊗ₜ[F] x) j = x * j b := rfl

/-- The embedding decomposition on the actual unit groups. -/
def unitEmbeddingEquiv : (B ⊗[F] L)ˣ ≃* ((B →ₐ[F] L) → Lˣ) :=
  (Units.mapEquiv (tensorEmbeddingEquiv F B L).toMulEquiv).trans MulEquiv.piUnits

/-- The action on the coordinates combines conjugation of the value with the inverse
permutation of embeddings. -/
theorem unitEmbeddingEquiv_action (σ : Gal(L/F)) (x : (B ⊗[F] L)ˣ) (j : B →ₐ[F] L) :
    unitEmbeddingEquiv F B L (tensorAction F B L σ x) j =
      σ • unitEmbeddingEquiv F B L x (σ.symm.toAlgHom.comp j) := by
  apply Units.ext
  change tensorEmbeddingEquiv F B L
      (Algebra.TensorProduct.lTensor (S := B) B σ.toAlgHom (x : B ⊗[F] L)) j =
    σ (tensorEmbeddingEquiv F B L (x : B ⊗[F] L) (σ.symm.toAlgHom.comp j))
  generalize (x : B ⊗[F] L) = x'
  induction x' using TensorProduct.inductionOn with
  | tmul b y => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

private abbrev inclusion : B →ₐ[F] L := IsScalarTower.toAlgHom F B L

/-- An automorphism over `B` also acts over `F`. -/
abbrev relativeAut : Gal(L/B) →* Gal(L/F) := AlgEquiv.restrictScalarsHom F

omit [FiniteDimensional F B] [Algebra.IsSeparable F B] [Normal F L] in
private theorem relativeAut_injective : Function.Injective (relativeAut F B L) := by
  intro g h hgh
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun hgh x)

omit [FiniteDimensional F B] [Algebra.IsSeparable F B] [Normal F L] in
private theorem relativeAut_symm_comp (σ : Gal(L/B)) :
    ((relativeAut F B L σ).symm.toAlgHom.comp (inclusion F B L)) = inclusion F B L :=
  AlgHom.ext fun x => σ.symm.commutes x

/-- The coefficient map given by the inclusion embedding, equivariant over `B`. -/
def projection : Rep.res (relativeAut F B L) (tensorUnitRepresentation F B L) ⟶
    unitsRepresentation B L :=
  Rep.ofHom
    { toLinearMap := ((Pi.evalMonoidHom (fun _ : B →ₐ[F] L => Lˣ) (inclusion F B L)).comp
        (unitEmbeddingEquiv F B L).toMonoidHom).toAdditive.toIntLinearMap.restrictScalars IntegerScalars
      isIntertwining' σ := by
        ext x
        change Additive.ofMul (unitEmbeddingEquiv F B L
          (tensorAction F B L (relativeAut F B L σ) x.toMul) (inclusion F B L)) =
            Additive.ofMul (σ • unitEmbeddingEquiv F B L x.toMul (inclusion F B L))
        rw [unitEmbeddingEquiv_action, relativeAut_symm_comp]
        rfl }

omit [FiniteDimensional F B] [Algebra.IsSeparable F B] [Normal F L] in
private theorem symm_comp_eq_iff (g : Gal(L/F)) :
    g.symm.toAlgHom.comp (inclusion F B L) = inclusion F B L ↔ g ∈ (relativeAut F B L).range := by
  constructor
  · intro h
    refine ⟨{ g with commutes' := fun x => ?_ }, rfl⟩
    have h' := DFunLike.congr_fun h x
    change g.symm (algebraMap B L x) = algebraMap B L x at h'
    exact (congrArg g h').symm.trans (g.apply_symm_apply _)
  · rintro ⟨σ, rfl⟩
    exact relativeAut_symm_comp F B L σ

attribute [local instance 1200] AddCommGroup.toIntModule in
open Classical in
private def coordinateSection : unitsRepresentation B L ⟶
    Rep.res (relativeAut F B L) (tensorUnitRepresentation F B L) :=
  Rep.ofHom
    { toLinearMap := LinearMap.restrictScalars IntegerScalars
        (((unitEmbeddingEquiv F B L).symm.toMonoidHom.comp
          (MonoidHom.mulSingle (fun _ : B →ₐ[F] L => Lˣ) (inclusion F B L))).toAdditive.toIntLinearMap)
      isIntertwining' σ := by
        ext x
        apply Additive.toMul.injective
        apply (unitEmbeddingEquiv F B L).injective
        funext j
        change unitEmbeddingEquiv F B L ((unitEmbeddingEquiv F B L).symm
          (Pi.mulSingle (inclusion F B L) (σ • (@Additive.toMul Lˣ x)))) j =
          unitEmbeddingEquiv F B L (tensorAction F B L (relativeAut F B L σ)
            ((unitEmbeddingEquiv F B L).symm (Pi.mulSingle (inclusion F B L) x.toMul))) j
        rw [unitEmbeddingEquiv_action, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        have hj : (relativeAut F B L σ).symm.toAlgHom.comp j = inclusion F B L ↔
            j = inclusion F B L := by
          constructor
          · intro h
            apply AlgHom.ext
            intro b
            apply (relativeAut F B L σ).symm.injective
            exact (DFunLike.congr_fun h b).trans
              ((DFunLike.congr_fun (relativeAut_symm_comp F B L σ) b).symm)
          · rintro rfl
            exact relativeAut_symm_comp F B L σ
        by_cases he : j = inclusion F B L
        · subst j
          rw [relativeAut_symm_comp]
          simp
          rfl
        · simp only [Pi.mulSingle_eq_of_ne he, Pi.mulSingle_eq_of_ne (mt hj.mp he), smul_one] }

variable [FiniteDimensional F L]

/-- The adjunction morphism from the actual tensor-unit representation to coinduction. -/
def toCoinduced : tensorUnitRepresentation F B L ⟶
    Rep.coind (relativeAut F B L) (unitsRepresentation B L) :=
  Rep.resCoindToHom _ _ _ (projection F B L)

omit [FiniteDimensional F L] in
private theorem toCoinduced_injective : Function.Injective (toCoinduced F B L).hom := by
  intro a b hab
  apply Additive.toMul.injective
  apply (unitEmbeddingEquiv F B L).injective
  funext j
  let g := AlgEquiv.ofBijective (j.liftNormal L) (AlgHom.normal_bijective F L L _)
  have hg : g.toAlgHom.comp (inclusion F B L) = j :=
    AlgHom.ext fun x => j.liftNormal_commutes L x
  have h := congrArg (fun v => (v.1 g⁻¹).toMul) hab
  change unitEmbeddingEquiv F B L (tensorAction F B L g⁻¹ a.toMul) (inclusion F B L) =
    unitEmbeddingEquiv F B L (tensorAction F B L g⁻¹ b.toMul) (inclusion F B L) at h
  rw [unitEmbeddingEquiv_action, unitEmbeddingEquiv_action] at h
  change g⁻¹ • unitEmbeddingEquiv F B L a.toMul (g.toAlgHom.comp (inclusion F B L)) =
    g⁻¹ • unitEmbeddingEquiv F B L b.toMul (g.toAlgHom.comp (inclusion F B L)) at h
  exact (MulAction.injective g⁻¹) (hg ▸ h)

private theorem toCoinduced_surjective : Function.Surjective (toCoinduced F B L).hom := by
  classical
  let : Fintype (Gal(L/F) ⧸ (relativeAut F B L).range) := Fintype.ofFinite _
  let s := Shapiro.coindSum (relativeAut F B L) (coordinateSection F B L)
  have hs : s ≫ toCoinduced F B L = 𝟙 _ := by
    apply Shapiro.coindSum_comp_resCoindToHom
    · intro a
      change Additive.ofMul (unitEmbeddingEquiv F B L ((unitEmbeddingEquiv F B L).symm
        (Pi.mulSingle (inclusion F B L) a.toMul)) (inclusion F B L)) = a
      rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same]
      rfl
    · intro g hg a
      change Additive.ofMul (unitEmbeddingEquiv F B L (tensorAction F B L g
        ((unitEmbeddingEquiv F B L).symm (Pi.mulSingle (inclusion F B L) a.toMul)))
        (inclusion F B L)) = 0
      rw [unitEmbeddingEquiv_action, MulEquiv.apply_symm_apply,
        Pi.mulSingle_eq_of_ne (mt (symm_comp_eq_iff F B L g).mp hg), smul_one]
      rfl
  intro c
  refine ⟨s.hom c, ?_⟩
  exact congrArg (fun f => f.hom c) hs

/-- Tensor units are coinduced from the actual fields, with the comparison defined by evaluation
at the inclusion embedding on all coefficient translates. -/
def coinducedIso : tensorUnitRepresentation F B L ≅
    Rep.coind (relativeAut F B L) (unitsRepresentation B L) :=
  Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.ofBijective (toCoinduced F B L).hom.toLinearMap
      ⟨toCoinduced_injective F B L, toCoinduced_surjective F B L⟩)
    (fun g => (toCoinduced F B L).hom.isIntertwining' g))

/-- Shapiro identifies the cohomologies using restriction and evaluation at the actual
inclusion embedding. -/
def cohomologyIso (n : ℕ) : groupCohomology (tensorUnitRepresentation F B L) n ≅
    relativeCohomology B L n :=
  (groupCohomology.functor IntegerScalars Gal(L/F) n).mapIso (coinducedIso F B L) ≪≫
    Shapiro.shapiroIsoOf (relativeAut_injective F B L) _ n

/-- On cohomology the isomorphism is restriction of cochains and coefficient evaluation. -/
theorem cohomologyIso_hom (n : ℕ) : (cohomologyIso F B L n).hom =
    groupCohomology.map (relativeAut F B L) (projection F B L) n :=
  Shapiro.map_resCoindToHom_comp_shapiroMapOf (relativeAut F B L) (projection F B L) n

end Langlands.ClassFieldTheory.Global.TensorUnitShapiro

import Langlands.GroupScheme.IntegralModel.LieLattice
import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.Lie.LinearBaseChangeNaturality
import Mathlib.RingTheory.LocalRing.Module

/-! # Reduction of the Lie lattice to the special fibre

Let `R` be a local domain with fraction field `K` and residue field `𝔣`, and let
`M : IntegralModel R K G` be a supplied integral model. Coefficient change `R → 𝔣` and the
inverse pullback comparison give an `R`-linear reduction map
`M.lieReduction : Lie(𝒢) → Lie(𝒢_𝔣)` to the actual Lie algebra of the special fibre. For a
smooth model, `𝔣 ⊗[R] Lie(𝒢) ≃ Lie(𝒢_𝔣)`, so the reduction map is surjective with kernel
`𝔪 • Lie(𝒢)`. Reduction commutes with differentials of model homomorphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

namespace GenericLie

variable (R : Type u) {K : Type u} [CommRing R] [Field K] [Algebra R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]

/-- The differential of the identity homomorphism is the identity. -/
theorem map_id (X : GenericLie R G) : map R (𝟙 G) X = X := by
  rw [map_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (equiv R G X).toMul.val ≫ (𝟙 G : G ⟶ G).hom.hom = (equiv R G X).toMul.val
  simp

variable {H L : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom]
  [IsAffineHom L.X.hom]

/-- Differentials of homomorphisms respect composition. -/
theorem map_comp (f : G ⟶ H) (g : H ⟶ L) (X : GenericLie R G) :
    map R (f ≫ g) X = map R g (map R f X) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

/-- If the differential `Lie.targetMapLinear f K` is surjective, so is `map R f`. -/
theorem map_surjective {f : G ⟶ H} (hf : Function.Surjective (Lie.targetMapLinear f K)) :
    Function.Surjective (map R f) := by
  intro Y
  obtain ⟨X, hX⟩ := hf (equiv R H Y)
  refine ⟨(equiv R G).symm X, ?_⟩
  rw [map_apply, LinearEquiv.apply_symm_apply, hX, LinearEquiv.symm_apply_apply]

end GenericLie

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [IsLocalRing R] {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- The special fibre of an integral model is affine over the residue field. -/
instance specialFibre_isAffineHom (M : IntegralModel R K G) :
    IsAffineHom M.specialFibre.X.hom := by
  change IsAffineHom (pullback.snd M.group.X.hom (residueBaseMap R))
  infer_instance

/-- The pullback of the model along `R → 𝔣`, in the form used by the Lie base-change
comparison, is affine over the residue field. -/
local instance algebraSpecialFibre_isAffineHom (M : IntegralModel R K G) :
    IsAffineHom ((GroupScheme.baseChange
      (algebraBaseMap R (IsLocalRing.ResidueField R))).obj M.group).X.hom := by
  change IsAffineHom (pullback.snd M.group.X.hom
    (algebraBaseMap R (IsLocalRing.ResidueField R)))
  infer_instance

omit [IsDomain R] in
/-- The base map `Spec 𝔣 ⟶ Spec R` of the residue algebra is the residue base map. -/
theorem algebraBaseMap_residueField :
    algebraBaseMap R (IsLocalRing.ResidueField R) = residueBaseMap R := by
  rw [residueBaseMap, ← IsLocalRing.ResidueField.algebraMap_eq]

variable (M : IntegralModel R K G)

/-- The pullback of the model along `Spec (algebraMap R 𝔣)`, the form used by the Lie
base-change comparison, is the special fibre. -/
def specialFibreAlgebraBaseIso :
    (GroupScheme.baseChange (algebraBaseMap R (IsLocalRing.ResidueField R))).obj M.group ≅
      M.specialFibre :=
  eqToIso (congrArg (fun b => (GroupScheme.baseChange b).obj M.group)
    algebraBaseMap_residueField)

variable [IsAffineHom G.X.hom]

/-- The actual Lie kernel of the model over the residue field is the Lie algebra of the special
fibre: the inverse pullback comparison followed by `specialFibreAlgebraBaseIso`. -/
def residueLieEquiv :
    Additive (lieKernel M.group (IsLocalRing.ResidueField R)) ≃ₗ[IsLocalRing.ResidueField R]
      GenericLie R M.specialFibre :=
  ((Lie.kernelBaseChangeLinearEquiv R (IsLocalRing.ResidueField R) M.group
      (IsLocalRing.ResidueField R)).symm.trans
    (lieKernelLinearEquiv M.specialFibreAlgebraBaseIso (IsLocalRing.ResidueField R))).trans
    (GenericLie.equiv R M.specialFibre).symm

/-- Reduction on the actual Lie module of the model: coefficient change from `R` to the
residue field, followed by `residueLieEquiv`. -/
def lieReduction : M.LieModule →ₗ[R] GenericLie R M.specialFibre where
  toFun X := M.residueLieEquiv
    (lieKernelMapLinear M.group (Algebra.ofId R (IsLocalRing.ResidueField R)) X)
  map_add' X Y := by simp only [map_add]
  map_smul' r X := by
    rw [map_smulₛₗ, map_smul]
    rfl

theorem lieReduction_apply (X : M.LieModule) :
    M.lieReduction X = M.residueLieEquiv
      (lieKernelMapLinear M.group (Algebra.ofId R (IsLocalRing.ResidueField R)) X) := rfl

/-- The maximal ideal kills the reduction: `𝔪 • Lie(𝒢)` lies in its kernel. -/
theorem smul_top_le_ker_lieReduction :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M.LieModule) ≤
      LinearMap.ker M.lieReduction := by
  rw [Submodule.smul_le]
  intro r hr X _
  rw [LinearMap.mem_ker, map_smul, GenericLie.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
    (IsLocalRing.residue_eq_zero_iff r).mpr hr, zero_smul]

variable {M}

/-- For a smooth model, the special-fibre Lie algebra is the reduction of `Lie(𝒢)`:
`𝔣 ⊗[R] Lie(𝒢) ≃ Lie(𝒢_𝔣)`. -/
def specialFibreLieEquiv (hM : M.IsSmooth) :
    IsLocalRing.ResidueField R ⊗[R] M.LieModule ≃ₗ[IsLocalRing.ResidueField R]
      GenericLie R M.specialFibre :=
  haveI : Smooth M.group.X.hom := hM
  (Lie.smoothKernelScalarExtension M.group (IsLocalRing.ResidueField R)).trans M.residueLieEquiv

theorem specialFibreLieEquiv_tmul (hM : M.IsSmooth) (a : IsLocalRing.ResidueField R)
    (X : M.LieModule) :
    specialFibreLieEquiv hM (a ⊗ₜ X) = a • M.lieReduction X := by
  have : Smooth M.group.X.hom := hM
  have h := Lie.smoothKernelScalarExtension_tmul M.group (IsLocalRing.ResidueField R) a X
  change M.residueLieEquiv
    (Lie.smoothKernelScalarExtension M.group (IsLocalRing.ResidueField R) (a ⊗ₜ X)) = _
  rw [h, map_smul, lieReduction_apply]

theorem lieReduction_eq_specialFibreLieEquiv (hM : M.IsSmooth) (X : M.LieModule) :
    M.lieReduction X = specialFibreLieEquiv hM (1 ⊗ₜ X) := by
  rw [specialFibreLieEquiv_tmul, one_smul]

/-- Reduction of `Lie(𝒢)` onto `Lie(𝒢_𝔣)` is surjective for a smooth model. -/
theorem lieReduction_surjective (hM : M.IsSmooth) : Function.Surjective M.lieReduction := by
  intro Y
  obtain ⟨t, rfl⟩ := (specialFibreLieEquiv hM).surjective Y
  obtain ⟨X, rfl⟩ := TensorProduct.mk_surjective R M.LieModule (IsLocalRing.ResidueField R)
    Ideal.Quotient.mk_surjective t
  exact ⟨X, lieReduction_eq_specialFibreLieEquiv hM X⟩

/-- For a smooth model, the kernel of reduction is exactly `𝔪 • Lie(𝒢)`. -/
theorem ker_lieReduction (hM : M.IsSmooth) :
    LinearMap.ker M.lieReduction =
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R M.LieModule) := by
  refine le_antisymm ?_ M.smul_top_le_ker_lieReduction
  intro X hX
  have h1 : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] X = 0 := by
    rw [LinearMap.mem_ker, lieReduction_eq_specialFibreLieEquiv hM] at hX
    exact (specialFibreLieEquiv hM).map_eq_zero_iff.mp hX
  suffices key : ∀ {N : Type u} [AddCommGroup N] [Module R N] (Y : N),
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] Y = 0 →
        Y ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) from key X h1
  intro N _ _ Y hY
  let : Module (IsLocalRing.ResidueField R) (N ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) :=
    inferInstanceAs (Module (R ⧸ IsLocalRing.maximalIdeal R)
      (N ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)))
  let : IsScalarTower R (IsLocalRing.ResidueField R)
      (N ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) :=
    inferInstanceAs (IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R)
      (N ⧸ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)))
  let g := TensorProduct.AlgebraTensorModule.lift
    (((LinearMap.ringLmapEquivSelf (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)
      _).symm (Submodule.mkQ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)))).restrictScalars R)
  have hg : g ((1 : IsLocalRing.ResidueField R) ⊗ₜ Y) =
      Submodule.mkQ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) Y := by simp [g]
  rw [hY, map_zero] at hg
  exact (Submodule.Quotient.mk_eq_zero _).mp hg.symm

section Hom

variable [IsAffineHom H.X.hom] {N : IntegralModel R K H} {f : G ⟶ H}

/-- `specialFibreAlgebraBaseIso` is natural in model homomorphisms. -/
theorem Hom.specialFibreAlgebraBaseIso_naturality (φ : M.Hom N f) :
    (GroupScheme.baseChange (algebraBaseMap R (IsLocalRing.ResidueField R))).map φ.hom ≫
        N.specialFibreAlgebraBaseIso.hom =
      M.specialFibreAlgebraBaseIso.hom ≫ φ.specialFibreMap := by
  have key : ∀ (b : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
      Spec (CommRingCat.of R)) (hb : b = residueBaseMap R),
      (GroupScheme.baseChange b).map φ.hom ≫
          eqToHom (congrArg (fun c => (GroupScheme.baseChange c).obj N.group) hb) =
        eqToHom (congrArg (fun c => (GroupScheme.baseChange c).obj M.group) hb) ≫
          (GroupScheme.baseChange (residueBaseMap R)).map φ.hom := by
    intro b hb
    subst hb
    simp
  exact key _ algebraBaseMap_residueField

/-- `residueLieEquiv` intertwines the residue-field differential of a model homomorphism with
the differential of its special-fibre map. -/
theorem Hom.residueLieEquiv_naturality (φ : M.Hom N f)
    (Y : Additive (lieKernel M.group (IsLocalRing.ResidueField R))) :
    N.residueLieEquiv (Lie.targetMapLinear φ.hom (IsLocalRing.ResidueField R) Y) =
      GenericLie.map R φ.specialFibreMap (M.residueLieEquiv Y) := by
  obtain ⟨Z, rfl⟩ := (Lie.kernelBaseChangeLinearEquiv R (IsLocalRing.ResidueField R) M.group
    (IsLocalRing.ResidueField R)).surjective Y
  rw [← Lie.kernelBaseChangeLinearEquiv_target]
  simp only [residueLieEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    GenericLie.map_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (Z.toMul.val ≫ ((GroupScheme.baseChange
      (algebraBaseMap R (IsLocalRing.ResidueField R))).map φ.hom).hom.hom) ≫
        N.specialFibreAlgebraBaseIso.hom.hom.hom =
      (Z.toMul.val ≫ M.specialFibreAlgebraBaseIso.hom.hom.hom) ≫ φ.specialFibreMap.hom.hom
  rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom,
    φ.specialFibreAlgebraBaseIso_naturality]

/-- Naturality of reduction: for a model homomorphism `φ`, reduction intertwines the
differential of `φ` with the differential of its special-fibre map. -/
theorem Hom.lieReduction_naturality (φ : M.Hom N f) (X : M.LieModule) :
    N.lieReduction (Lie.targetMapLinear φ.hom (CommRingCat.of R) X) =
      GenericLie.map R φ.specialFibreMap (M.lieReduction X) := by
  rw [lieReduction_apply, lieReduction_apply, ← lieKernelTargetLinear_map,
    φ.residueLieEquiv_naturality]

end Hom

end IntegralModel

end Langlands.GroupScheme

import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.Lie.FieldExtension
import Langlands.GroupScheme.Lie.SmoothScalarExtension
import Langlands.GroupScheme.Dynamic.AdjointDeterminantModelIndependence
import Mathlib.Algebra.Module.Lattice

/-! # The Lie lattice of an integral group model

Let `R` be a domain with fraction field `K` and `M : IntegralModel R K G` a supplied integral
model of an affine group `G` over `K`. The coefficient change `R → K`, the pullback comparison
and the supplied generic isomorphism give an `R`-linear map `M.lieMap : Lie(𝒢) → Lie(G)` of
actual dual-number Lie kernels. It is injective, and its range `M.lieLattice` is an `R`-lattice
in `Lie(G)` when the model is smooth (Kaletha–Prasad, §13.3.1). Model homomorphisms carry
Lie lattices into Lie lattices. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

set_option linter.unusedVariables false in
/-- The actual Lie algebra `Lie(G) = Additive (lieKernel G K)` of a group scheme over
`Spec K`, regarded also as an `R`-module through `R → K`. This is a type synonym; its
`K`-module structure is the original one. The ring `R` is a phantom parameter: it only selects
the `R`-module structure. -/
def GenericLie (R : Type u) {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) : Type u :=
  Additive (lieKernel G K)

namespace GenericLie

variable (R : Type u) {K : Type u} [CommRing R] [Field K] [Algebra R K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]

instance : AddCommGroup (GenericLie R G) :=
  inferInstanceAs (AddCommGroup (Additive (lieKernel G K)))

instance : Module K (GenericLie R G) :=
  inferInstanceAs (Module K (Additive (lieKernel G K)))

instance : Module R (GenericLie R G) :=
  Module.compHom (GenericLie R G) (algebraMap R K)

instance : IsScalarTower R K (GenericLie R G) where
  smul_assoc r c X := by
    change (r • c) • X = algebraMap R K r • (c • X)
    rw [Algebra.smul_def, mul_smul]

theorem smul_def (r : R) (X : GenericLie R G) : r • X = algebraMap R K r • X := rfl

/-- The identity `K`-linear equivalence with the original Lie algebra. -/
def equiv : GenericLie R G ≃ₗ[K] Additive (lieKernel G K) := LinearEquiv.refl K _

variable {G} {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom]

/-- The differential `Lie.targetMapLinear f K : Lie(G) → Lie(H)` of a homomorphism
`f : G ⟶ H`, regarded as an `R`-linear map of the type synonyms. -/
def map (f : G ⟶ H) : GenericLie R G →ₗ[R] GenericLie R H :=
  (((equiv R H).symm.toLinearMap.comp (Lie.targetMapLinear f K)).comp
    (equiv R G).toLinearMap).restrictScalars R

theorem map_apply (f : G ⟶ H) (X : GenericLie R G) :
    map R f X = (equiv R H).symm (Lie.targetMapLinear f K (equiv R G X)) := rfl

end GenericLie

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- The actual generic fibre of an integral model is affine over `Spec K`. -/
instance genericFibre_isAffineHom (M : IntegralModel R K G) :
    IsAffineHom M.genericFibre.X.hom := by
  change IsAffineHom (pullback.snd M.group.X.hom (Spec.algebraMap R K))
  infer_instance

/-- The generic group of an integral model is affine over its base. This discharges the
hypothesis `[IsAffineHom G.X.hom]` of the constructions below. -/
theorem generic_isAffineHom (M : IntegralModel R K G) : IsAffineHom G.X.hom := by
  have h := Over.w M.genericIso.inv.hom.hom
  rw [← h]
  have : IsIso M.genericIso.inv.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Grp.forget _).map M.genericIso.inv)))
  infer_instance

variable [IsAffineHom G.X.hom] (M : IntegralModel R K G)

/-- The actual Lie module `Lie(𝒢)` of the integral model, over `R`. -/
abbrev LieModule : Type u := Additive (lieKernel M.group (CommRingCat.of R))

/-- The `K`-linear identification of the Lie algebra of `M.group` over `K` with `Lie(G)`:
the inverse pullback comparison followed by the differential of the generic isomorphism. -/
def genericLieEquiv :
    Additive (lieKernel M.group K) ≃ₗ[K] GenericLie R G :=
  ((Lie.kernelBaseChangeLinearEquiv R K M.group K).symm.trans
    (lieKernelLinearEquiv M.genericIso K)).trans (GenericLie.equiv R G).symm

/-- The `R`-linear map `Lie(𝒢) → Lie(G)`: change of coefficients from `R` to `K`, followed by
`genericLieEquiv`. -/
def lieMap : M.LieModule →ₗ[R] GenericLie R G where
  toFun X := M.genericLieEquiv (lieKernelMapLinear M.group (Algebra.ofId R K) X)
  map_add' X Y := by simp only [map_add]
  map_smul' r X := by
    rw [map_smulₛₗ, map_smul]
    rfl

theorem lieMap_apply (X : M.LieModule) :
    M.lieMap X = M.genericLieEquiv (lieKernelMapLinear M.group (Algebra.ofId R K) X) := rfl

/-- The Lie map of an integral model is injective; no smoothness or flatness is needed, only
injectivity of `R → K` and affineness of the model. -/
theorem lieMap_injective : Function.Injective M.lieMap := by
  intro X Y h
  rw [lieMap_apply, lieMap_apply] at h
  have h' := M.genericLieEquiv.injective h
  apply Additive.toMul.injective
  apply Subtype.ext
  have hinj : Function.Injective
      (GeneralLinear.DualNumber.coefficientAlgMap
        (R := CommRingCat.of R) (Algebra.ofId R K)) := by
    intro a b hab
    have hK := IsFractionRing.injective R K
    apply TrivSqZeroExt.ext
    · exact hK (congrArg TrivSqZeroExt.fst hab)
    · exact hK (congrArg TrivSqZeroExt.snd hab)
  exact Lie.affineMap_jointly_injective M.group _ _
    (fun a b hab => hinj (congrArg Prod.fst hab))
    (congrArg (fun Z => (Additive.toMul Z).val) h')
    (congrArg (fun Z => (Additive.toMul Z).val) h')

/-- The Lie lattice `Lie(𝒢) ⊆ Lie(G)` of the integral model. -/
def lieLattice : Submodule R (GenericLie R G) := LinearMap.range M.lieMap

theorem mem_lieLattice (Y : GenericLie R G) :
    Y ∈ M.lieLattice ↔ ∃ X : M.LieModule, M.lieMap X = Y := Iff.rfl

/-- The Lie lattice is isomorphic to the actual Lie module of the model. -/
def lieLatticeEquiv : M.LieModule ≃ₗ[R] M.lieLattice :=
  LinearEquiv.ofInjective M.lieMap M.lieMap_injective

variable {M}

/-- For a smooth model, the scalar extension `K ⊗[R] Lie(𝒢) ≃ Lie(G)`. -/
def lieBaseChangeEquiv (hM : M.IsSmooth) :
    K ⊗[R] M.LieModule ≃ₗ[K] GenericLie R G :=
  haveI : Smooth M.group.X.hom := hM
  (Lie.smoothKernelScalarExtension M.group K).trans M.genericLieEquiv

theorem lieBaseChangeEquiv_tmul (hM : M.IsSmooth) (a : K) (X : M.LieModule) :
    lieBaseChangeEquiv hM (a ⊗ₜ X) = a • M.lieMap X := by
  have : Smooth M.group.X.hom := hM
  have h := Lie.smoothKernelScalarExtension_tmul M.group K a X
  change M.genericLieEquiv (Lie.smoothKernelScalarExtension M.group K (a ⊗ₜ X)) = _
  rw [h, map_smul, lieMap_apply]

/-- KP §13.3.1 on a supplied smooth model: `Lie(𝒢)` is an `R`-lattice in `Lie(G)`. -/
theorem lieLattice_isLattice (hM : M.IsSmooth) : Submodule.IsLattice K M.lieLattice where
  fg := by
    have : Smooth M.group.X.hom := hM
    have hfin : Module.Finite R M.LieModule := Lie.finite_lieKernel_of_smooth M.group
    rw [lieLattice, LinearMap.range_eq_map]
    exact hfin.fg_top.map _
  span_eq_top := by
    rw [eq_top_iff]
    rintro Y -
    obtain ⟨t, rfl⟩ := (lieBaseChangeEquiv hM).surjective Y
    induction t using TensorProduct.inductionOn with
    | tmul a X =>
      rw [lieBaseChangeEquiv_tmul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨X, rfl⟩)
    | add s t hs ht =>
      rw [LinearEquiv.map_add]
      exact Submodule.add_mem _ hs ht

section Hom

variable [IsAffineHom H.X.hom] {N : IntegralModel R K H} {f : G ⟶ H}

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- The pullback comparison of Lie kernels commutes with differentials of model
homomorphisms. -/
theorem Hom.kernelBaseChange_symm_target (φ : M.Hom N f)
    (Z : Additive (lieKernel M.genericFibre K)) :
    (Lie.kernelBaseChangeLinearEquiv R K N.group K).symm
        (Lie.targetMapLinear φ.hom K (Lie.kernelBaseChangeLinearEquiv R K M.group K Z)) =
      Lie.targetMapLinear ((GroupScheme.baseChange (Spec.algebraMap R K)).map φ.hom) K Z := by
  rw [LinearEquiv.symm_apply_eq]
  exact congrArg Additive.ofMul (Lie.kernelBaseChangeEquiv_target φ.hom Z.toMul).symm

/-- Naturality of the Lie map: for a model homomorphism `φ` extending `f`, the differential of
`φ` on `Lie(𝒢)` corresponds to the differential of `f` on `Lie(G)`. -/
theorem Hom.lieMap_naturality (φ : M.Hom N f) (X : M.LieModule) :
    N.lieMap (Lie.targetMapLinear φ.hom (CommRingCat.of R) X) =
      GenericLie.map R f (M.lieMap X) := by
  rw [lieMap_apply, lieMap_apply, ← lieKernelTargetLinear_map]
  generalize lieKernelMapLinear M.group (Algebra.ofId R K) X = Y
  obtain ⟨Z, rfl⟩ := (Lie.kernelBaseChangeLinearEquiv R K M.group K).surjective Y
  simp only [genericLieEquiv, LinearEquiv.trans_apply, Hom.kernelBaseChange_symm_target,
    LinearEquiv.symm_apply_apply, GenericLie.map_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (Z.toMul.val ≫ ((GroupScheme.baseChange (Spec.algebraMap R K)).map φ.hom).hom.hom) ≫
      N.genericIso.hom.hom.hom = (Z.toMul.val ≫ M.genericIso.hom.hom.hom) ≫ f.hom.hom
  rw [Category.assoc, Category.assoc]
  congr 1
  exact congrArg (fun g => g.hom.hom) φ.generic_comm

/-- A model homomorphism maps the Lie lattice of the source into that of the target. -/
theorem Hom.map_lieLattice_le (φ : M.Hom N f) :
    M.lieLattice.map (GenericLie.map R f) ≤ N.lieLattice := by
  rintro _ ⟨_, ⟨X, rfl⟩, rfl⟩
  exact ⟨Lie.targetMapLinear φ.hom (CommRingCat.of R) X, φ.lieMap_naturality X⟩

end Hom

end IntegralModel

end Langlands.GroupScheme

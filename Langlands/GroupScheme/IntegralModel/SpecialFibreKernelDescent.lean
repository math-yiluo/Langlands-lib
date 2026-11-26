import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelBaseChange
import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom
import Langlands.GroupScheme.IntegralModelReduction
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.GroupScheme.Unipotent.FieldReflectionProof
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.KernelSquareTransport

/-! # Descent of smooth connected unipotent special-fibre kernels

For a model homomorphism `ψ` over a local domain `R` and a local extension
`R → A` of local domains, the special-fibre kernel of the base-changed
homomorphism is the base change of the special-fibre kernel of `ψ` along the
residue field extension. Smoothness, connectedness and unipotence descend
along field extensions, so they descend from the kernel over `A` to the
kernel over `R`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

section FieldProperties

variable {k : Type u} [Field k]

/-- The three kernel properties of KP Axiom 4.1.22(1): a smooth, connected
and unipotent group scheme over a field. -/
def IsSmoothConnectedUnipotent (X : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  Smooth X.X.hom ∧ ConnectedSpace X.X.left ∧ IsUnipotent X

/-- The three kernel properties are invariant under isomorphism. -/
theorem IsSmoothConnectedUnipotent.of_iso {X Y : GroupScheme (Spec (CommRingCat.of k))}
    (e : X ≅ Y) (h : IsSmoothConnectedUnipotent Y) : IsSmoothConnectedUnipotent X := by
  obtain ⟨hs, hc, hu⟩ := h
  refine ⟨smooth_of_over_iso ((Grp.forget _).mapIso e) hs, ?_, IsUnipotent.of_iso e hu⟩
  let eX : X.X.left ≅ Y.X.left := (Over.forget _).mapIso ((Grp.forget _).mapIso e)
  exact (Homeomorph.connectedSpace_iff (Scheme.homeoOfIso eX)).mpr hc

/-- The three kernel properties descend along a field extension. -/
theorem IsSmoothConnectedUnipotent.of_baseChange {K : Type u} [Field K] [Algebra k K]
    {X : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom X.X.hom]
    (h : IsSmoothConnectedUnipotent
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj X)) :
    IsSmoothConnectedUnipotent X := by
  obtain ⟨hs, hc, hu⟩ := h
  have hb := fieldExtension_fpqc k K
  let : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := hb.1
  let : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := hb.2.1
  let : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k K))) := hb.2.2
  exact ⟨smooth_of_baseChange _ X hs, connectedSpace_of_baseChange _ X hc,
    IsUnipotent.of_baseChange hu⟩

end FieldProperties

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

/-- The residue field extension of a local homomorphism of local rings, as a
map of spectra. -/
abbrev residueExtensionMap :
    Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶
      Spec (CommRingCat.of (IsLocalRing.ResidueField R)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)))

omit [IsDomain R] [IsDomain A] in
/-- The residue maps commute with the coefficient change. -/
theorem residueBaseMap_comp_algebraMap :
    residueBaseMap A ≫ Spec.algebraMap R A =
      residueExtensionMap (R := R) A ≫ residueBaseMap R := by
  simp only [residueBaseMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1

/-- Special-fibre kernels change base along a commutative square of bases. -/
theorem isSmoothConnectedUnipotent_kernel_of_square
    {S₀ S₁ S₃ : Scheme.{u}} {k : Type u} [Field k]
    (a : S₁ ⟶ S₀) (b : Spec (CommRingCat.of k) ⟶ S₁)
    (a' : S₃ ⟶ S₀) (b' : Spec (CommRingCat.of k) ⟶ S₃) (hab : b ≫ a = b' ≫ a')
    {X Y : GroupScheme S₀} (φ : X ⟶ Y)
    (h : IsSmoothConnectedUnipotent
      (kernel ((GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map φ)))) :
    IsSmoothConnectedUnipotent
      (kernel ((GroupScheme.baseChange b').map ((GroupScheme.baseChange a').map φ))) := by
  have h₁ : IsSmoothConnectedUnipotent (kernel ((GroupScheme.baseChange (b ≫ a)).map φ)) :=
    IsSmoothConnectedUnipotent.of_iso
      (kernelSquareIso _ _ (baseChangeCompIso a b X) (baseChangeCompIso a b Y)
        (baseChangeCompIso_hom_naturality a b φ).symm) h
  rw [hab] at h₁
  exact IsSmoothConnectedUnipotent.of_iso
    (kernelSquareIso _ _ (baseChangeCompIso a' b' X) (baseChangeCompIso a' b' Y)
      (baseChangeCompIso_hom_naturality a' b' φ).symm).symm h₁

/-- **Descent of the special-fibre kernel properties.** If the special-fibre
kernel of the coefficient change of `ψ` along a local extension `R → A` is
smooth, connected and unipotent, then so is the special-fibre kernel of `ψ`. -/
theorem Hom.isSmoothConnectedUnipotent_kernel_of_baseChangeCoefficients
    (ψ : M.Hom N f)
    (h : IsSmoothConnectedUnipotent (kernel (ψ.baseChangeCoefficients A L).specialFibreMap)) :
    IsSmoothConnectedUnipotent (kernel ψ.specialFibreMap) :=
  ψ.specialFibreKernel_properties_of_baseChange A L h

/-- Reindex a model homomorphism along an equality of generic morphisms. -/
def Hom.ofGenericEq (ψ : M.Hom N f) {f' : G ⟶ H} (h : f = f') : M.Hom N f' where
  hom := ψ.hom
  generic_comm := h ▸ ψ.generic_comm

omit [IsLocalRing R] in
/-- Reindexing does not change the underlying integral homomorphism. -/
@[simp]
theorem Hom.ofGenericEq_hom (ψ : M.Hom N f) {f' : G ⟶ H} (h : f = f') :
    (ψ.ofGenericEq h).hom = ψ.hom := rfl

section Unramified

open Langlands.LocalGalois.Separable GaloisPointComparison
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G₀ : GroupScheme (Spec (CommRingCat.of F))} {M₀ N₀ : IntegralModel ↥𝒪[F] F G₀}

local instance specialFibreKernelDescentAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance specialFibreKernelDescentScalarTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance specialFibreKernelDescentLocalHom :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  haveI : IsLocalHom (algebraMap F (inertiaFixedField F)) :=
    isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- **Descent from the maximal unramified integers.** If every model
homomorphism with identity generic fibre between the base changes of `M₀` and
`N₀` to the maximal unramified integers has a smooth, connected and unipotent
special-fibre kernel, then so does every such homomorphism `M₀ → N₀`. -/
theorem Hom.isSmoothConnectedUnipotent_kernel_of_baseChangeUnramified
    (ψ : M₀.Hom N₀ (𝟙 G₀))
    (h : ∀ ψ' : M₀.baseChangeUnramified.Hom N₀.baseChangeUnramified (𝟙 _),
      IsSmoothConnectedUnipotent (kernel ψ'.specialFibreMap)) :
    IsSmoothConnectedUnipotent (kernel ψ.specialFibreMap) :=
  ψ.isSmoothConnectedUnipotent_kernel_of_baseChangeCoefficients
    (fixedFieldIntegers F) (inertiaFixedField F)
    (h ((ψ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)).ofGenericEq
      (CategoryTheory.Functor.map_id _ _)))

end Unramified

end IntegralModel

end Langlands.GroupScheme

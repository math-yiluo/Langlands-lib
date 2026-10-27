import Langlands.Algebra.LocalApproximationFlatnessPropagationStatement
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.BaseChange

/-! # Proof of forward propagation of component flatness -/

open scoped TensorProduct

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra

/-- Localizing a module over an auxiliary algebra preserves flatness over a fixed base ring. -/
theorem flat_of_isLocalizedModule_of_flat {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {P Q : Type*} [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    [AddCommGroup Q] [Module R Q] [Module A Q] [IsScalarTower R A Q]
    (T : Submonoid A) (g : P →ₗ[A] Q) [IsLocalizedModule T g] [Module.Flat R P] :
    Module.Flat R Q := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro N _ _ N'
  rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := A),
    ← IsLocalizedModule.map_lTensor (S := T) (g := g) (f := N'.subtype)]
  exact IsLocalizedModule.map_injective _ _ _ _
    (Module.Flat.lTensor_preserves_injective_linearMap _ N'.injective_subtype)

namespace LocalModuleSystem

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  {M : Type uM} [AddCommGroup M] [Module S M]

/-- Flatness of a component over its base ring propagates along a transition which is a prime
localization and whose module base-change map is bijective. -/
theorem flat_of_isPrimeLocalization_of_bijective
    {D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S}
    (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M) {i j : ι} (h : i ≤ j)
    (hloc : D.IsPrimeLocalization h) (hbij : Function.Bijective (E.moduleBaseChangeMap h)) :
    letI : Module (D.base i) (E.obj i) :=
      Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i))
    letI : Module (D.base j) (E.obj j) :=
      Module.compHom (E.obj j) (algebraMap (D.base j) (D.alg j))
    Module.Flat (D.base i) (E.obj i) → Module.Flat (D.base j) (E.obj j) := by
  intro hflat
  let instI : Module (D.base i) (E.obj i) :=
    Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i))
  let instJ : Module (D.base j) (E.obj j) :=
    Module.compHom (E.obj j) (algebraMap (D.base j) (D.alg j))
  -- The rings and algebra structures of the transition.
  let algBase : Algebra (D.base i) (D.base j) := (D.baseMap i j h).toAlgebra
  let algAlg : Algebra (D.alg i) (D.alg j) := (D.algMap i j h).toAlgebra
  let algRight : Algebra (D.base j) (D.RingBaseChange h) :=
    Algebra.TensorProduct.rightAlgebra
  let algB : Algebra (D.RingBaseChange h) (D.alg j) := (D.ringBaseChangeMap h).toAlgebra
  obtain ⟨p, hp, hlocp⟩ := hloc
  -- Scalar towers on the base and target rings.
  have towerI : IsScalarTower (D.base i) (D.alg i) (E.obj i) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have towerAlg : IsScalarTower (D.alg i) (D.RingBaseChange h) (D.alg j) :=
    IsScalarTower.of_algebraMap_eq fun s ↦ by
      change D.algMap i j h s = D.ringBaseChangeMap h (s ⊗ₜ[D.base i] 1)
      rw [LocalAlgebraSystem.ringBaseChangeMap_tmul, map_one, mul_one]
  -- The three restricted actions on the target component.
  let modAlg : Module (D.alg i) (E.obj j) := Module.compHom (E.obj j) (D.algMap i j h)
  let modB : Module (D.RingBaseChange h) (E.obj j) :=
    Module.compHom (E.obj j) (D.ringBaseChangeMap h)
  have : IsScalarTower (D.alg i) (D.alg j) (E.obj j) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower (D.RingBaseChange h) (D.alg j) (E.obj j) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower (D.alg i) (D.RingBaseChange h) (E.obj j) :=
    IsScalarTower.of_algebraMap_smul fun s m ↦ by
      change D.ringBaseChangeMap h (s ⊗ₜ[D.base i] 1) • m = D.algMap i j h s • m
      rw [LocalAlgebraSystem.ringBaseChangeMap_tmul, map_one, mul_one]
  have : IsScalarTower (D.base j) (D.RingBaseChange h) (E.obj j) :=
    IsScalarTower.of_algebraMap_smul fun r m ↦ by
      change D.ringBaseChangeMap h (1 ⊗ₜ[D.base i] r) • m =
        algebraMap (D.base j) (D.alg j) r • m
      rw [LocalAlgebraSystem.ringBaseChangeMap_tmul, map_one, one_mul]
  -- The transition as a semilinear map, and its extension to `P = A ⊗[Sᵢ] Mᵢ`.
  let F : E.obj i →ₗ[D.alg i] E.obj j :=
    { (E.map i j h).toAddMonoidHom with
      map_smul' := fun r m ↦ (E.map i j h).map_smulₛₗ r m }
  let g : D.RingBaseChange h ⊗[D.alg i] E.obj i →ₗ[D.RingBaseChange h] E.obj j :=
    F.liftBaseChange (D.RingBaseChange h)
  have hc : IsBaseChange (D.alg j)
      ((g : D.RingBaseChange h ⊗[D.alg i] E.obj i →ₗ[D.alg i] E.obj j) ∘ₗ
        TensorProduct.mk (D.alg i) (D.RingBaseChange h) (E.obj i) 1) := by
    refine IsBaseChange.of_equiv (LinearEquiv.ofBijective (E.moduleBaseChangeMap h) hbij)
      fun m ↦ ?_
    change E.moduleBaseChangeMap h (1 ⊗ₜ m) = g (1 ⊗ₜ m)
    rw [moduleBaseChangeMap_tmul, LinearMap.liftBaseChange_tmul, one_smul, one_smul]
    rfl
  have hg : IsBaseChange (D.alg j) g :=
    IsBaseChange.of_comp (TensorProduct.isBaseChange (D.alg i) (E.obj i) (D.RingBaseChange h)) hc
  have : IsLocalizedModule p.primeCompl g :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl (D.alg j) g).mpr hg
  -- The source `P` is flat over `Rⱼ`, being identified with `Rⱼ ⊗[Rᵢ] Mᵢ`.
  have : Module.Flat (D.base j) (D.RingBaseChange h ⊗[D.alg i] E.obj i) :=
    Module.Flat.of_linearEquiv
      (Algebra.IsPushout.cancelBaseChange (D.base i) (D.base j) (D.alg i) (D.RingBaseChange h)
        (E.obj i))
  exact flat_of_isLocalizedModule_of_flat p.primeCompl g

end LocalModuleSystem

/-- Forward propagation of component flatness in local approximation systems. -/
theorem localApproximationFlatnessPropagation :
    LocalApproximationFlatnessPropagationStatement.{uI, uA, uB, uN, uR, uS, uM} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E _ _ h hloc hbij ↦
    LocalModuleSystem.flat_of_isPrimeLocalization_of_bijective E h hloc hbij

end Langlands.Algebra

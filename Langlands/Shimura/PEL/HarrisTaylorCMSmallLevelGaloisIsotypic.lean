import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisTower
import Langlands.Shimura.ScalarExtensionFixedVectors
import Langlands.Shimura.ContinuousIsotypicGaloisRepresentation

/-! # Isotypic parts and multiplicity spaces of towers over sufficiently small CM levels, and
their Galois representations

For a level-trivial presheaf `H` of `K`-modules with an action of `Gal(F̄/F)` on the sufficiently
small CM levels, and a field extension `M` of `K`, this module extends the scalars of the tower
`colim_U H(U)` to `M`. It defines the isotypic part of a representation `τ` of `G(A_f)` over `M`,
its fixed vectors at a level, the multiplicity space and the Hecke multiplicity space at a level,
each with its Galois action. It identifies the fixed vectors at the level of `U` with
`M ⊗[K] H(U)` under the fixed-vector comparison. When `H(U)` is finite-dimensional with
continuous orbit maps, these spaces are continuous Galois representations, with Euler
polynomials at places where `H(U)` is unramified. See `HarrisTaylorCMSmallLevelGaloisIsotypic.md`.
-/

noncomputable section

universe uM uV

set_option autoImplicit false

open CategoryTheory Opposite

namespace Langlands.Shimura.SmallLevelGaloisTower

open CompactOpenLevel RestrictedLevelColimit
open Langlands.Shimura.LevelHecke (fixedVectorsActionFunctor LevelHeckeAlgebra)
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Shimura.HeckeMultiplicityGaloisRepresentation (heckeMultiplicityActionFunctor)
open Langlands.Shimura.ScalarExtensionFixedVectors
open Langlands.Shimura.ContinuousIsotypicGaloisRepresentation
open Langlands.Shimura.ContinuousGaloisAction (HasContinuousOrbits)
open Langlands.GaloisRepresentation (Objects ClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius)

variable {B : Type} [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] {σ : AlgebraInvolution ℚ B}
  {F : Type} [Field F] {K : Type} [Field K] (M : Type uM) [Field M] [Algebra K M]
  (H : σ.SmallLevelCategoryᵒᵖ ⥤ Action (ModuleCat.{0} K) (Field.absoluteGaloisGroup F))
  (hH : IsLevelTrivial H)

/-! ## Extension of scalars, isotypic parts and multiplicity spaces -/

section Spaces

/-- The tower `colim_U H(U)` with scalars extended to `M`: `M ⊗[K] colim_U H(U)`, a smooth
representation of `G(A_f)` over `M` with the commuting action of `Gal(F̄/F)`. -/
abbrev towerExtendScalars :=
  (extendScalarsActionFunctor M (Field.absoluteGaloisGroup F)).obj (towerAction H hH)

variable {V : Type uV} [AddCommGroup V] [Module M V] (τ : Representation M σ.FiniteAdelicPoints V)

/-- The `τ`-isotypic part of `M ⊗[K] colim_U H(U)`, with the restricted actions of `G(A_f)` and
of `Gal(F̄/F)`. -/
abbrev towerIsotypic :=
  (isotypicActionFunctor τ (Field.absoluteGaloisGroup F)).obj (towerExtendScalars M H hH)

/-- The vectors of the `τ`-isotypic part fixed by the ordinary level `inverseOpposite U`, with
the action of `Gal(F̄/F)`. -/
abbrev towerIsotypicFixedVectors (U : σ.SmallLevelCategory) :=
  (fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) (inverseOpposite U.obj).subgroup).obj
    (towerIsotypic M H hH τ)

/-- The multiplicity space `Hom_{G(A_f)}(τ, M ⊗[K] colim_U H(U))`, with `Gal(F̄/F)` acting by
composition. -/
abbrev towerMultiplicity :=
  (multiplicityActionFunctor τ (Field.absoluteGaloisGroup F)).obj (towerExtendScalars M H hH)

/-- The Hecke multiplicity space `Hom_{H(K)}(τ^K, (M ⊗[K] colim_U H(U))^K)` at the ordinary level
`K = inverseOpposite U`, for the Hecke algebra `H(K)` of `K` over `M`, with `Gal(F̄/F)` acting by
composition. -/
abbrev towerHeckeMultiplicity (U : σ.SmallLevelCategory) :=
  (heckeMultiplicityActionFunctor (inverseOpposite U.obj).subgroup
      (fixedVectors τ (inverseOpposite U.obj).subgroup) (Field.absoluteGaloisGroup F)).obj
    (towerExtendScalars M H hH)

/-- The evaluation map `V ⊗ Hom_{G(A_f)}(τ, M ⊗[K] colim_U H(U)) → (M ⊗[K] colim_U H(U))[τ]` is
surjective. -/
theorem towerIsotypicEvaluation_surjective :
    Function.Surjective (isotypicEvaluation τ (towerExtendScalars M H hH).V) :=
  isotypicEvaluation_surjective τ _

/-- The evaluation map is equivariant for `Gal(F̄/F)`, acting on the multiplicity space by
composition and on the isotypic part by restriction. -/
theorem towerIsotypicEvaluation_galois (γ : Field.absoluteGaloisGroup F) :
    isotypicEvaluation τ (towerExtendScalars M H hH).V ∘ₗ
        LinearMap.lTensor V
          (multiplicityRepresentation τ _ (towerExtendScalars M H hH) γ) =
      isotypicGaloisRepresentation τ _ (towerExtendScalars M H hH) γ ∘ₗ
        isotypicEvaluation τ (towerExtendScalars M H hH).V :=
  isotypicEvaluation_galois τ _ _ γ

end Spaces

/-! ## Fixed vectors at a level -/

section Level

variable {H hH}

/-- The leg of level `U` commutes with the Galois actions. -/
theorem towerFixedLeg_comm (U : σ.SmallLevelCategory) (g : Field.absoluteGaloisGroup F)
    (x : (H.obj (op U)).V) :
    (towerFixedLeg H hH U).hom.hom (((H.obj (op U)).ρ g).hom x) =
      (((fixedVectorsActionFunctor K (Field.absoluteGaloisGroup F)
        (inverseOpposite U.obj).subgroup).obj (towerAction H hH)).ρ g).hom
          ((towerFixedLeg H hH U).hom.hom x) :=
  congrArg (fun φ => φ.hom x) ((towerFixedLeg H hH U).comm g)

/-- Under the fixed-vector comparison, the leg of level `U` is surjective onto the vectors fixed
by `inverseOpposite U`. -/
theorem towerFixedLeg_surjective (h : TowerFixedVectorComparison H) (U : σ.SmallLevelCategory) :
    Function.Surjective (towerFixedLeg H hH U).hom.hom := by
  intro y
  refine ⟨(towerFixedLegIso H hH h U).inv.hom.hom y, ?_⟩
  have e := congrArg (fun φ => φ.hom.hom y) (towerFixedLegIso H hH h U).inv_hom_id
  exact e

/-- If `H(U)` is finite-dimensional, so are the vectors of the tower fixed by
`inverseOpposite U`, under the fixed-vector comparison. -/
theorem finite_towerFixedVectors (h : TowerFixedVectorComparison H) (U : σ.SmallLevelCategory)
    [Module.Finite K (H.obj (op U)).V] :
    Module.Finite K
      (fixedVectors (towerAction H hH).V.representation (inverseOpposite U.obj).subgroup) :=
  Module.Finite.of_surjective (towerFixedLeg H hH U).hom.hom (towerFixedLeg_surjective h U)

/-- If the Galois action on `H(U)` has continuous orbit maps, so has the Galois action on the
vectors of the tower fixed by `inverseOpposite U`, under the fixed-vector comparison. -/
theorem hasContinuousOrbits_towerFixedVectors [TopologicalSpace K]
    (h : TowerFixedVectorComparison H) (U : σ.SmallLevelCategory)
    (hU : HasContinuousOrbits (H.obj (op U))) :
    HasContinuousOrbits ((fixedVectorsActionFunctor K (Field.absoluteGaloisGroup F)
      (inverseOpposite U.obj).subgroup).obj (towerAction H hH)) :=
  ContinuousGaloisAction.hasContinuousOrbits_of_surjective (towerFixedLeg H hH U).hom.hom
    (towerFixedLeg_comm U) (towerFixedLeg_surjective h U) hU

/-- If the Galois action on `H(U)` is unramified at `v` along `ι`, so is the Galois action on the
vectors of the tower fixed by `inverseOpposite U`, under the fixed-vector comparison. -/
theorem isUnramifiedAlong_towerFixedVectors [NumberField F] {v : Global.FinitePlace F}
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v)}
    (h : TowerFixedVectorComparison H) (U : σ.SmallLevelCategory)
    (hu : IsUnramifiedAt (ModuleCat.{0} K) v (H.obj (op U))) :
    IsUnramifiedAlong (ModuleCat.{0} K) v ((fixedVectorsActionFunctor K
      (Field.absoluteGaloisGroup F) (inverseOpposite U.obj).subgroup).obj (towerAction H hH)) ι :=
  ContinuousGaloisAction.isUnramifiedAlong_of_surjective (towerFixedLeg H hH U).hom.hom
    (towerFixedLeg_comm U) (towerFixedLeg_surjective h U)
    ((DecompositionGroupAction.isUnramifiedAt_iff_along _ ι).1 hu)

/-- If `H(U)` is finite-dimensional over `K`, the vectors of `M ⊗[K] colim_U H(U)` fixed by
`inverseOpposite U` are finite-dimensional over `M`, under the fixed-vector comparison. -/
theorem finite_towerExtendScalarsFixedVectors (h : TowerFixedVectorComparison H)
    (U : σ.SmallLevelCategory) [Module.Finite K (H.obj (op U)).V] :
    Module.Finite M (fixedVectors (towerExtendScalars M H hH).V.representation
      (inverseOpposite U.obj).subgroup) :=
  haveI := finite_towerFixedVectors h U
  finite_fixedVectors_extendScalars M _ (towerAction H hH) _

/-- If the Galois action on `H(U)` has continuous orbit maps and `K → M` is continuous, the
Galois action on the vectors of `M ⊗[K] colim_U H(U)` fixed by `inverseOpposite U` has
continuous orbit maps, under the fixed-vector comparison. -/
theorem hasContinuousOrbits_towerExtendScalarsFixedVectors [TopologicalSpace K]
    [TopologicalSpace M] (hKM : Continuous (algebraMap K M)) (h : TowerFixedVectorComparison H)
    (U : σ.SmallLevelCategory) (hU : HasContinuousOrbits (H.obj (op U))) :
    HasContinuousOrbits ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F)
      (inverseOpposite U.obj).subgroup).obj (towerExtendScalars M H hH)) :=
  hasContinuousOrbits_fixedVectors_extendScalars M (towerAction H hH) _ hKM
    (hasContinuousOrbits_towerFixedVectors h U hU)

/-- If the Galois action on `H(U)` is unramified at `v`, the Galois action on the vectors of
`M ⊗[K] colim_U H(U)` fixed by `inverseOpposite U` is unramified at `v` along every `ι`, under
the fixed-vector comparison. -/
theorem isUnramifiedAlong_towerExtendScalarsFixedVectors [NumberField F]
    {v : Global.FinitePlace F} (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))
    (h : TowerFixedVectorComparison H) (U : σ.SmallLevelCategory)
    (hu : IsUnramifiedAt (ModuleCat.{0} K) v (H.obj (op U))) :
    IsUnramifiedAlong (ModuleCat.{uM} M) v ((fixedVectorsActionFunctor M
      (Field.absoluteGaloisGroup F) (inverseOpposite U.obj).subgroup).obj
        (towerExtendScalars M H hH)) ι :=
  isUnramifiedAlong_fixedVectors_extendScalars M (towerAction H hH) _
    (isUnramifiedAlong_towerFixedVectors h U hu)

/-- Extension of scalars from `K` to `M` of an isomorphism of Galois actions. -/
def baseChangeActionMapIso {A B : Action (ModuleCat.{0} K) (Field.absoluteGaloisGroup F)}
    (e : A ≅ B) :
    LatticeGaloisRepresentation.baseChangeAction (L := M) A ≅
      LatticeGaloisRepresentation.baseChangeAction (L := M) B :=
  let e₀ : A.V ≃ₗ[K] B.V := ((Action.forget _ _).mapIso e).toLinearEquiv
  Action.mkIso (LinearEquiv.baseChange K M A.V B.V e₀).toModuleIso fun g => by
    apply ModuleCat.hom_ext
    change (LinearEquiv.baseChange K M A.V B.V e₀).toLinearMap ∘ₗ (A.ρ g).hom.baseChange M =
      (B.ρ g).hom.baseChange M ∘ₗ (LinearEquiv.baseChange K M A.V B.V e₀).toLinearMap
    refine TensorProduct.AlgebraTensorModule.ext fun a x => ?_
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      LinearEquiv.baseChange_tmul]
    congr 1
    exact congrArg (fun φ => φ.hom x) (e.hom.comm g)

/-- Under the fixed-vector comparison, the vectors of `M ⊗[K] colim_U H(U)` fixed by
`inverseOpposite U` are isomorphic, as Galois actions, to `M ⊗[K] H(U)`. -/
def towerExtendScalarsFixedVectorsIso (h : TowerFixedVectorComparison H)
    (U : σ.SmallLevelCategory) :
    LatticeGaloisRepresentation.baseChangeAction (L := M) (H.obj (op U)) ≅
      (fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F)
        (inverseOpposite U.obj).subgroup).obj (towerExtendScalars M H hH) :=
  baseChangeActionMapIso M (towerFixedLegIso H hH h U) ≪≫
    fixedVectorsBaseChangeIso M (towerAction H hH) _

end Level

/-! ## Galois representations -/

section Objects

variable {H} [TopologicalSpace K] [TopologicalSpace M] [IsTopologicalRing M]
  (hKM : Continuous (algebraMap K M)) (h : TowerFixedVectorComparison H)
  (U : σ.SmallLevelCategory) (hU : HasContinuousOrbits (H.obj (op U)))
  {V : Type uV} [AddCommGroup V] [Module M V] (τ : Representation M σ.FiniteAdelicPoints V)

/-- The vectors of the `τ`-isotypic part of `M ⊗[K] colim_U H(U)` fixed by `inverseOpposite U`,
as a continuous Galois representation, when `H(U)` is finite-dimensional with continuous orbit
maps and the fixed-vector comparison holds. -/
def towerIsotypicFixedVectorsObjects [Module.Finite K (H.obj (op U)).V] : Objects F M :=
  haveI := finite_towerExtendScalarsFixedVectors M h U
  isotypicFixedVectorsObjects τ (inverseOpposite U.obj).subgroup (towerExtendScalars M H hH)
    (hasContinuousOrbits_towerExtendScalarsFixedVectors M hKM h U hU)

/-- A Galois element acts on a fixed vector of the isotypic part by its action on
`M ⊗[K] colim_U H(U)`. -/
theorem coe_towerIsotypicFixedVectorsObjects_representation_apply
    [Module.Finite K (H.obj (op U)).V] (g : Field.absoluteGaloisGroup F)
    (x : fixedVectors (isotypicObj τ (towerExtendScalars M H hH).V).representation
      (inverseOpposite U.obj).subgroup) :
    ((towerIsotypicFixedVectorsObjects M hH hKM h U hU τ).val.representation g x).1.1 =
      SmoothRep.hom ((towerExtendScalars M H hH).ρ g) x.1.1 :=
  haveI := finite_towerExtendScalarsFixedVectors M h U
  coe_isotypicFixedVectorsObjects_representation_apply τ _ _ _ g x

/-- If `H(U)` is unramified at `v`, the Galois representation on the fixed vectors of the
isotypic part has as Euler polynomial at `v` the reversed characteristic polynomial of its
geometric Frobenius endomorphism along any `ι`. -/
theorem hasEulerPolynomialAt_towerIsotypicFixedVectorsObjects [NumberField F]
    [Module.Finite K (H.obj (op U)).V]
    {v : Global.FinitePlace F} (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))
    (hu : IsUnramifiedAt (ModuleCat.{0} K) v (H.obj (op U))) :
    haveI := finite_towerExtendScalarsFixedVectors M h U
    HasEulerPolynomialAt (towerIsotypicFixedVectorsObjects M hH hKM h U hU τ) v
      (geometricFrobenius (ModuleCat.{uM} M) v (towerIsotypicFixedVectors M H hH τ U)
        ι).hom.charpoly.reverse :=
  haveI := finite_towerExtendScalarsFixedVectors M h U
  hasEulerPolynomialAt_isotypicFixedVectorsObjects τ _ _ _
    (isUnramifiedAlong_towerExtendScalarsFixedVectors M ι h U hu)

/-- The multiplicity space `Hom_{G(A_f)}(τ, M ⊗[K] colim_U H(U))`, when finite-dimensional, as a
continuous Galois representation, for `τ` spanned by the translates of its vectors fixed by
`inverseOpposite U`. -/
def towerMultiplicityObjects
    (hgen : Submodule.span M (⋃ g : σ.FiniteAdelicPoints,
      τ g '' (fixedVectors τ (inverseOpposite U.obj).subgroup : Set V)) = ⊤)
    [Module.Finite M (τ.IntertwiningMap (towerExtendScalars M H hH).V.representation)] :
    Objects F M :=
  multiplicityObjects τ (inverseOpposite U.obj).subgroup (towerExtendScalars M H hH) hgen
    (hasContinuousOrbits_towerExtendScalarsFixedVectors M hKM h U hU)

/-- A Galois element acts on an intertwining map by composition. -/
theorem towerMultiplicityObjects_representation_apply
    (hgen : Submodule.span M (⋃ g : σ.FiniteAdelicPoints,
      τ g '' (fixedVectors τ (inverseOpposite U.obj).subgroup : Set V)) = ⊤)
    [Module.Finite M (τ.IntertwiningMap (towerExtendScalars M H hH).V.representation)]
    (g : Field.absoluteGaloisGroup F) :
    (towerMultiplicityObjects M hH hKM h U hU τ hgen).val.representation g =
      ((towerMultiplicity M H hH τ).ρ g).hom :=
  rfl

/-- If `H(U)` is unramified at `v`, the Galois representation on the multiplicity space has as
Euler polynomial at `v` the reversed characteristic polynomial of its geometric Frobenius
endomorphism along any `ι`. -/
theorem hasEulerPolynomialAt_towerMultiplicityObjects [NumberField F]
    {v : Global.FinitePlace F} (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))
    (hgen : Submodule.span M (⋃ g : σ.FiniteAdelicPoints,
      τ g '' (fixedVectors τ (inverseOpposite U.obj).subgroup : Set V)) = ⊤)
    [Module.Finite M (τ.IntertwiningMap (towerExtendScalars M H hH).V.representation)]
    (hu : IsUnramifiedAt (ModuleCat.{0} K) v (H.obj (op U))) :
    HasEulerPolynomialAt (towerMultiplicityObjects M hH hKM h U hU τ hgen) v
      (geometricFrobenius (ModuleCat.{max uV uM} M) v (towerMultiplicity M H hH τ)
        ι).hom.charpoly.reverse :=
  hasEulerPolynomialAt_multiplicityObjects τ _ _ hgen _
    (isUnramifiedAlong_towerExtendScalarsFixedVectors M ι h U hu)

/-- The Hecke multiplicity space `Hom_{H(K)}(τ^K, (M ⊗[K] colim_U H(U))^K)` at
`K = inverseOpposite U`, when finite-dimensional, as a continuous Galois representation. -/
def towerHeckeMultiplicityObjects
    [Module.Finite M (fixedVectors τ (inverseOpposite U.obj).subgroup →ₗ[LevelHeckeAlgebra M
      (inverseOpposite U.obj).subgroup] fixedVectors (towerExtendScalars M H hH).V.representation
        (inverseOpposite U.obj).subgroup)] :
    Objects F M :=
  heckeMultiplicityContinuousObjects (inverseOpposite U.obj).subgroup
    (fixedVectors τ (inverseOpposite U.obj).subgroup) (towerExtendScalars M H hH)
    (hasContinuousOrbits_towerExtendScalarsFixedVectors M hKM h U hU)

/-- A Galois element acts on a Hecke-linear map by composition. -/
theorem towerHeckeMultiplicityObjects_representation_apply
    [Module.Finite M (fixedVectors τ (inverseOpposite U.obj).subgroup →ₗ[LevelHeckeAlgebra M
      (inverseOpposite U.obj).subgroup] fixedVectors (towerExtendScalars M H hH).V.representation
        (inverseOpposite U.obj).subgroup)]
    (g : Field.absoluteGaloisGroup F) :
    (towerHeckeMultiplicityObjects M hH hKM h U hU τ).val.representation g =
      ((towerHeckeMultiplicity M H hH τ U).ρ g).hom :=
  rfl

/-- If `H(U)` is unramified at `v`, the Galois representation on the Hecke multiplicity space
has as Euler polynomial at `v` the reversed characteristic polynomial of its geometric Frobenius
endomorphism along any `ι`. -/
theorem hasEulerPolynomialAt_towerHeckeMultiplicityObjects [NumberField F]
    {v : Global.FinitePlace F} (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))
    [Module.Finite M (fixedVectors τ (inverseOpposite U.obj).subgroup →ₗ[LevelHeckeAlgebra M
      (inverseOpposite U.obj).subgroup] fixedVectors (towerExtendScalars M H hH).V.representation
        (inverseOpposite U.obj).subgroup)]
    (hu : IsUnramifiedAt (ModuleCat.{0} K) v (H.obj (op U))) :
    HasEulerPolynomialAt (towerHeckeMultiplicityObjects M hH hKM h U hU τ) v
      (geometricFrobenius (ModuleCat.{max uV uM} M) v (towerHeckeMultiplicity M H hH τ U)
        ι).hom.charpoly.reverse :=
  hasEulerPolynomialAt_heckeMultiplicityContinuousObjects _ _ _ _
    (isUnramifiedAlong_towerExtendScalarsFixedVectors M ι h U hu)

end Objects

end Langlands.Shimura.SmallLevelGaloisTower

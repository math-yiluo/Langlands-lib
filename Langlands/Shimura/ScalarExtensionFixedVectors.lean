import Langlands.Shimura.ContinuousOrbitTransfer
import Langlands.Shimura.LevelHeckeAction
import Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension

/-! # Fixed vectors commute with extension of scalars

For a field extension `M` of `K`, extension of scalars `X ↦ M ⊗[K] X` of smooth representations
of a group `G` carrying a commuting action of a group `Γ`, and a subgroup `H` of `G`, the natural
map `M ⊗[K] X^H → (M ⊗[K] X)^H` is a linear equivalence commuting with `Γ`. For
`Γ = Gal(F̄/F)` it is an isomorphism of Galois actions, so finiteness, continuity of orbits and
unramifiedness of the Galois action on `X^H` pass to `(M ⊗[K] X)^H`. See
`ScalarExtensionFixedVectors.md`.
-/

noncomputable section

universe uF uK uM uG uV uΓ

set_option autoImplicit false

namespace Langlands.Shimura.ScalarExtensionFixedVectors

open CategoryTheory TensorProduct
open Langlands.Cohomology (smoothRepExtendScalars tmul_mem_fixedVectors_baseChangeRepresentation)
open Langlands.Shimura.LevelHecke (fixedVectorsActionFunctor)
open Langlands.Shimura.ContinuousGaloisAction (HasContinuousOrbits)
open Langlands.GaloisRepresentation (ClosureEmbedding)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAlong IsUnramifiedAt)

/-! ## Extension of scalars with a commuting action -/

section Extension

variable {K : Type uK} [Field K] (M : Type uM) [Field M] [Algebra K M]
  {G : Type uG} [Group G] [TopologicalSpace G] (Γ : Type uΓ) [Group Γ]

/-- Extension of scalars from `K` to `M` of smooth representations of `G` with a commuting action
of `Γ`: `X ↦ M ⊗[K] X`, with `G` and `Γ` acting on the second factor. -/
def extendScalarsActionFunctor :
    Action (SmoothRep.{uK, uG, uV} K G) Γ ⥤ Action (SmoothRep.{uM, uG, max uM uV} M G) Γ :=
  (smoothRepExtendScalars.{uV} K M G).mapAction Γ

variable (X : Action (SmoothRep.{uK, uG, uV} K G) Γ)

theorem extendScalarsActionFunctor_obj_V :
    ((extendScalarsActionFunctor M Γ).obj X).V = (smoothRepExtendScalars K M G).obj X.V :=
  rfl

@[simp] theorem extendScalarsActionFunctor_obj_representation_tmul (g : G) (m : M) (x : X.V) :
    ((extendScalarsActionFunctor M Γ).obj X).V.representation g (m ⊗ₜ[K] x) =
      m ⊗ₜ[K] X.V.representation g x :=
  rfl

@[simp] theorem extendScalarsActionFunctor_obj_ρ_tmul (γ : Γ) (m : M) (x : X.V) :
    SmoothRep.hom (((extendScalarsActionFunctor M Γ).obj X).ρ γ) (m ⊗ₜ[K] x) =
      m ⊗ₜ[K] SmoothRep.hom (X.ρ γ) x :=
  rfl

/-! ## Fixed vectors -/

variable (H : Subgroup G)

/-- The base change `M ⊗[K] X^H → M ⊗[K] X` of the inclusion of the `H`-fixed vectors takes values
in the `H`-fixed vectors of `M ⊗[K] X`. -/
theorem baseChange_subtype_mem_fixedVectors (t : M ⊗[K] fixedVectors X.V.representation H) :
    (fixedVectors X.V.representation H).subtype.baseChange M t ∈
      fixedVectors (Cohomology.baseChangeRepresentation M X.V.representation) H := by
  induction t using TensorProduct.inductionOn with
  | tmul m x => exact tmul_mem_fixedVectors_baseChangeRepresentation M X.V.representation H m x.2
  | add s t hs ht => rw [map_add]; exact add_mem hs ht

/-- The natural map `M ⊗[K] X^H → (M ⊗[K] X)^H`, `m ⊗ x ↦ m ⊗ x`. -/
def fixedVectorsBaseChange :
    M ⊗[K] fixedVectors X.V.representation H →ₗ[M]
      fixedVectors ((extendScalarsActionFunctor M Γ).obj X).V.representation H :=
  LinearMap.codRestrict _ ((fixedVectors X.V.representation H).subtype.baseChange M)
    (baseChange_subtype_mem_fixedVectors M Γ X H)

theorem coe_fixedVectorsBaseChange (t : M ⊗[K] fixedVectors X.V.representation H) :
    ((fixedVectorsBaseChange M Γ X H t : ((extendScalarsActionFunctor M Γ).obj X).V) :
        M ⊗[K] X.V) =
      (fixedVectors X.V.representation H).subtype.baseChange M t :=
  rfl

/-- The map `M ⊗[K] X^H → (M ⊗[K] X)^H` is injective, since `M` is flat over `K`. -/
theorem fixedVectorsBaseChange_injective :
    Function.Injective (fixedVectorsBaseChange M Γ X H) := by
  intro s t hst
  have hinj : Function.Injective ((fixedVectors X.V.representation H).subtype.baseChange M) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  exact hinj (congrArg Subtype.val hst)

/-- The map `M ⊗[K] X^H → (M ⊗[K] X)^H` is surjective: in a basis of `M` over `K`, the
coefficients of an `H`-fixed vector of `M ⊗[K] X` are `H`-fixed. -/
theorem fixedVectorsBaseChange_surjective :
    Function.Surjective (fixedVectorsBaseChange M Γ X H) := by
  classical
  rintro ⟨t, ht⟩
  let t' : M ⊗[K] X.V := t
  have ht' : ∀ h : H, (X.V.representation (h : G)).baseChange M t' = t' := fun h => ht h
  let b := Module.Free.chooseBasis K M
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := X.V) b
  have hcoeff : ∀ (h : G) (s : M ⊗[K] X.V) (i : Module.Free.ChooseBasisIndex K M),
      e (((X.V.representation h).baseChange M) s) i = X.V.representation h (e s i) := by
    intro h s i
    induction s using TensorProduct.inductionOn with
    | tmul m x =>
      rw [LinearMap.baseChange_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
    | add s s' hs hs' => simp only [map_add, Finsupp.add_apply, hs, hs']
  have hfix : ∀ i, e t' i ∈ fixedVectors X.V.representation H := by
    intro i h
    change X.V.representation (h : G) (e t' i) = e t' i
    rw [← hcoeff]
    exact congrArg (fun s => e s i) (ht' h)
  refine ⟨∑ i ∈ (e t').support,
    b i ⊗ₜ[K] (⟨e t' i, hfix i⟩ : fixedVectors X.V.representation H), Subtype.ext ?_⟩
  have hsum : (e t').sum (fun i x => b i ⊗ₜ[K] x) = t' := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  refine Eq.trans ?_ hsum
  show (fixedVectors X.V.representation H).subtype.baseChange M (∑ i ∈ (e t').support,
    b i ⊗ₜ[K] (⟨e t' i, hfix i⟩ : fixedVectors X.V.representation H)) = _
  simp only [map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply, Finsupp.sum]

/-- Fixed vectors commute with extension of scalars: `M ⊗[K] X^H ≃ (M ⊗[K] X)^H`. -/
def fixedVectorsBaseChangeEquiv :
    M ⊗[K] fixedVectors X.V.representation H ≃ₗ[M]
      fixedVectors ((extendScalarsActionFunctor M Γ).obj X).V.representation H :=
  LinearEquiv.ofBijective (fixedVectorsBaseChange M Γ X H)
    ⟨fixedVectorsBaseChange_injective M Γ X H, fixedVectorsBaseChange_surjective M Γ X H⟩

@[simp] theorem fixedVectorsBaseChangeEquiv_apply (t : M ⊗[K] fixedVectors X.V.representation H) :
    fixedVectorsBaseChangeEquiv M Γ X H t = fixedVectorsBaseChange M Γ X H t :=
  rfl

/-- The map `M ⊗[K] X^H → (M ⊗[K] X)^H` commutes with the actions of `Γ`. -/
theorem fixedVectorsBaseChange_comm (γ : Γ) (t : M ⊗[K] fixedVectors X.V.representation H) :
    fixedVectorsBaseChange M Γ X H
        ((fixedVectorsMap (SmoothRep.hom (X.ρ γ)) H).baseChange M t) =
      fixedVectorsMap (SmoothRep.hom (((extendScalarsActionFunctor M Γ).obj X).ρ γ)) H
        (fixedVectorsBaseChange M Γ X H t) := by
  induction t using TensorProduct.inductionOn with
  | tmul m x => rfl
  | add s t hs ht => simp only [map_add, hs, ht]

/-- If `X^H` is finite-dimensional over `K`, then `(M ⊗[K] X)^H` is finite-dimensional over
`M`. -/
theorem finite_fixedVectors_extendScalars [Module.Finite K (fixedVectors X.V.representation H)] :
    Module.Finite M (fixedVectors ((extendScalarsActionFunctor M Γ).obj X).V.representation H) :=
  Module.Finite.equiv (fixedVectorsBaseChangeEquiv M Γ X H)

end Extension

/-! ## Galois actions -/

section Galois

variable {F : Type uF} [Field F] {K : Type uK} [Field K] (M : Type uM) [Field M] [Algebra K M]
  {G : Type uG} [Group G] [TopologicalSpace G]
  (X : Action (SmoothRep.{uK, uG, uV} K G) (Field.absoluteGaloisGroup F)) (H : Subgroup G)

/-- Fixed vectors commute with extension of scalars as Galois actions: the extension of scalars
of the Galois action on `X^H` is isomorphic to the Galois action on `(M ⊗[K] X)^H`. -/
def fixedVectorsBaseChangeIso :
    LatticeGaloisRepresentation.baseChangeAction (L := M)
        ((fixedVectorsActionFunctor K (Field.absoluteGaloisGroup F) H).obj X) ≅
      (fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj
        ((extendScalarsActionFunctor M (Field.absoluteGaloisGroup F)).obj X) :=
  Action.mkIso (fixedVectorsBaseChangeEquiv M _ X H).toModuleIso fun γ =>
    ModuleCat.hom_ext (LinearMap.ext fun t => fixedVectorsBaseChange_comm M _ X H γ t)

@[simp] theorem fixedVectorsBaseChangeIso_hom_hom :
    (fixedVectorsBaseChangeIso M X H).hom.hom.hom = fixedVectorsBaseChange M _ X H :=
  rfl

/-- If the orbit maps of the Galois action on `X^H` are continuous over `K` and `K → M` is
continuous, then the orbit maps of the Galois action on `(M ⊗[K] X)^H` are continuous over
`M`. -/
theorem hasContinuousOrbits_fixedVectors_extendScalars [TopologicalSpace K] [TopologicalSpace M]
    (hKM : Continuous (algebraMap K M))
    (hX : HasContinuousOrbits
      ((fixedVectorsActionFunctor K (Field.absoluteGaloisGroup F) H).obj X)) :
    HasContinuousOrbits
      ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj
        ((extendScalarsActionFunctor M (Field.absoluteGaloisGroup F)).obj X)) :=
  ContinuousGaloisAction.hasContinuousOrbits_of_surjective (fixedVectorsBaseChange M _ X H)
    (fun γ t => fixedVectorsBaseChange_comm M _ X H γ t)
    (fixedVectorsBaseChange_surjective M _ X H)
    (ContinuousGaloisAction.hasContinuousOrbits_baseChangeAction hKM hX)

variable [NumberField F] {v : Global.FinitePlace F}

/-- If the Galois action on `X^H` is unramified at `v` along `ι`, so is the Galois action on
`(M ⊗[K] X)^H`. -/
theorem isUnramifiedAlong_fixedVectors_extendScalars
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} K) v
      ((fixedVectorsActionFunctor K (Field.absoluteGaloisGroup F) H).obj X) ι) :
    IsUnramifiedAlong (ModuleCat.{max uM uV} M) v
      ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj
        ((extendScalarsActionFunctor M (Field.absoluteGaloisGroup F)).obj X)) ι :=
  ContinuousGaloisAction.isUnramifiedAlong_of_surjective (fixedVectorsBaseChange M _ X H)
    (fun γ t => fixedVectorsBaseChange_comm M _ X H γ t)
    (fixedVectorsBaseChange_surjective M _ X H)
    (LatticeGaloisRepresentation.isUnramifiedAlong_baseChange _ hu)

/-- If the Galois action on `X^H` is unramified at `v`, so is the Galois action on
`(M ⊗[K] X)^H`. -/
theorem isUnramifiedAt_fixedVectors_extendScalars
    (hu : IsUnramifiedAt (ModuleCat.{uV} K) v
      ((fixedVectorsActionFunctor K (Field.absoluteGaloisGroup F) H).obj X)) :
    IsUnramifiedAt (ModuleCat.{max uM uV} M) v
      ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj
        ((extendScalarsActionFunctor M (Field.absoluteGaloisGroup F)).obj X)) :=
  isUnramifiedAlong_fixedVectors_extendScalars M X H hu

end Galois

end Langlands.Shimura.ScalarExtensionFixedVectors

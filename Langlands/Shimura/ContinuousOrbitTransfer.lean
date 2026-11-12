import Langlands.Shimura.ContinuousOrbitGaloisAction
import Langlands.Shimura.LatticeGaloisRepresentation

/-! # Transfer of continuous orbits and unramifiedness along equivariant linear maps

Continuity of the orbit maps of a Galois action on a module over a topological field (for the
module topology) passes to the target of a surjective equivariant linear map, to a
finite-dimensional source of a jointly injective family of equivariant linear maps, and to the
extension of scalars along a continuous field homomorphism. Unramifiedness at a finite place
passes along surjective equivariant maps and to sources of jointly injective families. See
`ContinuousOrbitTransfer.md`.
-/

noncomputable section

universe uF uK uL uV uW uJ

set_option autoImplicit false

namespace Langlands.Shimura.ContinuousGaloisAction

open CategoryTheory TensorProduct
open Langlands.GaloisRepresentation (ClosureEmbedding)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong localRestriction)

/-! ## Continuous orbits -/

section Orbits

variable {F : Type uF} [Field F] {L : Type uL} [Field L] [TopologicalSpace L]
  {A : Action (ModuleCat.{uV} L) (Field.absoluteGaloisGroup F)}
  {B : Action (ModuleCat.{uW} L) (Field.absoluteGaloisGroup F)}

/-- If the orbit maps of `A` are continuous, so are those of `B` for every surjective
equivariant linear map `A → B`: every linear map is continuous for the module topologies. -/
theorem hasContinuousOrbits_of_surjective (f : A.V →ₗ[L] B.V)
    (hf : ∀ (g : Field.absoluteGaloisGroup F) (x : A.V), f ((A.ρ g).hom x) = (B.ρ g).hom (f x))
    (hsurj : Function.Surjective f) (hA : HasContinuousOrbits A) : HasContinuousOrbits B := by
  let _ : TopologicalSpace A.V := moduleTopology L A.V
  have : IsModuleTopology L A.V := ⟨rfl⟩
  let _ : TopologicalSpace B.V := moduleTopology L B.V
  have : IsModuleTopology L B.V := ⟨rfl⟩
  have : ContinuousAdd B.V := IsModuleTopology.toContinuousAdd L B.V
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have horbit : (fun g : Field.absoluteGaloisGroup F => (B.ρ g).hom (f x)) =
      fun g => f ((A.ρ g).hom x) :=
    funext fun g => (hf g x).symm
  change Continuous fun g : Field.absoluteGaloisGroup F => (B.ρ g).hom (f x)
  rw [horbit]
  exact (IsModuleTopology.continuous_of_linearMap f).comp (hA x)

omit [TopologicalSpace L] in
/-- A family of linear maps on a finite-dimensional space that is jointly injective has a finite
jointly injective subfamily: a minimal finite intersection of kernels is contained in every
kernel. -/
theorem exists_finset_forall_eq_zero [Module.Finite L A.V] {J : Type uJ}
    (f : J → (A.V →ₗ[L] B.V)) (hinj : ∀ x, (∀ j, f j x = 0) → x = 0) :
    ∃ s : Finset J, ∀ x, (∀ j ∈ s, f j x = 0) → x = 0 := by
  classical
  obtain ⟨N, ⟨s, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal (R := L) (M := A.V)
    (Set.range fun s : Finset J => ⨅ j ∈ s, LinearMap.ker (f j)) ⟨_, ⟨∅, rfl⟩⟩
  have hle : ∀ j, ⨅ j' ∈ s, LinearMap.ker (f j') ≤ LinearMap.ker (f j) := by
    intro j
    have hsub : ⨅ j' ∈ insert j s, LinearMap.ker (f j') ≤ ⨅ j' ∈ s, LinearMap.ker (f j') :=
      biInf_mono fun _ h => Finset.mem_insert_of_mem h
    have heq := eq_of_le_of_not_lt hsub (hmin _ ⟨insert j s, rfl⟩)
    rw [← heq]
    exact iInf₂_le j (Finset.mem_insert_self j s)
  refine ⟨s, fun x hx => hinj x fun j => ?_⟩
  have hmem : x ∈ ⨅ j' ∈ s, LinearMap.ker (f j') := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    exact hx
  exact LinearMap.mem_ker.1 (hle j hmem)

/-- If the orbit maps of `B` are continuous, so are those of a finite-dimensional `A` for every
jointly injective family of equivariant linear maps `A → B`: a finite subfamily embeds `A` into a
finite product of copies of `B`, from which a linear retraction recovers `A` continuously. -/
theorem hasContinuousOrbits_of_forall_eq_zero [Module.Finite L A.V] {J : Type uJ}
    (f : J → (A.V →ₗ[L] B.V))
    (hf : ∀ (j : J) (g : Field.absoluteGaloisGroup F) (x : A.V),
      f j ((A.ρ g).hom x) = (B.ρ g).hom (f j x))
    (hinj : ∀ x, (∀ j, f j x = 0) → x = 0) (hB : HasContinuousOrbits B) :
    HasContinuousOrbits A := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_forall_eq_zero f hinj
  let E : A.V →ₗ[L] (s → B.V) := LinearMap.pi fun j => f j
  have hker : LinearMap.ker E = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => hs x fun j hj => ?_
    exact congrFun hx ⟨j, hj⟩
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective E hker
  let _ : TopologicalSpace A.V := moduleTopology L A.V
  have : IsModuleTopology L A.V := ⟨rfl⟩
  have : ContinuousAdd A.V := IsModuleTopology.toContinuousAdd L A.V
  let _ : TopologicalSpace B.V := moduleTopology L B.V
  have : IsModuleTopology L B.V := ⟨rfl⟩
  intro x
  have horbit : (fun g : Field.absoluteGaloisGroup F => (A.ρ g).hom x) =
      fun g => r fun j : s => (B.ρ g).hom (f j x) := by
    funext g
    have hrx := congrArg (fun φ : A.V →ₗ[L] A.V => φ ((A.ρ g).hom x)) hr
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hrx
    rw [← hrx]
    congr 1
    funext j
    exact hf j g x
  change Continuous fun g : Field.absoluteGaloisGroup F => (A.ρ g).hom x
  rw [horbit]
  exact (IsModuleTopology.continuous_of_linearMap r).comp
    (continuous_pi fun j => hB (f j x))

/-- If the orbit maps of `B` are continuous, so are those of a finite-dimensional `A` for every
injective equivariant linear map `A → B`. -/
theorem hasContinuousOrbits_of_injective [Module.Finite L A.V] (f : A.V →ₗ[L] B.V)
    (hf : ∀ (g : Field.absoluteGaloisGroup F) (x : A.V), f ((A.ρ g).hom x) = (B.ρ g).hom (f x))
    (hinj : Function.Injective f) (hB : HasContinuousOrbits B) : HasContinuousOrbits A :=
  hasContinuousOrbits_of_forall_eq_zero (J := PUnit.{1}) (fun _ => f) (fun _ => hf)
    (fun x hx => hinj (by rw [hx PUnit.unit, map_zero])) hB

end Orbits

/-! ## Extension of scalars -/

section BaseChange

variable {F : Type uF} [Field F] {K : Type uK} [Field K] [TopologicalSpace K] {L : Type uL}
  [Field L] [TopologicalSpace L] [Algebra K L]

/-- Along a field homomorphism `K → L` that is continuous, continuity of the orbit maps of a
Galois action over `K` passes to its extension of scalars `L ⊗[K] A`: the orbit of `c ⊗ x` is
the image of the orbit of `x` under the continuous semilinear map `y ↦ c ⊗ y`, and orbit maps of
sums are sums of orbit maps. -/
theorem hasContinuousOrbits_baseChangeAction (hKL : Continuous (algebraMap K L))
    {A : Action (ModuleCat.{uV} K) (Field.absoluteGaloisGroup F)} (hA : HasContinuousOrbits A) :
    HasContinuousOrbits (LatticeGaloisRepresentation.baseChangeAction (L := L) A) := by
  let _ : TopologicalSpace A.V := moduleTopology K A.V
  have : IsModuleTopology K A.V := ⟨rfl⟩
  let _ : TopologicalSpace (L ⊗[K] A.V) := moduleTopology L (L ⊗[K] A.V)
  have : IsModuleTopology L (L ⊗[K] A.V) := ⟨rfl⟩
  have : ContinuousAdd (L ⊗[K] A.V) := IsModuleTopology.toContinuousAdd L _
  intro y
  change Continuous fun g : Field.absoluteGaloisGroup F => ((A.ρ g).hom.baseChange L) y
  induction y using TensorProduct.inductionOn with
  | tmul c x =>
    let φ : A.V →ₛₗ[algebraMap K L] L ⊗[K] A.V :=
      { toFun := fun y => c ⊗ₜ y
        map_add' := fun y z => TensorProduct.tmul_add c y z
        map_smul' := fun k y => by
          rw [TensorProduct.tmul_smul, algebraMap_smul] }
    have horbit : (fun g : Field.absoluteGaloisGroup F => ((A.ρ g).hom.baseChange L) (c ⊗ₜ x)) =
        fun g => φ ((A.ρ g).hom x) :=
      funext fun g => LinearMap.baseChange_tmul _ c x
    rw [horbit]
    exact (IsModuleTopology.continuous_of_linearMapₛₗ hKL φ).comp (hA x)
  | add y z hy hz =>
    simp only [map_add]
    exact hy.add hz

end BaseChange

/-! ## Unramifiedness -/

section Unramified

variable {F : Type uF} [Field F] [NumberField F] {L : Type uL} [CommRing L]
  {A : Action (ModuleCat.{uV} L) (Field.absoluteGaloisGroup F)}
  {B : Action (ModuleCat.{uW} L) (Field.absoluteGaloisGroup F)}
  {v : Global.FinitePlace F} {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v)}

/-- Unramifiedness at `v` along `ι` passes to the target of a surjective equivariant linear
map. -/
theorem isUnramifiedAlong_of_surjective (f : A.V →ₗ[L] B.V)
    (hf : ∀ (g : Field.absoluteGaloisGroup F) (x : A.V), f ((A.ρ g).hom x) = (B.ρ g).hom (f x))
    (hsurj : Function.Surjective f) (hA : IsUnramifiedAlong (ModuleCat.{uV} L) v A ι) :
    IsUnramifiedAlong (ModuleCat.{uW} L) v B ι := by
  intro i
  refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := hsurj y
  change (B.ρ (localRestriction v ι i.val)).hom (f x) = f x
  rw [← hf, show A.ρ (localRestriction v ι i.val) = 𝟙 A.V from hA i]
  rfl

/-- Unramifiedness at `v` along `ι` passes to the source of a jointly injective family of
equivariant linear maps. -/
theorem isUnramifiedAlong_of_forall_eq_zero {J : Type uJ} (f : J → (A.V →ₗ[L] B.V))
    (hf : ∀ (j : J) (g : Field.absoluteGaloisGroup F) (x : A.V),
      f j ((A.ρ g).hom x) = (B.ρ g).hom (f j x))
    (hinj : ∀ x, (∀ j, f j x = 0) → x = 0) (hB : IsUnramifiedAlong (ModuleCat.{uW} L) v B ι) :
    IsUnramifiedAlong (ModuleCat.{uV} L) v A ι := by
  intro i
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : A.V) => ?_)
  change (A.ρ (localRestriction v ι i.val)).hom x = x
  refine sub_eq_zero.1 (hinj _ fun j => ?_)
  rw [map_sub, hf, show B.ρ (localRestriction v ι i.val) = 𝟙 B.V from hB i, sub_eq_zero]
  rfl

/-- Unramifiedness at `v` along `ι` passes to the source of an injective equivariant linear
map. -/
theorem isUnramifiedAlong_of_injective (f : A.V →ₗ[L] B.V)
    (hf : ∀ (g : Field.absoluteGaloisGroup F) (x : A.V), f ((A.ρ g).hom x) = (B.ρ g).hom (f x))
    (hinj : Function.Injective f) (hB : IsUnramifiedAlong (ModuleCat.{uW} L) v B ι) :
    IsUnramifiedAlong (ModuleCat.{uV} L) v A ι :=
  isUnramifiedAlong_of_forall_eq_zero (J := PUnit.{1}) (fun _ => f) (fun _ => hf)
    (fun x hx => hinj (by rw [hx PUnit.unit, map_zero])) hB

end Unramified

end Langlands.Shimura.ContinuousGaloisAction

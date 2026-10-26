import Langlands.Representation.RestrictedTensor.CyclicEvaluation
import Langlands.Representation.RestrictedTensor.FiniteTail
import Langlands.Representation.Tensor.FiniteProperties
import Mathlib.Algebra.Group.Submonoid.Finite

/-! # Injectivity of cyclic tensor evaluation -/

noncomputable section
open scoped Classical TensorProduct

namespace Langlands.RestrictedTensor.CyclicEvaluation

universe uK uI uG uV

variable {K : Type uK} [Field K] {ι : Type uI}
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable {V : Type uV} [AddCommGroup V] [Module K V]
variable (H : ∀ i, Subgroup (G i))
variable (π : Representation K (RestrictedGroup G H) V)

/-- The genuine coordinate restrictions of the ambient representation. -/
abbrev localAction (i : ι) : Representation K (G i) V :=
  π.comp (RestrictedProduct.mulSingleMonoidHom H i)

/-- Distinct coordinate restrictions commute, including on all ambient vectors. -/
theorem localAction_commuting : Commuting (localAction H π) := by
  intro i j hij g h x
  change π _ (π _ x) = π _ (π _ x)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  apply congrArg (fun g : RestrictedGroup G H => π g x)
  ext k
  by_cases hki : k = i
  · subst k
    simp [RestrictedProduct.mulSingleMonoidHom, hij]
  · by_cases hkj : k = j
    · subst k
      simp [RestrictedProduct.mulSingleMonoidHom, hki]
    · simp [RestrictedProduct.mulSingleMonoidHom, hki, hkj]

/-- Insert an arbitrary finite tuple into the actual restricted group. -/
def finiteInsertion (S : Finset ι) : (∀ i : S, G i) →* RestrictedGroup G H :=
  (finiteSplitMulEquiv H S).symm.toMonoidHom.comp
    (MonoidHom.inl (∀ i : S, G i) (ComplementGroup H S))

@[simp]
theorem finiteInsertion_apply (S : Finset ι) (g : ∀ i : S, G i) (j : ι) :
    finiteInsertion H S g j = if hj : j ∈ S then g ⟨j, hj⟩ else 1 := rfl

@[simp]
theorem finiteInsertion_mulSingle (S : Finset ι) (i : S) (g : G i) :
    finiteInsertion H S (Pi.mulSingle i g) =
      RestrictedProduct.mulSingleMonoidHom H i g := by
  ext j
  by_cases hj : j ∈ S
  · rw [finiteInsertion_apply, dite_eq_left hj]
    change (Pi.mulSingle i g : ∀ k : S, G k) ⟨j, hj⟩ = _
    by_cases hji : j = i
    · subst j
      simp [RestrictedProduct.mulSingleMonoidHom]
    · have hsub : (⟨j, hj⟩ : S) ≠ i := fun h => hji (congrArg Subtype.val h)
      simp [Pi.mulSingle_eq_of_ne hsub, RestrictedProduct.mulSingleMonoidHom, hji]
  · rw [finiteInsertion_apply, dite_eq_right hj]
    symm
    apply RestrictedProduct.mulSingle_eq_of_ne
    intro hji
    exact hj (hji ▸ i.2)

variable (v : V)

/-- The actual external tensor representation on a finite cyclic stage. -/
abbrev stageAction (S : Finset ι) :
    Representation K (∀ i : S, G i) (Stage K (Factor (localAction H π) v) S) :=
  FiniteTensor.external
    (fun i : S => (Cyclic.orbitSpan (localAction H π i) v).toRepresentation)

/-- For a finite product, equivariance on coordinate insertions implies equivariance. -/
theorem intertwines_of_mulSingle
    {J : Type*} [Finite J] [DecidableEq J] {A : J → Type*} [∀ j, Group (A j)]
    {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (ρ : Representation K (∀ j, A j) X) (τ : Representation K (∀ j, A j) Y)
    (f : X →ₗ[K] Y)
    (hf : ∀ j a, f.comp (ρ (Pi.mulSingle j a)) = (τ (Pi.mulSingle j a)).comp f)
    (g : ∀ j, A j) : f.comp (ρ g) = (τ g).comp f := by
  let P : Submonoid (∀ j, A j) :=
    { carrier := {g | ∀ x, f (ρ g x) = τ g (f x)}
      one_mem' := by
        intro x
        rw [map_one, map_one]
        rfl
      mul_mem' := by
        intro a b ha hb x
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb] }
  have hmem : g ∈ P := Submonoid.pi_mem_of_mulSingle_mem g (fun j => by
    intro x
    exact LinearMap.congr_fun (hf j (g j)) x)
  exact LinearMap.ext hmem

/-- Coordinate equivariance extends to the whole finite product group. -/
theorem evalStage_intertwines (S : Finset ι) (g : ∀ i : S, G i) :
    (evalStage (localAction H π) (localAction_commuting H π) v S).comp
        (stageAction H π v S g) =
      (π (finiteInsertion H S g)).comp
        (evalStage (localAction H π) (localAction_commuting H π) v S) := by
  refine intertwines_of_mulSingle (stageAction H π v S) (π.comp (finiteInsertion H S))
    (evalStage (localAction H π) (localAction_commuting H π) v S) ?_ g
  intro i a
  change (evalStage (localAction H π) (localAction_commuting H π) v S).comp
      (FiniteTensor.external
        (fun j : S => (Cyclic.orbitSpan (localAction H π j) v).toRepresentation)
        (Pi.mulSingle i a)) =
    (π (finiteInsertion H S (Pi.mulSingle i a))).comp
      (evalStage (localAction H π) (localAction_commuting H π) v S)
  rw [finiteInsertion_mulSingle, FiniteTensor.external_mulSingle]
  exact evalStage_coordinateAction (localAction H π) (localAction_commuting H π) v S i a

/-- Evaluation as an intertwiner from the finite external tensor to the
restriction of the ambient representation along finite insertion. -/
def stageIntertwiner (S : Finset ι) :
    (stageAction H π v S).IntertwiningMap (π.comp (finiteInsertion H S)) where
  toLinearMap := evalStage (localAction H π) (localAction_commuting H π) v S
  isIntertwining' := evalStage_intertwines H π v S

/-- Nonzero cyclic generators give nonzero finite-stage intertwiners. -/
theorem stageIntertwiner_ne_zero (hv : v ≠ 0) (S : Finset ι) :
    stageIntertwiner H π v S ≠ 0 := by
  intro h
  have he := congrArg (fun f : (stageAction H π v S).IntertwiningMap
      (π.comp (finiteInsertion H S)) =>
    f (PiTensorProduct.tprod K (fun i : S => Cyclic.generator (localAction H π i) v))) h
  have hh : v = 0 := by
    simpa [stageIntertwiner] using he
  exact hv hh

/-- Irreducible cyclic factors with scalar endomorphisms make every finite
evaluation injective. No irreducibility of the ambient representation is needed. -/
theorem evalStage_injective
    (hv : v ≠ 0)
    (hirr : ∀ i, (Cyclic.orbitSpan (localAction H π i) v).toRepresentation.IsIrreducible)
    (hscalar : ∀ i, ∀ f :
      (Cyclic.orbitSpan (localAction H π i) v).toRepresentation.IntertwiningMap
        (Cyclic.orbitSpan (localAction H π i) v).toRepresentation,
      ∃ c : K, f = c • Representation.IntertwiningMap.id _)
    (S : Finset ι) :
    Function.Injective (evalStage (localAction H π) (localAction_commuting H π) v S) := by
  let (i : S) :
    (Cyclic.orbitSpan (localAction H π i) v).toRepresentation.IsIrreducible := hirr i
  let : (stageAction H π v S).IsIrreducible :=
    FiniteTensor.isIrreducible_external _ (fun i => hscalar i)
  exact (Representation.IsIrreducible.injective_or_eq_zero
    (stageIntertwiner H π v S)).resolve_right (stageIntertwiner_ne_zero H π v hv S)

/-- Injectivity passes from all finite stages to the actual algebraic direct limit. -/
theorem eval_injective
    (hv : v ≠ 0)
    (hirr : ∀ i, (Cyclic.orbitSpan (localAction H π i) v).toRepresentation.IsIrreducible)
    (hscalar : ∀ i, ∀ f :
      (Cyclic.orbitSpan (localAction H π i) v).toRepresentation.IntertwiningMap
        (Cyclic.orbitSpan (localAction H π i) v).toRepresentation,
      ∃ c : K, f = c • Representation.IntertwiningMap.id _)
    (E : Finset ι) :
    Function.Injective (eval (localAction H π) (localAction_commuting H π) v E) := by
  intro x y hxy
  have hz : x - y = 0 := by
    obtain ⟨S, z, hz⟩ := exists_of E (fun i => Cyclic.generator (localAction H π i) v) (x - y)
    have he : evalStage (localAction H π) (localAction_commuting H π) v S.1 z = 0 := by
      rw [← eval_of, ← hz, map_sub, hxy, sub_self]
    have hz0 : z = 0 := evalStage_injective H π v hv hirr hscalar S.1 (by simpa using he)
    rw [hz, hz0, map_zero]
  exact sub_eq_zero.mp hz

end Langlands.RestrictedTensor.CyclicEvaluation

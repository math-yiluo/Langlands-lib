import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Uniform generalized central-character spaces

The exponent is uniform over all central elements for each vector.
The infinite generalized space is the increasing union over finite exponents.
-/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]

/-- Vectors killed by the same power `n` of every central operator minus its
specified character value. -/
def centralCharacterSpace (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) (n : ℕ) : Subrepresentation ρ where
  toSubmodule := ⨅ z : Subgroup.center G,
    Module.End.genEigenspace (ρ (z : G)) (χ z : R) n
  apply_mem_toSubmodule g := by
    intro v hv
    simp only [Submodule.mem_iInf] at hv ⊢
    intro z
    apply Module.End.mapsTo_genEigenspace_of_comp (ρ g) (μ := (χ z : R)) (k := n)
      (x := v) ?_ (hv z)
    change ρ (z : G) * ρ g = ρ g * ρ (z : G)
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp z.property g)]

@[simp]
theorem mem_centralCharacterSpace (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) (n : ℕ) (v : V) :
    v ∈ centralCharacterSpace ρ χ n ↔
      ∀ z : Subgroup.center G, ((ρ (z : G) - (χ z : R) • 1) ^ n) v = 0 := by
  change (v ∈ ⨅ z : Subgroup.center G,
    Module.End.genEigenspace (ρ (z : G)) (χ z : R) n) ↔ _
  simp only [Submodule.mem_iInf, Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]

/-- The finite central-character spaces increase with the uniform exponent. -/
theorem centralCharacterSpace_mono (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) :
    Monotone (fun n : ℕ => (centralCharacterSpace ρ χ n).toSubmodule) := by
  intro m n hmn
  apply iInf_mono
  intro z
  exact (Module.End.genEigenspace (ρ (z : G)) (χ z : R)).monotone
    (show (m : ℕ∞) ≤ (n : ℕ∞) by exact_mod_cast hmn)

/-- The actual generalized central-character subrepresentation, with a single
finite exponent for all central elements at each vector. -/
def generalizedCentralCharacterSpace (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) : Subrepresentation ρ where
  toSubmodule := ⨆ n : ℕ, (centralCharacterSpace ρ χ n).toSubmodule
  apply_mem_toSubmodule g := by
    intro v hv
    rw [Submodule.mem_iSup_of_directed _
      (centralCharacterSpace_mono ρ χ).directed_le] at hv ⊢
    obtain ⟨n, hn⟩ := hv
    exact ⟨n, (centralCharacterSpace ρ χ n).apply_mem_toSubmodule g hn⟩

@[simp]
theorem mem_generalizedCentralCharacterSpace (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) (v : V) :
    v ∈ generalizedCentralCharacterSpace ρ χ ↔
      ∃ n : ℕ, ∀ z : Subgroup.center G,
        ((ρ (z : G) - (χ z : R) • 1) ^ n) v = 0 := by
  change (v ∈ ⨆ n : ℕ, (centralCharacterSpace ρ χ n).toSubmodule) ↔ _
  rw [Submodule.mem_iSup_of_directed _ (centralCharacterSpace_mono ρ χ).directed_le]
  change (∃ n : ℕ, v ∈ centralCharacterSpace ρ χ n) ↔ _
  simp only [mem_centralCharacterSpace]

/-- The exponent-one space is exactly the prescribed scalar-action space. -/
theorem mem_centralCharacterSpace_one (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) (v : V) :
    v ∈ centralCharacterSpace ρ χ 1 ↔
      ∀ z : Subgroup.center G, ρ (z : G) v = (χ z : R) • v := by
  simp [mem_centralCharacterSpace, sub_eq_zero]

@[simp]
theorem centralCharacterSpace_zero (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) : centralCharacterSpace ρ χ 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change (v ∈ centralCharacterSpace ρ χ 0) ↔ v ∈ (⊥ : Submodule R V)
  simp [mem_centralCharacterSpace]

variable {ρ : Representation R G V} {σ : Representation R G W}

/-- An intertwiner preserves the same finite uniform exponent. -/
theorem map_mem_centralCharacterSpace (f : ρ.IntertwiningMap σ)
    (χ : Subgroup.center G →* Rˣ) (n : ℕ) {v : V}
    (hv : v ∈ centralCharacterSpace ρ χ n) :
    f v ∈ centralCharacterSpace σ χ n := by
  change v ∈ ⨅ z : Subgroup.center G,
    Module.End.genEigenspace (ρ (z : G)) (χ z : R) n at hv
  change f v ∈ ⨅ z : Subgroup.center G,
    Module.End.genEigenspace (σ (z : G)) (χ z : R) n
  simp only [Submodule.mem_iInf] at hv ⊢
  intro z
  exact Module.End.mapsTo_genEigenspace_of_comp f.toLinearMap
    (f.isIntertwining' (z : G)).symm (χ z : R) n (hv z)

/-- An intertwiner preserves the generalized central-character space. -/
theorem map_mem_generalizedCentralCharacterSpace (f : ρ.IntertwiningMap σ)
    (χ : Subgroup.center G →* Rˣ) {v : V}
    (hv : v ∈ generalizedCentralCharacterSpace ρ χ) :
    f v ∈ generalizedCentralCharacterSpace σ χ := by
  obtain ⟨n, hn⟩ := (mem_generalizedCentralCharacterSpace ρ χ v).mp hv
  exact (mem_generalizedCentralCharacterSpace σ χ (f v)).mpr
    ⟨n, (mem_centralCharacterSpace σ χ n (f v)).mp
      (map_mem_centralCharacterSpace f χ n
        ((mem_centralCharacterSpace ρ χ n v).mpr hn))⟩

/-- The actual intertwiner between finite central-character subrepresentations. -/
def centralCharacterMap (f : ρ.IntertwiningMap σ)
    (χ : Subgroup.center G →* Rˣ) (n : ℕ) :
    (centralCharacterSpace ρ χ n).toRepresentation.IntertwiningMap
      (centralCharacterSpace σ χ n).toRepresentation where
  toFun v := ⟨f v, map_mem_centralCharacterSpace f χ n v.property⟩
  map_add' v w := Subtype.ext (map_add f (v : V) (w : V))
  map_smul' c v := Subtype.ext (map_smul f c (v : V))
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change f (ρ g (v : V)) = σ g (f (v : V))
    exact Representation.IntertwiningMap.isIntertwining ρ σ f g (v : V)

/-- The actual intertwiner between generalized central-character
subrepresentations. -/
def generalizedCentralCharacterMap (f : ρ.IntertwiningMap σ)
    (χ : Subgroup.center G →* Rˣ) :
    (generalizedCentralCharacterSpace ρ χ).toRepresentation.IntertwiningMap
      (generalizedCentralCharacterSpace σ χ).toRepresentation where
  toFun v := ⟨f v, map_mem_generalizedCentralCharacterSpace f χ v.property⟩
  map_add' v w := Subtype.ext (map_add f (v : V) (w : V))
  map_smul' c v := Subtype.ext (map_smul f c (v : V))
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change f (ρ g (v : V)) = σ g (f (v : V))
    exact Representation.IntertwiningMap.isIntertwining ρ σ f g (v : V)

/-- Actual equivariant equivalence of generalized spaces under an equivalence
of the ambient representations. -/
def generalizedCentralCharacterEquiv (e : ρ.Equiv σ)
    (χ : Subgroup.center G →* Rˣ) :
    (generalizedCentralCharacterSpace ρ χ).toRepresentation.Equiv
      (generalizedCentralCharacterSpace σ χ).toRepresentation where
  __ := generalizedCentralCharacterMap e.toIntertwiningMap χ
  invFun := generalizedCentralCharacterMap e.symm.toIntertwiningMap χ
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv v := Subtype.ext (e.apply_symm_apply v)

/-- A central exponent is a character with open kernel whose uniform generalized
central-character space is nonzero. No finiteness or decomposition is asserted. -/
def IsCentralExponent [TopologicalSpace G] (ρ : Representation R G V)
    (χ : Subgroup.center G →* Rˣ) : Prop :=
  IsOpen (χ.ker : Set (Subgroup.center G)) ∧ generalizedCentralCharacterSpace ρ χ ≠ ⊥

end Langlands

import Langlands.Representation.Jacquet.CompatibleCoefficientActions

/-! # Native coefficient representations and their actual complex Jacquet quotients -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Jacquet.CoefficientRestriction

universe uR uG uV

section Native

variable {R : Type uR} [CommRing R] [Algebra ℂ R]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V] [Module ℂ V]
variable [IsScalarTower ℂ R V]

/-- Restrict each actual group operator to complex scalars, on the same carrier. -/
def complexRepresentation (σ : Representation R G V) : Representation ℂ G V where
  toFun g := (σ g).restrictScalars ℂ
  map_one' := by
    ext v
    change σ 1 v = v
    simp
  map_mul' g h := by
    ext v
    change σ (g * h) v = σ g (σ h v)
    simp only [map_mul, Module.End.mul_apply]

@[simp]
theorem complexRepresentation_apply (σ : Representation R G V) (g : G) (v : V) :
    complexRepresentation σ g v = σ g v := rfl

instance complexRepresentation_hasCompatibleCoefficients (σ : Representation R G V) :
    HasCompatibleCoefficients R (complexRepresentation σ) where
  map_smul r g v := (σ g).map_smul r v

variable (σ : Representation R G V)

/-- Restriction changes no smooth vectors. -/
theorem isSmooth_complexRepresentation [TopologicalSpace G] :
    IsSmooth (complexRepresentation σ) ↔ IsSmooth σ := Iff.rfl

/-- The same fixed-vector carrier has the original coefficient-module action. -/
def complexFixedVectorsEquiv (H : Subgroup G) :
    fixedVectors (complexRepresentation σ) H ≃ₗ[R] fixedVectors σ H :=
  LinearEquiv.refl R (fixedVectors σ H)

/-- The complex relation set, with its inherited coefficient structure, is
exactly the native coefficient relation submodule. -/
theorem coefficientRelations_eq_native (N : Subgroup G) :
    coefficientRelations R (complexRepresentation σ) N = relations σ N := by
  apply le_antisymm
  · have hle : relations (complexRepresentation σ) N ≤ (relations σ N).restrictScalars ℂ := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨n, v⟩, rfl⟩
      exact sub_mem_relations σ N n v
    exact hle
  · apply Submodule.span_le.2
    rintro _ ⟨⟨n, v⟩, rfl⟩
    exact sub_mem_relations (complexRepresentation σ) N n v

/-- Compare the literal complex and coefficient Jacquet quotients over the
coefficient ring, using equality of their actual relation submodules. -/
def coinvariantsEquiv (N : Subgroup G) :
    Coinvariants (complexRepresentation σ) N ≃ₗ[R] Coinvariants σ N := by
  change (V ⧸ coefficientRelations R (complexRepresentation σ) N) ≃ₗ[R]
    (V ⧸ relations σ N)
  exact Submodule.quotEquivOfEq _ _ (coefficientRelations_eq_native σ N)

@[simp]
theorem coinvariantsEquiv_mk (N : Subgroup G) (v : V) :
    coinvariantsEquiv σ N (mk (complexRepresentation σ) N v) = mk σ N v := rfl

theorem coinvariantsEquiv_action (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (m : M) (y : Coinvariants (complexRepresentation σ) N) :
    coinvariantsEquiv σ N (action (complexRepresentation σ) N M hMN m y) =
      action σ N M hMN m (coinvariantsEquiv σ N y) := by
  obtain ⟨v, rfl⟩ := mk_surjective (complexRepresentation σ) N y
  rw [action_mk, coinvariantsEquiv_mk, coinvariantsEquiv_mk, action_mk]
  rfl

end Native

section Relinearization

variable (R : Type uR) [CommRing R]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module R V]
variable (ρ : Representation ℂ G V) [HasCompatibleCoefficients R ρ]

/-- Retain a compatible actual complex action as a coefficient-linear action. -/
def representationOverCoefficients : Representation R G V where
  toFun g :=
    { toFun := ρ g
      map_add' := map_add (ρ g)
      map_smul' r v := HasCompatibleCoefficients.map_smul r g v }
  map_one' := by
    ext v
    change ρ 1 v = v
    simp
  map_mul' g h := by
    ext v
    change ρ (g * h) v = ρ g (ρ h v)
    simp only [map_mul, Module.End.mul_apply]

end Relinearization

section JacquetFixed

variable {R : Type uR} [CommRing R] [Algebra ℂ R]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V] [Module ℂ V]
variable [IsScalarTower ℂ R V]
variable (σ : Representation R G V)

/-- The quotient comparison is an actual coefficient representation equivalence. -/
def jacquetRepresentationEquiv (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) :
    (representationOverCoefficients R (action (complexRepresentation σ) N M hMN)).Equiv
      (action σ N M hMN) where
  toLinearEquiv := coinvariantsEquiv σ N
  isIntertwining' m := by
    apply LinearMap.ext
    intro y
    change coinvariantsEquiv σ N (action (complexRepresentation σ) N M hMN m y) =
      action σ N M hMN m (coinvariantsEquiv σ N y)
    exact coinvariantsEquiv_action σ N M hMN m y

/-- Transfer native coefficient finiteness on the actual Jacquet fixed vectors
to the actual complex Jacquet fixed-vector carrier. -/
def jacquetFixedVectorsEquiv (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (H : Subgroup M) :
    fixedVectors (action (complexRepresentation σ) N M hMN) H ≃ₗ[R]
      fixedVectors (action σ N M hMN) H :=
  Langlands.fixedVectorsEquiv (jacquetRepresentationEquiv σ N M hMN) H

end JacquetFixed

section Stability

variable {R : Type uR} [CommRing R] [Algebra ℂ R] [IsNoetherianRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module R V] [Module ℂ V]
variable [IsScalarTower ℂ R V]
variable (σ : Representation R G V) (hσ : IsSmooth σ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable {N M Nbar : Subgroup G} {g : G}
variable (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
variable (hcentral : ∀ m ∈ M, m * g = g * m)

include h hcentral in
/-- The family application needs only native coefficient finiteness on its
compact fixed vectors and its unnormalized Jacquet fixed vectors. -/
theorem compressedAction_eventuallyStable_of_native_finite
    [Module.Finite R (fixedVectors σ K.toSubgroup)]
    [Module.Finite R (fixedVectors (action σ N M hMN) (K.toSubgroup.comap M.subtype))] :
    LinearAlgebra.StableEndomorphism.EventuallyStable
      (compressedAction (complexRepresentation σ)
        ((isSmooth_complexRepresentation σ).mpr hσ) K hK g) := by
  let : Module.Finite R (fixedVectors (complexRepresentation σ) K.toSubgroup) :=
    Module.Finite.of_surjective (complexFixedVectorsEquiv σ K.toSubgroup).symm.toLinearMap
      (complexFixedVectorsEquiv σ K.toSubgroup).symm.surjective
  let : Module.Finite R (fixedVectors (action (complexRepresentation σ) N M hMN)
      (K.toSubgroup.comap M.subtype)) :=
    Module.Finite.of_surjective
      (jacquetFixedVectorsEquiv σ N M hMN (K.toSubgroup.comap M.subtype)).symm.toLinearMap
      (jacquetFixedVectorsEquiv σ N M hMN (K.toSubgroup.comap M.subtype)).symm.surjective
  exact (fixedJacquetMap_surjective_and_eventuallyStable_of_compatible_coefficients
    R (complexRepresentation σ) ((isSmooth_complexRepresentation σ).mpr hσ)
    K hK h hMN hcentral).2

end Stability

end Langlands.Jacquet.CoefficientRestriction

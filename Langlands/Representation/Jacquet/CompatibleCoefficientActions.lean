import Langlands.Representation.Jacquet.CompressionCoefficientLocalization

/-! # Compatible coefficient actions on actual compact and Jacquet fixed vectors -/

noncomputable section

set_option autoImplicit false

namespace Langlands

universe uR uG uV

section Coefficients

variable (R : Type uR) [CommRing R]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module R V]

/-- The existing coefficient action commutes with every group operator. -/
class HasCompatibleCoefficients (ρ : Representation ℂ G V) : Prop where
  map_smul : ∀ (r : R) (g : G) (v : V), ρ g (r • v) = r • ρ g v

variable (ρ : Representation ℂ G V) [HasCompatibleCoefficients R ρ]

/-- The actual fixed-vector set, as a coefficient submodule. -/
def coefficientFixedVectors (H : Subgroup G) : Submodule R V where
  carrier := fixedVectors ρ H
  zero_mem' := (fixedVectors ρ H).zero_mem
  add_mem' := (fixedVectors ρ H).add_mem
  smul_mem' r v hv k := by
    change ρ k.val (r • v) = r • v
    have hk : ρ k.val v = v := hv k
    rw [HasCompatibleCoefficients.map_smul, hk]

/-- Coefficient scalars on the actual complex fixed-vector carrier. -/
instance coefficientFixedVectorsModule (H : Subgroup G) :
    Module R (fixedVectors ρ H) :=
  inferInstanceAs (Module R (coefficientFixedVectors R ρ H))

@[simp]
theorem coefficientFixedVectors_smul_val (H : Subgroup G) (r : R)
    (x : fixedVectors ρ H) :
    (r • x).val = r • x.val := rfl

end Coefficients

namespace Jacquet

section Relations

variable (R : Type uR) [CommRing R]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module R V]
variable [SMulCommClass ℂ R V]
variable (ρ : Representation ℂ G V) [HasCompatibleCoefficients R ρ]

/-- The complex Jacquet relation submodule is stable under the given
coefficient scalars, since its generating relations have that property. -/
theorem coefficient_smul_mem_relations (N : Subgroup G) (r : R) {v : V}
    (hv : v ∈ relations ρ N) : r • v ∈ relations ρ N := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨⟨n, x⟩, rfl⟩ := hw
      change r • (ρ (n : G) x - x) ∈ relations ρ N
      rw [smul_sub, ← HasCompatibleCoefficients.map_smul]
      exact sub_mem_relations ρ N n (r • x)
  | zero => simpa only [smul_zero] using (relations ρ N).zero_mem
  | add x y _ _ hx hy => simpa only [smul_add] using (relations ρ N).add_mem hx hy
  | smul c x _ hx =>
      rw [← smul_comm c r x]
      exact (relations ρ N).smul_mem c hx

/-- The literal complex relation set, closed under coefficient scalars. -/
def coefficientRelations (N : Subgroup G) : Submodule R V where
  carrier := relations ρ N
  zero_mem' := (relations ρ N).zero_mem
  add_mem' := (relations ρ N).add_mem
  smul_mem' r _ hv := coefficient_smul_mem_relations R ρ N r hv

/-- The quotient by the same additive relation set inherits the actual
coefficient action on representatives. -/
instance coefficientCoinvariantsModule (N : Subgroup G) :
    Module R (Coinvariants ρ N) :=
  inferInstanceAs (Module R (V ⧸ coefficientRelations R ρ N))

@[simp]
theorem coefficient_mk_smul (N : Subgroup G) (r : R) (v : V) :
    mk ρ N (r • v) = r • mk ρ N v := rfl

/-- Coefficient scalars continue to commute with the actual unnormalized
normalizer action on the complex Jacquet quotient. -/
instance action_hasCompatibleCoefficients (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) :
    HasCompatibleCoefficients R (action ρ N M hMN) where
  map_smul r m y := by
    obtain ⟨v, rfl⟩ := mk_surjective ρ N y
    rw [← coefficient_mk_smul R ρ, action_mk,
      HasCompatibleCoefficients.map_smul, coefficient_mk_smul R ρ, action_mk]

/-- Multiplication by one coefficient is an actual complex intertwiner. -/
def coefficientIntertwiner (r : R) : ρ.IntertwiningMap ρ where
  toLinearMap :=
    { toFun := fun v => r • v
      map_add' := smul_add r
      map_smul' c v := (smul_comm c r v).symm }
  isIntertwining' g := by
    ext v
    exact (HasCompatibleCoefficients.map_smul r g v).symm

@[simp]
theorem fixedVectorsMap_coefficientIntertwiner (H : Subgroup G) (r : R)
    (x : fixedVectors ρ H) :
    fixedVectorsMap (coefficientIntertwiner R ρ r) H x = r • x := rfl

/-- The actual quotient restricted to fixed vectors respects the inherited
coefficient actions on its source and target. -/
theorem fixedJacquetMap_coefficient_smul (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (H : Subgroup G) (r : R)
    (x : fixedVectors ρ H) :
    fixedJacquetMap ρ N M hMN H (r • x) =
      r • fixedJacquetMap ρ N M hMN H x := by
  apply Subtype.ext
  exact coefficient_mk_smul R ρ N r x.val

end Relations

section Compact

variable (R : Type uR) [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module R V]
variable [SMulCommClass ℂ R V]
variable (ρ : Representation ℂ G V) [HasCompatibleCoefficients R ρ]
variable (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- Compact compression is coefficient-linear by its naturality with respect
to multiplication by each coefficient. -/
theorem compressedAction_coefficient_smul (g : G) (r : R)
    (x : fixedVectors ρ K.toSubgroup) :
    compressedAction ρ hρ K hK g (r • x) =
      r • compressedAction ρ hρ K hK g x := by
  have h := LinearMap.congr_fun
    (compressedAction_natural ρ ρ hρ hρ K hK g (coefficientIntertwiner R ρ r)) x
  exact h.symm

variable {N M Nbar : Subgroup G} {g : G}
variable (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
variable (hcentral : ∀ m ∈ M, m * g = g * m)

omit [IsTopologicalGroup G] in
/-- The actual central Levi automorphism is coefficient-linear on the actual
complex Jacquet fixed-vector carrier. -/
theorem fixedJacquetCentralEquiv_coefficient_smul (r : R)
    (y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :
    fixedJacquetCentralEquiv ρ h hMN hcentral (r • y) =
      r • fixedJacquetCentralEquiv ρ h hMN hcentral y := by
  apply Subtype.ext
  exact HasCompatibleCoefficients.map_smul (ρ := action ρ N M hMN)
    r (⟨g, h.mem_levi⟩ : M) y.val

include h hcentral in
/-- A global compatible coefficient action discharges all three scalar laws
in the finite-coefficient localization criterion. Finiteness is required only
of the two actual fixed-vector modules. -/
theorem fixedJacquetMap_surjective_and_eventuallyStable_of_compatible_coefficients
    [IsNoetherianRing R]
    [Module.Finite R (fixedVectors ρ K.toSubgroup)]
    [Module.Finite R (fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))] :
    Function.Surjective (fixedJacquetMap ρ N M hMN K.toSubgroup) ∧
      LinearAlgebra.StableEndomorphism.EventuallyStable (compressedAction ρ hρ K hK g) :=
  fixedJacquetMap_surjective_and_eventuallyStable_of_finite_coefficients
    R ρ hρ K hK h hMN hcentral
    (compressedAction_coefficient_smul R ρ hρ K hK g)
    (fixedJacquetMap_coefficient_smul R ρ N M hMN K.toSubgroup)
    (fixedJacquetCentralEquiv_coefficient_smul R ρ K h hMN hcentral)

end Compact

end Jacquet

end Langlands

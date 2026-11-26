import Langlands.Algebra.ReducedNorm
import Langlands.GroupScheme.Quaternionic.Involution

/-! # Unitary and special unitary points of a central simple algebra with involution

Let `F ⊆ E` be fields and `B` a finite-dimensional central simple `E`-algebra that is also
an `F`-algebra through `E`. An `F`-linear involution `τ` of `B` (a
`Quaternionic.FirstKindInvolution F B`) extends to every commutative `F`-algebra `R` as
`id_R ⊗ τ`. This module defines, for every such `R`,

* the relative reduced norm `(R ⊗[F] B)ˣ →* (E ⊗[F] R)ˣ`, the reduced norm of the
  central simple `E`-algebra `B` with coefficients in the `E`-algebra `E ⊗[F] R`;
* the unitary points `{u | u · τ_R(u) = 1}` and the special unitary points, those of
  relative reduced norm one,

together with their functoriality in `R`.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple.UnitaryPoints

open Langlands.GroupScheme.Quaternionic

variable (F E B : Type u) [Field F] [Field E] [Algebra F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]

/-- The coefficient identification `R ⊗[F] B ≃ (E ⊗[F] R) ⊗[E] B`. -/
def tensorEquiv (R : Type u) [CommRing R] [Algebra F R] :
    R ⊗[F] B ≃ₐ[F] (E ⊗[F] R) ⊗[E] B :=
  ((Algebra.TensorProduct.comm F R B).trans
    ((Algebra.TensorProduct.congr
      ((Algebra.TensorProduct.rid E E B).restrictScalars F).symm AlgEquiv.refl).trans
      ((Algebra.TensorProduct.assoc F E E B E R).restrictScalars F))).trans
    ((Algebra.TensorProduct.comm E B (E ⊗[F] R)).restrictScalars F)

@[simp] theorem tensorEquiv_tmul (R : Type u) [CommRing R] [Algebra F R] (r : R) (b : B) :
    tensorEquiv F E B R (r ⊗ₜ[F] b) = ((1 : E) ⊗ₜ[F] r) ⊗ₜ[E] b := rfl


/-- The coefficient identification is natural in the commutative coefficient algebra. -/
theorem tensorEquiv_naturality {R S : Type u} [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (f : R →ₐ[F] S) (x : R ⊗[F] B) :
    tensorEquiv F E B S (Algebra.TensorProduct.map f (AlgHom.id F B) x) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id E E) f) (AlgHom.id E B)
        (tensorEquiv F E B R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

section Unitary

variable {F B}

/-- The unitary points `{u | u · τ_R(u) = 1}` of `(B, τ)` with coefficients in `R`. -/
def unitaryPoints (τ : FirstKindInvolution F B) (R : Type u) [CommRing R] [Algebra F R] :
    Subgroup (R ⊗[F] B)ˣ where
  carrier := {u | (u : R ⊗[F] B) * τ.baseChange R u = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq, Units.val_mul, FirstKindInvolution.map_mul] at hu hv ⊢
    rw [mul_assoc, ← mul_assoc (v : R ⊗[F] B), hv, one_mul, hu]
  inv_mem' := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    have h : τ.baseChange R (u : R ⊗[F] B) = ((u⁻¹ : (R ⊗[F] B)ˣ) : R ⊗[F] B) := by
      calc τ.baseChange R (u : R ⊗[F] B)
          = ((u⁻¹ : (R ⊗[F] B)ˣ) : R ⊗[F] B) * ((u : R ⊗[F] B) * τ.baseChange R u) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = _ := by rw [hu, mul_one]
    have h' : τ.baseChange R ((u⁻¹ : (R ⊗[F] B)ˣ) : R ⊗[F] B) = u := by
      rw [← h, FirstKindInvolution.apply_apply]
    rw [h', Units.inv_mul]

theorem mem_unitaryPoints (τ : FirstKindInvolution F B) {R : Type u} [CommRing R]
    [Algebra F R] (u : (R ⊗[F] B)ˣ) :
    u ∈ unitaryPoints τ R ↔ (u : R ⊗[F] B) * τ.baseChange R u = 1 := Iff.rfl

/-- Coefficient change preserves unitary points. -/
theorem map_mem_unitaryPoints (τ : FirstKindInvolution F B) {R S : Type u} [CommRing R]
    [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S) {u : (R ⊗[F] B)ˣ}
    (hu : u ∈ unitaryPoints τ R) :
    Units.map (Algebra.TensorProduct.map f (AlgHom.id F B)).toMonoidHom u ∈
      unitaryPoints τ S := by
  rw [mem_unitaryPoints] at hu ⊢
  change Algebra.TensorProduct.map f (AlgHom.id F B) (u : R ⊗[F] B) *
    τ.baseChange S (Algebra.TensorProduct.map f (AlgHom.id F B) (u : R ⊗[F] B)) = 1
  rw [← FirstKindInvolution.map_baseChange, ← map_mul, hu, map_one]

end Unitary

variable [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

/-- The relative reduced norm on coefficient units: the reduced norm of the central simple
`E`-algebra `B` with coefficients in the `E`-algebra `E ⊗[F] R`, transported along
`tensorEquiv`. -/
def relativeNorm (R : Type u) [CommRing R] [Algebra F R] : (R ⊗[F] B)ˣ →* (E ⊗[F] R)ˣ :=
  (reducedNormUnits E B (E ⊗[F] R)).comp (Units.map (tensorEquiv F E B R).toMonoidHom)

theorem relativeNorm_val (R : Type u) [CommRing R] [Algebra F R] (x : (R ⊗[F] B)ˣ) :
    (relativeNorm F E B R x : E ⊗[F] R) =
      reducedNorm E B (E ⊗[F] R) (tensorEquiv F E B R (x : R ⊗[F] B)) := rfl

/-- The relative reduced norm is natural in the commutative coefficient algebra. -/
theorem relativeNorm_naturality {R S : Type u} [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (f : R →ₐ[F] S) (x : (R ⊗[F] B)ˣ) :
    relativeNorm F E B S (Units.map (Algebra.TensorProduct.map f (AlgHom.id F B)).toMonoidHom x) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id E E) f).toMonoidHom
        (relativeNorm F E B R x) := by
  apply Units.ext
  rw [relativeNorm_val]
  change reducedNorm E B (E ⊗[F] S)
      (tensorEquiv F E B S (Algebra.TensorProduct.map f (AlgHom.id F B) (x : R ⊗[F] B))) = _
  rw [tensorEquiv_naturality, reducedNorm_naturality]
  rfl

/-- On original algebra elements the relative reduced norm is the reduced norm over `E`,
extended to `E ⊗[F] R`. -/
theorem relativeNorm_includeRight (R : Type u) [CommRing R] [Algebra F R] (x : Bˣ) :
    (relativeNorm F E B R
        (Units.map (Algebra.TensorProduct.includeRight : B →ₐ[F] R ⊗[F] B).toMonoidHom x) :
        E ⊗[F] R) =
      reducedNorm E B E ((1 : E) ⊗ₜ[E] (x : B)) ⊗ₜ[F] (1 : R) := by
  rw [relativeNorm_val]
  change reducedNorm E B (E ⊗[F] R) (tensorEquiv F E B R ((1 : R) ⊗ₜ[F] (x : B))) = _
  rw [tensorEquiv_tmul]
  have h := reducedNorm_naturality E B
    (Algebra.TensorProduct.includeLeft : E →ₐ[E] E ⊗[F] R) ((1 : E) ⊗ₜ[E] (x : B))
  rw [Algebra.TensorProduct.map_tmul] at h
  exact h

variable {F E B}

variable (E) in
/-- The special unitary points of `(B, τ)` with coefficients in `R`: unitary points of
relative reduced norm one. -/
def specialUnitaryPoints (τ : FirstKindInvolution F B) (R : Type u) [CommRing R]
    [Algebra F R] : Subgroup (R ⊗[F] B)ˣ :=
  unitaryPoints τ R ⊓ (relativeNorm F E B R).ker

theorem mem_specialUnitaryPoints (τ : FirstKindInvolution F B) {R : Type u} [CommRing R]
    [Algebra F R] (u : (R ⊗[F] B)ˣ) :
    u ∈ specialUnitaryPoints E τ R ↔
      (u : R ⊗[F] B) * τ.baseChange R u = 1 ∧ relativeNorm F E B R u = 1 := Iff.rfl

/-- Coefficient change preserves special unitary points. -/
theorem map_mem_specialUnitaryPoints (τ : FirstKindInvolution F B) {R S : Type u}
    [CommRing R] [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    {u : (R ⊗[F] B)ˣ} (hu : u ∈ specialUnitaryPoints E τ R) :
    Units.map (Algebra.TensorProduct.map f (AlgHom.id F B)).toMonoidHom u ∈
      specialUnitaryPoints E τ S := by
  refine ⟨map_mem_unitaryPoints τ f hu.1, ?_⟩
  change relativeNorm F E B S _ = 1
  rw [relativeNorm_naturality, show relativeNorm F E B R u = 1 from hu.2, map_one]

variable (E) in
/-- Coefficient change on special unitary points. -/
def specialUnitaryMap (τ : FirstKindInvolution F B) {R S : Type u} [CommRing R]
    [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S) :
    specialUnitaryPoints E τ R →* specialUnitaryPoints E τ S :=
  ((Units.map (Algebra.TensorProduct.map f (AlgHom.id F B)).toMonoidHom).comp
    (specialUnitaryPoints E τ R).subtype).codRestrict (specialUnitaryPoints E τ S)
    (fun u => map_mem_specialUnitaryPoints τ f u.2)

@[simp] theorem specialUnitaryMap_val (τ : FirstKindInvolution F B) {R S : Type u}
    [CommRing R] [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (u : specialUnitaryPoints E τ R) :
    ((specialUnitaryMap E τ f u : (S ⊗[F] B)ˣ) : S ⊗[F] B) =
      Algebra.TensorProduct.map f (AlgHom.id F B) ((u : (R ⊗[F] B)ˣ) : R ⊗[F] B) := rfl

end Langlands.CentralSimple.UnitaryPoints

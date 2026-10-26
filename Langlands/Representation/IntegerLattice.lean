import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Complex.Basic

/-! # Commuting invertible tuples and representations of the integer lattice -/

universe u

namespace Langlands.IntegerLattice

/-- The additive integer lattice, written multiplicatively for `Representation`. -/
abbrev Lattice (d : ℕ) := Multiplicative (Fin d → ℤ)

/-- The standard lattice generator in coordinate `i`. -/
def generator (d : ℕ) (i : Fin d) : Lattice d :=
  Multiplicative.ofAdd (Pi.single i 1)

variable (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- A finite tuple of actual invertible complex-linear maps, commuting pairwise. -/
abbrev CommutingInvertibleTuple :=
  { u : Fin d → (Module.End ℂ V)ˣ // Pairwise fun i j => Commute (u i) (u j) }

private def coordinateEquiv : Lattice d ≃* (Fin d → Multiplicative ℤ) :=
  MulEquiv.piMultiplicative (fun _ : Fin d => ℤ)

private theorem coordinateEquiv_generator (i : Fin d) :
    coordinateEquiv d (generator d i) = Pi.mulSingle i (Multiplicative.ofAdd 1) := by
  ext j
  by_cases h : i = j
  · subst j
    simp [coordinateEquiv, generator]
  · simp [coordinateEquiv, generator, h]

private def powersFamilyEquiv :
    CommutingInvertibleTuple d V ≃
      { f : Fin d → (Multiplicative ℤ →* (Module.End ℂ V)ˣ) //
        Pairwise fun i j => ∀ x y, Commute (f i x) (f j y) } where
  toFun u := ⟨fun i => zpowersHom _ (u.1 i), fun _ _ hij x y =>
    (u.2 hij).zpow_zpow x.toAdd y.toAdd⟩
  invFun f := ⟨fun i => f.1 i (Multiplicative.ofAdd 1),
    fun _ _ hij => f.2 hij _ _⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    exact zpow_one (u.1 i)
  right_inv f := by
    apply Subtype.ext
    funext i
    exact (zpowersHom ((Module.End ℂ V)ˣ)).apply_symm_apply (f.1 i)

private def unitsRepresentationEquiv :
    (Lattice d →* (Module.End ℂ V)ˣ) ≃ Representation ℂ (Lattice d) V where
  toFun f := (Units.coeHom _).comp f
  invFun ρ := ρ.asGroupHom
  left_inv f := by
    ext n
    rfl
  right_inv ρ := by
    ext n
    rfl

/-- Renard C.III's tuple/representation equivalence, valid in arbitrary dimension. -/
def tupleRepresentationEquiv :
    CommutingInvertibleTuple d V ≃ Representation ℂ (Lattice d) V :=
  (((powersFamilyEquiv d V).trans MonoidHom.noncommPiCoprodEquiv).trans
    (coordinateEquiv d).symm.monoidHomCongrLeftEquiv).trans
    (unitsRepresentationEquiv d V)

/-- The action is the finite product of the specified integer powers. -/
theorem tupleRepresentationEquiv_apply (u : CommutingInvertibleTuple d V)
    (n : Lattice d) :
    tupleRepresentationEquiv d V u n =
      ((Finset.univ.noncommProd (fun i => u.1 i ^ n.toAdd i)
        (fun _ _ _ _ hij => (u.2 hij).zpow_zpow _ _) : (Module.End ℂ V)ˣ) :
        Module.End ℂ V) := rfl

/-- The reverse map takes the invertible values of a representation at the generators. -/
theorem tupleRepresentationEquiv_symm_apply (ρ : Representation ℂ (Lattice d) V)
    (i : Fin d) :
    ((tupleRepresentationEquiv d V).symm ρ).1 i = ρ.asGroupHom (generator d i) := by
  change ρ.asGroupHom ((coordinateEquiv d).symm
    (Pi.mulSingle i (Multiplicative.ofAdd 1))) = _
  rw [← coordinateEquiv_generator, MulEquiv.symm_apply_apply]

/-- The generator maps commute, as images of elements of the abelian lattice. -/
theorem generator_values_commute (ρ : Representation ℂ (Lattice d) V) (i j : Fin d) :
    Commute (ρ.asGroupHom (generator d i)) (ρ.asGroupHom (generator d j)) :=
  (Commute.all (generator d i) (generator d j)).map ρ.asGroupHom

/-- The underlying map of the reverse tuple is the original generator action. -/
@[simp] theorem tupleRepresentationEquiv_symm_apply_coe
    (ρ : Representation ℂ (Lattice d) V) (i : Fin d) :
    (((tupleRepresentationEquiv d V).symm ρ).1 i : Module.End ℂ V) =
      ρ (generator d i) := by
  rw [tupleRepresentationEquiv_symm_apply, Representation.asGroupHom_apply]

/-- The actual inverse of a reverse tuple entry is the action at the negative generator. -/
theorem tupleRepresentationEquiv_symm_apply_inv
    (ρ : Representation ℂ (Lattice d) V) (i : Fin d) :
    (((((tupleRepresentationEquiv d V).symm ρ).1 i)⁻¹ : (Module.End ℂ V)ˣ) :
      Module.End ℂ V) =
      ρ ((generator d i)⁻¹) := by
  rw [tupleRepresentationEquiv_symm_apply, ← map_inv, Representation.asGroupHom_apply]

/-- Evaluating at a standard generator recovers the exact unit, including its inverse. -/
@[simp] theorem tupleRepresentationEquiv_asGroupHom_generator
    (u : CommutingInvertibleTuple d V) (i : Fin d) :
    (tupleRepresentationEquiv d V u).asGroupHom (generator d i) = u.1 i := by
  rw [← tupleRepresentationEquiv_symm_apply]
  exact congrArg (fun t : CommutingInvertibleTuple d V => t.1 i)
    ((tupleRepresentationEquiv d V).symm_apply_apply u)

/-- Evaluating the constructed representation at a standard generator recovers its map. -/
@[simp] theorem tupleRepresentationEquiv_generator (u : CommutingInvertibleTuple d V)
    (i : Fin d) :
    tupleRepresentationEquiv d V u (generator d i) = (u.1 i : Module.End ℂ V) := by
  rw [← Representation.asGroupHom_apply, tupleRepresentationEquiv_asGroupHom_generator]

/-- The same integer-power product formula evaluated on a vector. -/
theorem tupleRepresentationEquiv_apply_apply (u : CommutingInvertibleTuple d V)
    (n : Lattice d) (v : V) :
    tupleRepresentationEquiv d V u n v =
      ((Finset.univ.noncommProd (fun i => u.1 i ^ n.toAdd i)
        (fun _ _ _ _ hij => (u.2 hij).zpow_zpow _ _) : (Module.End ℂ V)ˣ) :
        Module.End ℂ V) v :=
  congrArg (fun f : Module.End ℂ V => f v) (tupleRepresentationEquiv_apply d V u n)

/-- Two-sided reconstruction of the tuple. -/
@[simp] theorem tupleRepresentationEquiv_left_inv (u : CommutingInvertibleTuple d V) :
    (tupleRepresentationEquiv d V).symm (tupleRepresentationEquiv d V u) = u :=
  (tupleRepresentationEquiv d V).symm_apply_apply u

/-- Two-sided reconstruction of the representation. -/
@[simp] theorem tupleRepresentationEquiv_right_inv (ρ : Representation ℂ (Lattice d) V) :
    tupleRepresentationEquiv d V ((tupleRepresentationEquiv d V).symm ρ) = ρ :=
  (tupleRepresentationEquiv d V).apply_symm_apply ρ

/-- Every lattice action is reconstructed from all integer powers of its generator values. -/
theorem representation_eq_product (ρ : Representation ℂ (Lattice d) V) (n : Lattice d) :
    ρ n =
      ((Finset.univ.noncommProd
        (fun i => ρ.asGroupHom (generator d i) ^ n.toAdd i)
        (fun i _ j _ _ => (generator_values_commute d V ρ i j).zpow_zpow _ _) :
          (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
  have h := tupleRepresentationEquiv_apply d V ((tupleRepresentationEquiv d V).symm ρ) n
  rw [tupleRepresentationEquiv_right_inv] at h
  simpa only [tupleRepresentationEquiv_symm_apply] using h

/-- With no coordinates the action is the identity, the empty product. -/
@[simp] theorem tupleRepresentationEquiv_zero (u : CommutingInvertibleTuple 0 V)
    (n : Lattice 0) :
    tupleRepresentationEquiv 0 V u n = 1 := by
  rw [tupleRepresentationEquiv_apply]
  simp

/-- The source's finite-dimensional case is the same construction with no extra hypothesis. -/
def finiteDimensionalTupleRepresentationEquiv [FiniteDimensional ℂ V] :
    CommutingInvertibleTuple d V ≃ Representation ℂ (Lattice d) V :=
  tupleRepresentationEquiv d V

end Langlands.IntegerLattice

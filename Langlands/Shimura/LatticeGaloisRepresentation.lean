import Langlands.Shimura.ContinuousGaloisAction

/-! # Galois lattices and their continuous Galois representations

Let `O → L` be an algebra from a commutative ring to a topological field and let `V` be a Galois
action on a finite free `O`-module. Extending scalars gives a Galois action on the
finite-dimensional `L`-vector space `L ⊗[O] V`. If the matrix coefficients `g ↦ f(g · x)` of
the lattice, with values in `L`, are continuous, this is a continuous Galois representation. At a
finite place where the lattice is unramified, its Euler polynomial is the image in `L[X]` of the
Frobenius Euler polynomial of the lattice. See `LatticeGaloisRepresentation.md`.
-/

noncomputable section

universe uO uL uV uK

set_option autoImplicit false

namespace Langlands.Shimura.LatticeGaloisRepresentation

open CategoryTheory Polynomial TensorProduct
open Langlands.GaloisRepresentation (Objects ClosureEmbedding IsContinuous)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius localRestriction)

/-! ## Continuous finite-dimensional Galois actions -/

section General

variable {K : Type uK} [Field K] {L : Type uL} [Field L] [TopologicalSpace L]
  (M : Action (ModuleCat.{uV} L) (Field.absoluteGaloisGroup K)) [Module.Finite L M.V]

/-- A finite-dimensional Galois action whose representation is continuous for the module topology
on its endomorphisms, as a continuous Galois representation. -/
def ofContinuous (hM : IsContinuous (ContinuousGaloisAction.finiteRepresentation M)) :
    Objects.{uK, uL, uV} K L :=
  ⟨ContinuousGaloisAction.finiteRepresentation M, hM⟩

variable (hM : IsContinuous (ContinuousGaloisAction.finiteRepresentation M))

@[simp] theorem ofContinuous_val :
    (ofContinuous M hM).val = ContinuousGaloisAction.finiteRepresentation M :=
  rfl

variable [NumberField K] (v : Global.FinitePlace K)

/-- The continuous Galois representation has Euler polynomial `P` at `v` exactly when the action
is unramified at `v` with Frobenius Euler polynomial `P`. -/
theorem hasEulerPolynomialAt_ofContinuous_iff {P : L[X]} :
    GaloisRepresentation.HasEulerPolynomialAt (ofContinuous M hM) v P ↔
      IsUnramifiedAt (ModuleCat.{uV} L) v M ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial v M = P := by
  rw [GaloisRepresentation.hasEulerPolynomialAt_iff]
  exact and_congr (forall_congr' fun _ =>
    ⟨fun h => ModuleCat.hom_ext h, fun h => congrArg ModuleCat.Hom.hom h⟩) Iff.rfl

end General

/-! ## Extension of scalars of a Galois lattice -/

section Lattice

variable {K : Type uK} [Field K] {O : Type uO} [CommRing O] {L : Type uL} [Field L]
  [Algebra O L] (V : Action (ModuleCat.{uV} O) (Field.absoluteGaloisGroup K))

/-- The Galois action on `L ⊗[O] V` obtained by extending scalars along `O → L`. -/
def baseChangeAction :
    Action (ModuleCat.{max uL uV} L) (Field.absoluteGaloisGroup K) where
  V := ModuleCat.of L (L ⊗[O] V.V)
  ρ :=
    { toFun := fun g => ModuleCat.ofHom ((V.ρ g).hom.baseChange L)
      map_one' := by
        apply ModuleCat.hom_ext
        rw [map_one]
        exact LinearMap.baseChange_id
      map_mul' := fun g h => by
        apply ModuleCat.hom_ext
        rw [map_mul]
        exact LinearMap.baseChange_comp _ _ }

theorem baseChangeAction_ρ_hom (g : Field.absoluteGaloisGroup K) :
    ((baseChangeAction (L := L) V).ρ g).hom = (V.ρ g).hom.baseChange L :=
  rfl

instance [Module.Finite O V.V] : Module.Finite L (baseChangeAction (L := L) V).V :=
  inferInstanceAs (Module.Finite L (L ⊗[O] V.V))

instance [Module.Free O V.V] : Module.Free L (baseChangeAction (L := L) V).V :=
  inferInstanceAs (Module.Free L (L ⊗[O] V.V))

/-- The matrix coefficients `g ↦ f(g · x)` of the lattice, for `O`-linear forms `f` and vectors
`x`, are continuous with values in `L`. -/
def IsLatticeContinuous [TopologicalSpace L] : Prop :=
  ∀ (f : V.V →ₗ[O] O) (x : V.V),
    Continuous fun g : Field.absoluteGaloisGroup K => algebraMap O L (f ((V.ρ g).hom x))

section Places

variable [NumberField K] (v : Global.FinitePlace K)

variable {v} in
/-- If the lattice is unramified at `v` along `ι`, so is its extension of scalars. -/
theorem isUnramifiedAlong_baseChange
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} O) v V ι) :
    IsUnramifiedAlong (ModuleCat.{max uL uV} L) v (baseChangeAction (L := L) V) ι := by
  intro i
  apply ModuleCat.hom_ext
  change ((V.ρ (localRestriction v ι i.val)).hom).baseChange L = LinearMap.id
  rw [show V.ρ (localRestriction v ι i.val) = 𝟙 V.V from hu i]
  exact LinearMap.baseChange_id

variable [Module.Free O V.V] [Module.Finite O V.V]

/-- The Frobenius Euler polynomial of the extension of scalars is the image of the Frobenius
Euler polynomial of the lattice. -/
theorem frobeniusEulerPolynomial_baseChange :
    FrobeniusPolynomial.frobeniusEulerPolynomial v (baseChangeAction (L := L) V) =
      (FrobeniusPolynomial.frobeniusEulerPolynomial v V).map (algebraMap O L) := by
  let ι := Langlands.GaloisRepresentation.chosenClosureEmbedding
    (NumberField.FinitePlace.embedding (K := K) v)
  rw [FrobeniusPolynomial.frobeniusEulerPolynomial_eq_along ι,
    FrobeniusPolynomial.frobeniusEulerPolynomial_eq_along ι]
  change (((V.ρ (localRestriction v ι
      (Langlands.GaloisRepresentation.geometricFrobeniusLift v))).hom).baseChange L).charpoly.reverse =
    ((V.ρ (localRestriction v ι
      (Langlands.GaloisRepresentation.geometricFrobeniusLift v))).hom).charpoly.reverse.map
        (algebraMap O L)
  rw [LinearMap.charpoly_baseChange, Polynomial.reverse, Polynomial.reverse,
    (LinearMap.charpoly_monic _).natDegree_map, Polynomial.reflect_map]

end Places

/-! ## Continuity -/

section Continuity

variable [TopologicalSpace L] [IsTopologicalRing L] [Module.Free O V.V] [Module.Finite O V.V]

/-- If the matrix coefficients of a finite free Galois lattice are continuous, the Galois action
on the extension of scalars is continuous for the module topology on its endomorphisms. -/
theorem isContinuous_baseChange (hV : IsLatticeContinuous (L := L) V) :
    IsContinuous (ContinuousGaloisAction.finiteRepresentation (baseChangeAction (L := L) V)) := by
  classical
  let b := Module.Free.chooseBasis O V.V
  let bL : Module.Basis (Module.Free.ChooseBasisIndex O V.V) L
      (baseChangeAction (L := L) V).V :=
    Algebra.TensorProduct.basis L b
  let _ : TopologicalSpace (Module.End L (baseChangeAction (L := L) V).V) :=
    moduleTopology L (Module.End L (baseChangeAction (L := L) V).V)
  have : IsModuleTopology L (Module.End L (baseChangeAction (L := L) V).V) := ⟨rfl⟩
  have : ContinuousAdd (Module.End L (baseChangeAction (L := L) V).V) :=
    IsModuleTopology.toContinuousAdd L _
  have : IsModuleTopology L (Matrix (Module.Free.ChooseBasisIndex O V.V)
      (Module.Free.ChooseBasisIndex O V.V) L) :=
    inferInstanceAs (IsModuleTopology L (Module.Free.ChooseBasisIndex O V.V →
      Module.Free.ChooseBasisIndex O V.V → L))
  let e := LinearMap.toMatrix bL bL
  have hsymm : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hentries : Continuous fun g : Field.absoluteGaloisGroup K =>
      e ((baseChangeAction (L := L) V).ρ g).hom := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have heq : (fun g : Field.absoluteGaloisGroup K =>
        e ((baseChangeAction (L := L) V).ρ g).hom i j) =
        fun g => algebraMap O L (b.coord i ((V.ρ g).hom (b j))) := by
      funext g
      change LinearMap.toMatrix (Algebra.TensorProduct.basis L b)
          (Algebra.TensorProduct.basis L b)
          ((V.ρ g).hom.baseChange L : L ⊗[O] V.V →ₗ[L] L ⊗[O] V.V) i j =
        algebraMap O L (b.repr ((V.ρ g).hom (b j)) i)
      rw [LinearMap.toMatrix_apply, Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.basis_repr_tmul]
      simp
    rw [heq]
    exact hV (b.coord i) (b j)
  show Continuous ((ModuleCat.endRingEquiv (baseChangeAction (L := L) V).V).toMonoidHom.comp
    (baseChangeAction (L := L) V).ρ)
  have hfun : ⇑((ModuleCat.endRingEquiv (baseChangeAction (L := L) V).V).toMonoidHom.comp
      (baseChangeAction (L := L) V).ρ) =
      e.symm ∘ fun g => e ((baseChangeAction (L := L) V).ρ g).hom := by
    funext g
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
    rfl
  rw [hfun]
  exact hsymm.comp hentries

/-- A finite free Galois lattice with continuous matrix coefficients, with scalars extended to
`L`, as a continuous Galois representation. -/
def latticeObjects (hV : IsLatticeContinuous (L := L) V) : Objects.{uK, uL, max uL uV} K L :=
  ofContinuous (baseChangeAction (L := L) V) (isContinuous_baseChange V hV)

variable (hV : IsLatticeContinuous (L := L) V)

/-- The dimension of the Galois representation is the rank of the lattice. -/
theorem latticeObjects_rank [Nontrivial O] :
    (latticeObjects V hV).val.rank = Module.finrank O V.V :=
  Module.finrank_baseChange

variable [NumberField K] (v : Global.FinitePlace K)

/-- If the lattice is unramified at `v`, the continuous Galois representation has as Euler
polynomial at `v` the image of the Frobenius Euler polynomial of the lattice. -/
theorem hasEulerPolynomialAt_latticeObjects (hu : IsUnramifiedAt (ModuleCat.{uV} O) v V) :
    GaloisRepresentation.HasEulerPolynomialAt (latticeObjects V hV) v
      ((FrobeniusPolynomial.frobeniusEulerPolynomial v V).map (algebraMap O L)) :=
  (hasEulerPolynomialAt_ofContinuous_iff _ _ v).2
    ⟨isUnramifiedAlong_baseChange V hu, frobeniusEulerPolynomial_baseChange V v⟩

end Continuity

end Lattice

end Langlands.Shimura.LatticeGaloisRepresentation

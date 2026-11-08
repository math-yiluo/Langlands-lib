import Langlands.Shimura.FrobeniusPolynomial
import Langlands.Galois.FrobeniusLift
import Langlands.Representation.Smooth.Definitions

/-! # Smooth Galois actions as continuous Galois representations

A smooth representation of a topological group on a finitely generated module, one in which every
vector is fixed by an open subgroup, is trivial on an open subgroup and hence locally constant;
in particular it is continuous for every topology on the endomorphisms. A smooth action of the
absolute Galois group of a field `K` on a finite-dimensional space over a topological field `L` is
therefore a continuous Galois representation in the sense of
`Langlands.GaloisRepresentation.Objects`. At a finite place of a number field `K`, its
unramifiedness and Frobenius Euler polynomial agree with those of
`Langlands.Shimura.DecompositionGroupAction` and `Langlands.Shimura.FrobeniusPolynomial`.
See `ContinuousGaloisAction.md`.
-/

noncomputable section

universe u uG uV uK uL

set_option autoImplicit false

namespace Langlands.Shimura.ContinuousGaloisAction

open CategoryTheory Polynomial
open Langlands.GaloisRepresentation (Objects IsContinuous LocalGroup ClosureEmbedding
  chosenClosureEmbedding)
open Langlands.Shimura.DecompositionGroupAction (localRestriction geometricFrobenius)

/-! ## Smooth representations on finitely generated modules -/

section Smooth

variable {R : Type u} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module R V] [Module.Finite R V]

/-- A smooth representation on a finitely generated module is trivial on an open subgroup: the
intersection of open subgroups fixing a finite generating set. -/
theorem exists_openSubgroup_le_ker {ρ : Representation R G V} (hρ : IsSmooth ρ) :
    ∃ U : OpenSubgroup G, U.toSubgroup ≤ ρ.ker := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := V)
  choose U hU using hρ
  have htop : fixedVectors ρ (s.inf U).toSubgroup = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]
    intro x hx
    exact (Representation.mem_invariants _ x).2 fun h =>
      (Representation.mem_invariants _ x).1 (hU x)
        ⟨h.1, SetLike.le_def.1 (Finset.inf_le (f := U) hx) h.2⟩
  refine ⟨s.inf U, fun g hg => MonoidHom.mem_ker.2 (LinearMap.ext fun x => ?_)⟩
  have hx : x ∈ fixedVectors ρ (s.inf U).toSubgroup := htop ▸ Submodule.mem_top
  exact (Representation.mem_invariants _ x).1 hx ⟨g, hg⟩

variable [SeparatelyContinuousMul G]

/-- A smooth representation on a finitely generated module is locally constant: it is constant on
the cosets of an open subgroup in its kernel. -/
theorem isLocallyConstant_of_isSmooth {ρ : Representation R G V} (hρ : IsSmooth ρ) :
    IsLocallyConstant ρ := by
  obtain ⟨U, hU⟩ := exists_openSubgroup_le_ker hρ
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ?_
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (U : Set G), U.isOpen.preimage (continuous_const_mul g⁻¹), ?_,
    fun h hh => ?_⟩
  · change g⁻¹ * g ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem
  · have hk : ρ (g⁻¹ * h) = 1 := MonoidHom.mem_ker.1 (hU hh)
    calc
      ρ h = ρ (g * (g⁻¹ * h)) := by rw [mul_inv_cancel_left]
      _ = ρ g := by rw [map_mul, hk, mul_one]

/-- A smooth representation on a finitely generated module is continuous for every topology on
its endomorphisms. -/
theorem continuous_of_isSmooth [TopologicalSpace (Module.End R V)] {ρ : Representation R G V}
    (hρ : IsSmooth ρ) : Continuous ρ :=
  (isLocallyConstant_of_isSmooth hρ).continuous

end Smooth

/-! ## Smooth Galois actions as continuous Galois representations -/

section Galois

variable {K : Type uK} [Field K] {L : Type uL} [Field L]
  (M : Action (ModuleCat.{uV} L) (Field.absoluteGaloisGroup K)) [Module.Finite L M.V]

/-- The finite-dimensional representation of `Gal(K̄/K)` on the space of an action. -/
def finiteRepresentation : FiniteRepresentation.{uL, uK, uV} L (Field.absoluteGaloisGroup K) :=
  ⟨(Rep.ActionToRep L _).obj M, inferInstanceAs (Module.Finite L M.V)⟩

@[simp] theorem finiteRepresentation_representation_apply (g : Field.absoluteGaloisGroup K) :
    (finiteRepresentation M).representation g = (M.ρ g).hom :=
  rfl

theorem finiteRepresentation_rank : (finiteRepresentation M).rank = Module.finrank L M.V :=
  rfl

variable [TopologicalSpace L]

/-- A smooth Galois action on a finite-dimensional space is continuous for the module topology on
its endomorphisms over the topological coefficient field. -/
theorem isContinuous_finiteRepresentation
    (hM : IsSmooth ((Rep.ActionToRep L (Field.absoluteGaloisGroup K)).obj M).ρ) :
    IsContinuous (finiteRepresentation M) := by
  let _ : TopologicalSpace (Module.End L M.V) := moduleTopology L (Module.End L M.V)
  show Continuous ((ModuleCat.endRingEquiv M.V).toMonoidHom.comp M.ρ)
  exact continuous_of_isSmooth hM

/-- A smooth Galois action on a finite-dimensional space over a topological field, as a continuous
Galois representation. -/
def toObjects (hM : IsSmooth ((Rep.ActionToRep L (Field.absoluteGaloisGroup K)).obj M).ρ) :
    Objects.{uK, uL, uV} K L :=
  ⟨finiteRepresentation M, isContinuous_finiteRepresentation M hM⟩

variable (hM : IsSmooth ((Rep.ActionToRep L (Field.absoluteGaloisGroup K)).obj M).ρ)

@[simp] theorem toObjects_val : (toObjects M hM).val = finiteRepresentation M :=
  rfl

theorem characteristicPolynomial_toObjects (g : Field.absoluteGaloisGroup K) :
    GaloisRepresentation.characteristicPolynomial (toObjects M hM) g = (M.ρ g).hom.charpoly :=
  rfl

theorem eulerPolynomial_toObjects (g : Field.absoluteGaloisGroup K) :
    GaloisRepresentation.eulerPolynomial (toObjects M hM) g = (M.ρ g).hom.charpoly.reverse :=
  rfl

/-- The isomorphism class of a smooth Galois action as a continuous Galois representation. -/
def toClass : GaloisRepresentation.Classes.{uK, uL, uV} K L :=
  Quotient.mk _ (toObjects M hM)

variable {M}

/-- An isomorphism of actions is an equivalence of the associated Galois representations. -/
def toObjectsEquivOfIso {N : Action (ModuleCat.{uV} L) (Field.absoluteGaloisGroup K)}
    [Module.Finite L N.V]
    (hN : IsSmooth ((Rep.ActionToRep L (Field.absoluteGaloisGroup K)).obj N).ρ) (e : M ≅ N) :
    FiniteRepresentation.Equiv (toObjects M hM).val (toObjects N hN).val :=
  FiniteRepresentation.equivOfIso
    (ObjectProperty.isoMk _ ((Rep.ActionToRep L (Field.absoluteGaloisGroup K)).mapIso e))

/-- Isomorphic actions have the same class. -/
theorem toClass_eq_of_iso {N : Action (ModuleCat.{uV} L) (Field.absoluteGaloisGroup K)}
    [Module.Finite L N.V]
    (hN : IsSmooth ((Rep.ActionToRep L (Field.absoluteGaloisGroup K)).obj N).ρ) (e : M ≅ N) :
    toClass M hM = toClass N hN :=
  Quotient.sound ⟨toObjectsEquivOfIso hM hN e⟩

variable (M)

theorem classEulerPolynomial_toClass (g : Field.absoluteGaloisGroup K) :
    GaloisRepresentation.classEulerPolynomial g (toClass M hM) = (M.ρ g).hom.charpoly.reverse :=
  rfl

/-! ## Unramifiedness and Frobenius at finite places -/

variable [NumberField K] (v : Global.FinitePlace K)

theorem atFinitePlace_toObjects_representation_apply (g : LocalGroup v) :
    (GaloisRepresentation.atFinitePlace v (toObjects M hM)).val.representation g =
      (M.ρ (localRestriction v
        (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) g)).hom :=
  rfl

/-- Unramifiedness of the continuous Galois representation is unramifiedness of the action. -/
theorem isUnramifiedAt_toObjects_iff :
    GaloisRepresentation.IsUnramifiedAt (toObjects M hM) v ↔
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{uV} L) v M :=
  forall_congr' fun _ => ⟨fun h => ModuleCat.hom_ext h, fun h => congrArg ModuleCat.Hom.hom h⟩

/-- The Euler polynomial at the chosen geometric Frobenius lift is the Frobenius Euler polynomial
of the action. -/
theorem frobeniusEulerPolynomial_toObjects :
    GaloisRepresentation.frobeniusEulerPolynomial (toObjects M hM) v =
      FrobeniusPolynomial.frobeniusEulerPolynomial v M :=
  rfl

/-- The continuous Galois representation has Euler polynomial `P` at `v` exactly when the action
is unramified at `v` with Frobenius Euler polynomial `P`. -/
theorem hasEulerPolynomialAt_toObjects_iff {P : L[X]} :
    GaloisRepresentation.HasEulerPolynomialAt (toObjects M hM) v P ↔
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{uV} L) v M ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial v M = P := by
  rw [GaloisRepresentation.hasEulerPolynomialAt_iff, isUnramifiedAt_toObjects_iff,
    frobeniusEulerPolynomial_toObjects]

/-- The same criterion along any closure embedding at `v`, with the Euler polynomial of the
Frobenius endomorphism along that embedding. -/
theorem hasEulerPolynomialAt_toObjects_iff_along
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) {P : L[X]} :
    GaloisRepresentation.HasEulerPolynomialAt (toObjects M hM) v P ↔
      DecompositionGroupAction.IsUnramifiedAlong (ModuleCat.{uV} L) v M ι ∧
        (geometricFrobenius (ModuleCat.{uV} L) v M ι).hom.charpoly.reverse = P := by
  rw [hasEulerPolynomialAt_toObjects_iff, DecompositionGroupAction.isUnramifiedAt_iff_along M ι,
    FrobeniusPolynomial.frobeniusEulerPolynomial_eq_along ι]

end Galois

/-! ## Smooth linear representations -/

section Rep

variable {K : Type uK} [Field K] {L : Type uL} [Field L]
  (A : Rep.{uV} L (Field.absoluteGaloisGroup K)) [Module.Finite L A]

instance : Module.Finite L ((Rep.RepToAction L (Field.absoluteGaloisGroup K)).obj A).V :=
  inferInstanceAs (Module.Finite L A)

variable [TopologicalSpace L]

/-- A smooth linear representation of `Gal(K̄/K)` on a finite-dimensional space over a topological
field, as a continuous Galois representation, through the associated action. -/
def repToObjects (hA : IsSmooth A.ρ) : Objects.{uK, uL, uV} K L :=
  toObjects ((Rep.RepToAction L (Field.absoluteGaloisGroup K)).obj A) hA

variable (hA : IsSmooth A.ρ)

/-- The underlying representation is the given one. -/
theorem repToObjects_val_obj : (repToObjects A hA).val.obj = A :=
  rfl

variable [NumberField K] (v : Global.FinitePlace K)

/-- The continuous Galois representation has Euler polynomial `P` at `v` exactly when the
associated action is unramified at `v` with Frobenius Euler polynomial `P`. -/
theorem hasEulerPolynomialAt_repToObjects_iff {P : L[X]} :
    GaloisRepresentation.HasEulerPolynomialAt (repToObjects A hA) v P ↔
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{uV} L) v
          ((Rep.RepToAction L (Field.absoluteGaloisGroup K)).obj A) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial v
          ((Rep.RepToAction L (Field.absoluteGaloisGroup K)).obj A) = P :=
  hasEulerPolynomialAt_toObjects_iff ((Rep.RepToAction L (Field.absoluteGaloisGroup K)).obj A) hA v

end Rep

end Langlands.Shimura.ContinuousGaloisAction

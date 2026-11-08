import Langlands.Shimura.IsotypicDecompositionAction
import Langlands.Shimura.ContinuousGaloisAction
import Langlands.Shimura.LevelHeckeModule

/-! # Fixed vectors of smooth Galois actions as continuous Galois representations

Let `X` be a smooth representation of a group `G` with a commuting action of a topological group
`Γ`, and suppose that the action of `Γ` is smooth. For every subgroup `H` of `G`, the induced
action of `Γ` on the `H`-fixed vectors is smooth. For `Γ = Gal(K̄/K)` and finite-dimensional
`H`-fixed vectors over a topological field, the fixed vectors are therefore a continuous Galois
representation, whose Euler polynomial at a finite place where `X` is unramified is the
Frobenius Euler polynomial of the fixed vectors. On the module of `K`-fixed vectors over the
Hecke algebra of `K`, the geometric Frobenius endomorphism is Hecke-linear, and the Euler
polynomial is its reversed characteristic polynomial over the coefficient field. See
`FixedVectorGaloisRepresentation.md`.
-/

noncomputable section

universe uR uG uU uV uΓ uK

set_option autoImplicit false

namespace Langlands.Shimura.FixedVectorGaloisRepresentation

open CategoryTheory Polynomial
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Shimura.LevelHecke (fixedVectorsFunctor fixedVectorsActionFunctor
  heckeModuleFunctor heckeModuleActionFunctor LevelHeckeAlgebra)
open Langlands.GaloisRepresentation (Objects ClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius)

/-! ## Smoothness of the action on fixed vectors -/

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  (H : Subgroup G) {Γ : Type uΓ} [Group Γ] [TopologicalSpace Γ]

/-- If `Γ` acts smoothly on `X`, it acts smoothly on the `H`-fixed vectors. -/
theorem isSmooth_fixedVectors {X : Action (SmoothRep.{uR, uG, uV} R G) Γ}
    (hX : IsSmooth (galoisRepresentation X)) :
    IsSmooth ((Rep.ActionToRep R Γ).obj ((fixedVectorsActionFunctor R Γ H).obj X)).ρ := by
  intro x
  obtain ⟨V, hV⟩ := hX x.1
  exact ⟨V, (Representation.mem_invariants _ _).2 fun γ =>
    Subtype.ext ((Representation.mem_invariants _ _).1 hV γ)⟩

end Smooth

/-! ## The Frobenius endomorphism of Hecke modules of fixed vectors -/

section HeckeFrobenius

variable {K : Type uK} [Field K] [NumberField K] {R : Type uR} [CommRing R] {G : Type uG}
  [Group G] [TopologicalSpace G] (H : Subgroup G)
  (X : Action (SmoothRep.{uR, uG, uV} R G) (Field.absoluteGaloisGroup K))
  (v : Global.FinitePlace K) (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))

/-- The geometric Frobenius endomorphism at `v` along `ι` of the module of `H`-fixed vectors over
the Hecke algebra of `H`, as a Hecke-linear map. -/
def heckeFrobenius :
    fixedVectors X.V.representation H →ₗ[LevelHeckeAlgebra R H]
      fixedVectors X.V.representation H :=
  (geometricFrobenius (ModuleCat.{uV} (LevelHeckeAlgebra R H)) v
    ((heckeModuleActionFunctor R (Field.absoluteGaloisGroup K) H).obj X) ι).hom

/-- On a fixed vector, the Frobenius endomorphism is the action of the chosen geometric Frobenius
lift on `X`, restricted along `ι`. -/
theorem coe_heckeFrobenius_apply (x : fixedVectors X.V.representation H) :
    (heckeFrobenius H X v ι x : X.V) =
      SmoothRep.hom (X.ρ (DecompositionGroupAction.localRestriction v ι
        (GaloisRepresentation.geometricFrobeniusLift v))) x :=
  rfl

/-- The Frobenius endomorphism commutes with the Hecke algebra of `H`. -/
theorem heckeFrobenius_smul (a : LevelHeckeAlgebra R H) (x : fixedVectors X.V.representation H) :
    heckeFrobenius H X v ι (a • x) = a • heckeFrobenius H X v ι x :=
  map_smul _ a x

end HeckeFrobenius

/-! ## Continuous Galois representations on fixed vectors -/

section Galois

variable {K : Type uK} [Field K] {L : Type uR} [Field L] {G : Type uG} [Group G]
  [TopologicalSpace G] (H : Subgroup G)
  (X : Action (SmoothRep.{uR, uG, uV} L G) (Field.absoluteGaloisGroup K))

instance [Module.Finite L (fixedVectors X.V.representation H)] :
    Module.Finite L ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X).V :=
  inferInstanceAs (Module.Finite L (fixedVectors X.V.representation H))

variable [Module.Finite L (fixedVectors X.V.representation H)] [TopologicalSpace L]

/-- The `H`-fixed vectors of a smooth Galois action, finite-dimensional over a topological
field, as a continuous Galois representation. -/
def fixedVectorsObjects (hX : IsSmooth (galoisRepresentation X)) :
    Objects.{uK, uR, uV} K L :=
  ContinuousGaloisAction.toObjects
    ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X)
    (isSmooth_fixedVectors H hX)

variable (hX : IsSmooth (galoisRepresentation X))

/-- A Galois element acts on the fixed vectors by the restriction of its action on `X`. -/
theorem fixedVectorsObjects_representation_apply (g : Field.absoluteGaloisGroup K) :
    (fixedVectorsObjects H X hX).val.representation g =
      fixedVectorsMap (SmoothRep.hom (X.ρ g)) H :=
  rfl

/-- The dimension of the Galois representation is that of the fixed vectors. -/
theorem fixedVectorsObjects_rank :
    (fixedVectorsObjects H X hX).val.rank = Module.finrank L (fixedVectors X.V.representation H) :=
  rfl

variable [NumberField K] (v : Global.FinitePlace K)

/-- The Galois representation on the fixed vectors has Euler polynomial `P` at `v` exactly when
the fixed vectors are unramified at `v` with Frobenius Euler polynomial `P`. -/
theorem hasEulerPolynomialAt_fixedVectorsObjects_iff {P : L[X]} :
    HasEulerPolynomialAt (fixedVectorsObjects H X hX) v P ↔
      IsUnramifiedAt (ModuleCat.{uV} L) v
          ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial v
          ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) = P :=
  ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff _ _ v

omit [Module.Finite L (fixedVectors X.V.representation H)] [TopologicalSpace L] in
variable {v} in
/-- If `X` is unramified at `v` along `ι`, so are its `H`-fixed vectors. -/
theorem isUnramifiedAlong_fixedVectors
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hu : IsUnramifiedAlong (SmoothRep.{uR, uG, uV} L G) v X ι) :
    IsUnramifiedAlong (ModuleCat.{uV} L) v
      ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) ι :=
  hu.mapAction (fixedVectorsFunctor L H)

omit [Module.Finite L (fixedVectors X.V.representation H)] [TopologicalSpace L] in
variable {v} in
/-- If the `H`-fixed vectors of `X` are unramified at `v` along `ι`, so are the `H`-fixed vectors
of every isotypic part of `X`, which form a Galois-stable subspace. -/
theorem isUnramifiedAlong_fixedVectors_isotypic {U : Type uU} [AddCommGroup U] [Module L U]
    (τ : Representation L G U) {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} L) v
      ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) ι) :
    IsUnramifiedAlong (ModuleCat.{uV} L) v
      ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj
        ((isotypicActionFunctor τ (Field.absoluteGaloisGroup K)).obj X)) ι := by
  intro i
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have hx : (x.1.1 : X.V) ∈ fixedVectors X.V.representation H :=
    (Representation.mem_invariants _ _).2 fun g =>
      congrArg Subtype.val ((Representation.mem_invariants _ _).1 x.2 g)
  have key : SmoothRep.hom (X.ρ (DecompositionGroupAction.localRestriction v ι i.val)) x.1.1 =
      x.1.1 :=
    congrArg Subtype.val
      (congrArg (fun f => f.hom (⟨x.1.1, hx⟩ : fixedVectors X.V.representation H)) (hu i))
  exact Subtype.ext (Subtype.ext key)

/-- If the fixed vectors are unramified at `v` along `ι`, the Galois representation on them has
as Euler polynomial at `v` the reversed characteristic polynomial of their geometric Frobenius
endomorphism along `ι`. -/
theorem hasEulerPolynomialAt_fixedVectorsObjects_of_isUnramifiedAlong
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} L) v
      ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) ι) :
    HasEulerPolynomialAt (fixedVectorsObjects H X hX) v
      (geometricFrobenius (ModuleCat.{uV} L) v
        ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) ι).hom.charpoly.reverse :=
  (ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff_along _ _ v ι).2 ⟨hu, rfl⟩

/-- If the fixed vectors are unramified at `v`, the Galois representation on them has as Euler
polynomial at `v` their Frobenius Euler polynomial. -/
theorem hasEulerPolynomialAt_fixedVectorsObjects_of_isUnramifiedAt
    (hu : IsUnramifiedAt (ModuleCat.{uV} L) v
      ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X)) :
    HasEulerPolynomialAt (fixedVectorsObjects H X hX) v
      (FrobeniusPolynomial.frobeniusEulerPolynomial v
        ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X)) :=
  (hasEulerPolynomialAt_fixedVectorsObjects_iff H X hX v).2 ⟨hu, rfl⟩

/-! ### Hecke modules -/

omit [Module.Finite L (fixedVectors X.V.representation H)] [TopologicalSpace L] in
/-- The geometric Frobenius endomorphism of the `H`-fixed vectors is the Hecke-linear geometric
Frobenius endomorphism of the Hecke module of `H`-fixed vectors, with scalars restricted to
`L`. -/
theorem geometricFrobenius_fixedVectors_eq_restrictScalars
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    (geometricFrobenius (ModuleCat.{uV} L) v
        ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) ι).hom =
      (heckeFrobenius H X v ι).restrictScalars L :=
  rfl

/-- If the `H`-fixed vectors are unramified at `v` along `ι`, the Galois representation on them
has as Euler polynomial at `v` the reversed characteristic polynomial over `L` of the
Hecke-linear geometric Frobenius endomorphism of the Hecke module of `H`-fixed vectors along
`ι`. -/
theorem hasEulerPolynomialAt_fixedVectorsObjects_heckeFrobenius
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} L) v
      ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) ι) :
    HasEulerPolynomialAt (fixedVectorsObjects H X hX) v
      ((heckeFrobenius H X v ι).restrictScalars L).charpoly.reverse :=
  hasEulerPolynomialAt_fixedVectorsObjects_of_isUnramifiedAlong H X hX v hu

end Galois

end Langlands.Shimura.FixedVectorGaloisRepresentation

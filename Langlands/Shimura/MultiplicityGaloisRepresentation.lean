import Langlands.Shimura.IsotypicDecompositionAction
import Langlands.Shimura.ContinuousGaloisAction
import Langlands.Cohomology.HyperextHomLocalization

/-! # Smooth multiplicity spaces as continuous Galois representations

Let `τ` be a representation of a group `G` that is finitely generated over the group algebra,
and let `X` be a smooth representation of `G` with a commuting action of a topological group `Γ`
that is smooth (every vector fixed by an open subgroup). Then the restricted action of `Γ` on the
`τ`-isotypic part and the action of `Γ` on the multiplicity space `Hom_G(τ, X)` by composition
are smooth: an intertwining map is determined by its values on finitely many generators of `τ`.
For `Γ = Gal(K̄/K)` and a finite-dimensional multiplicity space over a topological field, the
multiplicity space is therefore a continuous Galois representation, whose Euler polynomial at a
finite place where `X` is unramified is the Frobenius Euler polynomial of the multiplicity space.
See `MultiplicityGaloisRepresentation.md`.
-/

noncomputable section

universe uR uG uU uV uΓ uK

set_option autoImplicit false

namespace Langlands.Shimura.MultiplicityGaloisRepresentation

open CategoryTheory Polynomial
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Cohomology.HyperextAbutment (isotypicPart)
open Langlands.GaloisRepresentation (Objects ClosureEmbedding)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius)

/-! ## Smoothness of isotypic parts and multiplicity spaces -/

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  {U : Type uU} [AddCommGroup U] [Module R U] (τ : Representation R G U)
  {Γ : Type uΓ} [Group Γ] [TopologicalSpace Γ]

/-- The restricted action of `Γ` on the `τ`-isotypic part of a smooth `Γ`-action is smooth. -/
theorem isSmooth_isotypicGaloisRepresentation {X : Action (SmoothRep.{uR, uG, uV} R G) Γ}
    (hX : IsSmooth (galoisRepresentation X)) :
    IsSmooth (isotypicGaloisRepresentation τ Γ X) := by
  intro x
  obtain ⟨V, hV⟩ := hX x.1
  exact ⟨V, (Representation.mem_invariants _ _).2 fun γ =>
    Subtype.ext ((Representation.mem_invariants _ _).1 hV γ)⟩

/-- If `τ` is finitely generated over the group algebra and `Γ` acts smoothly on `X`, then `Γ`
acts smoothly on the multiplicity space `Hom_G(τ, X)`: an open subgroup fixing the values of an
intertwining map on finitely many generators fixes the intertwining map. -/
theorem isSmooth_multiplicityRepresentation [Module.Finite (MonoidAlgebra R G) τ.asModule]
    {X : Action (SmoothRep.{uR, uG, uV} R G) Γ} (hX : IsSmooth (galoisRepresentation X)) :
    IsSmooth (multiplicityRepresentation τ Γ X) := by
  classical
  obtain ⟨t, ht⟩ :=
    Langlands.Cohomology.HyperextScalarExtension.exists_finset_eq_top_of_finite_asModule τ
  intro φ
  choose V hV using fun u : U => hX (φ u)
  refine ⟨t.inf V, (Representation.mem_invariants _ _).2 fun γ => ?_⟩
  have hfix : ∀ u ∈ t, SmoothRep.hom (X.ρ γ.1) (φ u) = φ u := fun u hu =>
    (Representation.mem_invariants _ _).1 (hV u)
      ⟨γ.1, SetLike.le_def.1 (Finset.inf_le (f := V) hu) γ.2⟩
  have hstable : ∀ (g : G), ∀ u ∈ LinearMap.eqLocus
      ((SmoothRep.hom (X.ρ γ.1)).toLinearMap ∘ₗ φ.toLinearMap) φ.toLinearMap,
      τ g u ∈ LinearMap.eqLocus
        ((SmoothRep.hom (X.ρ γ.1)).toLinearMap ∘ₗ φ.toLinearMap) φ.toLinearMap := by
    intro g u hu
    rw [LinearMap.mem_eqLocus] at hu ⊢
    change SmoothRep.hom (X.ρ γ.1) (φ (τ g u)) = φ (τ g u)
    change SmoothRep.hom (X.ρ γ.1) (φ u) = φ u at hu
    rw [φ.isIntertwining, ← galoisRepresentation_apply, galoisRepresentation_commutes,
      galoisRepresentation_apply, hu]
  have htop := ht _ hstable fun u hu => LinearMap.mem_eqLocus.2 (hfix u hu)
  exact Representation.IntertwiningMap.ext (LinearMap.eqLocus_eq_top.1 htop)

end Smooth

/-! ## Continuous Galois representations on multiplicity spaces -/

section Galois

variable {K : Type uK} [Field K] {L : Type uR} [Field L] {G : Type uG} [Group G]
  [TopologicalSpace G] {U : Type uU} [AddCommGroup U] [Module L U] (τ : Representation L G U)
  (X : Action (SmoothRep.{uR, uG, uV} L G) (Field.absoluteGaloisGroup K))

instance [Module.Finite L (τ.IntertwiningMap X.V.representation)] :
    Module.Finite L ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup K)).obj X).V :=
  inferInstanceAs (Module.Finite L (τ.IntertwiningMap X.V.representation))

variable [Module.Finite (MonoidAlgebra L G) τ.asModule]
  [Module.Finite L (τ.IntertwiningMap X.V.representation)] [TopologicalSpace L]

/-- The multiplicity space `Hom_G(τ, X)` of a smooth Galois action, finite-dimensional over a
topological field, as a continuous Galois representation with `Gal(K̄/K)` acting by
composition. -/
def multiplicityObjects (hX : IsSmooth (galoisRepresentation X)) :
    Objects.{uK, uR, max uU uV} K L :=
  ContinuousGaloisAction.toObjects
    ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup K)).obj X)
    (isSmooth_multiplicityRepresentation τ hX)

variable (hX : IsSmooth (galoisRepresentation X))

/-- A Galois element acts on an intertwining map by composition with its action on `X`. -/
theorem multiplicityObjects_representation_apply (g : Field.absoluteGaloisGroup K)
    (φ : τ.IntertwiningMap X.V.representation) :
    (multiplicityObjects τ X hX).val.representation g φ = (SmoothRep.hom (X.ρ g)).comp φ :=
  rfl

/-- The dimension of the Galois representation is that of the multiplicity space. -/
theorem multiplicityObjects_rank :
    (multiplicityObjects τ X hX).val.rank = Module.finrank L (τ.IntertwiningMap X.V.representation) :=
  rfl

variable [NumberField K] (v : Global.FinitePlace K)

/-- The Galois representation on the multiplicity space has Euler polynomial `P` at `v` exactly
when the multiplicity space is unramified at `v` with Frobenius Euler polynomial `P`. -/
theorem hasEulerPolynomialAt_multiplicityObjects_iff {P : L[X]} :
    GaloisRepresentation.HasEulerPolynomialAt (multiplicityObjects τ X hX) v P ↔
      IsUnramifiedAt (ModuleCat.{max uU uV} L) v
          ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup K)).obj X) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial v
          ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup K)).obj X) = P :=
  ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff _ _ v

/-- If `X` is unramified at `v` along a closure embedding `ι`, the Galois representation on the
multiplicity space has as Euler polynomial at `v` the reversed characteristic polynomial
`det(1 - Frob_v X)` of the geometric Frobenius endomorphism of the multiplicity space along
`ι`. -/
theorem hasEulerPolynomialAt_multiplicityObjects_of_isUnramifiedAlong
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hu : IsUnramifiedAlong (SmoothRep.{uR, uG, uV} L G) v X ι) :
    GaloisRepresentation.HasEulerPolynomialAt (multiplicityObjects τ X hX) v
      (geometricFrobenius (ModuleCat.{max uU uV} L) v
        ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup K)).obj X) ι).hom.charpoly.reverse :=
  (ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff_along _ _ v ι).2
    ⟨hu.multiplicity τ, rfl⟩

/-- If `X` is unramified at `v`, the Galois representation on the multiplicity space has as Euler
polynomial at `v` the Frobenius Euler polynomial of the multiplicity space. -/
theorem hasEulerPolynomialAt_multiplicityObjects_of_isUnramifiedAt
    (hu : IsUnramifiedAt (SmoothRep.{uR, uG, uV} L G) v X) :
    GaloisRepresentation.HasEulerPolynomialAt (multiplicityObjects τ X hX) v
      (FrobeniusPolynomial.frobeniusEulerPolynomial v
        ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup K)).obj X)) :=
  (hasEulerPolynomialAt_multiplicityObjects_iff τ X hX v).2
    ⟨DecompositionGroupAction.IsUnramifiedAlong.multiplicity τ hu, rfl⟩

end Galois

end Langlands.Shimura.MultiplicityGaloisRepresentation

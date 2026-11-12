import Langlands.Shimura.ContinuousOrbitTransfer
import Langlands.Shimura.HeckeMultiplicityGaloisRepresentation

/-! # Continuous Galois representations on fixed-level isotypic parts and multiplicity spaces

Let `X` be a smooth representation of a group `G` over a topological field `M` with a commuting
action of `Gal(F̄/F)`, whose `H`-fixed vectors, for a subgroup `H`, form a finite-dimensional space
on which the Galois group acts with continuous orbit maps; the Galois action on `X` itself need not
be smooth. For a representation `τ` of `G`, the `H`-fixed vectors of the `τ`-isotypic part, the
multiplicity space `Hom_G(τ, X)` (when `τ` is spanned by the translates of its `H`-fixed vectors)
and the Hecke multiplicity space `Hom_{H(H)}(T, X^H)` map equivariantly and jointly injectively to
`X^H`. Hence, when finite-dimensional, they are continuous Galois representations, unramified
wherever `X^H` is, with Euler polynomials given by their geometric Frobenius endomorphisms. See
`ContinuousIsotypicGaloisRepresentation.md`.
-/

noncomputable section

universe uF uM uG uU uT uV

set_option autoImplicit false

namespace Langlands.Shimura.ContinuousIsotypicGaloisRepresentation

open CategoryTheory Polynomial
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Shimura.HeckeMultiplicityGaloisRepresentation
  (heckeMultiplicityActionFunctor isUnramifiedAlong_heckeMultiplicity)
open Langlands.Shimura.LevelHecke (fixedVectorsActionFunctor LevelHeckeAlgebra)
open Langlands.Shimura.ContinuousGaloisAction (HasContinuousOrbits
  isContinuous_finiteRepresentation_of_hasContinuousOrbits)
open Langlands.GaloisRepresentation (Objects ClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius)

/-! ## Finite-dimensional Galois actions with continuous orbits -/

section General

variable {F : Type uF} [Field F] {M : Type uM} [Field M] [TopologicalSpace M]
  [IsTopologicalRing M] (A : Action (ModuleCat.{uV} M) (Field.absoluteGaloisGroup F))
  [Module.Finite M A.V]

/-- A finite-dimensional Galois action whose orbit maps are continuous, as a continuous Galois
representation. -/
def continuousOrbitsObjects (hA : HasContinuousOrbits A) : Objects.{uF, uM, uV} F M :=
  LatticeGaloisRepresentation.ofContinuous A
    (isContinuous_finiteRepresentation_of_hasContinuousOrbits A hA)

variable (hA : HasContinuousOrbits A)

theorem continuousOrbitsObjects_representation_apply (g : Field.absoluteGaloisGroup F) :
    (continuousOrbitsObjects A hA).val.representation g = (A.ρ g).hom :=
  rfl

/-- The dimension of the Galois representation is that of the space of the action. -/
theorem continuousOrbitsObjects_rank :
    (continuousOrbitsObjects A hA).val.rank = Module.finrank M A.V :=
  rfl

variable [NumberField F] (v : Global.FinitePlace F)

/-- The Galois representation has Euler polynomial `P` at `v` exactly when the action is
unramified at `v` with Frobenius Euler polynomial `P`. -/
theorem hasEulerPolynomialAt_continuousOrbitsObjects_iff {P : M[X]} :
    HasEulerPolynomialAt (continuousOrbitsObjects A hA) v P ↔
      IsUnramifiedAt (ModuleCat.{uV} M) v A ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial v A = P :=
  LatticeGaloisRepresentation.hasEulerPolynomialAt_ofContinuous_iff A _ v

/-- The same criterion along any closure embedding at `v`, with the reversed characteristic
polynomial of the geometric Frobenius endomorphism along that embedding. -/
theorem hasEulerPolynomialAt_continuousOrbitsObjects_iff_along
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v)) {P : M[X]} :
    HasEulerPolynomialAt (continuousOrbitsObjects A hA) v P ↔
      IsUnramifiedAlong (ModuleCat.{uV} M) v A ι ∧
        (geometricFrobenius (ModuleCat.{uV} M) v A ι).hom.charpoly.reverse = P := by
  rw [hasEulerPolynomialAt_continuousOrbitsObjects_iff,
    DecompositionGroupAction.isUnramifiedAt_iff_along A ι,
    FrobeniusPolynomial.frobeniusEulerPolynomial_eq_along ι]

/-- If the action is unramified at `v` along `ι`, the Galois representation has as Euler
polynomial at `v` the reversed characteristic polynomial of the geometric Frobenius endomorphism
along `ι`. -/
theorem hasEulerPolynomialAt_continuousOrbitsObjects_of_isUnramifiedAlong
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} M) v A ι) :
    HasEulerPolynomialAt (continuousOrbitsObjects A hA) v
      (geometricFrobenius (ModuleCat.{uV} M) v A ι).hom.charpoly.reverse :=
  (hasEulerPolynomialAt_continuousOrbitsObjects_iff_along A hA v ι).2 ⟨hu, rfl⟩

end General

/-! ## Fixed vectors of isotypic parts -/

section Isotypic

variable {F : Type uF} [Field F] {M : Type uM} [Field M] {G : Type uG} [Group G]
  [TopologicalSpace G] {U : Type uU} [AddCommGroup U] [Module M U] (τ : Representation M G U)
  (H : Subgroup G) (X : Action (SmoothRep.{uM, uG, uV} M G) (Field.absoluteGaloisGroup F))

/-- The inclusion of the `H`-fixed vectors of the `τ`-isotypic part of `X` into the `H`-fixed
vectors of `X`, as a morphism of Galois actions. -/
def isotypicFixedVectorsι :
    (fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj
        ((isotypicActionFunctor τ (Field.absoluteGaloisGroup F)).obj X) ⟶
      (fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X :=
  (fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).map
    ((isotypicActionι τ (Field.absoluteGaloisGroup F)).app X)

@[simp] theorem coe_isotypicFixedVectorsι_apply
    (x : fixedVectors (isotypicObj τ X.V).representation H) :
    ((isotypicFixedVectorsι τ H X).hom.hom x).1 = x.1.1 :=
  rfl

theorem isotypicFixedVectorsι_injective :
    Function.Injective (isotypicFixedVectorsι τ H X).hom.hom := fun _ _ hxy =>
  Subtype.ext (Subtype.ext (congrArg (fun z : fixedVectors X.V.representation H => (z : X.V)) hxy))

/-- The inclusion commutes with the Galois actions. -/
theorem isotypicFixedVectorsι_comm (g : Field.absoluteGaloisGroup F)
    (x : fixedVectors (isotypicObj τ X.V).representation H) :
    (isotypicFixedVectorsι τ H X).hom.hom
        ((((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj
          ((isotypicActionFunctor τ (Field.absoluteGaloisGroup F)).obj X)).ρ g).hom x) =
      (((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X).ρ g).hom
        ((isotypicFixedVectorsι τ H X).hom.hom x) :=
  rfl

/-- If `X^H` is finite-dimensional, so are the `H`-fixed vectors of the `τ`-isotypic part. -/
instance [Module.Finite M (fixedVectors X.V.representation H)] :
    Module.Finite M ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj
      ((isotypicActionFunctor τ (Field.absoluteGaloisGroup F)).obj X)).V :=
  Module.Finite.of_injective (isotypicFixedVectorsι τ H X).hom.hom
    (isotypicFixedVectorsι_injective τ H X)

/-- If the Galois action on a finite-dimensional `X^H` has continuous orbits, so has the Galois
action on the `H`-fixed vectors of the `τ`-isotypic part. -/
theorem hasContinuousOrbits_isotypicFixedVectors [TopologicalSpace M]
    [Module.Finite M (fixedVectors X.V.representation H)]
    (hX : HasContinuousOrbits ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X)) :
    HasContinuousOrbits ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj
      ((isotypicActionFunctor τ (Field.absoluteGaloisGroup F)).obj X)) :=
  ContinuousGaloisAction.hasContinuousOrbits_of_injective (isotypicFixedVectorsι τ H X).hom.hom
    (isotypicFixedVectorsι_comm τ H X) (isotypicFixedVectorsι_injective τ H X) hX

variable [TopologicalSpace M] [IsTopologicalRing M]
  [Module.Finite M (fixedVectors X.V.representation H)]

/-- The `H`-fixed vectors of the `τ`-isotypic part of `X`, as a continuous Galois representation,
when `X^H` is finite-dimensional with continuous orbit maps. -/
def isotypicFixedVectorsObjects
    (hX : HasContinuousOrbits ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X)) :
    Objects.{uF, uM, uV} F M :=
  continuousOrbitsObjects _ (hasContinuousOrbits_isotypicFixedVectors τ H X hX)

variable (hX : HasContinuousOrbits ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X))

/-- A Galois element acts on an `H`-fixed vector of the isotypic part by its action on `X`. -/
theorem coe_isotypicFixedVectorsObjects_representation_apply (g : Field.absoluteGaloisGroup F)
    (x : fixedVectors (isotypicObj τ X.V).representation H) :
    ((isotypicFixedVectorsObjects τ H X hX).val.representation g x).1.1 =
      SmoothRep.hom (X.ρ g) x.1.1 :=
  rfl

variable [NumberField F] {v : Global.FinitePlace F}

/-- If `X^H` is unramified at `v` along `ι`, the Galois representation on the `H`-fixed vectors
of the `τ`-isotypic part has as Euler polynomial at `v` the reversed characteristic polynomial of
its geometric Frobenius endomorphism along `ι`. -/
theorem hasEulerPolynomialAt_isotypicFixedVectorsObjects
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} M) v
      ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X) ι) :
    HasEulerPolynomialAt (isotypicFixedVectorsObjects τ H X hX) v
      (geometricFrobenius (ModuleCat.{uV} M) v
        ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj
          ((isotypicActionFunctor τ (Field.absoluteGaloisGroup F)).obj X)) ι).hom.charpoly.reverse :=
  hasEulerPolynomialAt_continuousOrbitsObjects_of_isUnramifiedAlong _ _ v
    (FixedVectorGaloisRepresentation.isUnramifiedAlong_fixedVectors_isotypic H X τ hu)

end Isotypic

/-! ## Multiplicity spaces -/

section Multiplicity

variable {F : Type uF} [Field F] {M : Type uM} [Field M] {G : Type uG} [Group G]
  [TopologicalSpace G] {U : Type uU} [AddCommGroup U] [Module M U] (τ : Representation M G U)
  (H : Subgroup G) (X : Action (SmoothRep.{uM, uG, uV} M G) (Field.absoluteGaloisGroup F))

/-- Restriction of intertwining maps `τ → X` to the `H`-fixed vectors:
`Hom_G(τ, X) → Hom(τ^H, X^H)`. -/
def multiplicityRestriction :
    τ.IntertwiningMap X.V.representation →ₗ[M]
      (fixedVectors τ H →ₗ[M] fixedVectors X.V.representation H) where
  toFun φ := fixedVectorsMap φ H
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext rfl
  map_smul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

@[simp] theorem coe_multiplicityRestriction_apply (φ : τ.IntertwiningMap X.V.representation)
    (u : fixedVectors τ H) :
    (multiplicityRestriction τ H X φ u : X.V) = φ u :=
  rfl

/-- Evaluation of intertwining maps `τ → X` at an `H`-fixed vector `u` of `τ`, with values in the
`H`-fixed vectors of `X`. -/
def multiplicityEvaluation (u : fixedVectors τ H) :
    τ.IntertwiningMap X.V.representation →ₗ[M] fixedVectors X.V.representation H :=
  LinearMap.applyₗ u ∘ₗ multiplicityRestriction τ H X

@[simp] theorem coe_multiplicityEvaluation_apply (u : fixedVectors τ H)
    (φ : τ.IntertwiningMap X.V.representation) :
    (multiplicityEvaluation τ H X u φ : X.V) = φ u :=
  rfl

/-- Evaluation at an `H`-fixed vector commutes with the Galois actions. -/
theorem multiplicityEvaluation_comm (u : fixedVectors τ H) (g : Field.absoluteGaloisGroup F)
    (φ : τ.IntertwiningMap X.V.representation) :
    multiplicityEvaluation τ H X u
        ((((multiplicityActionFunctor τ (Field.absoluteGaloisGroup F)).obj X).ρ g).hom φ) =
      (((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X).ρ g).hom
        (multiplicityEvaluation τ H X u φ) :=
  rfl

/-- If `τ` is spanned by the translates of its `H`-fixed vectors, an intertwining map `τ → X`
vanishing on the `H`-fixed vectors of `τ` is zero. -/
theorem eq_zero_of_forall_multiplicityEvaluation_eq_zero
    (hgen : Submodule.span M (⋃ g : G, τ g '' (fixedVectors τ H : Set U)) = ⊤)
    (φ : τ.IntertwiningMap X.V.representation)
    (hφ : ∀ u, multiplicityEvaluation τ H X u φ = 0) : φ = 0 := by
  refine Representation.IntertwiningMap.ext (LinearMap.ext_on hgen ?_)
  intro w hw
  obtain ⟨g, u, hu, rfl⟩ := Set.mem_iUnion.1 hw
  have h0 : φ u = 0 := congrArg Subtype.val (hφ ⟨u, hu⟩)
  change φ (τ g u) = 0
  rw [φ.isIntertwining, h0, map_zero]

/-- If `τ` is spanned by the translates of its `H`-fixed vectors, restriction to the `H`-fixed
vectors is injective. -/
theorem multiplicityRestriction_injective
    (hgen : Submodule.span M (⋃ g : G, τ g '' (fixedVectors τ H : Set U)) = ⊤) :
    Function.Injective (multiplicityRestriction τ H X) := by
  refine (injective_iff_map_eq_zero _).2 fun φ hφ =>
    eq_zero_of_forall_multiplicityEvaluation_eq_zero τ H X hgen φ fun u => ?_
  change multiplicityRestriction τ H X φ u = 0
  rw [hφ, LinearMap.zero_apply]

/-- If `τ` is spanned by the translates of its `H`-fixed vectors and both `τ^H` and `X^H` are
finite-dimensional, the multiplicity space `Hom_G(τ, X)` is finite-dimensional. -/
theorem finite_multiplicity [Module.Finite M (fixedVectors τ H)]
    [Module.Finite M (fixedVectors X.V.representation H)]
    (hgen : Submodule.span M (⋃ g : G, τ g '' (fixedVectors τ H : Set U)) = ⊤) :
    Module.Finite M (τ.IntertwiningMap X.V.representation) :=
  Module.Finite.of_injective _ (multiplicityRestriction_injective τ H X hgen)

instance [Module.Finite M (τ.IntertwiningMap X.V.representation)] :
    Module.Finite M ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup F)).obj X).V :=
  inferInstanceAs (Module.Finite M (τ.IntertwiningMap X.V.representation))

/-- If `τ` is spanned by the translates of its `H`-fixed vectors and the Galois action on `X^H`
has continuous orbits, so has the Galois action on a finite-dimensional multiplicity space. -/
theorem hasContinuousOrbits_multiplicity [TopologicalSpace M]
    [Module.Finite M (τ.IntertwiningMap X.V.representation)]
    (hgen : Submodule.span M (⋃ g : G, τ g '' (fixedVectors τ H : Set U)) = ⊤)
    (hX : HasContinuousOrbits ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X)) :
    HasContinuousOrbits ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup F)).obj X) :=
  ContinuousGaloisAction.hasContinuousOrbits_of_forall_eq_zero (multiplicityEvaluation τ H X)
    (multiplicityEvaluation_comm τ H X)
    (fun φ hφ => eq_zero_of_forall_multiplicityEvaluation_eq_zero τ H X hgen φ hφ) hX

/-- If `τ` is spanned by the translates of its `H`-fixed vectors and `X^H` is unramified at `v`
along `ι`, so is the multiplicity space. -/
theorem isUnramifiedAlong_multiplicity [NumberField F] {v : Global.FinitePlace F}
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v)}
    (hgen : Submodule.span M (⋃ g : G, τ g '' (fixedVectors τ H : Set U)) = ⊤)
    (hu : IsUnramifiedAlong (ModuleCat.{uV} M) v
      ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X) ι) :
    IsUnramifiedAlong (ModuleCat.{max uU uV} M) v
      ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup F)).obj X) ι :=
  ContinuousGaloisAction.isUnramifiedAlong_of_forall_eq_zero (multiplicityEvaluation τ H X)
    (multiplicityEvaluation_comm τ H X)
    (fun φ hφ => eq_zero_of_forall_multiplicityEvaluation_eq_zero τ H X hgen φ hφ) hu

variable [TopologicalSpace M] [IsTopologicalRing M]
  [Module.Finite M (τ.IntertwiningMap X.V.representation)]
  (hgen : Submodule.span M (⋃ g : G, τ g '' (fixedVectors τ H : Set U)) = ⊤)
  (hX : HasContinuousOrbits ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X))

/-- The multiplicity space `Hom_G(τ, X)`, when finite-dimensional, as a continuous Galois
representation with the Galois group acting by composition, for `τ` spanned by the translates of
its `H`-fixed vectors and `X^H` with continuous orbit maps. -/
def multiplicityObjects : Objects.{uF, uM, max uU uV} F M :=
  continuousOrbitsObjects _ (hasContinuousOrbits_multiplicity τ H X hgen hX)

/-- A Galois element acts on an intertwining map by composition with its action on `X`. -/
theorem multiplicityObjects_representation_apply (g : Field.absoluteGaloisGroup F)
    (φ : τ.IntertwiningMap X.V.representation) :
    (multiplicityObjects τ H X hgen hX).val.representation g φ = (SmoothRep.hom (X.ρ g)).comp φ :=
  rfl

/-- The dimension of the Galois representation is that of the multiplicity space. -/
theorem multiplicityObjects_rank :
    (multiplicityObjects τ H X hgen hX).val.rank =
      Module.finrank M (τ.IntertwiningMap X.V.representation) :=
  rfl

/-- If `X^H` is unramified at `v` along `ι`, the Galois representation on the multiplicity space
has as Euler polynomial at `v` the reversed characteristic polynomial of its geometric Frobenius
endomorphism along `ι`. -/
theorem hasEulerPolynomialAt_multiplicityObjects [NumberField F] {v : Global.FinitePlace F}
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} M) v
      ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X) ι) :
    HasEulerPolynomialAt (multiplicityObjects τ H X hgen hX) v
      (geometricFrobenius (ModuleCat.{max uU uV} M) v
        ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup F)).obj X) ι).hom.charpoly.reverse :=
  hasEulerPolynomialAt_continuousOrbitsObjects_of_isUnramifiedAlong _ _ v
    (isUnramifiedAlong_multiplicity τ H X hgen hu)

end Multiplicity

/-! ## Hecke multiplicity spaces -/

section HeckeMultiplicity

variable {F : Type uF} [Field F] {M : Type uM} [Field M] {G : Type uG} [Group G]
  [TopologicalSpace G] (H : Subgroup G) (T : Type uT) [AddCommGroup T]
  [Module (LevelHeckeAlgebra M H) T]
  (X : Action (SmoothRep.{uM, uG, uV} M G) (Field.absoluteGaloisGroup F))

/-- Evaluation of Hecke-linear maps `T → X^H` at `t`. -/
def heckeMultiplicityEvaluation (t : T) :
    (T →ₗ[LevelHeckeAlgebra M H] fixedVectors X.V.representation H) →ₗ[M]
      fixedVectors X.V.representation H where
  toFun φ := φ t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem heckeMultiplicityEvaluation_apply (t : T)
    (φ : T →ₗ[LevelHeckeAlgebra M H] fixedVectors X.V.representation H) :
    heckeMultiplicityEvaluation H T X t φ = φ t :=
  rfl

/-- Evaluation commutes with the Galois actions. -/
theorem heckeMultiplicityEvaluation_comm (t : T) (g : Field.absoluteGaloisGroup F)
    (φ : T →ₗ[LevelHeckeAlgebra M H] fixedVectors X.V.representation H) :
    heckeMultiplicityEvaluation H T X t
        ((((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup F)).obj X).ρ g).hom φ) =
      (((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X).ρ g).hom
        (heckeMultiplicityEvaluation H T X t φ) :=
  rfl

/-- If `T` is finitely generated over the Hecke algebra and `X^H` is finite-dimensional, the
Hecke multiplicity space is finite-dimensional: a Hecke-linear map is determined by its values on
finitely many generators. -/
theorem finite_heckeMultiplicity [Module.Finite (LevelHeckeAlgebra M H) T]
    [Module.Finite M (fixedVectors X.V.representation H)] :
    Module.Finite M (T →ₗ[LevelHeckeAlgebra M H] fixedVectors X.V.representation H) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := LevelHeckeAlgebra M H) (M := T)
  let E : (T →ₗ[LevelHeckeAlgebra M H] fixedVectors X.V.representation H) →ₗ[M]
      (s → fixedVectors X.V.representation H) :=
    LinearMap.pi fun t => heckeMultiplicityEvaluation H T X t
  refine Module.Finite.of_injective E fun φ ψ h => LinearMap.ext_on hs fun t ht => ?_
  exact congrFun h ⟨t, ht⟩

/-- If the Galois action on `X^H` has continuous orbits, so has the Galois action on a
finite-dimensional Hecke multiplicity space. -/
theorem hasContinuousOrbits_heckeMultiplicity [TopologicalSpace M]
    [Module.Finite M (T →ₗ[LevelHeckeAlgebra M H] fixedVectors X.V.representation H)]
    (hX : HasContinuousOrbits ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X)) :
    HasContinuousOrbits ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup F)).obj X) :=
  ContinuousGaloisAction.hasContinuousOrbits_of_forall_eq_zero (heckeMultiplicityEvaluation H T X)
    (heckeMultiplicityEvaluation_comm H T X) (fun _ hφ => LinearMap.ext hφ) hX

variable [TopologicalSpace M] [IsTopologicalRing M]
  [Module.Finite M (T →ₗ[LevelHeckeAlgebra M H] fixedVectors X.V.representation H)]
  (hX : HasContinuousOrbits ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X))

/-- The Hecke multiplicity space `Hom_{H(H)}(T, X^H)`, when finite-dimensional, as a continuous
Galois representation with the Galois group acting by composition, for `X^H` with continuous
orbit maps. -/
def heckeMultiplicityContinuousObjects : Objects.{uF, uM, max uT uV} F M :=
  continuousOrbitsObjects _ (hasContinuousOrbits_heckeMultiplicity H T X hX)

/-- A Galois element acts on a Hecke-linear map by composition with its action on `X^H`. -/
theorem heckeMultiplicityContinuousObjects_representation_apply (g : Field.absoluteGaloisGroup F)
    (φ : T →ₗ[LevelHeckeAlgebra M H] fixedVectors X.V.representation H) :
    (heckeMultiplicityContinuousObjects H T X hX).val.representation g φ =
      (HeckeMultiplicityGaloisRepresentation.fixedVectorsHeckeMap H (X.ρ g)).comp φ :=
  rfl

/-- The dimension of the Galois representation is that of the Hecke multiplicity space. -/
theorem heckeMultiplicityContinuousObjects_rank :
    (heckeMultiplicityContinuousObjects H T X hX).val.rank =
      Module.finrank M (T →ₗ[LevelHeckeAlgebra M H] fixedVectors X.V.representation H) :=
  rfl

/-- If `X^H` is unramified at `v` along `ι`, the Galois representation on the Hecke multiplicity
space has as Euler polynomial at `v` the reversed characteristic polynomial of its geometric
Frobenius endomorphism along `ι`, which is composition with the Hecke-linear Frobenius
endomorphism of `X^H` (`geometricFrobenius_heckeMultiplicity_apply`). -/
theorem hasEulerPolynomialAt_heckeMultiplicityContinuousObjects [NumberField F]
    {v : Global.FinitePlace F} {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} M) v
      ((fixedVectorsActionFunctor M (Field.absoluteGaloisGroup F) H).obj X) ι) :
    HasEulerPolynomialAt (heckeMultiplicityContinuousObjects H T X hX) v
      (geometricFrobenius (ModuleCat.{max uT uV} M) v
        ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup F)).obj X)
          ι).hom.charpoly.reverse :=
  hasEulerPolynomialAt_continuousOrbitsObjects_of_isUnramifiedAlong _ _ v
    (isUnramifiedAlong_heckeMultiplicity H T X hu)

end HeckeMultiplicity

end Langlands.Shimura.ContinuousIsotypicGaloisRepresentation

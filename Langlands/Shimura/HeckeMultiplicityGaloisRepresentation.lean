import Langlands.Shimura.FixedVectorGaloisRepresentation

/-! # Hecke multiplicity spaces of fixed vectors as continuous Galois representations

Let `X` be a smooth representation of a group `G` with a commuting action of a group `Γ`, let
`H` be a subgroup of `G`, and let `T` be a module over the Hecke algebra of `H`. The Hecke
multiplicity space `Hom_{H(H)}(T, X^H)` of Hecke-linear maps from `T` to the `H`-fixed vectors is
a module over the coefficient ring on which `Γ` acts by composition. If `Γ` is a topological
group acting smoothly on `X` and `T` is finitely generated over the Hecke algebra, this action is
smooth. For `Γ = Gal(K̄/K)` and a finite-dimensional multiplicity space over a topological field,
it is therefore a continuous Galois representation, whose Euler polynomial at a finite place
where the `H`-fixed vectors are unramified is the reversed characteristic polynomial of
composition with the Hecke-linear Frobenius endomorphism. See
`HeckeMultiplicityGaloisRepresentation.md`.
-/

noncomputable section

universe uR uG uT uV uΓ uK

set_option autoImplicit false

namespace Langlands.Shimura.HeckeMultiplicityGaloisRepresentation

open CategoryTheory Polynomial
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Shimura.LevelHecke (fixedVectorsActionFunctor LevelHeckeAlgebra)
open Langlands.Shimura.FixedVectorGaloisRepresentation (heckeFrobenius)
open Langlands.GaloisRepresentation (Objects ClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius)

/-! ## Hecke multiplicity spaces -/

section Functor

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  (H : Subgroup G)

/-- A morphism of smooth representations restricted to `H`-fixed vectors, as a map of modules
over the Hecke algebra of `H`. -/
def fixedVectorsHeckeMap {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    fixedVectors A.representation H →ₗ[LevelHeckeAlgebra R H]
      fixedVectors B.representation H where
  toFun := fixedVectorsMap (SmoothRep.hom f) H
  map_add' := map_add _
  map_smul' a v := LevelHecke.fixedVectorsMap_heckeAct (SmoothRep.hom f) H H a v

@[simp] theorem coe_fixedVectorsHeckeMap_apply {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (v : fixedVectors A.representation H) :
    (fixedVectorsHeckeMap H f v : B) = SmoothRep.hom f v :=
  rfl

variable (T : Type uT) [AddCommGroup T] [Module (LevelHeckeAlgebra R H) T]

/-- The Hecke multiplicity space `Hom_{H(H)}(T, A^H)` of Hecke-linear maps from `T` to the
`H`-fixed vectors, as a module over the coefficient ring, functorial in the smooth
representation `A` by composition. -/
def heckeMultiplicityFunctor : SmoothRep.{uR, uG, uV} R G ⥤ ModuleCat.{max uT uV} R where
  obj A := ModuleCat.of R (T →ₗ[LevelHeckeAlgebra R H] fixedVectors A.representation H)
  map f := ModuleCat.ofHom
    { toFun := fun φ => (fixedVectorsHeckeMap H f).comp φ
      map_add' := fun _ _ => LinearMap.comp_add _ _ _
      map_smul' := fun r φ => LinearMap.ext fun t =>
        LinearMap.map_smul_of_tower (fixedVectorsHeckeMap H f) r (φ t) }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem heckeMultiplicityFunctor_map_apply {A B : SmoothRep.{uR, uG, uV} R G}
    (f : A ⟶ B) (φ : T →ₗ[LevelHeckeAlgebra R H] fixedVectors A.representation H) :
    ((heckeMultiplicityFunctor H T).map f).hom φ = (fixedVectorsHeckeMap H f).comp φ :=
  rfl

variable (Γ : Type uΓ) [Group Γ]

/-- The Hecke multiplicity spaces of a smooth representation with a commuting `Γ`-action, with
`Γ` acting by composition with its action on the fixed vectors. -/
def heckeMultiplicityActionFunctor :
    Action (SmoothRep.{uR, uG, uV} R G) Γ ⥤ Action (ModuleCat.{max uT uV} R) Γ :=
  (heckeMultiplicityFunctor H T).mapAction Γ

/-- The Hecke multiplicity space as a linear representation of `Γ`. -/
def heckeMultiplicityRepresentation (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) :
    Representation R Γ (T →ₗ[LevelHeckeAlgebra R H] fixedVectors X.V.representation H) :=
  ((Rep.ActionToRep R Γ).obj ((heckeMultiplicityActionFunctor H T Γ).obj X)).ρ

@[simp] theorem heckeMultiplicityRepresentation_apply (X : Action (SmoothRep.{uR, uG, uV} R G) Γ)
    (γ : Γ) (φ : T →ₗ[LevelHeckeAlgebra R H] fixedVectors X.V.representation H) :
    heckeMultiplicityRepresentation H T Γ X γ φ = (fixedVectorsHeckeMap H (X.ρ γ)).comp φ :=
  rfl

end Functor

/-! ## Smoothness -/

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  (H : Subgroup G) (T : Type uT) [AddCommGroup T] [Module (LevelHeckeAlgebra R H) T]
  {Γ : Type uΓ} [Group Γ] [TopologicalSpace Γ]

/-- If `Γ` acts smoothly on `X` and `T` is finitely generated over the Hecke algebra of `H`, then
`Γ` acts smoothly on the Hecke multiplicity space: an open subgroup fixing the values of a
Hecke-linear map on finitely many generators of `T` fixes the map. -/
theorem isSmooth_heckeMultiplicityRepresentation [Module.Finite (LevelHeckeAlgebra R H) T]
    {X : Action (SmoothRep.{uR, uG, uV} R G) Γ} (hX : IsSmooth (galoisRepresentation X)) :
    IsSmooth (heckeMultiplicityRepresentation H T Γ X) := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := LevelHeckeAlgebra R H) (M := T)
  intro φ
  choose V hV using fun u : T => hX ((φ u : fixedVectors X.V.representation H) : X.V)
  refine ⟨t.inf V, (Representation.mem_invariants _ _).2 fun γ => ?_⟩
  refine LinearMap.ext_on ht fun u hu => ?_
  apply Subtype.ext
  exact (Representation.mem_invariants _ _).1 (hV u)
    ⟨γ.1, SetLike.le_def.1 (Finset.inf_le (f := V) hu) γ.2⟩

end Smooth

/-! ## Continuous Galois representations -/

section Galois

variable {K : Type uK} [Field K] {L : Type uR} [Field L] {G : Type uG} [Group G]
  [TopologicalSpace G] (H : Subgroup G) (T : Type uT) [AddCommGroup T]
  [Module (LevelHeckeAlgebra L H) T]
  (X : Action (SmoothRep.{uR, uG, uV} L G) (Field.absoluteGaloisGroup K))

instance [Module.Finite L (T →ₗ[LevelHeckeAlgebra L H] fixedVectors X.V.representation H)] :
    Module.Finite L
      ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup K)).obj X).V :=
  inferInstanceAs
    (Module.Finite L (T →ₗ[LevelHeckeAlgebra L H] fixedVectors X.V.representation H))

variable [Module.Finite (LevelHeckeAlgebra L H) T]
  [Module.Finite L (T →ₗ[LevelHeckeAlgebra L H] fixedVectors X.V.representation H)]
  [TopologicalSpace L]

/-- A finite-dimensional Hecke multiplicity space of a smooth Galois action over a topological
field, as a continuous Galois representation with `Gal(K̄/K)` acting by composition. -/
def heckeMultiplicityObjects (hX : IsSmooth (galoisRepresentation X)) :
    Objects.{uK, uR, max uT uV} K L :=
  ContinuousGaloisAction.toObjects
    ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup K)).obj X)
    (isSmooth_heckeMultiplicityRepresentation H T hX)

variable (hX : IsSmooth (galoisRepresentation X))

/-- A Galois element acts on a Hecke-linear map by composition with its action on the fixed
vectors. -/
theorem heckeMultiplicityObjects_representation_apply (g : Field.absoluteGaloisGroup K)
    (φ : T →ₗ[LevelHeckeAlgebra L H] fixedVectors X.V.representation H) :
    (heckeMultiplicityObjects H T X hX).val.representation g φ =
      (fixedVectorsHeckeMap H (X.ρ g)).comp φ :=
  rfl

/-- The dimension of the Galois representation is that of the Hecke multiplicity space. -/
theorem heckeMultiplicityObjects_rank :
    (heckeMultiplicityObjects H T X hX).val.rank =
      Module.finrank L (T →ₗ[LevelHeckeAlgebra L H] fixedVectors X.V.representation H) :=
  rfl

variable [NumberField K] (v : Global.FinitePlace K)

/-- The Galois representation on the Hecke multiplicity space has Euler polynomial `P` at `v`
exactly when the multiplicity space is unramified at `v` with Frobenius Euler polynomial `P`. -/
theorem hasEulerPolynomialAt_heckeMultiplicityObjects_iff {P : L[X]} :
    HasEulerPolynomialAt (heckeMultiplicityObjects H T X hX) v P ↔
      IsUnramifiedAt (ModuleCat.{max uT uV} L) v
          ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup K)).obj X) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial v
          ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup K)).obj X) = P :=
  ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff _ _ v

omit [Module.Finite (LevelHeckeAlgebra L H) T]
  [Module.Finite L (T →ₗ[LevelHeckeAlgebra L H] fixedVectors X.V.representation H)]
  [TopologicalSpace L] in
variable {v} in
/-- If the `H`-fixed vectors of `X` are unramified at `v` along `ι`, so is the Hecke
multiplicity space. -/
theorem isUnramifiedAlong_heckeMultiplicity
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} L) v
      ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) ι) :
    IsUnramifiedAlong (ModuleCat.{max uT uV} L) v
      ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup K)).obj X) ι := by
  intro i
  refine ModuleCat.hom_ext (LinearMap.ext fun
    (φ : T →ₗ[LevelHeckeAlgebra L H] fixedVectors X.V.representation H) =>
      LinearMap.ext fun t => ?_)
  exact congrArg (fun f => f.hom (φ t)) (hu i)

omit [Module.Finite (LevelHeckeAlgebra L H) T]
  [Module.Finite L (T →ₗ[LevelHeckeAlgebra L H] fixedVectors X.V.representation H)]
  [TopologicalSpace L] in
/-- The geometric Frobenius endomorphism of the Hecke multiplicity space is composition with the
Hecke-linear Frobenius endomorphism of the Hecke module of `H`-fixed vectors. -/
theorem geometricFrobenius_heckeMultiplicity_apply
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (φ : T →ₗ[LevelHeckeAlgebra L H] fixedVectors X.V.representation H) :
    (geometricFrobenius (ModuleCat.{max uT uV} L) v
        ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup K)).obj X) ι).hom φ =
      (heckeFrobenius H X v ι).comp φ :=
  rfl

/-- If the `H`-fixed vectors of `X` are unramified at `v` along `ι`, the Galois representation
on the Hecke multiplicity space has as Euler polynomial at `v` the reversed characteristic
polynomial of its geometric Frobenius endomorphism along `ι`, which is composition with the
Hecke-linear Frobenius endomorphism. -/
theorem hasEulerPolynomialAt_heckeMultiplicityObjects_of_isUnramifiedAlong
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hu : IsUnramifiedAlong (ModuleCat.{uV} L) v
      ((fixedVectorsActionFunctor L (Field.absoluteGaloisGroup K) H).obj X) ι) :
    HasEulerPolynomialAt (heckeMultiplicityObjects H T X hX) v
      (geometricFrobenius (ModuleCat.{max uT uV} L) v
        ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup K)).obj X)
          ι).hom.charpoly.reverse :=
  (ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff_along _ _ v ι).2
    ⟨isUnramifiedAlong_heckeMultiplicity H T X hu, rfl⟩

end Galois

end Langlands.Shimura.HeckeMultiplicityGaloisRepresentation

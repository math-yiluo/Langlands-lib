import Langlands.Shimura.IsotypicGaloisAction
import Langlands.Shimura.DecompositionGroupAction

/-! # Decomposition groups acting on isotypic parts and multiplicity spaces

Mapping actions through a functor preserves unramifiedness at a finite place and sends the
geometric Frobenius endomorphism to its image. For a representation `τ`, restricting a Galois
action on smooth representations to a decomposition group commutes with taking `τ`-isotypic
parts; the Frobenius endomorphism of the isotypic part is the restriction of the Frobenius
endomorphism of the ambient representation, and the evaluation map intertwines the Frobenius
endomorphisms of the multiplicity space and of the isotypic part. See
`IsotypicDecompositionAction.md`.
-/

noncomputable section

universe u u' t t' uK uR uG uU uV

set_option autoImplicit false

namespace Langlands.Shimura.IsotypicDecompositionAction

open CategoryTheory TensorProduct Langlands.GaloisRepresentation
open Langlands.Shimura.DecompositionGroupAction Langlands.Shimura.IsotypicGaloisAction
open Langlands.Cohomology.HyperextAbutment (isotypicPart)

variable {K : Type uK} [Field K] [NumberField K] (v : Global.FinitePlace K)

/-! ## Mapping actions through a functor -/

section MapAction

variable {V : Type u} [Category.{t} V] {W : Type u'} [Category.{t'} W] (F : V ⥤ W)

variable {v} in
/-- Mapping an action through a functor preserves unramifiedness at `v` along `ι`. -/
theorem _root_.Langlands.Shimura.DecompositionGroupAction.IsUnramifiedAlong.mapAction
    {M : Action V (Field.absoluteGaloisGroup K)}
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hM : IsUnramifiedAlong V v M ι) :
    IsUnramifiedAlong W v ((F.mapAction (Field.absoluteGaloisGroup K)).obj M) ι :=
  fun i => (congrArg F.map (hM i)).trans (F.map_id M.V)

/-- The Frobenius endomorphism of an action mapped through a functor is the image of the
Frobenius endomorphism. -/
theorem geometricFrobenius_mapAction (M : Action V (Field.absoluteGaloisGroup K))
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    geometricFrobenius W v ((F.mapAction (Field.absoluteGaloisGroup K)).obj M) ι =
      F.map (geometricFrobenius V v M ι) :=
  rfl

end MapAction

/-! ## Isotypic parts and multiplicity spaces -/

section Isotypic

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  {U : Type uU} [AddCommGroup U] [Module R U] (τ : Representation R G U)

/-- Restricting to the decomposition group at `v` along `ι` commutes with taking `τ`-isotypic
parts; the components are identities. -/
def isotypicAtFinitePlaceIso
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    isotypicActionFunctor τ (Field.absoluteGaloisGroup K) ⋙
        atFinitePlace (SmoothRep.{uR, uG, uV} R G) v ι ≅
      atFinitePlace (SmoothRep.{uR, uG, uV} R G) v ι ⋙ isotypicActionFunctor τ (LocalGroup v) :=
  mapActionResIso _ (isotypicFunctor τ) (localRestriction v ι)

@[simp] theorem isotypicAtFinitePlaceIso_hom_app_hom
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (X : Action (SmoothRep.{uR, uG, uV} R G) (Field.absoluteGaloisGroup K)) :
    ((isotypicAtFinitePlaceIso v τ ι).hom.app X).hom = 𝟙 (isotypicObj τ X.V) :=
  rfl

variable {v} in
/-- The `τ`-isotypic part of an action unramified at `v` along `ι` is unramified. -/
theorem _root_.Langlands.Shimura.DecompositionGroupAction.IsUnramifiedAlong.isotypic
    {X : Action (SmoothRep.{uR, uG, uV} R G) (Field.absoluteGaloisGroup K)}
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hX : IsUnramifiedAlong _ v X ι) :
    IsUnramifiedAlong _ v ((isotypicActionFunctor τ (Field.absoluteGaloisGroup K)).obj X) ι :=
  hX.mapAction (isotypicFunctor τ)

/-- The Frobenius endomorphism of the `τ`-isotypic part is the restriction of the Frobenius
endomorphism of the ambient representation. -/
theorem isotypic_geometricFrobenius
    (X : Action (SmoothRep.{uR, uG, uV} R G) (Field.absoluteGaloisGroup K))
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    geometricFrobenius _ v ((isotypicActionFunctor τ (Field.absoluteGaloisGroup K)).obj X) ι =
      isotypicMap τ (geometricFrobenius _ v X ι) :=
  rfl

/-- The inclusion of the `τ`-isotypic part intertwines the Frobenius endomorphisms. -/
theorem geometricFrobenius_isotypicι
    (X : Action (SmoothRep.{uR, uG, uV} R G) (Field.absoluteGaloisGroup K))
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    geometricFrobenius _ v ((isotypicActionFunctor τ (Field.absoluteGaloisGroup K)).obj X) ι ≫
        (isotypicι τ).app X.V =
      (isotypicι τ).app X.V ≫ geometricFrobenius _ v X ι :=
  geometricFrobenius_naturality ((isotypicActionι τ (Field.absoluteGaloisGroup K)).app X) ι

/-- An element of the decomposition group acts on the multiplicity space of the restricted
action as its restriction to `Gal(K̄/K)`. -/
theorem multiplicityRepresentation_atFinitePlace
    (X : Action (SmoothRep.{uR, uG, uV} R G) (Field.absoluteGaloisGroup K))
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) (g : LocalGroup v) :
    multiplicityRepresentation τ (LocalGroup v) ((atFinitePlace _ v ι).obj X) g =
      multiplicityRepresentation τ (Field.absoluteGaloisGroup K) X (localRestriction v ι g) :=
  rfl

variable {v} in
/-- The multiplicity spaces of an action unramified at `v` along `ι` are unramified. -/
theorem _root_.Langlands.Shimura.DecompositionGroupAction.IsUnramifiedAlong.multiplicity
    {X : Action (SmoothRep.{uR, uG, uV} R G) (Field.absoluteGaloisGroup K)}
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hX : IsUnramifiedAlong _ v X ι) :
    IsUnramifiedAlong _ v
      ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup K)).obj X) ι :=
  hX.mapAction (multiplicityFunctor τ)

/-- Evaluation `τ ⊗ Hom_G(τ, X) → X[τ]` intertwines the Frobenius endomorphisms of the
multiplicity space and of the `τ`-isotypic part. -/
theorem isotypicEvaluation_geometricFrobenius
    (X : Action (SmoothRep.{uR, uG, uV} R G) (Field.absoluteGaloisGroup K))
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    isotypicEvaluation τ X.V ∘ₗ LinearMap.lTensor U
        (geometricFrobenius _ v
          ((multiplicityActionFunctor τ (Field.absoluteGaloisGroup K)).obj X) ι).hom =
      (SmoothRep.hom (geometricFrobenius _ v
          ((isotypicActionFunctor τ (Field.absoluteGaloisGroup K)).obj X) ι)).toLinearMap ∘ₗ
        isotypicEvaluation τ X.V :=
  isotypicEvaluation_galois τ (Field.absoluteGaloisGroup K) X
    (localRestriction v ι (geometricFrobeniusLift v))

end Isotypic

end Langlands.Shimura.IsotypicDecompositionAction

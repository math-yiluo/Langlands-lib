/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import WeilConjectures.Topology.ContinuousMapCondensedRing
/-!
# Data for the integral coefficient comparison

The existing definitions are relocated unchanged to permit the ring comparison lemma
and the assembly theorem to share them without an import cycle.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale

/-- The constant set sheaves with finite labels, regarded as presheaves.
(blueprint: lemma-comparison-completed-coefficients--1). -/
noncomputable def sfbFiniteConstantSets (X : Scheme.{u}) :
    FintypeCat.{u} ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1) :=
  forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1} ⋙
    constantSheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⋙
      sheafToPresheaf _ _

/-- The presheaves represented by the relative finite test schemes, namely the coproducts
of copies of X by `profinite_test_object_functor`.
(blueprint: lemma-comparison-completed-coefficients--1). -/
noncomputable def sfbFiniteRepresentables (X : Scheme.{u}) :
    FintypeCat.{u} ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1) :=
  FintypeCat.toProfinite ⋙ profiniteToProEtOf X ⋙ uliftYoneda.{u + 1}

/-- The finite quotient at exponent n+1, bundled using its recorded finiteness theorem.
(blueprint: lemma-comparison-completed-coefficients--1). -/
noncomputable def sfbIntegralFiniteLevel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) : FintypeCat.{u} :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  FintypeCat.of (Padic.coefficientExtensionRing l E (n + 1))

/-- The finite quotient tower with exactly the specified reduction maps.
(blueprint: lemma-comparison-completed-coefficients--1). -/
noncomputable def sfbIntegralFiniteTower (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : ℕᵒᵖ ⥤ FintypeCat.{u} :=
  Functor.ofOpSequence (fun n ↦
    FintypeCat.homMk (X := sfbIntegralFiniteLevel l E (n + 1))
      (Y := sfbIntegralFiniteLevel l E n) (Padic.coefficientExtensionTransition l E (n + 1)))

/-- The integers with their extending absolute-value topology, bundled as a profinite set.
integers-profinite-tower
(blueprint: lemma-comparison-completed-coefficients--1). -/
noncomputable def sfbIntegralProfinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Profinite.{u} :=
  letI := Padic.coefficientExtensionIntegersTopology l E
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.1
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.1
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.2.1
  Profinite.of (Padic.coefficientExtensionIntegers l E)

/-- The condensed integer ring, using its actual continuous-function sections.
(blueprint: lemma-comparison-completed-coefficients--1). -/
noncomputable def sfbCondensedIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  letI := spectralNorm.normedField (Padic l) E
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers l E)) :=
    Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheafOfUniverse (Padic.coefficientExtensionIntegers l E))
  Mon.mk (Profinite.continuousMapRingObjOfUniverse (Padic.coefficientExtensionIntegers l E))

/-- The existing completed ring sheaf, as an abelian sheaf with its ring-object structure.
(blueprint: lemma-comparison-completed-coefficients--1). -/
noncomputable abbrev sfbCompletedIntegersAb (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (completedIntegralCoefficientSheafUnrestricted l E X)

/-- The canonical adjunction whose unit specifies sections pulled back from the point.
(blueprint: lemma-comparison-completed-coefficients--1). -/
noncomputable def sfbIntegralPointAdjunction (X : Scheme.{u}) :
    sfbPullbackFromPoint X ⊣ sfbPullbackFromPointRightAdjoint X :=
  pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))

/-- The finite-level set representation, including the canonical comparison between
constant ring sheaves and constant set sheaves.
(blueprint: lemma-comparison-completed-coefficients--1). -/
noncomputable def sfbIntegralFiniteRepresentation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) (n : ℕ) :
    (integralCoefficientSheaf l E X n).obj ⋙ forget RingCat.{u + 1} ≅
      uliftYoneda.{u + 1}.obj
        ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj (sfbIntegralFiniteLevel l E n))) :=
  (sheafToPresheaf _ _).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
    a.app (sfbIntegralFiniteLevel l E n)

end AlgebraicGeometry.ProEtale

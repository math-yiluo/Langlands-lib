import Langlands.BruhatTits.IntegralModels.TorusRootModelFamily
import Langlands.GroupScheme.Rational.RootProductStatement

/-! # Ordered integral open cells over the maximal unramified integers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

namespace TorusRootModelFamilyData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  {C : MaximalUnramified.BuildingData F G} {E : UnramifiedZeroDatum F G}
  {x : C.Apartment} {Ω : Set C.Apartment}
  {N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G}
  {nneg npos : ℕ}

/-- The prescribed factor order: the first list of roots, the torus, and
the second list of roots. Either root list may be empty. -/
def orderedIntegralIndex (aneg : Fin nneg → relativeRoots C.i)
    (apos : Fin npos → relativeRoots C.i) :
    Fin (nneg + (npos + 1)) → Option (relativeRoots C.i) :=
  Fin.addCases (fun j => some (aneg j)) (Fin.cases none (fun j => some (apos j)))

variable (A : TorusRootModelFamilyData C E x Ω N)

/-- The actual integral group models in the prescribed order. No sign or
completeness condition is required to define the product. -/
def orderedIntegralFactor (aneg : Fin nneg → relativeRoots C.i)
    (apos : Fin npos → relativeRoots C.i)
    (j : Fin (nneg + (npos + 1))) :
    GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))) :=
  (A.model (orderedIntegralIndex aneg apos j)).group

/-- Each factor's supplied compatible homomorphism into the ambient model. -/
def orderedIntegralFactorMap (aneg : Fin nneg → relativeRoots C.i)
    (apos : Fin npos → relativeRoots C.i) (j : Fin (nneg + (npos + 1))) :
    A.orderedIntegralFactor aneg apos j ⟶ N.group :=
  (A.modelMap (orderedIntegralIndex aneg apos j)).hom

/-- The underlying scheme over the integral base of the actual finite product
of the listed root models, torus model, and remaining listed root models. -/
abbrev orderedIntegralProduct (aneg : Fin nneg → relativeRoots C.i)
    (apos : Fin npos → relativeRoots C.i) :
    Over (Spec (CommRingCat.of (fixedFieldIntegers F))) :=
  (∏ᶜ A.orderedIntegralFactor aneg apos).X

/-- Ordered multiplication using the ambient group law, as a morphism of
schemes over the integral base. It is not asserted to preserve the group law
of the direct product. -/
def orderedIntegralMultiplication (aneg : Fin nneg → relativeRoots C.i)
    (apos : Fin npos → relativeRoots C.i) :
    A.orderedIntegralProduct aneg apos ⟶ N.group.X :=
  RelativeRoot.orderedMultiplication (A.orderedIntegralFactorMap aneg apos)

end TorusRootModelFamilyData

/-- **KP Proposition 8.3.14(3), open-immersion clause, over the actual maximal
unramified integers.** For compatible centralizer data, every smooth model
with the exact zero-point fixer admits actual torus/root model data whose
negative-root/torus/positive-root multiplication is an open immersion for
every generic cocharacter and every ordering of the indivisible roots of
each sign. Existence of the family and the open immersion are conclusions. -/
def UnramifiedOrderedIntegralOpenCellStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G),
    (torusCentralizer C.i).IsRepresentedBy E.i →
    ∀ (x : C.Apartment) (Ω : Set C.Apartment),
      Ω.Nonempty →
      (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) →
      ∀ N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G,
        N.IsSmooth →
        N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) →
        ∃ A : TorusRootModelFamilyData C E x Ω N,
          ∀ (ν : cocharacterLattice C.S), IsGenericCocharacter C.i ν →
          ∀ (nneg npos : ℕ) (aneg : Fin nneg → relativeRoots C.i)
            (apos : Fin npos → relativeRoots C.i),
            Function.Injective aneg →
            Set.range (fun j => (aneg j : characterLattice C.S)) =
              RelativeRoot.indivisiblePositiveRoots C.i (-ν) →
            Function.Injective apos →
            Set.range (fun j => (apos j : characterLattice C.S)) =
              RelativeRoot.indivisiblePositiveRoots C.i ν →
            IsOpenImmersion (A.orderedIntegralMultiplication aneg apos).left

end Langlands.BruhatTits.IntegralModels

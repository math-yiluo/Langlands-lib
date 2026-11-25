/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteArrowEquations

/-! # Normalized cyclic coefficient reduction of an arrow

Source: diagonal tower coefficient changes, paragraph (1), reduction first modulo
an ell power and then along the finite coefficient algebra.
(blueprint: def-diagonal-cyclic-cartier-frame).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Cyclic coefficients at a positive prime-power exponent are finite.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-cartier-frame). -/
instance cyclicResidueFinite (l : ℕ) [Fact l.Prime] (n : ℕ) :
    Finite (diagonalResidue.{u} l n) :=
  cartierResidue_finite l (Fact.out : l.Prime) (n + 1)

/-- The actual continuous reduction, at exponent n+1, as a condensed ring-object map.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-cartier-frame). -/
def cyclicMap (l : ℕ) [Fact l.Prime] (n : ℕ) :
    Profinite.continuousMapRingObj.{u} ℤ_[l] ⟶
      Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1))) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (completedPadicReduction l n)

instance cyclicMap_isMonHom (l : ℕ) [Fact l.Prime] (n : ℕ) :
    IsMonHom (cyclicMap.{u} l n) := by
  dsimp only [cyclicMap]
  infer_instance

/-- The ordinary tensor quotient of the base integral Tate line.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-cartier-frame). -/
def cyclicLine (l : ℕ) [Fact l.Prime] (n : ℕ) (X : Scheme.{u}) :
    Modules (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) X :=
  (Mod.extendScalars (coefficientMap (cyclicMap l n) X)).obj (zlLine l X)

/-- Its tensor unit, which fixes the semilinear endpoint.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-cartier-frame). -/
def cyclicLineMap (l : ℕ) [Fact l.Prime] (n : ℕ) (X : Scheme.{u}) :
    (zlLine l X).X ⟶ (cyclicLine l n X).X :=
  Mod.extendUnitHom (coefficientMap (cyclicMap l n) X) (zlLine l X)

attribute [local irreducible] cyclicMap cyclicLine cyclicLineMap derivedScalars

/-- An ordinary finite realization of a supplied arrow, as its Ext representative.
All endpoint maps are supplied; this definition chooses no data.
Source: finite reduction of the diagonal (1)
(blueprint: def-diagonal-cyclic-cartier-frame). -/
def finiteRealizedClass
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {A : Type (u + 1)} [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (Y : Scheme.{u})
    {L : ∀ X : Scheme.{u}, Modules R X}
    (eW : FiniteRealization R A (diagonalSurface Y))
    (line : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y))
    (s : eW.F.obj (source R Y) ≅
      (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    (α : (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj
      (source R Y) ⟶
      ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y)))⟦(2 : ℤ)⟧) :
    GeoCartierClass A N hA (diagonalImmersion Y) :=
  Ext.homEquiv.symm
    ((DerivedCategory.singleFunctor _ 0).map s.inv ≫
      SpTowerClasses.mapSingleArrow eW.F (X := source R Y)
        (Y := L (diagonalSurface Y)) (2 : ℤ) α ≫
        ((DerivedCategory.singleFunctor _ 0).map line.hom)⟦(2 : ℤ)⟧')

attribute [local irreducible] finiteRealizedClass

/-- Only the coefficient objects and normalized endpoint maps for reduction modulo
ell^(n+1). There is no class equation and no choice of a diagonal or trace here.
In particular a frame can be used to reduce any arrow with these endpoints.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-cartier-frame). -/
structure CyclicCartierFrame (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ) where
  eP : FiniteRealization
    (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1))))
    (diagonalResidue.{u} l n) (ProjectiveLine Y)
  eW : FiniteRealization
    (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1))))
    (diagonalResidue.{u} l n) (diagonalSurface Y)
  units : ∀ X : Scheme.{u}, Endpoint (cyclicMap l n)
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))
    (Mod.regular (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) X))
    (coefficientMap (cyclicMap l n) X)
  supported : Endpoint (cyclicMap l n)
    (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (source (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) Y)
    (supportMap (cyclicMap l n) Y (units (ProjectiveLine Y)).semilinear.hom).hom
  line : Endpoint (cyclicMap l n) (zlLine l (diagonalSurface Y))
    (cyclicLine l n (diagonalSurface Y)) (cyclicLineMap l n (diagonalSurface Y))
  integralRoots : IntegralRoots l (bottomField l) (diagonalSurface Y)
  finiteRoots : FiniteRoots (diagonalSurface Y) (l ^ (n + 1))
  lineEndpoint : eW.LineEndpoint (cyclicLine l n (diagonalSurface Y))
    (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalSurface Y))
    (integralRoots.hom ≫ cyclicLineMap l n (diagonalSurface Y))
    (limit.π (Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l
      (Fact.out : l.Prime)) (op n) ≫
        finiteRoots.toLine (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1)))
  sourceComparison : FiniteSourceComparison
    (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1))))
    (diagonalResidue.{u} l n) Y eP eW

/-- Apply the specified derived scalar functor and its normalized endpoints,
then take the ordinary finite realization. This is an explicit construction,
independent of every completed class, trace, or geometric normalization theorem.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-cartier-frame). -/
def CyclicCartierFrame.reduce (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    (p : CyclicCartierFrame l Y n)
    (α : (DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y)) 0).obj
        (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y) ⟶
      ((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y)) 0).obj
          (zlLine l (diagonalSurface Y)))⟦(2 : ℤ)⟧) :
    GeoCartierClass (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y) :=
  finiteRealizedClass (L := cyclicLine l n) (l ^ (n + 1))
    (cartierResidue_cast l (n + 1)) Y p.eW p.lineEndpoint.iso p.sourceComparison.iso
    (p.supported.iso.inv ≫ (derivedScalars (cyclicMap l n) (diagonalSurface Y)).map α ≫
      p.line.shift (cyclicMap l n))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

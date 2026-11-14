import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesStatement
import Langlands.Geometry.Building.RootUnitaryCoordinateCompatibility
import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.SpecialLinearDynamicRoots
import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints
import Langlands.GroupScheme.Examples.SU3MatrixGeneration

/-! # Coherent valued opposite-root coordinates over the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

section FixedFields

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}

/-- The character and equivariance data of `RootFieldCoordinates`, on a specified field. -/
structure RootFieldCoordinatesOn (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (s : S.toGrp ⟶ Z) (a : characterLattice S)
    (E : Type u) [Field E] [Algebra k E] where
  equiv : Multiplicative E ≃* rootGroupPoints i a
  character : rationalCharacters (GaloisPointComparison.baseChanged k E Z)
  restriction :
    characterRestrict ((GroupScheme.baseChange (GaloisPointComparison.baseMap k E)).map s)
        character =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k E)
        ((rationalCharacters.equivCharacterLattice S).symm a)
  conjugation : ∀ (z : rationalPoints Z) (t : E),
    rationalPoints.map j z * (equiv (Multiplicative.ofAdd t) : rationalPoints G) *
        (rationalPoints.map j z)⁻¹ =
      (equiv (Multiplicative.ofAdd
        ((rationalCharacterEval character
          (GaloisPointComparison.rationalExtend k E Z z) : E) * t)) :
            rationalPoints G)

/-- Forget the specified-field packaging without changing any coordinate or character. -/
def RootFieldCoordinatesOn.toRootFieldCoordinates
    {i : S.toGrp ⟶ G} {j : Z ⟶ G} {s : S.toGrp ⟶ Z} {a : characterLattice S}
    {E : Type u} [Field E] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (R : RootFieldCoordinatesOn i j s a E) : RootFieldCoordinates i j s a where
  extension := E
  equiv := R.equiv
  character := R.character
  restriction := R.restriction
  conjugation := R.conjugation

/-- The entire `RootUnitaryCoordinates` action and double-root data on a specified tower.
Each sign carries its own character. -/
structure RootUnitaryCoordinatesOn (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (s : S.toGrp ⟶ Z) (a : characterLattice S)
    (E L : Type u) [Field E] [Field L] [Algebra k E] [Algebra E L] [Algebra k L]
    [IsScalarTower k E L] [Algebra.IsQuadraticExtension E L]
    [Algebra.IsSeparable E L] where
  equiv : SU3Root.rationalParameters E L ≃* rootGroupPoints i a
  double : ∀ g : rationalPoints G, g ∈ rootGroupPoints i (2 • a) ↔
    ∃ p ∈ SU3Root.Parameters.central (SU3Root.fieldInvolution E L),
      (equiv p : rationalPoints G) = g
  character : rationalCharacters (GaloisPointComparison.baseChanged k L Z)
  restriction :
    characterRestrict ((GroupScheme.baseChange (GaloisPointComparison.baseMap k L)).map s)
        character =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k L)
        ((rationalCharacters.equivCharacterLattice S).symm a)
  conjugation : ∀ (z : rationalPoints Z) (p : SU3Root.rationalParameters E L),
    rationalPoints.map j z * (equiv p : rationalPoints G) * (rationalPoints.map j z)⁻¹ =
      (equiv (SU3Root.Parameters.scale
        (rationalCharacterEval character
          (GaloisPointComparison.rationalExtend k L Z z) : L) p) :
            rationalPoints G)

/-- Recover the existing unitary-coordinate record on exactly the same tower. -/
def RootUnitaryCoordinatesOn.toRootUnitaryCoordinates
    {i : S.toGrp ⟶ G} {j : Z ⟶ G} {s : S.toGrp ⟶ Z} {a : characterLattice S}
    {E L : Type u} [Field E] [Field L] [Algebra k E] [Algebra E L] [Algebra k L]
    [IsScalarTower k E L] [Algebra.IsQuadraticExtension E L]
    [Algebra.IsSeparable E L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (R : RootUnitaryCoordinatesOn i j s a E L) : RootUnitaryCoordinates i j s a where
  base := E
  extension := L
  equiv := R.equiv
  double := R.double
  character := R.character
  restriction := R.restriction
  conjugation := R.conjugation

end FixedFields

section Valued

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]

/-- Opposite nonmultipliable root coordinates with one SL2 map, an actual induced-torus
coroot morphism, and one point realizing both original-base-normalized depths. -/
structure ValuedSL2RootCoordinates (B : MaximalUnramified.BuildingData F H)
    (hZ : IsTorus B.centralizer.Z) (b : characterLattice B.S) where
  extension : Type u
  [field : Field extension]
  [algebra : Algebra (UnramifiedClosure F) extension]
  [finite : FiniteDimensional (UnramifiedClosure F) extension]
  [separable : Algebra.IsSeparable (UnramifiedClosure F) extension]
  positive : RootFieldCoordinatesOn B.i B.centralizer.j B.centralizer.s b extension
  negative : RootFieldCoordinatesOn B.i B.centralizer.j B.centralizer.s (-b) extension
  rho : Matrix.SpecialLinearGroup (Fin 2) extension →* rationalPoints H
  rho_upper : ∀ t : extension,
    rho (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t) =
      (positive.equiv (Multiplicative.ofAdd t) : rationalPoints H)
  rho_lower : ∀ t : extension,
    rho (Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t) =
      (negative.equiv (Multiplicative.ofAdd t) : rationalPoints H)
  coroot : (WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) extension).toGrp ⟶
    (B.centralizerTorus hZ).toGrp
  coroot_points : ∀ t : extensionˣ,
    rationalPoints.map B.centralizer.j
        (rationalPoints.map coroot
          ((WeilGm.rationalUnitsEquiv (UnramifiedClosure F) extension).symm t)) =
      rho (SpecialLinear.Root.contractingMatrix (by decide : (0 : Fin 2) ≠ 1) t)
  origin : B.Apartment
  depth_positive : ∀ t : extension,
    origin.val b (positive.equiv (Multiplicative.ofAdd t)) =
      Langlands.FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) extension t
  depth_negative : ∀ t : extension,
    origin.val (-b) (negative.equiv (Multiplicative.ofAdd t)) =
      Langlands.FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) extension t

attribute [instance] ValuedSL2RootCoordinates.field ValuedSL2RootCoordinates.algebra
  ValuedSL2RootCoordinates.finite ValuedSL2RootCoordinates.separable

/-- Opposite multipliable root coordinates on one quadratic tower with one SU3 map,
an actual induced-torus morphism, and a common point for both roots and their doubles. -/
structure ValuedSU3RootCoordinates (B : MaximalUnramified.BuildingData F H)
    (hZ : IsTorus B.centralizer.Z) (b : characterLattice B.S) where
  base : Type u
  extension : Type u
  [baseField : Field base]
  [field : Field extension]
  [baseAlgebra : Algebra (UnramifiedClosure F) base]
  [quadraticAlgebra : Algebra base extension]
  [algebra : Algebra (UnramifiedClosure F) extension]
  [scalarTower : IsScalarTower (UnramifiedClosure F) base extension]
  [baseFinite : FiniteDimensional (UnramifiedClosure F) base]
  [baseSeparable : Algebra.IsSeparable (UnramifiedClosure F) base]
  [quadratic : Algebra.IsQuadraticExtension base extension]
  [quadraticSeparable : Algebra.IsSeparable base extension]
  [finite : FiniteDimensional (UnramifiedClosure F) extension]
  [separable : Algebra.IsSeparable (UnramifiedClosure F) extension]
  positive : RootUnitaryCoordinatesOn B.i B.centralizer.j B.centralizer.s b base extension
  negative : RootUnitaryCoordinatesOn B.i B.centralizer.j B.centralizer.s (-b) base extension
  rho : SU3Root.specialUnitarySubgroup (SU3Root.fieldInvolution base extension) →*
    rationalPoints H
  rho_upper : ∀ p : SU3Root.rationalParameters base extension,
    rho ⟨SU3Root.Parameters.embedding (SU3Root.fieldInvolution base extension) p,
      SU3Root.embedding_mem_specialUnitarySubgroup (SU3Root.fieldInvolution base extension) p⟩ =
      (positive.equiv p : rationalPoints H)
  rho_lower : ∀ p : SU3Root.rationalParameters base extension,
    rho ⟨SU3Root.oppositeEmbedding (SU3Root.fieldInvolution base extension) p,
      SU3Root.oppositeEmbedding_mem_specialUnitarySubgroup
        (SU3Root.fieldInvolution base extension) p⟩ =
      (negative.equiv p : rationalPoints H)
  coroot : (WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) extension).toGrp ⟶
    (B.centralizerTorus hZ).toGrp
  coroot_points : ∀ t : extensionˣ,
    rationalPoints.map B.centralizer.j
        (rationalPoints.map coroot
          ((WeilGm.rationalUnitsEquiv (UnramifiedClosure F) extension).symm t)) =
      rho ⟨SU3Root.diagonal (SU3Root.fieldInvolution base extension) t,
        SU3Root.diagonal_mem_specialUnitarySubgroup (SU3Root.fieldInvolution base extension) t⟩
  origin : B.Apartment
  depth_positive : ∀ p : SU3Root.rationalParameters base extension,
    origin.val b (positive.equiv p) =
      SU3Root.towerDepth (UnramifiedClosure F) base extension (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) p
  depth_negative : ∀ p : SU3Root.rationalParameters base extension,
    origin.val (-b) (negative.equiv p) =
      SU3Root.towerDepth (UnramifiedClosure F) base extension (MaximalUnramified.valuation F)
        (MaximalUnramified.valuationSubring_isHenselian F) p
  depth_double_positive :
    ∀ q : SU3Root.Parameters.central (SU3Root.fieldInvolution base extension),
    origin.val (2 • b) (positive.equiv q.val) =
      SU3Root.towerCentralDepth (UnramifiedClosure F) base extension
        (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F) q
  depth_double_negative :
    ∀ q : SU3Root.Parameters.central (SU3Root.fieldInvolution base extension),
    origin.val (2 • (-b)) (negative.equiv q.val) =
      SU3Root.towerCentralDepth (UnramifiedClosure F) base extension
        (MaximalUnramified.valuation F) (MaximalUnramified.valuationSubring_isHenselian F) q

attribute [instance] ValuedSU3RootCoordinates.baseField ValuedSU3RootCoordinates.field
  ValuedSU3RootCoordinates.baseAlgebra ValuedSU3RootCoordinates.quadraticAlgebra
  ValuedSU3RootCoordinates.algebra ValuedSU3RootCoordinates.scalarTower
  ValuedSU3RootCoordinates.baseFinite ValuedSU3RootCoordinates.baseSeparable
  ValuedSU3RootCoordinates.quadratic ValuedSU3RootCoordinates.quadraticSeparable
  ValuedSU3RootCoordinates.finite ValuedSU3RootCoordinates.separable

end Valued

end Langlands.Geometry.Building

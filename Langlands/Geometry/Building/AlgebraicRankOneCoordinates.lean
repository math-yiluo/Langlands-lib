import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinates

/-! # Algebraic opposite-root rank-one coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

section Algebraic

variable {k : Type u} [Field k]
  {S Z : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Coherent opposite-root field coordinates with one SL2 homomorphism and an actual
induced-torus morphism; no valuation or apartment point is part of this record. -/
structure AlgebraicSL2RootCoordinates (i : S.toGrp ⟶ G) (j : Z.toGrp ⟶ G)
    (s : S.toGrp ⟶ Z.toGrp) (b : characterLattice S) where
  extension : Type u
  [field : Field extension]
  [algebra : Algebra (k) extension]
  [finite : FiniteDimensional (k) extension]
  [separable : Algebra.IsSeparable (k) extension]
  positive : RootFieldCoordinatesOn i j s b extension
  negative : RootFieldCoordinatesOn i j s (-b) extension
  rho : Matrix.SpecialLinearGroup (Fin 2) extension →* rationalPoints G
  rho_upper : ∀ t : extension,
    rho (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t) =
      (positive.equiv (Multiplicative.ofAdd t) : rationalPoints G)
  rho_lower : ∀ t : extension,
    rho (Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t) =
      (negative.equiv (Multiplicative.ofAdd t) : rationalPoints G)
  coroot : (WeilGm.commGroupScheme (CommRingCat.of (k)) extension).toGrp ⟶
    Z.toGrp
  coroot_points : ∀ t : extensionˣ,
    rationalPoints.map j
        (rationalPoints.map coroot
          ((WeilGm.rationalUnitsEquiv (k) extension).symm t)) =
      rho (SpecialLinear.Root.contractingMatrix (by decide : (0 : Fin 2) ≠ 1) t)

attribute [instance] AlgebraicSL2RootCoordinates.field AlgebraicSL2RootCoordinates.algebra
  AlgebraicSL2RootCoordinates.finite AlgebraicSL2RootCoordinates.separable

/-- Coherent opposite-root unitary coordinates on one quadratic tower with one SU3
homomorphism and an actual induced-torus morphism, without valuation data. -/
structure AlgebraicSU3RootCoordinates (i : S.toGrp ⟶ G) (j : Z.toGrp ⟶ G)
    (s : S.toGrp ⟶ Z.toGrp) (b : characterLattice S) where
  base : Type u
  extension : Type u
  [baseField : Field base]
  [field : Field extension]
  [baseAlgebra : Algebra (k) base]
  [quadraticAlgebra : Algebra base extension]
  [algebra : Algebra (k) extension]
  [scalarTower : IsScalarTower (k) base extension]
  [baseFinite : FiniteDimensional (k) base]
  [baseSeparable : Algebra.IsSeparable (k) base]
  [quadratic : Algebra.IsQuadraticExtension base extension]
  [quadraticSeparable : Algebra.IsSeparable base extension]
  [finite : FiniteDimensional (k) extension]
  [separable : Algebra.IsSeparable (k) extension]
  positive : RootUnitaryCoordinatesOn i j s b base extension
  negative : RootUnitaryCoordinatesOn i j s (-b) base extension
  rho : SU3Root.specialUnitarySubgroup (SU3Root.fieldInvolution base extension) →*
    rationalPoints G
  rho_upper : ∀ p : SU3Root.rationalParameters base extension,
    rho ⟨SU3Root.Parameters.embedding (SU3Root.fieldInvolution base extension) p,
      SU3Root.embedding_mem_specialUnitarySubgroup (SU3Root.fieldInvolution base extension) p⟩ =
      (positive.equiv p : rationalPoints G)
  rho_lower : ∀ p : SU3Root.rationalParameters base extension,
    rho ⟨SU3Root.oppositeEmbedding (SU3Root.fieldInvolution base extension) p,
      SU3Root.oppositeEmbedding_mem_specialUnitarySubgroup
        (SU3Root.fieldInvolution base extension) p⟩ =
      (negative.equiv p : rationalPoints G)
  coroot : (WeilGm.commGroupScheme (CommRingCat.of (k)) extension).toGrp ⟶
    Z.toGrp
  coroot_points : ∀ t : extensionˣ,
    rationalPoints.map j
        (rationalPoints.map coroot
          ((WeilGm.rationalUnitsEquiv (k) extension).symm t)) =
      rho ⟨SU3Root.diagonal (SU3Root.fieldInvolution base extension) t,
        SU3Root.diagonal_mem_specialUnitarySubgroup (SU3Root.fieldInvolution base extension) t⟩

attribute [instance] AlgebraicSU3RootCoordinates.baseField AlgebraicSU3RootCoordinates.field
  AlgebraicSU3RootCoordinates.baseAlgebra AlgebraicSU3RootCoordinates.quadraticAlgebra
  AlgebraicSU3RootCoordinates.algebra AlgebraicSU3RootCoordinates.scalarTower
  AlgebraicSU3RootCoordinates.baseFinite AlgebraicSU3RootCoordinates.baseSeparable
  AlgebraicSU3RootCoordinates.quadratic AlgebraicSU3RootCoordinates.quadraticSeparable
  AlgebraicSU3RootCoordinates.finite AlgebraicSU3RootCoordinates.separable

end Algebraic

section ForgetValuation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  {B : MaximalUnramified.BuildingData F H} {hZ : IsTorus B.centralizer.Z}
  {b : characterLattice B.S}

/-- Discard the common origin and depths, preserving all SL2 algebraic data. -/
def ValuedSL2RootCoordinates.toAlgebraic (C : ValuedSL2RootCoordinates B hZ b) :
    AlgebraicSL2RootCoordinates (Z := B.centralizerTorus hZ)
      B.i B.centralizer.j B.centralizer.s b where
  extension := C.extension
  positive := C.positive
  negative := C.negative
  rho := C.rho
  rho_upper := C.rho_upper
  rho_lower := C.rho_lower
  coroot := C.coroot
  coroot_points := C.coroot_points

/-- Discard the common origin and depths, preserving all SU3 algebraic data. -/
def ValuedSU3RootCoordinates.toAlgebraic (C : ValuedSU3RootCoordinates B hZ b) :
    AlgebraicSU3RootCoordinates (Z := B.centralizerTorus hZ)
      B.i B.centralizer.j B.centralizer.s b where
  base := C.base
  extension := C.extension
  positive := C.positive
  negative := C.negative
  rho := C.rho
  rho_upper := C.rho_upper
  rho_lower := C.rho_lower
  coroot := C.coroot
  coroot_points := C.coroot_points

end ForgetValuation

end Langlands.Geometry.Building

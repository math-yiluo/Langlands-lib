import Langlands.GroupScheme.Lie.RootOrbitCharacterAction
import Langlands.GroupScheme.Rational.AffineCharacterTowerDescent

/-! # Actual root characters over root-orbit fields -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Plancherel.TorusNormKernel
open Langlands.GroupScheme.AffineCharacterFiniteGalois
open Langlands.GroupScheme.AffineCharacterTowerDescent

section Values

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "T_L" =>
  CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k L)) T

/-- A character of the split base change, regarded as a rational character of the
actual base-changed group. -/
def baseChangedCharacter (χ : characterLattice T_L) :
    rationalCharacters (GaloisPointComparison.baseChanged k L T.toGrp) :=
  (rationalCharacters.equivCharacterLattice T_L).symm χ

/-- The coefficient comparison `pointE` is inverse to the affine base-change equivalence. -/
theorem affineBaseChangeEquiv_pointE {D : Type u} [CommRing D] [Algebra k D] [Algebra L D]
    [IsScalarTower k L D] (y : GroupScheme.affinePoints T.toGrp (CommAlgCat.of k D)) :
    Lie.affineBaseChangeEquiv k L T.toGrp D (pointE k L D T.toGrp y) = y := by
  change (Lie.affineBaseTestIso k L D).inv ≫ GroupScheme.baseChangePointsEquiv _ _ _
    (pointE k L D T.toGrp y) = y
  rw [baseChangePointsEquiv_pointE]
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (𝟙 _ ≫ y.left) = y.left
  simp

/-- Values of a base-changed character are the actual character values. -/
theorem valueE_baseChangedCharacter (χ : characterLattice T_L) {D : Type u} [CommRing D]
    [Algebra k D] [Algebra L D] [IsScalarTower k L D]
    (y : GroupScheme.affinePoints T.toGrp (CommAlgCat.of k D)) :
    valueE (baseChangedCharacter k L T χ) D y =
      Lie.characterValue χ (pointE k L D T.toGrp y) := rfl

/-- At an extended rational point, a base-changed character takes its value at the
base-changed original point. -/
theorem rationalCharacterEval_baseChangedCharacter (χ : characterLattice T_L)
    (z : rationalPoints T.toGrp) :
    (rationalCharacterEval (baseChangedCharacter k L T χ)
        (GaloisPointComparison.rationalExtend k L T.toGrp z) : L) =
      Lie.characterValue χ
        (rationalBaseChangePoint k L T (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)) := by
  rw [← valueE_baseChangeCoeffEquiv, GaloisPointComparison.baseChangeCoeffEquiv_rationalExtend,
    valueE_baseChangedCharacter]
  congr 2

end Values

section Galois

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.toGrp.X.left]
  (E : Type u) [Field E] [Algebra k E] [Algebra E L] [IsScalarTower k E L]

local notation "T_L" =>
  CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k L)) T

/-- The coefficient Galois action on universal tensors, as an `L`-algebra map into the
Galois-twisted test algebra. -/
def tensorConjTest (σ : L ≃ₐ[E] L) :
    L ⊗[k] Coord T.toGrp →ₐ[L]
      Lie.GaloisTestAlgebra (σ.restrictScalars k) (L ⊗[k] Coord T.toGrp) where
  toRingHom := (tensorConj T.toGrp E L σ).toRingHom
  commutes' c := by
    change tensorConj T.toGrp E L σ (c ⊗ₜ 1) = σ c ⊗ₜ 1
    rw [tensorConj_tmul]

/-- The universal tensor value of a base-changed character is its actual value at the
universal tensor point. -/
theorem tensorValue_baseChangedCharacter (χ : characterLattice T_L) :
    tensorValue T.toGrp L (baseChangedCharacter k L T χ) =
      Lie.characterValue χ (pointE k L (L ⊗[k] Coord T.toGrp) T.toGrp (tensorPoint T.toGrp L)) :=
  rfl

/-- The coefficient Galois action moves the universal point of the base change to its
Galois-twisted test point. -/
theorem affineMap_tensorConjTest (σ : L ≃ₐ[E] L) :
    Lie.affineMap ((GroupScheme.baseChange (algebraBaseMap k L)).obj T.toGrp)
        (tensorConjTest T E σ)
        (pointE k L (L ⊗[k] Coord T.toGrp) T.toGrp (tensorPoint T.toGrp L)) =
      Lie.galoisTestPoint k L (σ.restrictScalars k) (L ⊗[k] Coord T.toGrp) T.toGrp
        (pointE k L (L ⊗[k] Coord T.toGrp) T.toGrp (tensorPoint T.toGrp L)) := by
  apply (Lie.affineBaseChangeEquiv k L T.toGrp
    (Lie.GaloisTestAlgebra (σ.restrictScalars k) (L ⊗[k] Coord T.toGrp))).injective
  rw [Lie.affineBaseChangeEquiv_naturality, Lie.affineBaseChangeEquiv_galoisTestPoint,
    affineBaseChangeEquiv_pointE]
  change Lie.affineMap T.toGrp ((tensorConjTest T E σ).restrictScalars k)
      (Lie.affineMap T.toGrp
        (Algebra.TensorProduct.includeRight : Coord T.toGrp →ₐ[k] L ⊗[k] Coord T.toGrp)
        (CharacterUnits.universalPoint T.toGrp)) =
    Lie.affineMap T.toGrp
      (Algebra.TensorProduct.includeRight : Coord T.toGrp →ₐ[k] L ⊗[k] Coord T.toGrp)
      (CharacterUnits.universalPoint T.toGrp)
  rw [← Lie.affineMap_comp]
  refine congrArg (fun f => Lie.affineMap T.toGrp f (CharacterUnits.universalPoint T.toGrp)) ?_
  apply AlgHom.ext
  intro a
  change tensorConj T.toGrp E L σ (1 ⊗ₜ a) = 1 ⊗ₜ a
  rw [tensorConj_tmul, map_one]

/-- The coefficient Galois action carries the universal tensor value of a split
character to that of its canonical Galois transport. -/
theorem tensorConj_tensorValue_baseChangedCharacter (σ : L ≃ₐ[E] L)
    (χ : characterLattice T_L) :
    tensorConj T.toGrp E L σ
        (tensorValue T.toGrp L (baseChangedCharacter k L T χ) : L ⊗[k] Coord T.toGrp) =
      tensorValue T.toGrp L (baseChangedCharacter k L T
        (characterLattice.galoisRepresentation k L T (σ.restrictScalars k) χ)) := by
  have h2 : Lie.characterValue χ
      (Lie.galoisTestPoint k L (σ.restrictScalars k) (L ⊗[k] Coord T.toGrp) T.toGrp
        (pointE k L (L ⊗[k] Coord T.toGrp) T.toGrp (tensorPoint T.toGrp L))) =
      Units.map (tensorConjTest T E σ).toRingHom.toMonoidHom
        (Lie.characterValue χ
          (pointE k L (L ⊗[k] Coord T.toGrp) T.toGrp (tensorPoint T.toGrp L))) :=
    (congrArg (Lie.characterValue χ) (affineMap_tensorConjTest T E σ)).symm.trans
      (CoordinateWeights.characterValue_affineMap (tensorConjTest T E σ) χ _)
  have h3 := (Lie.characterValue_galoisRepresentation k L (σ.restrictScalars k)
    (L ⊗[k] Coord T.toGrp) T χ
      (pointE k L (L ⊗[k] Coord T.toGrp) T.toGrp (tensorPoint T.toGrp L))).trans h2
  rw [tensorValue_baseChangedCharacter, tensorValue_baseChangedCharacter, h3, Units.coe_map]
  rfl

end Galois

section RootOrbit

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

attribute [local instance] rootsGaloisAction

variable [FiniteDimensional k L]

/-- Every automorphism of `L` over the root-orbit field fixes the root. -/
theorem galoisRepresentation_rootOrbitField (β : roots (T := T_L) (G := G_L) j_L)
    (σ : L ≃ₐ[rootOrbitField k L j β] L) :
    characterLattice.galoisRepresentation k L T (σ.restrictScalars k) β.val = β.val := by
  have hmem : σ.restrictScalars k ∈ MulAction.stabilizer (L ≃ₐ[k] L) β :=
    (IntermediateField.fixingSubgroup_fixedField _).le
      ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => σ.commutes ⟨x, hx⟩)
  exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hmem)

variable [IsAffine T.toGrp.X.left]

/-- The universal tensor value of a split root is fixed by `Gal(L / E_β)`. -/
theorem tensorConj_tensorValue_root (β : roots (T := T_L) (G := G_L) j_L)
    (σ : L ≃ₐ[rootOrbitField k L j β] L) :
    tensorConj T.toGrp (rootOrbitField k L j β) L σ
        (tensorValue T.toGrp L (baseChangedCharacter k L T β.val) :
          L ⊗[k] Coord T.toGrp) =
      tensorValue T.toGrp L (baseChangedCharacter k L T β.val) := by
  rw [tensorConj_tensorValue_baseChangedCharacter,
    galoisRepresentation_rootOrbitField k L j β σ]

variable [IsGalois k L]

/-- The actual character of `T` over the root-orbit field `E_β` whose base change to `L`
is the split root `β`. -/
def rootOrbitCharacter (β : roots (T := T_L) (G := G_L) j_L) :
    rationalCharacters (GaloisPointComparison.baseChanged k (rootOrbitField k L j β) T.toGrp) :=
  fixedDescend T.toGrp (rootOrbitField k L j β) L (baseChangedCharacter k L T β.val)
    (tensorConj_tensorValue_root k L j β)

set_option maxRecDepth 4000 in
/-- Over `L` the root-orbit character has the values of the split root. -/
theorem valueE_rootOrbitCharacter (β : roots (T := T_L) (G := G_L) j_L)
    (y : GroupScheme.affinePoints T.toGrp (CommAlgCat.of k L)) :
    valueE (rootOrbitCharacter k L j β) L y =
      Lie.characterValue β.val (pointE k L L T.toGrp y) :=
  (valueE_fixedDescend T.toGrp (rootOrbitField k L j β) L _ _ y).trans
    (valueE_baseChangedCharacter k L T β.val y)

/-- At a rational point of `T`, the root-orbit character takes the value of the split
root at the base-changed point. -/
theorem rationalCharacterEval_rootOrbitCharacter (β : roots (T := T_L) (G := G_L) j_L)
    (z : rationalPoints T.toGrp) :
    (rationalCharacterEval (rootOrbitCharacter k L j β)
        (GaloisPointComparison.rationalExtend k (rootOrbitField k L j β) T.toGrp z) :
          rootOrbitField k L j β) =
      rootOrbitCharacterValue k L j β (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) := by
  apply Subtype.ext
  rw [rootOrbitCharacterValue_coe, ← rationalCharacterEval_baseChangedCharacter]
  exact rationalCharacterEval_fixedDescend T.toGrp (rootOrbitField k L j β) L _ _ z

/-- If `β` lies over the original character `a` of `S`, the root-orbit character restricts
along `S → T` to the base change of `a`. -/
theorem characterRestrict_rootOrbitCharacter [IsAffine S.toGrp.X.left] (f : S ⟶ T)
    (a : characterLattice S) {β : roots (T := T_L) (G := G_L) j_L}
    (hβ : β ∈ rootRestrictionFiber k L j f a) :
    characterRestrict
        ((GroupScheme.baseChange
          (GaloisPointComparison.baseMap k (rootOrbitField k L j β))).map
            (CommGroupScheme.groupHom f))
        (rootOrbitCharacter k L j β) =
      rationalCharacters.baseChange
        (GaloisPointComparison.baseMap k (rootOrbitField k L j β))
        ((rationalCharacters.equivCharacterLattice S).symm a) := by
  apply characterRestrict_fixedDescend
  exact congrArg (fun φ => Additive.ofMul (CommGroupScheme.groupHom φ)) hβ

/-- The degree-normalized norm order of the root-orbit character at a rational point is
the pairing of `a` with the integer centralizer valuation of the point. -/
theorem characterNormOrder_rootOrbitCharacter [IsAffine S.toGrp.X.left] (f : S ⟶ T)
    (a : characterLattice S) {β : roots (T := T_L) (G := G_L) j_L}
    (hβ : β ∈ rootRestrictionFiber k L j f a)
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (h : Function.Bijective
      (BruhatTits.Cartan.restrictionEvaluation (CommGroupScheme.groupHom f)))
    (z : rationalPoints T.toGrp) :
    Geometry.Building.IntegerValuation.characterNormOrder v (rootOrbitCharacter k L j β) z =
      RealTorusSpace.eval S a
        (Geometry.Building.IntegerValuation.centralizerValuation v
          (CommGroupScheme.groupHom f) h z).toAdd :=
  Geometry.Building.IntegerValuation.characterNormOrder_eq_eval v _ h
    (characterRestrict_rootOrbitCharacter k L j f a hβ) z

end RootOrbit

end Langlands.GroupScheme

import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction
import Langlands.GroupScheme.SplitExistence.Assembly

/-! # Coordinate tori and actual root data of field Chevalley groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence SplitExistence.ChevalleyData

variable (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I]

/-- The identity coordinates identify `D(ℤ^I)` with the coordinate split torus. -/
def coordinateTorusIso :
    Tk (X := I → ℤ) k ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
  CommGroupScheme.isoOfGroupIso
    (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ)))

/-- Evaluation at a coordinate lattice vector is the same exponent character
after the actual torus isomorphism. -/
theorem charOf_eq_coordinate (m : I → ℤ) :
    charOf k m = (coordinateTorusIso k I).hom ≫
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m := by
  apply CommGroupScheme.hom_ext_points
  intro T x
  apply (Gm.pointsEquiv _ T).injective
  rw [gmPoints_charOf]
  change _ = Gm.pointsEquiv _ T
    ((x ≫ (Diagonalizable.splitIso (CommRingCat.of k)
      (AddEquiv.refl (I → ℤ))).hom.hom.hom) ≫
        (CommGroupScheme.groupHom
          (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m)).hom.hom)
  rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
    splitTorus.pointsEquiv_characterLatticeEquiv_symm]
  have hx : splitTorus.pointsEquiv I T
      (x ≫ (Diagonalizable.splitIso (CommRingCat.of k)
        (AddEquiv.refl (I → ℤ))).hom.hom.hom) =
      Diagonalizable.splitPointsEquiv (CommRingCat.of k)
        (AddEquiv.refl (I → ℤ)) T x :=
    isoOfPointModels_hom _ _ _ _ _
      (fun a y => splitTorus.pointsEquiv_naturality I a y) T x
  rw [hx]
  conv_lhs => rw [← Finset.univ_sum_single m, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  change torusPointsEquiv k T x (Multiplicative.ofAdd (Pi.single i (m i))) =
    torusPointsEquiv k T x (Multiplicative.ofAdd (Pi.single i 1)) ^ m i
  rw [← map_zpow, ← ofAdd_zsmul]
  congr 2
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

@[simp]
theorem coordinateTorusIso_character (m : I → ℤ) :
    characterLattice.congr (coordinateTorusIso k I) (charOf k m) =
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m := by
  change (coordinateTorusIso k I).inv ≫ charOf k m = _
  rw [charOf_eq_coordinate, Iso.inv_hom_id_assoc]

variable {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))

omit [DecidableEq I] in
/-- A coordinate datum with standard pairing realizes the actual lattice pairing. -/
theorem fieldRealization_toLinearMap
    (hpair : ∀ m n, P.toLinearMap m n = ∑ i, m i * n i) :
    (CoordinateRootDatum.fieldRealization k P).toLinearMap =
      latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) := by
  ext χ ν
  obtain ⟨m, rfl⟩ := (splitTorus.characterLatticeEquiv k I).symm.surjective χ
  obtain ⟨n, rfl⟩ := (splitTorus.cocharacterLatticeEquiv k I).symm.surjective ν
  change P.toLinearMap
    ((splitTorus.characterLatticeEquiv k I) ((splitTorus.characterLatticeEquiv k I).symm m))
    ((splitTorus.cocharacterLatticeEquiv k I)
      ((splitTorus.cocharacterLatticeEquiv k I).symm n)) = _
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    splitTorus.latticePairing_symm_symm, hpair]

variable {k I P} {b : P.Base} {D : ChevalleyData P b}
  (G : D.ChevGroup k)

/-- The torus of a field Chevalley group, expressed in the fixed coordinate torus. -/
def coordinateTorusHom :
    splitTorus (Spec (CommRingCat.of k)) I ⟶ G.H :=
  CommGroupScheme.groupHom (coordinateTorusIso k I).inv ≫ G.t

/-- Coordinate expression preserves maximality of the field Chevalley torus. -/
theorem isMaximalTorus_coordinateTorusHom [Finite J] [P.IsReduced] :
    IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (coordinateTorusHom G) :=
  IsMaximalTorus.precomp_torusIso (coordinateTorusIso k I).symm G.isMaximalTorus

/-- The same full coordinate datum is the actual datum of the coordinate torus
in any field Chevalley group, provided its pairing is standard. -/
theorem isRootDatumOf_coordinateTorusHom [Finite J] [P.IsReduced]
    [IsAffineHom G.H.X.hom] [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]
    (hpair : ∀ m n, P.toLinearMap m n = ∑ i, m i * n i) :
    IsRootDatumOf (coordinateTorusHom G) (CoordinateRootDatum.fieldRealization k P) := by
  let e := (chevDatumEquiv k P).comp (CoordinateRootDatum.fieldRealizationEquiv k P).symm
  refine IsRootDatumOf.precomp_torusIso (coordinateTorusIso k I).symm
    G.isRootDatumOf (fieldRealization_toLinearMap k I P hpair) e ?_
  intro χ
  obtain ⟨m, rfl⟩ := (CoordinateRootDatum.fieldRealizationEquiv k P).weightEquiv.surjective χ
  change charEquiv k
    ((CoordinateRootDatum.fieldRealizationEquiv k P).weightEquiv.symm
      ((CoordinateRootDatum.fieldRealizationEquiv k P).weightEquiv m)) = _
  rw [LinearEquiv.symm_apply_apply]
  change charEquiv k m = characterLattice.congr (coordinateTorusIso k I).symm
    ((CoordinateRootDatum.fieldRealizationEquiv k P).weightEquiv m)
  rw [charEquiv_apply, RootPairing.Equiv.weightEquiv_apply,
    CoordinateRootDatum.fieldRealizationEquiv_weightMap]
  exact charOf_eq_coordinate k I m

end Langlands.GroupScheme.ChevalleyIntegral

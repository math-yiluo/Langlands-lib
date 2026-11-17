import Langlands.GroupScheme.Torus.FiniteMultiplicativeTypeSplitting
import Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift
import Langlands.GroupScheme.Torus.MultiplicativeTypeAffineInfinitesimalCentrality

/-! # Centrality from a multiplicative-type residue over an Artinian local ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.FiniteFlatArtinianCentrality

/-- A diagonalizable pullback along a surjection is diagonalizable over the
actual quotient by its kernel. -/
theorem isDiagonalizable_quotient_of_surjective
    {B L : CommRingCat.{u}} (f : B ⟶ L) (hf : Function.Surjective f.hom)
    {N : GroupScheme (Spec B)}
    (hN : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.map f)).obj N)) :
    RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.algebraMap B (B ⧸ RingHom.ker f.hom))).obj N) := by
  let e := f.hom.quotientKerEquivOfSurjective hf
  let q := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hq : q ≫ Spec.map f =
      Spec.algebraMap B (B ⧸ RingHom.ker f.hom) := by
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map f = _
    rw [← Spec.map_comp]
    congr 1
    ext x
    change e.symm (f.hom x) = Ideal.Quotient.mk _ x
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
    (Descent.pullbackComparison (Spec.map f) q _ hq N).symm (hN.baseChange q)

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {N G : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffine N.X.left] [IsFinite N.X.hom] [Flat N.X.hom]

/-- A finite affine flat group with absolute multiplicative-type residue
becomes diagonalizable over a faithfully flat algebra. -/
theorem isDiagonalizable_lift
    (hN : IsMultiplicativeType ((baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj N)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
      Module.FaithfullyFlat R B ∧
      RelativeMultiplicativeType.IsDiagonalizable
        ((baseChange (Spec.algebraMap R B)).obj N) := by
  let k := IsLocalRing.ResidueField R
  let Nk := (baseChange (Spec.algebraMap R k)).obj N
  have : IsFinite Nk.X.hom := by
    change IsFinite (pullback.snd N.X.hom (Spec.algebraMap R k))
    infer_instance
  let s := hN.finiteSeparableSplitting
  let L := s.carrier
  let B := Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift.Carrier R L
  let b := Spec.algebraMap R B
  let d := Spec.map (CommRingCat.ofHom
    (Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift.toField R L))
  let r := Spec.algebraMap k L ≫ Spec.algebraMap R k
  have hdr : d ≫ b = r := by
    change Spec.map (CommRingCat.ofHom
      (Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift.toField R L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R k))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift.toField_algebraMap
      R L x
  let NB := (baseChange b).obj N
  have : IsAffine NB.X.left := by
    change IsAffine (pullback N.X.hom b)
    infer_instance
  have : IsFinite NB.X.hom := by
    change IsFinite (pullback.snd N.X.hom b)
    infer_instance
  have : Flat NB.X.hom := by
    change Flat (pullback.snd N.X.hom b)
    infer_instance
  have hd : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange d).obj NB) := by
    let e := Descent.pullbackComparison b d r hdr N ≪≫
      (Descent.pullbackComparison (Spec.algebraMap R k)
        (Spec.algebraMap k L) r rfl N).symm
    exact RelativeMultiplicativeType.IsDiagonalizable.of_iso e s.split
  have hq := isDiagonalizable_quotient_of_surjective
    (CommRingCat.ofHom
      (Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift.toField R L))
    (Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift.toField_surjective R L) hd
  have hB : RelativeMultiplicativeType.IsDiagonalizable NB :=
    Diagonalizable.isDiagonalizable_of_nilpotent_reduction
      (RingHom.ker
        (Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift.toField R L))
      (Langlands.CommutativeAlgebra.FiniteSeparableArtinianLift.isNilpotent_ker_toField R L)
      hq
  exact ⟨B, inferInstance, inferInstance, inferInstance, hB⟩

/-- Centrality lifts from the actual residue map for a finite affine flat
source of absolute multiplicative type on the residue field and affine target. -/
theorem isCentral_of_multiplicativeType_residue [IsAffine G.X.left]
    (i : N ⟶ G)
    (hN : IsMultiplicativeType ((baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj N))
    (hc : IsCentral ((baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map i)) :
    IsCentral i := by
  obtain ⟨B, hB, hA, hff, hdiag⟩ := isDiagonalizable_lift R hN
  let := hB
  let := hA
  let := hff
  have hflat : Flat (Spec.algebraMap R B) ∧ Surjective (Spec.algebraMap R B) :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R B))).2
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
  let := hflat.1
  let := hflat.2
  apply IsCentral.of_baseChange (Spec.algebraMap R B)
  apply MultiplicativeTypeAffineInfinitesimalCentrality.isCentral_baseChange_of_isDiagonalizable
    (R := CommRingCat.of R) (B := CommRingCat.of B)
    i hdiag (IsLocalRing.maximalIdeal R) _ hc
  have hnil := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hnil

/-- The unchanged monomorphic source, bundled as commutative by the lifted
all-test centrality. -/
def commGroupSchemeOfMultiplicativeTypeResidue [IsAffine G.X.left]
    (i : N ⟶ G) [Mono i.hom.hom]
    (hN : IsMultiplicativeType ((baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj N))
    (hc : IsCentral ((baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map i)) :
    CommGroupScheme (Spec (CommRingCat.of R)) :=
  (isCentral_of_multiplicativeType_residue R i hN hc).commGroupScheme

@[simp]
theorem commGroupSchemeOfMultiplicativeTypeResidue_toGrp [IsAffine G.X.left]
    (i : N ⟶ G) [Mono i.hom.hom]
    (hN : IsMultiplicativeType ((baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj N))
    (hc : IsCentral ((baseChange
      (Spec.algebraMap R (IsLocalRing.ResidueField R))).map i)) :
    (commGroupSchemeOfMultiplicativeTypeResidue R i hN hc).toGrp = N := rfl

end Langlands.GroupScheme.FiniteFlatArtinianCentrality

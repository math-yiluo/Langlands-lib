import Langlands.GroupScheme.Rational.RootSubgroupOverRing
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Rational.KernelCentralizerSmooth
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth

/-! # Actual smooth connected root groups over a domain -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

namespace CharacterFpqc

variable (R : Type u) [CommRing R] [IsDomain R]
  (I : Type u) [Fintype I] [DecidableEq I]

/-- The existing monomial character comparison holds over any domain. -/
theorem splitIso_comp_character_overDomain (m : I → ℤ) :
    (Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))).hom ≫
        CommGroupScheme.groupHom ((splitTorus.characterLatticeEquiv R I).symm m) =
      Diagonalizable.restrictMap (CommRingCat.of R) (scaleHom m) ≫
        (Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (PUnit.{u + 1} → ℤ))).hom ≫
          (splitTorus.gmIso _).inv := by
  apply hom_ext_points
  intro T x
  apply (Gm.pointsEquiv (Spec (CommRingCat.of R)) T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, splitTorus.pointsEquiv_characterLatticeEquiv_symm,
    splitIso_hom_points, Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    gmIso_inv_points, splitIso_hom_points]
  have h1 := Diagonalizable.pointsEquiv_restrictMap (CommRingCat.of R) (scaleHom m) x
    (Pi.single PUnit.unit 1)
  rw [scaleHom_apply, Pi.single_eq_same, one_smul] at h1
  change _ = DFunLike.coe (F := Multiplicative (PUnit.{u + 1} → ℤ) →* _)
    (Corepresented.pointsEquiv (Diagonalizable.functor (CommRingCat.of R) (PUnit.{u + 1} → ℤ))
      (Diagonalizable.grpCorepresentation (CommRingCat.of R) (PUnit.{u + 1} → ℤ)) T
      (x ≫ (Diagonalizable.restrictMap (CommRingCat.of R) (scaleHom m)).hom.hom))
    (.ofAdd (Pi.single PUnit.unit 1))
  rw [h1]
  set χ := Corepresented.pointsEquiv (Diagonalizable.functor (CommRingCat.of R) (I → ℤ))
    (Diagonalizable.grpCorepresentation (CommRingCat.of R) (I → ℤ)) T x
  change ∏ i, Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _ χ i ^ m i =
    DFunLike.coe (F := Multiplicative (I → ℤ) →* _) χ (.ofAdd m)
  conv_rhs => rw [← (Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _).symm_apply_apply χ]
  rfl


end CharacterFpqc

open CharacterFpqc in
/-- A nonzero character of a split torus over a domain is fpqc. -/
theorem characterFpqc_overDomain (R : Type u) [CommRing R] [IsDomain R]
    (S : CommGroupScheme (Spec (CommRingCat.of R))) (hS : IsSplitTorus S.toGrp)
    (a : characterLattice S) (ha : a ≠ 0) :
    QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left ∧
      Flat (CommGroupScheme.groupHom a).hom.hom.left ∧
        Surjective (CommGroupScheme.groupHom a).hom.hom.left := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) :=
    Additive.ofMul (e.inv ≫ CommGroupScheme.groupHom a)
  let E : S ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I := Additive.ofMul e.hom
  have haχ : a = E ≫ χ := by
    change a = Additive.ofMul (e.hom ≫ e.inv ≫ CommGroupScheme.groupHom a)
    rw [e.hom_inv_id_assoc]
    rfl
  set m := splitTorus.characterLatticeEquiv R I χ with hm_def
  have hχ : χ = (splitTorus.characterLatticeEquiv R I).symm m := by
    rw [hm_def, AddEquiv.symm_apply_apply]
  have hm : m ≠ 0 := by
    intro h0
    apply ha
    rw [haχ, hχ, h0, map_zero, Limits.comp_zero]
  let E₁ := e ≪≫ (Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))).symm
  let E₂ := Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (PUnit.{u + 1} → ℤ)) ≪≫
    (splitTorus.gmIso _).symm
  have ha' : CommGroupScheme.groupHom a =
      E₁.hom ≫ Diagonalizable.restrictMap (CommRingCat.of R) (scaleHom m) ≫ E₂.hom := by
    rw [haχ, hχ]
    change e.hom ≫ CommGroupScheme.groupHom ((splitTorus.characterLatticeEquiv R I).symm m) = _
    rw [(Iso.eq_inv_comp _).2 (splitIso_comp_character_overDomain R I m)]
    simp only [E₁, E₂, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hleft : (CommGroupScheme.groupHom a).hom.hom.left =
      E₁.hom.hom.hom.left ≫
        (Diagonalizable.restrictMap (CommRingCat.of R) (scaleHom m)).hom.hom.left ≫
          E₂.hom.hom.hom.left := by
    rw [ha']
    rfl
  have : IsIso E₁.hom.hom.hom.left := Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) E₁.hom
  have : IsIso E₂.hom.hom.hom.left := Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) E₂.hom
  have : Nontrivial (CommRingCat.of R) := inferInstanceAs (Nontrivial R)
  obtain ⟨hflat, hsurj⟩ := Diagonalizable.flat_and_surjective_restrictMap (CommRingCat.of R)
    (scaleHom m) (scaleHom_injective hm)
  have : QuasiCompact
      (Diagonalizable.restrictMap (CommRingCat.of R) (scaleHom m)).hom.hom.left := by
    have hqc : QuasiCompact (Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom (CommRingCat.of R) (scaleHom m)))) :=
      inferInstance
    rw [Diagonalizable.restrictMap_left]
    exact hqc
  rw [hleft]
  exact ⟨inferInstance, inferInstance, inferInstance⟩


namespace Domain

variable {R : Type u} [CommRing R] [IsDomain R]
    {S : CommGroupScheme (Spec (CommRingCat.of R))}
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- Conjugation by the full character kernel in its actual diagonalizable model. -/
def kernelAction : AutomorphicAction
    (Diagonalizable.groupScheme (CommRingCat.of R)
      (Diagonalizable.quotientLattice a)).toGrp G :=
  (((AutomorphicAction.conjugation i).restrict (characterKernelι a)).restrict
    (Diagonalizable.kernelDiagonalizableIso S hS a).inv)

omit [IsAffine G.X.left] in
/-- The diagonalizable reparametrization preserves the full kernel centralizer. -/
theorem kernelAction_fixedSubgroup :
    (kernelAction hS i a).fixedSubgroup = kernelCentralizer i a :=
  AutomorphicAction.fixedSubgroup_restrict_iso
    ((AutomorphicAction.conjugation i).restrict (characterKernelι a))
    (Diagonalizable.kernelDiagonalizableIso S hS a).symm

/-- The actual closed kernel-centralizer group scheme over the original domain. -/
def centralizer : GroupScheme (Spec (CommRingCat.of R)) :=
  CharacterAction.schemeFixedGroupScheme (kernelAction hS i a)

/-- Its actual inclusion into the ambient group scheme. -/
def centralizerHom : centralizer hS i a ⟶ G :=
  CharacterAction.schemeFixedHom (kernelAction hS i a)

/-- The constructed inclusion represents the centralizer on every scheme test. -/
theorem isRepresentedBy_centralizerHom :
    (kernelCentralizer i a).IsRepresentedBy (centralizerHom hS i a) := by
  rw [← kernelAction_fixedSubgroup hS i a]
  exact CharacterAction.isRepresentedBy_schemeFixedHom (kernelAction hS i a)

theorem isClosedSubgroup_centralizerHom : IsClosedSubgroup (centralizerHom hS i a) :=
  CharacterAction.isClosedSubgroup_schemeFixedHom (kernelAction hS i a)

instance centralizer_isAffineHom : IsAffineHom (centralizer hS i a).X.hom := by
  have : IsClosedImmersion (centralizerHom hS i a).hom.hom.left :=
    isClosedSubgroup_centralizerHom hS i a
  rw [← (centralizerHom hS i a).hom.hom.w]
  infer_instance

/-- Smoothness uses the full diagonalizable kernel, including any torsion. -/
theorem smooth_centralizer [Smooth G.X.hom] : Smooth (centralizer hS i a).X.hom :=
  CharacterAction.smooth_schemeFixedGroupScheme (kernelAction hS i a) inferInstance

include hS in
/-- Every nonzero character has an actual smooth affine geometrically connected
root representative, without any supplied centralizer or quotient action. -/
theorem subgroup_has_smooth_geometricallyConnected_closed_representative
    [Smooth G.X.hom] (ha : a ≠ 0) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of R))) (j : U ⟶ G),
      (subgroup i a).IsRepresentedBy j ∧ IsClosedSubgroup j ∧
        IsAffineHom U.X.hom ∧ Smooth U.X.hom ∧ GeometricallyConnected U.X.hom := by
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc_overDomain R S hS a ha
  let : QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom a).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom a).hom.hom.left := hsurj
  let : Smooth (centralizer hS i a).X.hom := smooth_centralizer hS i a
  exact ⟨Ring.subgroupScheme i a (centralizerHom hS i a)
      (isRepresentedBy_centralizerHom hS i a),
    Ring.subgroupHom i a (centralizerHom hS i a) (isRepresentedBy_centralizerHom hS i a),
    Ring.isRepresentedBy_subgroupHom i a (centralizerHom hS i a)
      (isRepresentedBy_centralizerHom hS i a) (isClosedSubgroup_centralizerHom hS i a),
    Ring.isClosedSubgroup_subgroupHom i a (centralizerHom hS i a)
      (isRepresentedBy_centralizerHom hS i a) (isClosedSubgroup_centralizerHom hS i a),
    inferInstance,
    Ring.smooth_subgroupScheme i a (centralizerHom hS i a)
      (isRepresentedBy_centralizerHom hS i a),
    Ring.geometricallyConnected_subgroupScheme i a (centralizerHom hS i a)
      (isRepresentedBy_centralizerHom hS i a)⟩

end Domain

end Langlands.GroupScheme.RelativeRoot

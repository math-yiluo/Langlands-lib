import Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement
import Langlands.GroupScheme.Reductive.LocalSplitWeylFamily

/-! # Root parametrizations and Weyl points under arbitrary coefficient base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitRootBaseChange

open LocalSplitCell RelativeRoot

section RootBaseChange

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- Coordinates of the points of the base change of `𝔾ₐ` to a commutative algebra `A`: a point over `Z`
corresponds to a point of `𝔾ₐ` over `Z` regarded over `Spec R`, with the same coordinate. -/
def gaCoordinates (Z : Over (Spec (CommRingCat.of A))) :
    (Z ⟶ ((GroupScheme.baseChange (algebraBaseMap R A)).obj (Ga R)).X) ≃*
      Multiplicative (Fin 1 → Γ(Z.left, ⊤)) :=
  (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (Ga R) Z).trans
    (VectorGroup.coordinates (CommRingCat.of R) 1 ((Over.map (algebraBaseMap R A)).obj Z))

/-- The coordinate comparison with the standard additive group is natural on every test. -/
theorem gaIso_naturality {Z W : Over (Spec (CommRingCat.of A))} (f : W ⟶ Z)
    (a : Z ⟶ ((GroupScheme.baseChange (algebraBaseMap R A)).obj (Ga R)).X) :
    ((gaCoordinates (R := R) A W).trans (VectorGroup.coordinates (CommRingCat.of A) 1 W).symm)
        (f ≫ a) =
      f ≫ ((gaCoordinates (R := R) A Z).trans
        (VectorGroup.coordinates (CommRingCat.of A) 1 Z).symm) a := by
  apply (VectorGroup.coordinates (CommRingCat.of A) 1 W).injective
  apply Multiplicative.toAdd.injective
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    VectorGroup.coordinates_comp, gaCoordinates,
    GroupScheme.baseChangePointsEquiv_naturality]
  rfl

/-- The base change of `𝔾ₐ` from `R` to a commutative algebra `A` is `𝔾ₐ` over `A`. -/
def gaIso : (GroupScheme.baseChange (algebraBaseMap R A)).obj (Ga R) ≅ Ga A :=
  isoOfPoints
    (fun Z => (gaCoordinates (R := R) A Z).trans
      (VectorGroup.coordinates (CommRingCat.of A) 1 Z).symm)
    (gaIso_naturality A)

/-- The additive-group base-change isomorphism preserves the coordinate on every test. -/
theorem coordinates_comp_gaIso_hom (Z : Over (Spec (CommRingCat.of A)))
    (a : Z ⟶ ((GroupScheme.baseChange (algebraBaseMap R A)).obj (Ga R)).X) :
    VectorGroup.coordinates (CommRingCat.of A) 1 Z (a ≫ (gaIso (R := R) A).hom.hom.hom) =
      gaCoordinates (R := R) A Z a := by
  have h := comp_isoOfPoints_hom
    (fun Z => (gaCoordinates (R := R) A Z).trans
      (VectorGroup.coordinates (CommRingCat.of A) 1 Z).symm)
    (gaIso_naturality A) Z a
  rw [gaIso, h]
  exact (VectorGroup.coordinates (CommRingCat.of A) 1 Z).apply_symm_apply _

theorem baseChangePointsEquiv_scalarPoint (Z : Over (Spec (CommRingCat.of A)))
    (c : Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (Ga R) Z
        (VectorGroup.scalarPoint (CommRingCat.of A) Z c ≫ (gaIso (R := R) A).inv.hom.hom) =
      VectorGroup.scalarPoint (CommRingCat.of R) ((Over.map (algebraBaseMap R A)).obj Z) c := by
  have h := coordinates_comp_gaIso_hom (R := R) A Z
    (VectorGroup.scalarPoint (CommRingCat.of A) Z c ≫ (gaIso (R := R) A).inv.hom.hom)
  change VectorGroup.coordinates (CommRingCat.of A) 1 Z
    ((VectorGroup.scalarPoint (CommRingCat.of A) Z c ≫ (gaIso (R := R) A).inv.hom.hom) ≫
      (gaIso (R := R) A).hom.hom.hom) = _ at h
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id] at h
  apply VectorGroup.points_ext
  intro j
  rw [VectorGroup.coordinates_scalarPoint]
  change (gaCoordinates (R := R) A Z _).toAdd j = c
  rw [← h, VectorGroup.coordinates_scalarPoint]

variable {G : GroupScheme (Spec (CommRingCat.of R))}

/-- The base change to `A` of a map `u : 𝔾ₐ ⟶ G`, with source the standard `𝔾ₐ` over `A`. -/
def baseChangeRoot (u : Ga R ⟶ G) : Ga A ⟶ (GroupScheme.baseChange (algebraBaseMap R A)).obj G :=
  (gaIso (R := R) A).inv ≫ (GroupScheme.baseChange (algebraBaseMap R A)).map u

/-- The values of the base-changed root map correspond to the values of the original map. -/
theorem baseChangePointsEquiv_rootPoint (u : Ga R ⟶ G) (Z : Over (Spec (CommRingCat.of A)))
    (c : Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z (rootPoint (baseChangeRoot A u) Z c) =
      rootPoint u ((Over.map (algebraBaseMap R A)).obj Z) c := by
  rw [rootPoint, baseChangeRoot, Grp.comp_hom_hom, ← Category.assoc,
    GroupScheme.baseChangePointsEquiv_comp, baseChangePointsEquiv_scalarPoint, rootPoint]

/-- Ordered products of base-changed root maps correspond to the original ordered products. -/
theorem baseChangePointsEquiv_orderedProduct {J : Type u} (u : J → (Ga R ⟶ G)) {r : ℕ}
    (e : Fin r → J) (Z : Over (Spec (CommRingCat.of A))) (c : Fin r → Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
        (orderedProduct (fun α => baseChangeRoot A (u α)) e Z c) =
      orderedProduct u e ((Over.map (algebraBaseMap R A)).obj Z) c := by
  simp only [orderedProduct, map_list_prod, List.map_ofFn, Function.comp_def,
    baseChangePointsEquiv_rootPoint]

variable {I : Type u} [Fintype I]

/-- The base-changed root map represents the root subgroup of the base-changed torus for the
same exponent character. -/
theorem isRepresentedBy_baseChangeRoot (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (m : I → ℤ) (u : Ga R ⟶ G)
    (hu : (subgroup (S := splitTorus.commGroupScheme _ I) i
      (splitTorus.exponentCharacter _ I m)).IsRepresentedBy u) :
    (subgroup (S := splitTorus.commGroupScheme (Spec (CommRingCat.of A)) I)
      (splitTorus.baseChangeHom (K := A) G I i)
      (splitTorus.exponentCharacter _ I m)).IsRepresentedBy (baseChangeRoot A u) := by
  have h := hu.baseChange (algebraBaseMap R A)
  rw [← subgroup_baseChange] at h
  have hsq : (GroupScheme.baseChange (algebraBaseMap R A)).map i ≫
      (Iso.refl ((GroupScheme.baseChange (algebraBaseMap R A)).obj G)).hom =
      CommGroupScheme.groupHom (splitTorus.commBaseChangeIso (algebraBaseMap R A) I).hom ≫
        splitTorus.baseChangeHom (K := A) G I i := by
    change _ ≫ 𝟙 _ = (splitTorus.baseChangeIso (algebraBaseMap R A) I).hom ≫
      (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫ _
    rw [Category.comp_id, Iso.hom_inv_id_assoc]
  have htr := subgroup_comap_of_transport (splitTorus.commBaseChangeIso (algebraBaseMap R A) I)
    (Iso.refl _) hsq (characterLattice.baseChange (algebraBaseMap R A) _
      (splitTorus.exponentCharacter _ I m))
  have ha : characterLattice.congr (splitTorus.commBaseChangeIso (algebraBaseMap R A) I)
      (characterLattice.baseChange (algebraBaseMap R A) _ (splitTorus.exponentCharacter _ I m)) =
      splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I m := by
    rw [characterLattice.congr_apply, ← splitTorus.exponentCharacter_baseChange,
      Iso.inv_hom_id_assoc]
  rw [ha, Iso.refl_hom, SubgroupFunctor.comap_id] at htr
  rw [htr]
  refine ⟨?_, ?_⟩
  · have : Mono ((GroupScheme.baseChange (algebraBaseMap R A)).map u).hom.hom := h.1
    change Mono ((gaIso (R := R) A).inv.hom.hom ≫
      ((GroupScheme.baseChange (algebraBaseMap R A)).map u).hom.hom)
    infer_instance
  · exact (SubgroupFunctor.range_iso_comp (gaIso (R := R) A).symm _).trans h.2

/-- Torus values of the base-changed torus map correspond to torus values of the original
map. -/
theorem baseChangePointsEquiv_torus (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {Z : Over (Spec (CommRingCat.of A))} (t : Z ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
        (t ≫ (splitTorus.baseChangeHom (K := A) G I i).hom.hom) =
      GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
          (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) ≫ i.hom.hom := by
  rw [← GroupScheme.baseChangePointsEquiv_comp, Category.assoc, ← Grp.comp_hom_hom]
  rfl

/-- Character values on torus points correspond under base change. -/
theorem charValue_exponentCharacter_baseChange (m : I → ℤ) {Z : Over (Spec (CommRingCat.of A))}
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X) :
    VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I m) Z t =
      VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I m) ((Over.map (algebraBaseMap R A)).obj Z)
        (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
          (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom)) := by
  rw [VectorGroup.charValue, VectorGroup.charValue, splitTorus.pointsEquiv_exponentCharacter,
    splitTorus.pointsEquiv_exponentCharacter]
  have h := splitTorus.pointsEquiv_baseChangeIso_hom (algebraBaseMap R A) I Z
    (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id] at h
  rw [h]
  rfl

/-- Root parametrizations stay root parametrizations after base change to a commutative algebra. -/
theorem isRootParametrization_baseChangeRoot (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (m : I → ℤ) (u : Ga R ⟶ G) (hu : IsRootParametrization i m u) :
    IsRootParametrization (splitTorus.baseChangeHom (K := A) G I i) m (baseChangeRoot A u) where
  represents := isRepresentedBy_baseChangeRoot A i m u hu.represents
  isClosedSubgroup := by
    have hc := hu.isClosedSubgroup.baseChange (algebraBaseMap R A)
    change IsClosedImmersion ((gaIso (R := R) A).inv.hom.hom.left ≫
      ((GroupScheme.baseChange (algebraBaseMap R A)).map u).hom.hom.left)
    have : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap R A)).map u).hom.hom.left :=
      hc
    have : IsIso (gaIso (R := R) A).inv.hom.hom.left :=
      (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map (gaIso (R := R) A).inv))
    infer_instance
  equivariant Z t c := by
    apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z).injective
    rw [map_mul, map_mul, map_inv, baseChangePointsEquiv_torus, baseChangePointsEquiv_rootPoint,
      baseChangePointsEquiv_rootPoint, hu.equivariant,
      charValue_exponentCharacter_baseChange (R := R) A]

end RootBaseChange

section BaseChange

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

theorem baseScalar_map (Z : Over (Spec (CommRingCat.of A))) (d : R) :
    baseScalar ((Over.map (algebraBaseMap R A)).obj Z) d = baseScalar Z (algebraMap R A d) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Z.hom ≫ algebraBaseMap R A).appTop).hom d =
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Z.hom.appTop).hom (algebraMap R A d)
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Base change to a commutative algebra commutes with rescaling. -/
theorem baseChangeRoot_scaleHom (d : R) (v : Ga R ⟶ G) :
    baseChangeRoot A (scaleHom d ≫ v) =
      scaleHom (algebraMap R A d) ≫ baseChangeRoot A v := by
  apply hom_ext_rootPoint
  intro Z c
  apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z).injective
  rw [baseChangePointsEquiv_rootPoint, rootPoint_scaleHom, rootPoint_scaleHom,
    baseChangePointsEquiv_rootPoint, baseScalar_map]

end BaseChange

section WeylBaseChange

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} (A : Type u) [CommRing A] [Algebra R A]

/-- The base change to a commutative algebra of a Weyl point built from two root maps is the Weyl point of
the base-changed root maps, with the same exponent automorphism. -/
theorem isWeylPoint_baseChange {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {u v : Ga R ⟶ G} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)} (h : IsWeylPoint i (weylPoint u v) f) :
    IsWeylPoint (splitTorus.baseChangeHom (K := A) G I i)
      (weylPoint (baseChangeRoot A u) (baseChangeRoot A v)) f := by
  intro Z t
  let E := GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
  let ET := GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
  let Z' := (Over.map (algebraBaseMap R A)).obj Z
  apply E.injective
  have hN : E (toUnit Z ≫ weylPoint (baseChangeRoot A u) (baseChangeRoot A v)) =
      toUnit Z' ≫ weylPoint u v := by
    rw [toUnit_comp_eq_constantPoint, constantPoint_weylPoint, map_mul, map_mul,
      baseChangePointsEquiv_rootPoint, baseChangePointsEquiv_rootPoint,
      toUnit_comp_eq_constantPoint, constantPoint_weylPoint]
  have hexp : (splitTorus.exponentIso (Spec (CommRingCat.of A)) I f).hom ≫
      (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv =
        (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
          (GroupScheme.baseChange (algebraBaseMap R A)).map
            (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc,
      splitTorus.exponentIso_baseChange (Spec (CommRingCat.of R)) I (algebraBaseMap R A) f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : ET ((t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom) ≫
      (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) =
        ET (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) ≫
          (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom.hom.hom := by
    rw [← GroupScheme.baseChangePointsEquiv_comp, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hexp]
  rw [map_mul, map_mul, map_inv, hN, baseChangePointsEquiv_torus, ← Category.assoc,
    baseChangePointsEquiv_torus, ht, h Z' _, Category.assoc]

end WeylBaseChange

end Langlands.GroupScheme.LocalSplitRootBaseChange

import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.GeneralLinearCharacterClassification
import Langlands.GroupScheme.Rational.GeneralLinearScalarCenter

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] {R : CommRingCat.{u}}

theorem characterOnAffineMatrices_zsmul (m : ℤ)
    (χ : rationalCharacters (groupScheme n R)) (A : CommAlgCat.{u} R) (g : GL n A) :
    characterOnAffineMatrices (m • χ).toMul A g =
      characterOnAffineMatrices χ.toMul A g ^ m := by
  change Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
      ((affinePointsEquiv n R A).symm g ≫ (χ.toMul ^ m).hom.hom) =
    Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
      ((affinePointsEquiv n R A).symm g ≫ χ.toMul.hom.hom) ^ m
  rw [Grp.Hom.hom_hom_zpow, GrpObj.comp_zpow, map_zpow]

theorem gm_pointsEquiv_eq_affinePointsEquiv (A : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op A) ⟶ (Gm (Spec R)).X) :
    Gm.pointsEquiv (Spec R) ((algSpec R).obj (op A)) x =
      Units.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom.toMonoidHom
        (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom x) := by
  apply Units.ext
  change (Gm.pointsEquiv (Spec R) ((algSpec R).obj (op A)) x).val =
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).hom _)
  simp
  rfl

theorem characterOnAffineMatrices_determinantCharacter (A : CommAlgCat.{u} R) (g : GL n A) :
    characterOnAffineMatrices (determinantCharacter n R).toMul A g =
      Matrix.GeneralLinearGroup.det g := by
  apply Units.map_injective
    (f := (Corepresented.affineSectionsIso A).inv.hom.toRingHom.toMonoidHom)
    (Corepresented.affineSectionsAlgEquiv A).symm.injective
  change Units.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom.toMonoidHom
      (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
        ((affinePointsEquiv n R A).symm g ≫ (determinantCharacter n R).toMul.hom.hom)) = _
  rw [← gm_pointsEquiv_eq_affinePointsEquiv]
  change characterEval (determinantCharacter n R) ((algSpec R).obj (op A))
    ((affinePointsEquiv n R A).symm g) = _
  rw [characterEval_determinantCharacter, pointsEquiv_eq_affinePointsEquiv,
    MulEquiv.apply_symm_apply]
  exact Matrix.GeneralLinearGroup.map_det _ g

theorem rationalCharacter_eq_zsmul_determinant [IsDomain R]
    (χ : rationalCharacters (groupScheme n R)) :
    ∃ m : ℤ, χ = m • determinantCharacter n R := by
  obtain ⟨m, hm⟩ := exists_characterOnAffineMatrices_power χ.toMul
  have he : χ.toMul = (m • determinantCharacter n R).toMul := by
    apply characterOnAffineMatrices_ext
    intro A g
    rw [characterOnAffineMatrices_zsmul, characterOnAffineMatrices_determinantCharacter]
    exact hm A g
  exact ⟨m, congrArg Additive.ofMul he⟩

theorem det_coordinateDiagonalUnits {A : Type*} [CommRing A] (i : n) (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (coordinateDiagonalUnits A i a) = a := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.det, coordinateDiagonalUnits, diagonalMatrixUnits_val,
    Pi.mulSingle_apply, apply_ite]

theorem characterRestrict_coordinate_determinant (i : n) :
    characterRestrict (coordinateDiagonalHom n R i) (determinantCharacter n R) =
      Additive.ofMul (𝟙 (Gm (Spec R)).toGrp) := by
  apply rationalCharacters.ext_characterEval
  intro T x
  rw [characterEval_characterRestrict, characterEval_determinantCharacter,
    pointsEquiv_coordinateDiagonalHom, det_coordinateDiagonalUnits]
  change Gm.pointsEquiv (Spec R) T x = Gm.pointsEquiv (Spec R) T (x ≫ 𝟙 _)
  rw [Category.comp_id]

theorem determinant_zsmul_injective [IsDomain R] [Nonempty n] :
    Function.Injective (fun m : ℤ => m • determinantCharacter n R) := by
  obtain ⟨i⟩ := ‹Nonempty n›
  intro a b h
  have he := congrArg (fun χ => gmEndEquiv R (characterRestrict (coordinateDiagonalHom n R i) χ)) h
  simp only [map_zsmul, characterRestrict_coordinate_determinant] at he
  change a • gmEndEquiv R (𝟙 (Gm (Spec R))) = b • gmEndEquiv R (𝟙 (Gm (Spec R))) at he
  have hid : gmEndEquiv R (𝟙 (Gm (Spec R))) = 1 := gmEndEquiv_id R
  simpa only [hid, smul_eq_mul, mul_one] using he

theorem rationalCharacter_empty [IsEmpty n] (χ : rationalCharacters (groupScheme n R)) : χ = 0 := by
  apply congrArg Additive.ofMul
  apply characterOnAffineMatrices_ext
  intro A g
  rw [characterOnAffineMatrices_empty]
  change 1 = Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
    ((affinePointsEquiv n R A).symm g ≫ (0 : rationalCharacters (groupScheme n R)).toMul.hom.hom)
  rw [rationalCharacters.comp_zero, map_one]

theorem characterRestrict_scalar_determinant :
    characterRestrict (scalarTorus n R) (determinantCharacter n R) =
      (Fintype.card n : ℤ) • Additive.ofMul (𝟙 (Gm (Spec R)).toGrp) := by
  apply rationalCharacters.ext_characterEval
  intro T x
  rw [characterEval_characterRestrict, characterEval_determinantCharacter,
    pointsEquiv_scalarTorus, Matrix.GeneralLinearGroup.det_scalar, characterEval_zsmul]
  change Gm.pointsEquiv (Spec R) T x ^ Fintype.card n =
    Gm.pointsEquiv (Spec R) T (x ≫ 𝟙 _) ^ (Fintype.card n : ℤ)
  rw [Category.comp_id, zpow_natCast]

theorem central_morphism_point_matrix {H : GroupScheme (Spec R)} {j : H ⟶ groupScheme n R}
    (hj : IsCentral j) (T : Over (Spec R)) (x : T ⟶ H.X) :
    pointsEquiv n R T (x ≫ j.hom.hom) ∈ Subgroup.center (GL n Γ(T.left, ⊤)) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  have hc := (commute_of_mem_center (hj T x) ((pointsEquiv n R T).symm g)).map
    (pointsEquiv n R T).toMonoidHom
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hc.eq.symm

theorem scalarTorus_isSplitComponent [Nonempty n] (k : Type u) [Field k] :
    IsSplitComponent (scalarTorus n (CommRingCat.of k)) := by
  refine ⟨isCentralSplitTorus_scalarTorus n k, ?_⟩
  intro A' j hj f hf
  have : IsClosedImmersion j.hom.hom.left := hj.1.2
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hm : Mono ((Grp.forget _).map j) := by
    change Mono j.hom.hom
    infer_instance
  have : Mono j := (Grp.forget _).mono_of_mono_map (f := j) hm
  exact scalarPointFormula_factor_isIso (scalarTorus n (CommRingCat.of k))
    (pointsEquiv_scalarTorus) j (central_morphism_point_matrix hj.2) f hf

end Langlands.GroupScheme.GeneralLinear

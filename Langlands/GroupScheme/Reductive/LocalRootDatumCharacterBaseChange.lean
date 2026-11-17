import Langlands.GroupScheme.Reductive.LocalSplitIsogenyRootDatumAdapter

/-! # Open-local root-datum character formulas after arbitrary base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace splitTorus

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {I I' : Type u} [Fintype I] [Fintype I']

/-- Restore coordinates after pullback without changing point coordinates. -/
theorem pointsEquiv_baseChangeIso_inv (U : Over S')
    (x : U ⟶ (splitTorus S' I).X) :
    pointsEquiv I ((Over.map b).obj U)
        (GroupScheme.baseChangePointsEquiv b (splitTorus S I) U
          (x ≫ (baseChangeIso b I).inv.hom.hom)) = pointsEquiv I U x := by
  change baseChangePointsEquiv b I U (x ≫ (baseChangeIso b I).inv.hom.hom) =
    pointsEquiv I U x
  have h := pointsEquiv_baseChangeIso_hom b I U
    (x ≫ (baseChangeIso b I).inv.hom.hom)
  simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id] using h.symm

/-- Coordinate pullback of a torus homomorphism acts by the original map
on the same point over the original base. -/
theorem pointsEquiv_coordinateBaseChangeHom
    (tau : commGroupScheme S I ⟶ commGroupScheme S I')
    (U : Over S') (x : U ⟶ (splitTorus S' I).X) :
    pointsEquiv I' U (x ≫ (CommGroupScheme.groupHom
        (coordinateBaseChangeHom b tau)).hom.hom) =
      pointsEquiv I' ((Over.map b).obj U)
        (GroupScheme.baseChangePointsEquiv b (splitTorus S I) U
          (x ≫ (baseChangeIso b I).inv.hom.hom) ≫
            (CommGroupScheme.groupHom tau).hom.hom) := by
  change pointsEquiv I' U
    (((x ≫ (baseChangeIso b I).inv.hom.hom) ≫
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom tau)).hom.hom) ≫
        (baseChangeIso b I').hom.hom.hom) = _
  rw [pointsEquiv_baseChangeIso_hom]
  change pointsEquiv I' ((Over.map b).obj U)
    (GroupScheme.baseChangePointsEquiv b (splitTorus S I') U
      ((x ≫ (baseChangeIso b I).inv.hom.hom) ≫
        ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom tau)).hom.hom)) = _
  rw [GroupScheme.baseChangePointsEquiv_comp]

/-- An all-test monomial formula on an open becomes an actual equality
of characters after any base change whose image lies in that open. -/
theorem coordinateBaseChangeHom_character_of_open_points
    (tau : commGroupScheme S I ⟶ commGroupScheme S I')
    (V : S.Opens) (hb : b ⁻¹ᵁ V = ⊤) (m : I' → ℤ) (n : I → ℤ)
    (h : ∀ (U : Over S), U.hom ⁻¹ᵁ V = ⊤ →
      ∀ (x : U ⟶ (splitTorus S I).X),
        ∏ a, pointsEquiv I' U (x ≫ (CommGroupScheme.groupHom tau).hom.hom) a ^ m a =
          ∏ a, pointsEquiv I U x a ^ n a) :
    coordinateBaseChangeHom b tau ≫ exponentCharacter S' I' m =
      exponentCharacter S' I n := by
  change CommGroupScheme.groupHom
      (coordinateBaseChangeHom b tau ≫ exponentCharacter S' I' m) =
    CommGroupScheme.groupHom (exponentCharacter S' I n)
  apply hom_ext_points
  intro U x
  apply (Gm.pointsEquiv S' U).injective
  change Gm.pointsEquiv S' U
      ((x ≫ (CommGroupScheme.groupHom (coordinateBaseChangeHom b tau)).hom.hom) ≫
        (CommGroupScheme.groupHom (exponentCharacter S' I' m)).hom.hom) =
    Gm.pointsEquiv S' U
      (x ≫ (CommGroupScheme.groupHom (exponentCharacter S' I n)).hom.hom)
  rw [pointsEquiv_exponentCharacter, pointsEquiv_exponentCharacter,
    pointsEquiv_coordinateBaseChangeHom]
  have hU : ((Over.map b).obj U).hom ⁻¹ᵁ V = ⊤ := by
    change (U.hom ≫ b) ⁻¹ᵁ V = ⊤
    rw [Scheme.Hom.comp_preimage, hb, Scheme.Hom.preimage_top]
  have he := h ((Over.map b).obj U) hU
    (GroupScheme.baseChangePointsEquiv b (splitTorus S I) U
      (x ≫ (baseChangeIso b I).inv.hom.hom))
  rw [pointsEquiv_baseChangeIso_inv] at he
  exact he

end splitTorus

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)} [P.IsReduced] [Q.IsReduced]

/-- A common root-datum weight map exists near every base point, as an
actual character identity on every scheme with image in the neighbourhood. -/
def HasZariskiLocalRootDatumTorusCharacterMap
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (Q : RootDatum J' (I' → ℤ) (I' → ℤ)) [P.IsReduced] [Q.IsReduced] : Prop :=
  ∀ s : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens,
    s ∈ V ∧ ∃ (p : ℕ) (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P),
      ∀ (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of R)), b ⁻¹ᵁ V = ⊤ →
        ∀ m : I' → ℤ,
          splitTorus.coordinateBaseChangeHom b tau ≫ splitTorus.exponentCharacter B I' m =
            splitTorus.exponentCharacter B I (r.weightMap m)

/-- The local clause of the explicit intrinsic proposition yields actual
open-local character identities over an arbitrary commutative ring. -/
theorem hasZariskiLocalRootDatumTorusCharacterMap_of_affineSplitSurjectionRootDatum
    (hAffine : AffineSplitSurjectionRootDatumStatement.{u})
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hi : IsClosedSubgroup i)
    (hmaxG : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hj : IsClosedSubgroup j)
    (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
    (hP : @IsFibrewiseRootDatumOf R _ I _ G hG.isAffineHom i J P)
    (hQ : @IsFibrewiseRootDatumOf R _ I' _ H hH.isAffineHom j J' Q)
    (hfreeP : ∀ a : J, Nonempty
      (@splitTorus.exponentWeightSpace (CommRingCat.of R) I _ G hG.isAffineHom i
        (P.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (hfreeQ : ∀ a : J', Nonempty
      (@splitTorus.exponentWeightSpace (CommRingCat.of R) I' _ H hH.isAffineHom j
        (Q.root a) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (phi : G ⟶ H) (hfinite : LocallyQuasiFinite phi.hom.hom.left)
    (hsurj : Surjective phi.hom.hom.left)
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j) :
    HasZariskiLocalRootDatumTorusCharacterMap tau P Q := by
  have h := hAffine R G H hG hH I I' i j J J' P Q hi hmaxG hP hfreeP
    hj hmaxH hQ hfreeQ phi (CommGroupScheme.groupHom tau) hfinite hsurj hphi
  intro s
  obtain ⟨V, hs, p, r, _, hpoints⟩ := h.1 s
  refine ⟨V, hs, p, r, fun B b hb m => ?_⟩
  exact splitTorus.coordinateBaseChangeHom_character_of_open_points b tau V hb m
    (r.weightMap m) (fun U hU x => hpoints U hU x m)

end Langlands.GroupScheme

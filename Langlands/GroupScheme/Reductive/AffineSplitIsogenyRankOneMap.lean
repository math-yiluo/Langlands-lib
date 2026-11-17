import Langlands.GroupScheme.Reductive.AffineSplitIsogenyWeylMap
import Langlands.GroupScheme.Reductive.LocalSplitRankOneLaws
import Langlands.GroupScheme.Reductive.SplitBorelPositiveCoordinates

/-! # Coroot maps and powered rank-one laws -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {H : GroupScheme (Spec (CommRingCat.of R))}

variable (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)

/-- The source coroot followed by the prescribed torus map. -/
def corootMap (S : Scheme.{u}) (a : J) : (Gm S).toGrp ⟶ splitTorus S I' :=
  CommGroupScheme.groupHom (splitTorus.exponentCocharacter S I (P.coroot a)) ≫ torusMap S f

variable
  (hPpair : ∀ m n : I → ℤ, P.toLinearMap m n = ∑ j, m j * n j)
  (hQpair : ∀ m n : I' → ℤ, Q.toLinearMap m n = ∑ j, m j * n j)

include hPpair hQpair in
/-- The transpose equation realizes the prescribed coweight map on actual cocharacters. -/
theorem exponentCocharacter_comp_torusMap (S : Scheme.{u}) (ν : I → ℤ) :
    CommGroupScheme.groupHom (splitTorus.exponentCocharacter S I ν) ≫ torusMap S f =
      CommGroupScheme.groupHom (splitTorus.exponentCocharacter S I' (f.coweightMap ν)) := by
  classical
  change CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter S I ν ≫ splitTorus.exponentHom S I I' f.weightMap) = _
  apply congrArg CommGroupScheme.groupHom
  apply splitTorus.hom_ext_projections S I'
  intro j'
  rw [Category.assoc, splitTorus.exponentHom_comp_proj,
    splitTorus.exponentCocharacter_comp_exponentCharacter,
    splitTorus.exponentCocharacter_comp_proj]
  congr 1
  have h := f.pairing_apply (Pi.single j' 1) ν
  rw [hPpair, hQpair] at h
  simpa [Pi.single_apply] using h

include hPpair hQpair in
/-- The prescribed torus map carries a source cocharacter point by the coweight map. -/
theorem cocharPoint_comp_torusMap (ν : I → ℤ)
    (Z : Over (Spec (CommRingCat.of R))) (d : Γ(Z.left, ⊤)ˣ) :
    cocharPoint ν Z d ≫ (torusMap _ f).hom.hom =
      cocharPoint (f.coweightMap ν) Z d := by
  rw [cocharPoint_eq_comp, cocharPoint_eq_comp, Category.assoc,
    ← Grp.comp_hom_hom, exponentCocharacter_comp_torusMap f hPpair hQpair]

/-- Evaluation of an integer multiple of a cocharacter is evaluation at the same power. -/
theorem cocharPoint_nat_smul (ν : I' → ℤ) (q : ℕ)
    (Z : Over (Spec (CommRingCat.of R))) (d : Γ(Z.left, ⊤)ˣ) :
    cocharPoint ((q : ℤ) • ν) Z d = cocharPoint ν Z (d ^ q) := by
  apply (splitTorus.pointsEquiv I' Z).injective
  simp only [cocharPoint, MulEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
  funext j'
  rw [← zpow_natCast d q, ← zpow_mul]

include hPpair hQpair in
/-- The actual coroot map is the target coroot multiplied by its root factor. -/
theorem corootMap_eq (S : Scheme.{u}) (a : J) :
    corootMap f S a =
      CommGroupScheme.groupHom (splitTorus.exponentCocharacter S I'
        ((f.rootFactor (f.indexEquiv.symm a) : ℤ) • Q.coroot (f.indexEquiv.symm a))) := by
  rw [corootMap, exponentCocharacter_comp_torusMap f hPpair hQpair]
  congr 2
  simpa only [Equiv.apply_symm_apply] using f.coroot_coweightMap (f.indexEquiv.symm a)

include hPpair hQpair in
/-- The all-test coroot identity retains the root-factor power on the unit. -/
theorem corootPoint_comp_torusMap (a : J)
    (Z : Over (Spec (CommRingCat.of R))) (d : Γ(Z.left, ⊤)ˣ) :
    cocharPoint (P.coroot a) Z d ≫ (torusMap _ f).hom.hom =
      cocharPoint (Q.coroot (f.indexEquiv.symm a)) Z
        (d ^ f.rootFactor (f.indexEquiv.symm a)) := by
  rw [cocharPoint_comp_torusMap f hPpair hQpair]
  have h := f.coroot_coweightMap (f.indexEquiv.symm a)
  simp only [Equiv.apply_symm_apply] at h
  rw [h, cocharPoint_nat_smul]

variable (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)

include hchar in
/-- The root-factor power fixes minus one in the functions on every test scheme. -/
theorem neg_one_pow_rootFactor_sections (j' : J')
    (Z : Over (Spec (CommRingCat.of R))) :
    (-1 : Γ(Z.left, ⊤)) ^ f.rootFactor j' = -1 := by
  have h := add_pow_rootFactor_sections f hchar j' Z (-1) 1
  rw [neg_add_cancel, zero_pow (f.rootFactor_pos j').ne', one_pow] at h
  linear_combination -h

include hchar in
/-- The corresponding power fixes the unit minus one, including in characteristic two. -/
theorem unit_neg_one_pow_rootFactor (j' : J')
    (Z : Over (Spec (CommRingCat.of R))) :
    (-1 : Γ(Z.left, ⊤)ˣ) ^ f.rootFactor j' = -1 := by
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using
    neg_one_pow_rootFactor_sections f hchar j' Z

/-- Opposite powered roots have the same exponent, at the corresponding opposite index. -/
theorem rootPoint_poweredRootFamily_opposite (u' : J' → (Ga R ⟶ H)) (a : J)
    (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)) :
    rootPoint (poweredRootFamily f hchar u' (P.reflectionPerm a a)) Z x =
      rootPoint (u' (Q.reflectionPerm (f.indexEquiv.symm a) (f.indexEquiv.symm a))) Z
        (x ^ f.rootFactor (f.indexEquiv.symm a)) := by
  rw [rootPoint_poweredRootFamily, f.indexEquiv_symm_reflectionPerm,
    f.rootFactor_reflectionPerm]

include hPpair hQpair in
/-- Every actual target rank-one law transfers to its powered source pair under the
prescribed torus map, with the same source coroot. -/
theorem rankOneLaws_poweredRootFamily
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (u' : J' → (Ga R ⟶ H)) (a : J)
    (hL : RankOneLaws i' (Q.coroot (f.indexEquiv.symm a))
      (u' (f.indexEquiv.symm a))
      (u' (Q.reflectionPerm (f.indexEquiv.symm a) (f.indexEquiv.symm a)))) :
    RankOneLaws (torusMap _ f ≫ i') (P.coroot a)
      (poweredRootFamily f hchar u' a)
      (poweredRootFamily f hchar u' (P.reflectionPerm a a)) := by
  have hN : weylPoint (poweredRootFamily f hchar u' a)
        (poweredRootFamily f hchar u' (P.reflectionPerm a a)) =
      weylPoint (u' (f.indexEquiv.symm a))
        (u' (Q.reflectionPerm (f.indexEquiv.symm a) (f.indexEquiv.symm a))) :=
    rootWeylPoint_poweredRootFamily f hchar u' a
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z x
    rw [hN, rootPoint_poweredRootFamily, rootPoint_neg,
      rootPoint_poweredRootFamily_opposite, ← rootPoint_neg]
    exact hL.1 Z _
  · intro Z x
    rw [hN, rootPoint_poweredRootFamily_opposite, rootPoint_neg,
      rootPoint_poweredRootFamily, ← rootPoint_neg]
    exact hL.2.1 Z _
  · intro Z
    rw [hN, hL.2.2.1 Z, Grp.comp_hom_hom, ← Category.assoc,
      corootPoint_comp_torusMap f hPpair hQpair, unit_neg_one_pow_rootFactor f hchar]
  · intro Z x y d hd
    have hdq : ((d ^ f.rootFactor (f.indexEquiv.symm a) : Γ(Z.left, ⊤)ˣ) :
        Γ(Z.left, ⊤)) = 1 + x ^ f.rootFactor (f.indexEquiv.symm a) *
          y ^ f.rootFactor (f.indexEquiv.symm a) := by
      change (d : Γ(Z.left, ⊤)) ^ f.rootFactor (f.indexEquiv.symm a) = _
      rw [hd, add_pow_rootFactor_sections f hchar, one_pow, mul_pow]
    rw [rootPoint_poweredRootFamily, rootPoint_poweredRootFamily_opposite,
      hL.2.2.2 Z _ _ _ hdq, rootPoint_poweredRootFamily_opposite,
      rootPoint_poweredRootFamily, Grp.comp_hom_hom, ← Category.assoc,
      corootPoint_comp_torusMap f hPpair hQpair]
    simp only [mul_pow, ← inv_pow, Units.val_pow_eq_pow_val]

end Langlands.GroupScheme.AffineRootDatumIsogeny

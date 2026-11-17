import Langlands.GroupScheme.Reductive.LocalOppositeRootNormalization

/-! # Rigidity of actual opposite-root restrictions over local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace OppositePower

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {f : G ⟶ H} {xp : Ga R ⟶ G} {yp : Ga R ⟶ H}
  {c : R} {q : ℕ}

/-- Rescaling the source coordinate multiplies its power coefficient by the
corresponding power of the scalar. -/
theorem HasPowerFormula.scaleSource
    (h : HasPowerFormula f xp yp c q) (s : R) :
    HasPowerFormula f (scaleHom s ≫ xp) yp (c * s ^ q) q := by
  intro Z x
  rw [rootPoint_scaleHom, h]
  simp only [map_mul, map_pow, mul_pow, mul_assoc]

/-- Rescaling the target coordinate by a unit divides its power coefficient
by that unit. -/
theorem HasPowerFormula.scaleTarget
    (h : HasPowerFormula f xp yp c q) (t : Rˣ) :
    HasPowerFormula f xp (scaleHom (t : R) ≫ yp) ((↑t⁻¹ : R) * c) q := by
  intro Z x
  rw [h, rootPoint_scaleHom]
  congr 1
  rw [map_mul, ← mul_assoc, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

/-- If separate unit rescalings normalize the two opposite pairs, their
original negative restrictions still agree. -/
theorem opposite_maps_eq_of_normalizations
    {T U : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ G} {j : U.toGrp ⟶ H}
    {xm : Ga R ⟶ G} {ym : Ga R ⟶ H}
    (s t : Rˣ)
    (hs : HasGaussRelation i xp (scaleHom (s : R) ≫ xm))
    (ht : HasGaussRelation j yp (scaleHom (t : R) ≫ ym))
    (hsep : SeparatesPositive j yp (scaleHom (t : R) ≫ ym))
    (F : G ⟶ H) (τ σ : T.toGrp ⟶ U.toGrp)
    (hfT : i ≫ f = τ ≫ j) (hFT : i ≫ F = σ ≫ j)
    (c : Rˣ) (d d' : R) (hq : 0 < q)
    (hp : HasPowerFormula f xp yp (c : R) q)
    (hP : HasPowerFormula F xp yp (c : R) q)
    (hm : HasPowerFormula f xm ym d q)
    (hM : HasPowerFormula F xm ym d' q) :
    xm ≫ f = xm ≫ F := by
  have he := opposite_maps_eq_of_gauss hs ht hsep f F τ σ hfT hFT
    c _ _ hq hp hP ((hm.scaleSource (s : R)).scaleTarget t)
      ((hM.scaleSource (s : R)).scaleTarget t)
  exact (cancel_epi (scaleIso s).hom).1
    (by simpa only [scaleIso, Category.assoc] using he)

end OppositePower

namespace LocalSplitCell

open OppositePower

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I I' : Type u} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {J J' : Type u}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}

/-- For actual opposite roots of reductive groups over any local ring, equal
positive unit power formulas and common positive degrees force equality on the
negative root. The negative coefficients need not be units. -/
theorem opposite_maps_eq_of_powerFormulas
    (hG : IsReductive G) (hH : IsReductive H)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H j Q)
    (a : J) (b : J')
    (xp xm : Ga R ⟶ G) (yp ym : Ga R ⟶ H)
    (hxp : IsRootParametrization i (P.root a) xp)
    (hxm : IsRootParametrization i (-P.root a) xm)
    (hyp : IsRootParametrization j (Q.root b) yp)
    (hym : IsRootParametrization j (-Q.root b) ym)
    (f F : G ⟶ H)
    (τ σ : splitTorus (Spec (CommRingCat.of R)) I ⟶
      splitTorus (Spec (CommRingCat.of R)) I')
    (hfT : i ≫ f = τ ≫ j) (hFT : i ≫ F = σ ≫ j)
    (c : Rˣ) (d d' : R) {q : ℕ} (hq : 0 < q)
    (hp : HasPowerFormula f xp yp (c : R) q)
    (hP' : HasPowerFormula F xp yp (c : R) q)
    (hm : HasPowerFormula f xm ym d q)
    (hM : HasPowerFormula F xm ym d' q) :
    xm ≫ f = xm ≫ F := by
  obtain ⟨s, hs, _, _⟩ :=
    exists_unit_oppositeNormalization hG i hi hmax hP a hxp hxm
  obtain ⟨t, ht, hsep, _⟩ :=
    exists_unit_oppositeNormalization hH j hj hmax' hQ b hyp hym
  exact opposite_maps_eq_of_normalizations s t hs.hasGaussRelation ht.hasGaussRelation
    hsep F τ σ hfT hFT c d d' hq hp hP' hm hM

end LocalSplitCell

open LocalSplitCell OppositePower

/-- The actual opposite-root comparison over arbitrary local rings, with the
power formulas and positive unit coefficient retained as explicit inputs. -/
def LocalOppositeRootRigidityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (I I' : Type u) [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom],
    IsReductive G → IsReductive H →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H),
      IsClosedSubgroup i → IsClosedSubgroup j →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j →
      ∀ (J J' : Type u)
        (P : RootDatum J (I → ℤ) (I → ℤ))
        (Q : RootDatum J' (I' → ℤ) (I' → ℤ)),
        IsFibrewiseRootDatumOf I G i P → IsFibrewiseRootDatumOf I' H j Q →
        ∀ (a : J) (b : J') (xp xm : Ga R ⟶ G) (yp ym : Ga R ⟶ H),
          IsRootParametrization i (P.root a) xp →
          IsRootParametrization i (-P.root a) xm →
          IsRootParametrization j (Q.root b) yp →
          IsRootParametrization j (-Q.root b) ym →
          ∀ (f F : G ⟶ H)
            (τ σ : splitTorus (Spec (CommRingCat.of R)) I ⟶
              splitTorus (Spec (CommRingCat.of R)) I'),
            i ≫ f = τ ≫ j → i ≫ F = σ ≫ j →
            ∀ (c : Rˣ) (d d' : R) (q : ℕ), 0 < q →
              HasPowerFormula f xp yp (c : R) q →
              HasPowerFormula F xp yp (c : R) q →
              HasPowerFormula f xm ym d q →
              HasPowerFormula F xm ym d' q →
              xm ≫ f = xm ≫ F

theorem localOppositeRootRigidity : LocalOppositeRootRigidityStatement.{u} := by
  intro R _ _ I I' _ _ _ _ G H _ _ hG hH i j hi hj hmax hmax'
    J J' P Q hP hQ a b xp xm yp ym hxp hxm hyp hym f F τ σ hfT hFT
    c d d' q hq hp hP' hm hM
  exact opposite_maps_eq_of_powerFormulas hG hH i j hi hj hmax hmax' hP hQ
    a b xp xm yp ym hxp hxm hyp hym f F τ σ hfT hFT c d d' hq hp hP' hm hM

end Langlands.GroupScheme

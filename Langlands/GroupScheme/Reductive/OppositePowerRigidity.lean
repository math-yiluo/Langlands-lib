import Langlands.GroupScheme.Reductive.NaturalPowerRigidity
import Langlands.GroupScheme.Reductive.RankOneRingRelation
import Langlands.GroupScheme.Reductive.LocalSplitRootTransport

/-! # Opposite power coefficients from normalized Gauss relations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.OppositePower

open LocalSplitCell

variable {R : Type u} [CommRing R]

/-- Cancellation of a unit coefficient compares the two denominator units. -/
theorem pow_eq_of_scaled_inverse_eq {A : Type u} [CommRing A]
    (c u v : Aˣ) (q : ℕ)
    (h : (c : A) * (↑u⁻¹ : A) ^ q = (↑v⁻¹ : A) * (c : A)) :
    (u : A) ^ q = (v : A) := by
  have h' : (↑u⁻¹ : A) ^ q = (↑v⁻¹ : A) :=
    c.isUnit.mul_left_cancel (by simpa only [mul_comm (↑v⁻¹ : A) (c : A)] using h)
  have hu : u⁻¹ ^ q = v⁻¹ := Units.ext (by simpa only [Units.val_pow_eq_pow_val] using h')
  have hi := congrArg (fun a : Aˣ => a⁻¹) hu
  simpa only [inv_pow, inv_inv, Units.val_pow_eq_pow_val] using congrArg Units.val hi

/-- A unit-denominator identity on every coefficient algebra determines its
highest coefficient, even when the base has zero divisors. -/
theorem coefficient_eq_one {q : ℕ} (hq : 0 < q) (a : R)
    (h : ∀ (A : CommAlgCat.{u} (CommRingCat.of R)) (x : A) (u v : Aˣ),
      (u : A) = 1 + x →
      (v : A) = 1 + algebraMap R A a * x ^ q →
      (u : A) ^ q = (v : A)) : a = 1 := by
  let B := FractionRing R[X]
  let f : R[X] →+* B := algebraMap R[X] B
  let : Algebra R B := (f.comp Polynomial.C).toAlgebra
  let A : CommAlgCat.{u} (CommRingCat.of R) := CommAlgCat.of R B
  have hC (r : R) : f (Polynomial.C r) = algebraMap R A r := rfl
  have hu : IsUnit (f (1 + Polynomial.X)) := by
    apply IsLocalization.map_units (M := nonZeroDivisors R[X]) B ⟨_, ?_⟩
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
    simp
  have hv : IsUnit (f (1 + Polynomial.C a * Polynomial.X ^ q)) := by
    apply IsLocalization.map_units (M := nonZeroDivisors R[X]) B ⟨_, ?_⟩
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
    simp [hq.ne]
  have he := h A (f Polynomial.X) hu.unit hv.unit
    (by simp only [IsUnit.unit_spec, map_add, map_one])
    (by simp only [IsUnit.unit_spec, map_add, map_one, map_mul, map_pow, hC])
  have hp : (1 + Polynomial.X : R[X]) ^ q =
      1 + Polynomial.C a * Polynomial.X ^ q := by
    apply IsFractionRing.injective R[X] B
    simpa only [IsUnit.unit_spec, map_pow] using he
  have hc := congrArg (fun p : R[X] => p.coeff q) hp
  simpa only [Polynomial.coeff_one_add_X_pow, Nat.choose_self, Nat.cast_one,
    Polynomial.coeff_add, Polynomial.coeff_one, ite_eq_right hq.ne',
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one, zero_add] using hc.symm

variable {G H : GroupScheme (Spec (CommRingCat.of R))}
  {T U : CommGroupScheme (Spec (CommRingCat.of R))}

/-- A normalized opposite-root Gauss relation on every test scheme. The middle
factor is only required to belong to the supplied torus. -/
def HasGaussRelation (i : T.toGrp ⟶ G) (xp xm : Ga R ⟶ G) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤))
    (u : Γ(Z.left, ⊤)ˣ), (u : Γ(Z.left, ⊤)) = 1 + x * y →
    ∃ t : Z ⟶ T.X,
      rootPoint xp Z x * rootPoint xm Z y =
        rootPoint xm Z ((↑u⁻¹ : Γ(Z.left, ⊤)) * y) *
          ((t ≫ i.hom.hom) * rootPoint xp Z ((↑u⁻¹ : Γ(Z.left, ⊤)) * x))

/-- The target opposite-root/torus cell separates its positive coordinate.
No openness assertion for the rank-one cell in an ambient group is imposed. -/
def SeparatesPositive (j : U.toGrp ⟶ H) (yp ym : Ga R ⟶ H) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R))) (y y' x x' : Γ(Z.left, ⊤))
    (t t' : Z ⟶ U.X),
    rootPoint ym Z y * ((t ≫ j.hom.hom) * rootPoint yp Z x) =
      rootPoint ym Z y' * ((t' ≫ j.hom.hom) * rootPoint yp Z x') → x = x'

/-- The restriction of an actual homomorphism is a prescribed power map on all
test schemes, in supplied source and target coordinates. -/
def HasPowerFormula (f : G ⟶ H) (xp : Ga R ⟶ G) (yp : Ga R ⟶ H)
    (c : R) (q : ℕ) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
    rootPoint xp Z x ≫ f.hom.hom =
      rootPoint yp Z (baseScalar Z c * x ^ q)

/-- Comparing the two Gauss decompositions compares their denominator units. -/
theorem denominator_pow_eq_of_gauss
    {i : T.toGrp ⟶ G} {j : U.toGrp ⟶ H}
    {xp xm : Ga R ⟶ G} {yp ym : Ga R ⟶ H}
    (hs : HasGaussRelation i xp xm) (ht : HasGaussRelation j yp ym)
    (hsep : SeparatesPositive j yp ym)
    (f : G ⟶ H) (τ : T.toGrp ⟶ U.toGrp) (htorus : i ≫ f = τ ≫ j)
    (c : Rˣ) (d : R) (q : ℕ)
    (hp : HasPowerFormula f xp yp (c : R) q)
    (hm : HasPowerFormula f xm ym d q)
    (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤))
    (u v : Γ(Z.left, ⊤)ˣ)
    (hu : (u : Γ(Z.left, ⊤)) = 1 + x)
    (hv : (v : Γ(Z.left, ⊤)) =
      1 + baseScalar Z (c : R) * baseScalar Z d * x ^ q) :
    (u : Γ(Z.left, ⊤)) ^ q = (v : Γ(Z.left, ⊤)) := by
  obtain ⟨t, hs'⟩ := hs Z 1 x u (by simpa only [one_mul] using hu)
  obtain ⟨t', ht'⟩ := ht Z (baseScalar Z (c : R))
    (baseScalar Z d * x ^ q) v (by simpa only [mul_assoc] using hv)
  have hf := congrArg (fun a => a ≫ f.hom.hom) hs'
  simp only [MonObj.mul_comp] at hf
  rw [hp, hm, hm, hp] at hf
  have hti : (t ≫ i.hom.hom) ≫ f.hom.hom =
      (t ≫ τ.hom.hom) ≫ j.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, htorus, Grp.comp_hom_hom,
      ← Category.assoc]
  rw [hti] at hf
  simp only [one_pow, mul_one] at hf
  have he := hsep Z _ _ _ _ _ _ (hf.symm.trans ht')
  exact pow_eq_of_scaled_inverse_eq
    (Units.map (baseScalar Z).toMonoidHom c) u v q he

/-- A positive unit coefficient forces the opposite coefficient to be its
inverse. The two normalized relations and target coordinate separation remain
explicit premises. -/
theorem mul_eq_one_of_gauss
    {i : T.toGrp ⟶ G} {j : U.toGrp ⟶ H}
    {xp xm : Ga R ⟶ G} {yp ym : Ga R ⟶ H}
    (hs : HasGaussRelation i xp xm) (ht : HasGaussRelation j yp ym)
    (hsep : SeparatesPositive j yp ym)
    (f : G ⟶ H) (τ : T.toGrp ⟶ U.toGrp) (htorus : i ≫ f = τ ≫ j)
    (c : Rˣ) (d : R) {q : ℕ} (hq : 0 < q)
    (hp : HasPowerFormula f xp yp (c : R) q)
    (hm : HasPowerFormula f xm ym d q) : (c : R) * d = 1 := by
  apply coefficient_eq_one hq
  intro A x u v hu hv
  let Z := Corepresented.RingCoordinates.specOver (CommRingCat.of R) A
  let g : A →+* Γ(Z.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let u' : Γ(Z.left, ⊤)ˣ := Units.map g.toMonoidHom u
  let v' : Γ(Z.left, ⊤)ˣ := Units.map g.toMonoidHom v
  have hbase (r : R) : baseScalar Z r = g (algebraMap R A r) := by
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom (baseScalar Z r) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap R A r))
    rw [gamma_baseScalar, Iso.inv_hom_id_apply]
  have hu' : (u' : Γ(Z.left, ⊤)) = 1 + g x := by
    change g (u : A) = _
    rw [hu, map_add, map_one]
  have hv' : (v' : Γ(Z.left, ⊤)) =
      1 + baseScalar Z (c : R) * baseScalar Z d * (g x) ^ q := by
    change g (v : A) = _
    rw [hv, map_add, map_one, map_mul, map_pow, map_mul, map_mul, ← hbase, ← hbase]
  have he := denominator_pow_eq_of_gauss hs ht hsep f τ htorus c d q
    hp hm Z (g x) u' v' hu' hv'
  have he' : g ((u : A) ^ q) = g (v : A) := by
    change g (u : A) ^ q = g (v : A) at he
    simpa only [map_pow] using he
  exact ((ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1) he'

/-- Under the same normalized data and the same positive power formula, the
opposite restrictions of two actual homomorphisms agree. -/
theorem opposite_maps_eq_of_gauss
    {i : T.toGrp ⟶ G} {j : U.toGrp ⟶ H}
    {xp xm : Ga R ⟶ G} {yp ym : Ga R ⟶ H}
    (hs : HasGaussRelation i xp xm) (ht : HasGaussRelation j yp ym)
    (hsep : SeparatesPositive j yp ym)
    (f F : G ⟶ H) (τ σ : T.toGrp ⟶ U.toGrp)
    (hfT : i ≫ f = τ ≫ j) (hFT : i ≫ F = σ ≫ j)
    (c : Rˣ) (d d' : R) {q : ℕ} (hq : 0 < q)
    (hp : HasPowerFormula f xp yp (c : R) q)
    (hP : HasPowerFormula F xp yp (c : R) q)
    (hm : HasPowerFormula f xm ym d q)
    (hM : HasPowerFormula F xm ym d' q) : xm ≫ f = xm ≫ F := by
  have hd := mul_eq_one_of_gauss hs ht hsep f τ hfT c d hq hp hm
  have hd' := mul_eq_one_of_gauss hs ht hsep F σ hFT c d' hq hP hM
  have hdd : d = d' := c.isUnit.mul_left_cancel (hd.trans hd'.symm)
  apply hom_ext_rootPoint
  intro Z x
  rw [rootPoint_comp, rootPoint_comp, hm, hM, hdd]

end Langlands.GroupScheme.OppositePower

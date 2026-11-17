import Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement
import Langlands.GroupScheme.Reductive.AffineSplitIsogenyTorusMap
import Langlands.GroupScheme.Reductive.LocalSplitCell
import Langlands.GroupScheme.Rational.TorusLinearization.AdditivePolynomials

/-! # Characteristic-power root maps over arbitrary affine bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace AdditiveLinePower

open LocalSplitCell

variable {R : Type u} [CommRing R]

/-- The standard additive coordinate. -/
abbrev coordinate {U : Over (Spec (CommRingCat.of R))} (x : U ⟶ (Ga R).X) :
    Γ(U.left, ⊤) :=
  LocalSplitCell.gaCoord (Z := U) x

theorem coordinate_injective {U : Over (Spec (CommRingCat.of R))} :
    Function.Injective (coordinate (R := R) (U := U)) := by
  intro x y h
  apply VectorGroup.points_ext
  intro j
  rw [Fin.fin_one_eq_zero j]
  exact h

@[simp]
theorem coordinate_scalarPoint (U : Over (Spec (CommRingCat.of R))) (c : Γ(U.left, ⊤)) :
    coordinate (VectorGroup.scalarPoint (CommRingCat.of R) U c) = c :=
  VectorGroup.coordinates_scalarPoint _ _ _ _

@[simp]
theorem coordinate_mul {U : Over (Spec (CommRingCat.of R))} (x y : U ⟶ (Ga R).X) :
    coordinate (x * y) = coordinate x + coordinate y :=
  congrFun (VectorGroup.coordinates_mul x y) 0

@[simp]
theorem coordinate_one (U : Over (Spec (CommRingCat.of R))) :
    coordinate (1 : U ⟶ (Ga R).X) = 0 := by
  exact congrFun (congrArg Multiplicative.toAdd
    (map_one (VectorGroup.coordinates (CommRingCat.of R) 1 U))) 0

/-- The actual scheme map on the additive line with coordinate `X ↦ X^q`. -/
def powerMap (q : ℕ) : (Ga R).X ⟶ (Ga R).X :=
  VectorGroup.scalarPoint (CommRingCat.of R) _ (coordinate (𝟙 (Ga R).X) ^ q)

@[simp]
theorem coordinate_comp_powerMap (q : ℕ) {U : Over (Spec (CommRingCat.of R))}
    (x : U ⟶ (Ga R).X) :
    coordinate (x ≫ powerMap q) = coordinate x ^ q := by
  change (VectorGroup.coordinates _ _ _ _).toAdd 0 = _
  rw [VectorGroup.coordinates_comp]
  change x.left.appTop (coordinate (powerMap q)) = _
  rw [powerMap, coordinate_scalarPoint, map_pow]
  congr 1

@[simp]
theorem scalarPoint_comp_powerMap (q : ℕ) (U : Over (Spec (CommRingCat.of R)))
    (c : Γ(U.left, ⊤)) :
    VectorGroup.scalarPoint (CommRingCat.of R) U c ≫ powerMap q =
      VectorGroup.scalarPoint (CommRingCat.of R) U (c ^ q) := by
  apply coordinate_injective
  simp only [coordinate_comp_powerMap, coordinate_scalarPoint]

/-- An additive positive monomial gives an actual group-scheme homomorphism. -/
def powerHom (q : ℕ) (hq : 0 < q)
    (hadd : ∀ (U : Over (Spec (CommRingCat.of R))) (a b : Γ(U.left, ⊤)),
      (a + b) ^ q = a ^ q + b ^ q) : Ga R ⟶ Ga R :=
  homOfPoints (fun U =>
    { toFun := fun x => x ≫ powerMap q
      map_one' := by
        apply coordinate_injective
        simp only [coordinate_comp_powerMap, coordinate_one, zero_pow hq.ne']
      map_mul' := fun x y => by
        apply coordinate_injective
        simp only [coordinate_comp_powerMap, coordinate_mul]
        exact hadd U _ _ })
    (fun a x => by
      change (a ≫ x) ≫ powerMap q = a ≫ x ≫ powerMap q
      exact Category.assoc _ _ _)

@[simp]
theorem powerHom_hom (q : ℕ) (hq : 0 < q)
    (hadd : ∀ (U : Over (Spec (CommRingCat.of R))) (a b : Γ(U.left, ⊤)),
      (a + b) ^ q = a ^ q + b ^ q) :
    (powerHom q hq hadd).hom.hom = powerMap (R := R) q := by
  have h := comp_homOfPoints
    (fun U =>
      { toFun := fun x => x ≫ powerMap (R := R) q
        map_one' := by
          apply coordinate_injective
          simp only [coordinate_comp_powerMap, coordinate_one, zero_pow hq.ne']
        map_mul' := fun x y => by
          apply coordinate_injective
          simp only [coordinate_comp_powerMap, coordinate_mul]
          exact hadd U _ _ })
    (fun a x => by
      change (a ≫ x) ≫ powerMap q = a ≫ x ≫ powerMap q
      exact Category.assoc _ _ _) (Ga R).X (𝟙 (Ga R).X)
  change (𝟙 (Ga R).X) ≫ (powerHom q hq hadd).hom.hom =
    (𝟙 (Ga R).X) ≫ powerMap q at h
  simpa only [Category.id_comp] using h

end AdditiveLinePower

namespace AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}

/-- Root factors are additive powers over every algebra over the coefficient ring. -/
theorem add_pow_rootFactor (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (j' : J') (A : Type*) [CommRing A] [Algebra R A] (a b : A) :
    (a + b) ^ f.rootFactor j' = a ^ f.rootFactor j' + b ^ f.rootFactor j' := by
  by_cases hq : f.rootFactor j' = 1
  · simp only [hq, pow_one]
  have hp : p.Prime := f.characteristicExponent.resolve_left (by
    intro hp
    obtain ⟨n, hn⟩ := f.rootFactor_pow j'
    exact hq (by simpa only [hp, one_pow] using hn))
  have : Fact p.Prime := ⟨hp⟩
  have hA : (p : A) = 0 := by
    rw [← map_natCast (algebraMap R A), hchar j' hq, map_zero]
  obtain ⟨n, hn⟩ := f.rootFactor_pow j'
  rw [hn]
  exact TorusLinearization.add_pow_prime_pow_of_natCast_eq_zero p hA a b n

/-- The root-factor monomial is additive on all scheme tests, including empty tests. -/
theorem add_pow_rootFactor_sections (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (j' : J') (U : Over (Spec (CommRingCat.of R))) (a b : Γ(U.left, ⊤)) :
    (a + b) ^ f.rootFactor j' = a ^ f.rootFactor j' + b ^ f.rootFactor j' := by
  let : Algebra R Γ(U.left, ⊤) := ((algΓ (CommRingCat.of R)).obj U).unop.algebra
  exact add_pow_rootFactor f hchar j' _ a b

/-- The actual additive-group homomorphism with exponent given by one root factor. -/
def rootPower (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0) (j' : J') :
    Ga R ⟶ Ga R :=
  AdditiveLinePower.powerHom (f.rootFactor j') (f.rootFactor_pos j')
    (add_pow_rootFactor_sections f hchar j')

@[simp]
theorem rootPower_hom (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0) (j' : J') :
    (rootPower f hchar j').hom.hom =
      AdditiveLinePower.powerMap (R := R) (f.rootFactor j') :=
  AdditiveLinePower.powerHom_hom _ _ _

/-- The additive root map obtained from a target root parametrization. -/
def rootMap {H : GroupScheme (Spec (CommRingCat.of R))}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0) (j' : J')
    (u' : Ga R ⟶ H) : Ga R ⟶ H :=
  rootPower f hchar j' ≫ u'

/-- Evaluation of the root map is the prescribed characteristic-power formula. -/
theorem rootPoint_rootMap {H : GroupScheme (Spec (CommRingCat.of R))}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0) (j' : J')
    (u' : Ga R ⟶ H) (U : Over (Spec (CommRingCat.of R))) (c : Γ(U.left, ⊤)) :
    rootPoint (rootMap f hchar j' u') U c =
      rootPoint u' U (c ^ f.rootFactor j') := by
  rw [rootPoint, rootMap, Grp.comp_hom_hom, ← Category.assoc, rootPower_hom,
    AdditiveLinePower.scalarPoint_comp_powerMap, rootPoint]

/-- The root equation is an equality of actual characters over any scheme. -/
theorem root_character (S : Scheme.{u})
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P) (j' : J') :
    Additive.ofMul (torusMap S f) ≫ splitTorus.exponentCharacter S I' (Q.root j') =
      (f.rootFactor j' : ℤ) •
        splitTorus.exponentCharacter S I (P.root (f.indexEquiv j')) := by
  classical
  change splitTorus.exponentHom S I I' f.weightMap ≫
    splitTorus.exponentCharacter S I' (Q.root j') = _
  rw [splitTorus.exponentHom_comp_exponentCharacter, f.root_weightMap]
  exact (splitTorus.exponentCharacterLinear S I).map_smul _ _

/-- The pullback of a target root character evaluates to the powered source character. -/
theorem root_charValue (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (j' : J') (U : Over (Spec (CommRingCat.of R)))
    (t : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    VectorGroup.charValue (splitTorus.exponentCharacter _ I' (Q.root j')) U
        (t ≫ (torusMap _ f).hom.hom) =
      VectorGroup.charValue
        (splitTorus.exponentCharacter _ I (P.root (f.indexEquiv j'))) U t ^
          f.rootFactor j' := by
  classical
  have hχ := root_character (Spec (CommRingCat.of R)) f j'
  change splitTorus.exponentHom _ I I' f.weightMap ≫
    splitTorus.exponentCharacter _ I' (Q.root j') = _ at hχ
  rw [torusMap, VectorGroup.charValue,
    ← comp_groupHom_comp t (splitTorus.exponentHom _ I I' f.weightMap)
      (splitTorus.exponentCharacter _ I' (Q.root j')), hχ,
    VectorGroup.charValue,
    comp_groupHom_zsmul t (f.rootFactor j' : ℤ)
      (splitTorus.exponentCharacter _ I (P.root (f.indexEquiv j'))),
    map_zpow, zpow_natCast,
    Units.val_pow_eq_pow_val]

/-- The powered target root map intertwines the source torus action prescribed by `f`. -/
theorem rootMap_equivariant {H : GroupScheme (Spec (CommRingCat.of R))}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0) (j' : J')
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H) (u' : Ga R ⟶ H)
    (hu' : IsRootParametrization i' (Q.root j') u')
    (U : Over (Spec (CommRingCat.of R)))
    (t : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(U.left, ⊤)) :
    (t ≫ (torusMap _ f ≫ i').hom.hom) * rootPoint (rootMap f hchar j' u') U c *
        (t ≫ (torusMap _ f ≫ i').hom.hom)⁻¹ =
      rootPoint (rootMap f hchar j' u') U
        (VectorGroup.charValue
          (splitTorus.exponentCharacter _ I (P.root (f.indexEquiv j'))) U t * c) := by
  simp only [rootPoint_rootMap, Grp.comp_hom_hom, ← Category.assoc]
  rw [hu'.equivariant, root_charValue, mul_pow]

end AffineRootDatumIsogeny

end Langlands.GroupScheme

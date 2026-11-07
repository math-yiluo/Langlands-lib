import Langlands.Geometry.Building.RootUnitaryCoordinateCompatibility
import Langlands.GroupScheme.Rational.RootHeisenbergEquivariant
import Langlands.GroupScheme.Examples.SU3RootHeisenbergComparison

/-! # Quadratic unitary coordinates from a Heisenberg normal form with field data

A torus-equivariant Heisenberg normal form of a multipliable root group, for the centralizer
acting by conjugation, together with rational field coordinates on the quotient and on the
doubled root group, gives quadratic unitary coordinates. The field coordinates must turn the
cocycle into a trace-compatible, non-symmetric function and the centralizer action into
scaling by a character.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z U U₂ : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {jZ : Z ⟶ G} {a : characterLattice S}
  {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
  {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}

/-- Points of the root group killed by the quotient map commute with all points of the root
group. -/
theorem commute_of_comp_q
    (C : DoubleRootCommutatorPairing i a hj hj₂) {T : Over (Spec (CommRingCat.of k))}
    (g h : T ⟶ U.X) (hh : h ≫ C.q.hom.hom = 1) : Commute g h := by
  let : Mono j.hom.hom := hj.1
  have h1 : lift (g ≫ C.q.hom.hom) (1 : T ⟶ C.V.X) ≫ C.pairing = 1 := by
    have h2 := C.lift_pairing_mul T (g ≫ C.q.hom.hom) 1 1
    rw [mul_one] at h2
    exact mul_left_cancel (h2.symm.trans (mul_one _).symm)
  have hp := C.lift_pairing T g h
  rw [hh, h1, MonObj.one_comp] at hp
  have hc : (g * h) ≫ j.hom.hom = (h * g) ≫ j.hom.hom := by
    rw [MonObj.mul_comp, MonObj.mul_comp]
    have h3 := hp.symm
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  exact (cancel_mono j.hom.hom).1 hc

/-- **Field data for a Heisenberg normal form.** Rational coordinates of the quotient `V(k)` by a
separable quadratic extension `extension / base` and of `U_{2a}(k)` by its trace-zero
elements. In them the cocycle is a function `form`, additive in its second argument, trace
compatible and not symmetric. A character of `Z_extension` restricting to `a` scales the
first coordinate, and its norm the second, under the action of `Z(k)`. -/
structure HeisenbergUnitaryData (C : DoubleRootCommutatorPairing i a hj hj₂)
    {hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ Z.X) (t : T ⟶ S.X),
      (AutomorphicAction.conjugation jZ).act z (t ≫ i.hom.hom) = t ≫ i.hom.hom}
    (N : EquivariantHeisenbergNormalForm C (AutomorphicAction.conjugation jZ) hfix)
    (s : S.toGrp ⟶ Z) where
  /-- The field over which the quadratic unitary group is defined. -/
  base : Type u
  /-- The separable quadratic extension of `base` carrying the coordinates. -/
  extension : Type u
  [baseField : Field base]
  [field : Field extension]
  [baseAlgebra : Algebra k base]
  [quadraticAlgebra : Algebra base extension]
  [algebra : Algebra k extension]
  [scalarTower : IsScalarTower k base extension]
  [quadratic : Algebra.IsQuadraticExtension base extension]
  [quadraticSeparable : Algebra.IsSeparable base extension]
  [finite : FiniteDimensional k extension]
  [separable : Algebra.IsSeparable k extension]
  /-- Coordinates of the rational points of the quotient. -/
  first : Multiplicative extension ≃* rationalPoints C.V
  /-- Coordinates of the rational points of the doubled root group. -/
  second : Multiplicative (SU3Root.Parameters.traceZero (SU3Root.fieldInvolution base extension)) ≃*
    rationalPoints U₂
  /-- The cocycle in these coordinates. -/
  form : extension → extension → extension
  cocycle_eq : ∀ x y : extension,
    (Multiplicative.toAdd
      (second.symm (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫
        N.cocycle))).1 = form x y
  form_add : ∀ x y y' : extension, form x (y + y') = form x y + form x y'
  form_trace : ∀ f x y : extension,
    form (f * x) y + form x (f * y) = (f + SU3Root.conjugation base extension f) * form x y
  form_nonsymm : ∃ x y : extension, form x y ≠ form y x
  /-- The character of `Z_extension` through which the centralizer scales the coordinates. -/
  character : rationalCharacters (GaloisPointComparison.baseChanged k extension Z)
  restriction :
    characterRestrict ((GroupScheme.baseChange (GaloisPointComparison.baseMap k extension)).map s)
        character =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k extension)
        ((rationalCharacters.equivCharacterLattice S).symm a)
  first_act : ∀ (z : rationalPoints Z) (x : extension),
    (C.torusQuotientAction (AutomorphicAction.conjugation jZ) hfix).act z
        (first (Multiplicative.ofAdd x)) =
      first (Multiplicative.ofAdd ((rationalCharacterEval character
        (GaloisPointComparison.rationalExtend k extension Z z) : extension) * x))
  second_act : ∀ (z : rationalPoints Z)
    (w w' : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution base extension)),
    (w' : extension) = (rationalCharacterEval character
        (GaloisPointComparison.rationalExtend k extension Z z) : extension) *
      SU3Root.conjugation base extension (rationalCharacterEval character
        (GaloisPointComparison.rationalExtend k extension Z z) : extension) * w →
    (rootActionOfFixesTorus (AutomorphicAction.conjugation jZ) i hfix (2 • a) j₂ hj₂).act z
        (second (Multiplicative.ofAdd w)) =
      second (Multiplicative.ofAdd w')

attribute [instance] HeisenbergUnitaryData.baseField HeisenbergUnitaryData.field
  HeisenbergUnitaryData.baseAlgebra HeisenbergUnitaryData.quadraticAlgebra
  HeisenbergUnitaryData.algebra HeisenbergUnitaryData.scalarTower
  HeisenbergUnitaryData.quadratic HeisenbergUnitaryData.quadraticSeparable
  HeisenbergUnitaryData.finite HeisenbergUnitaryData.separable

namespace HeisenbergUnitaryData

variable {C : DoubleRootCommutatorPairing i a hj hj₂}
  {hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ Z.X) (t : T ⟶ S.X),
    (AutomorphicAction.conjugation jZ).act z (t ≫ i.hom.hom) = t ≫ i.hom.hom}
  {N : EquivariantHeisenbergNormalForm C (AutomorphicAction.conjugation jZ) hfix}
  {s : S.toGrp ⟶ Z} (R : HeisenbergUnitaryData C N s)

/-- The cocycle in coordinates has trace-zero values. -/
theorem form_traceZero (x y : R.extension) :
    R.form x y + SU3Root.conjugation R.base R.extension (R.form x y) = 0 := by
  rw [← R.cocycle_eq]
  exact (Multiplicative.toAdd (R.second.symm (lift (R.first (Multiplicative.ofAdd x))
    (R.first (Multiplicative.ofAdd y)) ≫ N.cocycle))).property

theorem exists_normalizedCocycle : ∃ A : R.extension,
    A + SU3Root.conjugation R.base R.extension A ≠ 0 ∧
      ∀ x y, R.form x y = SU3Root.normalizedCocycle R.base R.extension A x y :=
  SU3Root.exists_eq_normalizedCocycle R.base R.extension R.form R.form_add R.form_trace
    R.form_traceZero R.form_nonsymm

/-- The coefficient of the normalized cocycle. -/
def coefficient : R.extension := Classical.choose R.exists_normalizedCocycle

theorem coefficient_ne_zero :
    R.coefficient + SU3Root.conjugation R.base R.extension R.coefficient ≠ 0 :=
  (Classical.choose_spec R.exists_normalizedCocycle).1

theorem form_eq (x y : R.extension) :
    R.form x y = SU3Root.normalizedCocycle R.base R.extension R.coefficient x y :=
  (Classical.choose_spec R.exists_normalizedCocycle).2 x y

/-- The root-group point with Heisenberg coordinates `(w, x)`. -/
def point (w : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension))
    (x : R.extension) : rationalPoints U :=
  (R.second (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
    (R.first (Multiplicative.ofAdd x) ≫ N.sec)

omit R in
theorem inclusion_comp_q (M : HeisenbergNormalForm C) {T : Over (Spec (CommRingCat.of k))}
    (w : T ⟶ U₂.X) : (w ≫ M.inclusion.hom.hom) ≫ C.q.hom.hom = 1 := by
  have hw : w ≫ M.inclusion.hom.hom ∈
      (SubgroupFunctor.range (kernelι C.q)).carrier T := by
    rw [← M.range_inclusion]
    exact SubgroupFunctor.mem_range.2 ⟨w, rfl⟩
  exact (mem_range_kernelι_iff C.q _).1 hw

theorem point_comp_q (w : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension))
    (x : R.extension) :
    R.point w x ≫ C.q.hom.hom = R.first (Multiplicative.ofAdd x) := by
  rw [point, MonObj.mul_comp, inclusion_comp_q N.toHeisenbergNormalForm, Category.assoc, N.sec_comp,
    Category.comp_id, one_mul]

/-- The Heisenberg law of the points. -/
theorem point_mul (w w' : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension))
    (x x' : R.extension) :
    R.point w x * R.point w' x' =
      R.point (w + w' + SU3Root.normalizedCocycle R.base R.extension R.coefficient x x')
        (x + x') := by
  have hcomm : Commute (R.first (Multiplicative.ofAdd x) ≫ N.sec)
      (R.second (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom) :=
    commute_of_comp_q C _ _ (inclusion_comp_q N.toHeisenbergNormalForm _)
  have hsec := N.sec_mul _ (R.first (Multiplicative.ofAdd x)) (R.first (Multiplicative.ofAdd x'))
  have hβ : lift (R.first (Multiplicative.ofAdd x)) (R.first (Multiplicative.ofAdd x')) ≫
      N.cocycle = R.second (Multiplicative.ofAdd
        (SU3Root.normalizedCocycle R.base R.extension R.coefficient x x')) := by
    apply R.second.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [R.cocycle_eq, R.form_eq]
    rfl
  simp only [point, ofAdd_add, map_mul, MonObj.mul_comp]
  rw [hβ] at hsec
  calc (R.second (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
        (R.first (Multiplicative.ofAdd x) ≫ N.sec) *
        ((R.second (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom) *
          (R.first (Multiplicative.ofAdd x') ≫ N.sec))
      = (R.second (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
          ((R.first (Multiplicative.ofAdd x) ≫ N.sec) *
            (R.second (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom)) *
          (R.first (Multiplicative.ofAdd x') ≫ N.sec) := by group
    _ = (R.second (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
          ((R.second (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom) *
            (R.first (Multiplicative.ofAdd x) ≫ N.sec)) *
          (R.first (Multiplicative.ofAdd x') ≫ N.sec) := by rw [hcomm.eq]
    _ = (R.second (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom) *
          (R.second (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom) *
          ((R.first (Multiplicative.ofAdd x) ≫ N.sec) *
            (R.first (Multiplicative.ofAdd x') ≫ N.sec)) := by group
    _ = _ := by rw [hsec]; group

/-- The Heisenberg bijection of the normalized cocycle. -/
abbrev heisenberg : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension) ×
    R.extension ≃ SU3Root.rationalParameters R.base R.extension :=
  SU3Root.heisenbergEquiv R.coefficient_ne_zero

theorem heisenberg_zero : R.heisenberg (0, 0) = 1 := by
  apply SU3Root.Parameters.ext
  · rfl
  · change -(R.coefficient + SU3Root.conjugation R.base R.extension R.coefficient)⁻¹ *
        ((0 : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension)) :
          R.extension) +
      R.coefficient * (R.coefficient + SU3Root.conjugation R.base R.extension R.coefficient)⁻¹ *
        0 * SU3Root.conjugation R.base R.extension 0 = 0
    simp

/-- The root-group point of a quadratic root parameter. -/
def toPoints : SU3Root.rationalParameters R.base R.extension →* rationalPoints U where
  toFun p := R.point (R.heisenberg.symm p).1 (R.heisenberg.symm p).2
  map_one' := by
    rw [← R.heisenberg_zero, Equiv.symm_apply_apply]
    simp only [point, ofAdd_zero, map_one, MonObj.one_comp, N.one_sec, mul_one]
  map_mul' p p' := by
    obtain ⟨⟨w, x⟩, rfl⟩ := R.heisenberg.surjective p
    obtain ⟨⟨w', x'⟩, rfl⟩ := R.heisenberg.surjective p'
    have hmul : R.heisenberg (w, x) * R.heisenberg (w', x') =
        R.heisenberg (w + w' + SU3Root.normalizedCocycle R.base R.extension R.coefficient x x',
          x + x') := by
      simp only [heisenberg, SU3Root.heisenbergEquiv_apply]
      exact SU3Root.heisenbergParameter_mul R.coefficient_ne_zero w w' x x'
    simp only [hmul, Equiv.symm_apply_apply]
    exact (R.point_mul w w' x x').symm

theorem toPoints_heisenberg
    (w : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension))
    (x : R.extension) : R.toPoints (R.heisenberg (w, x)) = R.point w x := by
  change R.point (R.heisenberg.symm (R.heisenberg (w, x))).1
    (R.heisenberg.symm (R.heisenberg (w, x))).2 = _
  rw [Equiv.symm_apply_apply]

theorem point_injective
    {w w' : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension)}
    {x x' : R.extension} (h : R.point w x = R.point w' x') : w = w' ∧ x = x' := by
  have hx : x = x' := by
    have h1 := congrArg (· ≫ C.q.hom.hom) h
    simp only [R.point_comp_q] at h1
    exact Multiplicative.ofAdd.injective (R.first.injective h1)
  subst hx
  refine ⟨?_, rfl⟩
  have h2 : R.second (Multiplicative.ofAdd w) ≫ N.inclusion.hom.hom =
      R.second (Multiplicative.ofAdd w') ≫ N.inclusion.hom.hom := mul_right_cancel h
  let := N.mono_inclusion
  exact Multiplicative.ofAdd.injective (R.second.injective ((cancel_mono _).1 h2))

theorem toPoints_bijective : Function.Bijective R.toPoints := by
  constructor
  · intro p p' h
    obtain ⟨⟨w, x⟩, rfl⟩ := R.heisenberg.surjective p
    obtain ⟨⟨w', x'⟩, rfl⟩ := R.heisenberg.surjective p'
    rw [R.toPoints_heisenberg, R.toPoints_heisenberg] at h
    obtain ⟨hw, hx⟩ := R.point_injective h
    rw [hw, hx]
  · intro g
    obtain ⟨w₀, hw₀⟩ := N.exists_eq_mul_sec g
    refine ⟨R.heisenberg (Multiplicative.toAdd (R.second.symm w₀),
      Multiplicative.toAdd (R.first.symm (g ≫ C.q.hom.hom))), ?_⟩
    rw [R.toPoints_heisenberg]
    simp only [point, ofAdd_toAdd, MulEquiv.apply_symm_apply]
    exact hw₀.symm

/-- The parametrization of the rational root group. -/
def equiv : SU3Root.rationalParameters R.base R.extension ≃* rootGroupPoints i a :=
  (MulEquiv.ofBijective R.toPoints R.toPoints_bijective).trans (hj.pointsEquiv _)

theorem equiv_coe (p : SU3Root.rationalParameters R.base R.extension) :
    (R.equiv p : rationalPoints G) = R.toPoints p ≫ j.hom.hom :=
  hj.pointsEquiv_apply_coe _

theorem point_zero_comp
    (w : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension)) :
    R.point w 0 ≫ j.hom.hom = R.second (Multiplicative.ofAdd w) ≫ j₂.hom.hom := by
  simp only [point, ofAdd_zero, map_one, N.one_sec, mul_one, Category.assoc,
    N.inclusion_comp_hom]

/-- The zero-first-coordinate parameters are exactly the points of `U_{2a}(k)`. -/
theorem double (g : rationalPoints G) : g ∈ rootGroupPoints i (2 • a) ↔
    ∃ p ∈ SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension),
      (R.equiv p : rationalPoints G) = g := by
  constructor
  · intro hg
    obtain ⟨w₀, hw₀⟩ := (hj₂.pointsEquiv _).surjective ⟨g, hg⟩
    refine ⟨R.heisenberg (Multiplicative.toAdd (R.second.symm w₀), 0),
      (SU3Root.Parameters.mem_central _).2 rfl, ?_⟩
    rw [R.equiv_coe, R.toPoints_heisenberg, R.point_zero_comp, ofAdd_toAdd,
      MulEquiv.apply_symm_apply]
    have h1 := congrArg Subtype.val hw₀
    rwa [hj₂.pointsEquiv_apply_coe] at h1
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨⟨w, x⟩, rfl⟩ := R.heisenberg.surjective p
    have hx : x = 0 := hp
    subst hx
    rw [R.equiv_coe, R.toPoints_heisenberg, R.point_zero_comp]
    have h1 := (hj₂.pointsEquiv _ (R.second (Multiplicative.ofAdd w))).property
    rwa [hj₂.pointsEquiv_apply_coe] at h1

/-- The scaling value of a rational centralizer point. -/
abbrev scaleValue (z : rationalPoints Z) : R.extension :=
  (rationalCharacterEval R.character (GaloisPointComparison.rationalExtend k R.extension Z z) :
    R.extension)

theorem scale_mem_traceZero (c : R.extension)
    (w : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension)) :
    c * SU3Root.conjugation R.base R.extension c * (w : R.extension) ∈
      SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension) := by
  have hw : (w : R.extension) + SU3Root.conjugation R.base R.extension w = 0 := w.property
  rw [SU3Root.Parameters.mem_traceZero, SU3Root.fieldInvolution_bar, map_mul, map_mul,
    SU3Root.conjugation_involutive R.base R.extension c]
  linear_combination (c * SU3Root.conjugation R.base R.extension c) * hw

/-- The whole centralizer scales the parameters through the character. -/
theorem conjugation (z : rationalPoints Z) (p : SU3Root.rationalParameters R.base R.extension) :
    rationalPoints.map jZ z * (R.equiv p : rationalPoints G) * (rationalPoints.map jZ z)⁻¹ =
      (R.equiv (SU3Root.Parameters.scale (R.scaleValue z) p) : rationalPoints G) := by
  obtain ⟨⟨w, x⟩, rfl⟩ := R.heisenberg.surjective p
  let w' : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension) :=
    ⟨_, R.scale_mem_traceZero (R.scaleValue z) w⟩
  have hscale : SU3Root.Parameters.scale (R.scaleValue z) (R.heisenberg (w, x)) =
      R.heisenberg (w', R.scaleValue z * x) :=
    (SU3Root.heisenbergParameter_scale R.coefficient_ne_zero (R.scaleValue z) w w' x rfl).symm
  rw [hscale, R.equiv_coe, R.equiv_coe, R.toPoints_heisenberg, R.toPoints_heisenberg,
    rationalPoints.map_apply, ← AutomorphicAction.conjugation_act,
    ← rootActionOfFixesTorus_act_comp (AutomorphicAction.conjugation jZ) i hfix a j hj]
  congr 1
  rw [point, point, AutomorphicAction.act_mul_right, N.act_inclusion_torus, N.act_sec_torus,
    R.second_act z w w' rfl, R.first_act]

/-- **Quadratic unitary coordinates** from a torus-equivariant Heisenberg normal form with
field data. -/
def rootUnitaryCoordinates : RootUnitaryCoordinates i jZ s a where
  base := R.base
  extension := R.extension
  equiv := R.equiv
  double := R.double
  character := R.character
  restriction := R.restriction
  conjugation := R.conjugation

end HeisenbergUnitaryData

end Langlands.Geometry.Building

import Langlands.GroupScheme.Dynamic.OrbitOpenLift
import Langlands.GroupScheme.SchemeAction

/-! # Limits of multiplicative-group orbits in a scheme with an action -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {S : Scheme.{u}} {X : Over S} (b : SchemeAction (Gm S).toGrp X)

/-- The orbit map `t ↦ t • x` of a point `x : T ⟶ X` under a multiplicative-group action,
as the morphism `T ×_S 𝔾_{m,S} ⟶ X`. -/
def gmOrbit {T : Over S} (x : T ⟶ X) : T ⊗ (Gm S).X ⟶ X :=
  b.act (snd T (Gm S).X) (fst T (Gm S).X ≫ x)

/-- Orbit maps are natural in the test scheme. -/
theorem whiskerRight_gmOrbit {T T' : Over S} (c : T' ⟶ T) (x : T ⟶ X) :
    c ▷ (Gm S).X ≫ b.gmOrbit x = b.gmOrbit (c ≫ x) := by
  simp only [gmOrbit, b.naturality, whiskerRight_snd, whiskerRight_fst_assoc]

/-- `e : T ×_S 𝔸¹_S ⟶ X` extends the orbit map of `x` along `T ×_S 𝔾_{m,S} ⊆ T ×_S 𝔸¹_S`. -/
def IsGmOrbitExtension {T : Over S} (x : T ⟶ X) (e : T ⊗ AffineLine.scheme S ⟶ X) : Prop :=
  T ◁ AffineLine.unitInclusion S ≫ e = b.gmOrbit x

/-- Restricting an extension along a test morphism extends the restricted orbit. -/
theorem IsGmOrbitExtension.whiskerRight {T T' : Over S} (c : T' ⟶ T) {x : T ⟶ X}
    {e : T ⊗ AffineLine.scheme S ⟶ X} (he : b.IsGmOrbitExtension x e) :
    b.IsGmOrbitExtension (c ≫ x) (c ▷ AffineLine.scheme S ≫ e) := by
  rw [IsGmOrbitExtension, whisker_exchange_assoc, he, whiskerRight_gmOrbit]

/-- An extension restricts to the original point at the unit section. -/
theorem IsGmOrbitExtension.eval_one {T : Over S} {x : T ⟶ X}
    {e : T ⊗ AffineLine.scheme S ⟶ X} (he : b.IsGmOrbitExtension x e) :
    lift (𝟙 T) (toUnit T ≫ η[(Gm S).X]) ≫ T ◁ AffineLine.unitInclusion S ≫ e = x := by
  rw [he, gmOrbit, b.naturality, lift_snd, lift_fst_assoc, Category.id_comp]
  exact b.act_one x

variable [IsSeparated X.hom]

/-- For a separated target, an orbit map has at most one extension. -/
theorem IsGmOrbitExtension.unique {T : Over S} {x : T ⟶ X}
    {e e' : T ⊗ AffineLine.scheme S ⟶ X} (he : b.IsGmOrbitExtension x e)
    (he' : b.IsGmOrbitExtension x e') : e = e' :=
  AffineLine.hom_ext_of_unitInclusion (he.trans he'.symm)

/-- Equivariance of an orbit extension: `e(t, s x) = s • e(t, x)`. The two morphisms on
`(T ×_S 𝔾_{m,S}) ×_S 𝔸¹_S` agree on `(T ×_S 𝔾_{m,S}) ×_S 𝔾_{m,S}`, hence everywhere. -/
theorem IsGmOrbitExtension.scale {T : Over S} {x : T ⟶ X}
    {e : T ⊗ AffineLine.scheme S ⟶ X} (he : b.IsGmOrbitExtension x e) :
    b.act (fst _ _ ≫ snd T (Gm S).X) (fst T (Gm S).X ▷ AffineLine.scheme S ≫ e) =
      AffineLine.scale T ≫ e := by
  apply AffineLine.hom_ext_of_unitInclusion
  rw [AffineLine.whiskerLeft_unitInclusion_scale_assoc, he, b.naturality,
    whisker_exchange_assoc, he, b.whiskerRight_gmOrbit]
  simp only [gmOrbit, b.naturality, whiskerLeft_fst_assoc, lift_fst_assoc, lift_snd,
    b.act_mul, Category.assoc]

/-- The zero value of an orbit extension is fixed by the action on all refinements. -/
theorem IsGmOrbitExtension.isFixed_evalZero {T : Over S} {x : T ⟶ X}
    {e : T ⊗ AffineLine.scheme S ⟶ X} (he : b.IsGmOrbitExtension x e) :
    b.IsFixed (Dynamic.evalZero e) := by
  rw [b.isFixed_iff_universal]
  have h0 := congrArg Dynamic.evalZero (he.scale b)
  have hl : Dynamic.evalZero
      (b.act (fst _ _ ≫ snd T (Gm S).X) (fst T (Gm S).X ▷ AffineLine.scheme S ≫ e)) =
      b.act (snd T (Gm S).X) (fst T (Gm S).X ≫ Dynamic.evalZero e) := by
    rw [← Dynamic.evalZero_whiskerRight]
    unfold Dynamic.evalZero
    rw [b.naturality, lift_fst_assoc, Category.id_comp]
  rw [hl] at h0
  refine h0.trans ?_
  rw [Dynamic.evalZero, ← Category.assoc, AffineLine.lift_zeroSection_scale, Category.assoc]
  rfl

/-- Equivariance evaluated on arbitrary test points. -/
theorem IsGmOrbitExtension.eval_scale {T Q : Over S} {x : T ⟶ X}
    {e : T ⊗ AffineLine.scheme S ⟶ X} (he : b.IsGmOrbitExtension x e)
    (c : Q ⟶ T) (a : Q ⟶ (Gm S).X) (v : Γ(Q.left, ⊤)) :
    b.act a (lift c ((AffineLine.homEquiv Q).symm v) ≫ e) =
      lift c ((AffineLine.homEquiv Q).symm ((Gm.pointsEquiv S Q a : Γ(Q.left, ⊤)) * v)) ≫ e := by
  have h := congrArg
    (fun w => lift (lift c a) ((AffineLine.homEquiv Q).symm v) ≫ w) (he.scale b)
  simpa only [b.naturality, Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_snd,
    lift_whiskerRight_assoc, lift_fst, AffineLine.lift_comp_scale_assoc] using h

/-- Stability of a subscheme `j : U ⟶ X` under the action, on every scheme over the base. -/
def IsGmStable {U : Over S} (j : U ⟶ X) : Prop :=
  ∀ (Q : Over S) (a : Q ⟶ (Gm S).X) (z : Q ⟶ U), ∃ z' : Q ⟶ U, z' ≫ j = b.act a (z ≫ j)

omit [IsSeparated X.hom] in
/-- Stability in both scalar directions preserves factorization through the subscheme. -/
theorem IsGmStable.factors_iff {U Q : Over S} {j : U ⟶ X} (hj : b.IsGmStable j)
    (a : Q ⟶ (Gm S).X) (y : Q ⟶ X) :
    (∃ z : Q ⟶ U, z ≫ j = b.act a y) ↔ ∃ z : Q ⟶ U, z ≫ j = y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨z', hz'⟩ := hj Q a⁻¹ z
    refine ⟨z', ?_⟩
    rw [hz', hz, ← b.act_mul, inv_mul_cancel, b.act_one]
  · rintro ⟨z, rfl⟩
    exact hj Q a z

section Field

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (b : SchemeAction (Gm (Spec (CommRingCat.of k))).toGrp X) [IsSeparated X.hom]

/-- At field-valued coordinates, scaling the parameter moves the orbit extension by the
action. -/
theorem IsGmOrbitExtension.fieldEvaluation_scale {K : Type u} [Field K]
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X}
    {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ X}
    (he : b.IsGmOrbitExtension x e) (f : k →+* K) (v : K) (a : Kˣ) :
    b.act (AffineLine.fieldUnit f a)
        (AffineLine.fieldEvaluation f v ≫
          AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e) =
      AffineLine.fieldEvaluation f ((a : K) * v) ≫
        AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e := by
  simpa only [AffineLine.fieldEvaluation_comp_polynomialPoint_assoc,
    AffineLine.pointsEquiv_fieldUnit, map_mul] using
    he.eval_scale b (AffineLine.fieldBase f) (AffineLine.fieldUnit f a)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv v)

/-- Pulling back a stable open along an orbit extension gives an all-field
scalar-invariant open subset of the polynomial affine line. -/
theorem IsGmOrbitExtension.isScalarInvariantOpen
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X}
    {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ X}
    (he : b.IsGmOrbitExtension x e)
    {U : Over (Spec (CommRingCat.of k))} (j : U ⟶ X)
    [IsOpenImmersion j.left] (hj : b.IsGmStable j) :
    AffineLine.IsScalarInvariantOpen
      ((AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e).left ⁻¹ᵁ
        j.left.opensRange) := by
  intro K _ f v a
  change (AffineLine.fieldEvaluation f ((a : K) * v) ≫
      AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e).left
        (⊥ : PrimeSpectrum K) ∈ j.left.opensRange ↔
    (AffineLine.fieldEvaluation f v ≫
      AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e).left
        (⊥ : PrimeSpectrum K) ∈ j.left.opensRange
  rw [AffineLine.fieldTest_mem_opensRange_iff, AffineLine.fieldTest_mem_opensRange_iff,
    ← he.fieldEvaluation_scale b f v a]
  exact hj.factors_iff b _ _

variable {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X}
  {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
    AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ X}
  {U : Over (Spec (CommRingCat.of k))} (j : U ⟶ X)
  [IsOpenImmersion j.left] (hj : b.IsGmStable j)
  (he : b.IsGmOrbitExtension x e)
  (h0 : (Dynamic.evalZero e).left (⊥ : PrimeSpectrum k) ∈ j.left.opensRange)

/-- Lift the polynomial presentation of an orbit extension into its stable open. -/
def polynomialGmOrbitOpenLift :
    AffineLine.polynomialScheme (𝟙 (Spec (CommRingCat.of k))) ⟶ U :=
  Over.homMk
    (AffineLine.invariantOpenLift j.left
      (AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e).left
      (he.isScalarInvariantOpen b j hj)
      (by rw [AffineLine.polynomialPoint_eval_zero]; exact h0))
    (by
      rw [← Over.w j, ← Category.assoc, AffineLine.invariantOpenLift_fac, Over.w])

@[reassoc]
theorem polynomialGmOrbitOpenLift_fac :
    polynomialGmOrbitOpenLift b j hj he h0 ≫ j =
      AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e :=
  Over.OverMorphism.ext (AffineLine.invariantOpenLift_fac _ _
    (he.isScalarInvariantOpen b j hj)
    (by rw [AffineLine.polynomialPoint_eval_zero]; exact h0))

/-- An orbit extension whose zero value lies in a stable open factors through that open. -/
def gmOrbitOpenLift :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ U :=
  AffineLine.polynomialPointInv (𝟙 (Spec (CommRingCat.of k))) ≫
    polynomialGmOrbitOpenLift b j hj he h0

@[reassoc]
theorem gmOrbitOpenLift_fac :
    gmOrbitOpenLift b j hj he h0 ≫ j = e := by
  rw [gmOrbitOpenLift, Category.assoc, polynomialGmOrbitOpenLift_fac,
    ← Category.assoc, AffineLine.polynomialPointInv_comp_polynomialPoint,
    Category.id_comp]

end Field

end Langlands.GroupScheme.SchemeAction

import Langlands.GroupScheme.Cartier.RelativeHomFunctoriality
import Langlands.GroupScheme.Cartier.Characters
import Langlands.GroupScheme.Torus.RelativeDiagonalizableHomLocality
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof

/-! # Characters of a diagonalizable group on character-valued points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cartier.DiagonalizableCharacters

open RelativeMultiplicativeType

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]

variable (S M) in
/-- The commutative diagonalizable model `D_S(M)`: the base change of the group-algebra
model over `Spec ℤ`. Its underlying group scheme is `RelativeMultiplicativeType.diagonalizable`. -/
abbrev model : CommGroupScheme S :=
  (CommGroupScheme.baseChange (Gm.toSpecZ S)).obj
    (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) M)

example : (model S M).toGrp = diagonalizable S M := rfl

variable (M) in
/-- Points of `D_S(M)_T` over a scheme `V` over `T` are homomorphisms `M → Γ(V)ˣ`. -/
def testPointsEquiv (T : Over S) (V : Over T.left) :
    (V ⟶ (testBaseChange T (model S M)).X) ≃* (Multiplicative M →* (Γ(V.left, ⊤))ˣ) :=
  (baseChangePointsEquiv T.hom (model S M).toGrp V).trans
    (pointsEquiv S M ((Over.map T.hom).obj V))

lemma testPointsEquiv_apply (T : Over S) (V : Over T.left)
    (x : V ⟶ (testBaseChange T (model S M)).X) :
    testPointsEquiv M T V x =
      pointsEquiv S M ((Over.map T.hom).obj V) (baseChangePointsEquiv T.hom _ V x) := rfl

lemma testPointsEquiv_naturality (T : Over S) {V V' : Over T.left} (b : V' ⟶ V)
    (x : V ⟶ (testBaseChange T (model S M)).X) :
    testPointsEquiv M T V' (b ≫ x) =
      (Units.map b.left.appTop.hom.toMonoidHom).comp (testPointsEquiv M T V x) := by
  rw [testPointsEquiv_apply, baseChangePointsEquiv_naturality, pointsEquiv_comp]
  rfl

lemma testPointsEquiv_symm_naturality (T : Over S) {V V' : Over T.left} (b : V' ⟶ V)
    (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    (testPointsEquiv M T V').symm ((Units.map b.left.appTop.hom.toMonoidHom).comp t) =
      b ≫ (testPointsEquiv M T V).symm t := by
  apply (testPointsEquiv M T V').injective
  rw [MulEquiv.apply_symm_apply, testPointsEquiv_naturality, MulEquiv.apply_symm_apply]

/-- The action of a character of `D_S(M)` over `T` on character-valued points over a scheme
`V` over `T`: the unit obtained by applying the character to the point. -/
def act {T : Over S} (χ : (characters (model S M)).obj (op T)) (V : Over T.left) :
    (Multiplicative M →* (Γ(V.left, ⊤))ˣ) →* (Γ(V.left, ⊤))ˣ :=
  (Gm.baseChangeUnitsEquiv T.hom V).toMonoidHom.comp
    ((((yonedaGrp.map (Additive.toMul χ)).app (op V)).hom).comp
      (testPointsEquiv M T V).symm.toMonoidHom)

lemma act_apply {T : Over S} (χ : (characters (model S M)).obj (op T)) (V : Over T.left)
    (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    act χ V t = Gm.baseChangeUnitsEquiv T.hom V
      ((testPointsEquiv M T V).symm t ≫ (Additive.toMul χ).hom.hom) := rfl


lemma act_naturality {T : Over S} (χ : (characters (model S M)).obj (op T)) {V V' : Over T.left}
    (b : V' ⟶ V) (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    act χ V' ((Units.map b.left.appTop.hom.toMonoidHom).comp t) =
      Units.map b.left.appTop.hom.toMonoidHom (act χ V t) := by
  rw [act_apply, act_apply, testPointsEquiv_symm_naturality, Category.assoc,
    Gm.baseChangeUnitsEquiv_naturality]

/-- A character is determined by its action on character-valued points. -/
lemma act_ext {T : Over S} {χ ψ : (characters (model S M)).obj (op T)}
    (h : ∀ (V : Over T.left) (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ), act χ V t = act ψ V t) :
    χ = ψ := by
  have : Additive.toMul χ = Additive.toMul ψ := by
    apply hom_ext_points
    intro V x
    apply (Gm.baseChangeUnitsEquiv T.hom V).injective
    have hx := h V (testPointsEquiv M T V x)
    rwa [act_apply, act_apply, MulEquiv.symm_apply_apply] at hx
  exact this

lemma act_add {T : Over S} (χ ψ : (characters (model S M)).obj (op T)) (V : Over T.left)
    (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    act (χ + ψ) V t = act χ V t * act ψ V t := by
  rw [act_apply, act_apply, act_apply, ← map_mul]
  congr 1
  exact MonObj.comp_mul _ _ _

lemma act_zero {T : Over S} (V : Over T.left) (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    act (0 : (characters (model S M)).obj (op T)) V t = 1 := by
  rw [act_apply, ← map_one (Gm.baseChangeUnitsEquiv T.hom V)]
  congr 1
  exact MonObj.comp_one _

/-- The point formula for Cartier restriction along `a : T' ⟶ T`. -/
lemma act_restrict {T T' : Over S} (a : T' ⟶ T) (χ : (characters (model S M)).obj (op T))
    (V : Over T'.left) (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    act ((characters (model S M)).map a.op χ) V t = act χ ((Over.map a.left).obj V) t := by
  have hpt : restrictPointsEquiv (model S M) a V ((testPointsEquiv M T' V).symm t) =
      (testPointsEquiv M T ((Over.map a.left).obj V)).symm t := by
    apply (testPointsEquiv M T ((Over.map a.left).obj V)).injective
    have h1 := baseChangePointsEquiv_restrictPointsEquiv (model S M) a V
      ((testPointsEquiv M T' V).symm t)
    rw [MulEquiv.apply_symm_apply, testPointsEquiv_apply]
    erw [h1]
    rw [pointsEquiv_comp]
    conv_rhs => rw [← MulEquiv.apply_symm_apply (testPointsEquiv M T' V) t]
    rfl
  rw [act_apply, act_apply, Gm.baseChangeUnitsEquiv_apply, Gm.baseChangeUnitsEquiv_apply]
  change Gm.pointsEquiv S _ (baseChangePointsEquiv T'.hom (Gm S).toGrp V
    ((testPointsEquiv M T' V).symm t ≫
      (restrict (model S M) (Gm S) a χ).toMul.hom.hom)) = _
  rw [baseChangePointsEquiv_restrict, Gm.pointsEquiv_naturality, hpt]
  rfl

/-! ### Evaluation characters -/

variable (S) in
/-- The global evaluation character `D_S(M) → 𝔾_m` at `m : M`: the base change from `Spec ℤ`
of the character `t ↦ t(m)` of the group-algebra model. -/
def globalEval (m : M) : model S M ⟶ Gm S :=
  (CommGroupScheme.baseChange (Gm.toSpecZ S)).map
      (DiagonalizableCharacter.evalCharacter ZU.{u} M m) ≫
    (Gm.commBaseChangeIso (Gm.toSpecZ S)).hom

lemma globalEval_apply (m : M) (V : Over S) (x : V ⟶ (diagonalizable S M).X) :
    Gm.pointsEquiv S V (x ≫ (Additive.toMul (globalEval S m)).hom.hom) =
      pointsEquiv S M V x (Multiplicative.ofAdd m) := by
  change Gm.pointsEquiv S V (x ≫ ((GroupScheme.baseChange (Gm.toSpecZ S)).map
      (CommGroupScheme.groupHom (DiagonalizableCharacter.evalCharacter ZU.{u} M m))).hom.hom ≫
      (Gm.baseChangeIso (Gm.toSpecZ S)).hom.hom.hom) = _
  rw [← Category.assoc, Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply]
  erw [baseChangePointsEquiv_comp]
  rw [DiagonalizableCharacter.evalCharacter_apply]
  rfl

variable (T : Over S) in
/-- The evaluation character at `m : M` over a test scheme `T`: the base change to `T` of the
global evaluation character. -/
def evalChar (m : M) : (characters (model S M)).obj (op T) :=
  (CommGroupScheme.baseChange T.hom).map (globalEval S m)

lemma act_evalChar (T : Over S) (m : M) (V : Over T.left)
    (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    act (evalChar T m) V t = t (Multiplicative.ofAdd m) := by
  rw [act_apply, Gm.baseChangeUnitsEquiv_apply]
  erw [baseChangePointsEquiv_comp]
  rw [globalEval_apply]
  conv_rhs => rw [← MulEquiv.apply_symm_apply (testPointsEquiv M T V) t]
  rfl

lemma restrict_evalChar {T T' : Over S} (a : T' ⟶ T) (m : M) :
    (characters (model S M)).map a.op (evalChar T m) = evalChar T' m :=
  restrict_baseChange_map (globalEval S m) a

lemma evalChar_add (T : Over S) (m m' : M) :
    evalChar T (m + m') = evalChar T m + evalChar T m' := by
  apply act_ext
  intro V t
  rw [act_add, act_evalChar, act_evalChar, act_evalChar, ofAdd_add, map_mul]

lemma evalChar_zero (T : Over S) : evalChar T (0 : M) = 0 := by
  apply act_ext
  intro V t
  rw [act_zero, act_evalChar, ofAdd_zero, map_one]

/-- A character is the evaluation character at `m` iff it acts on every character-valued point
`t` by `t ↦ t(m)`. -/
lemma eq_evalChar_iff {T : Over S} (χ : (characters (model S M)).obj (op T)) (m : M) :
    χ = evalChar T m ↔
      ∀ (V : Over T.left) (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ),
        act χ V t = t (Multiplicative.ofAdd m) := by
  constructor
  · rintro rfl V t
    exact act_evalChar T m V t
  · intro h
    apply act_ext
    intro V t
    rw [h, act_evalChar]

/-! ### Characters from natural actions on character-valued points -/

/-- A family of homomorphisms from character-valued points to units, one for each scheme `V`
over `T.left`, is natural if it commutes with pullback of sections along morphisms over
`T.left`. -/
def IsNaturalAct {T : Over S}
    (φ : ∀ V : Over T.left, (Multiplicative M →* (Γ(V.left, ⊤))ˣ) →* (Γ(V.left, ⊤))ˣ) :
    Prop :=
  ∀ {V V' : Over T.left} (b : V' ⟶ V) (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ),
    φ V' ((Units.map b.left.appTop.hom.toMonoidHom).comp t) =
      Units.map b.left.appTop.hom.toMonoidHom (φ V t)

lemma isNaturalAct_act {T : Over S} (χ : (characters (model S M)).obj (op T)) :
    IsNaturalAct (act χ) :=
  fun b t => act_naturality χ b t

/-- The homomorphisms of points underlying `ofAct`. -/
def ofActPoints {T : Over S}
    (φ : ∀ V : Over T.left, (Multiplicative M →* (Γ(V.left, ⊤))ˣ) →* (Γ(V.left, ⊤))ˣ)
    (V : Over T.left) :
    (V ⟶ (testBaseChange T (model S M)).X) →* (V ⟶ (testBaseChange T (Gm S)).X) :=
  (Gm.baseChangeUnitsEquiv T.hom V).symm.toMonoidHom.comp
    ((φ V).comp (testPointsEquiv M T V).toMonoidHom)

lemma baseChangeUnitsEquiv_ofActPoints {T : Over S}
    (φ : ∀ V : Over T.left, (Multiplicative M →* (Γ(V.left, ⊤))ˣ) →* (Γ(V.left, ⊤))ˣ)
    (V : Over T.left) (x : V ⟶ (testBaseChange T (model S M)).X) :
    Gm.baseChangeUnitsEquiv T.hom V (ofActPoints φ V x) = φ V (testPointsEquiv M T V x) :=
  MulEquiv.apply_symm_apply _ _

lemma ofActPoints_naturality {T : Over S}
    (φ : ∀ V : Over T.left, (Multiplicative M →* (Γ(V.left, ⊤))ˣ) →* (Γ(V.left, ⊤))ˣ)
    (hφ : IsNaturalAct φ) {V V' : Over T.left} (b : V' ⟶ V)
    (x : V ⟶ (testBaseChange T (model S M)).X) :
    ofActPoints φ V' (b ≫ x) = b ≫ ofActPoints φ V x := by
  apply (Gm.baseChangeUnitsEquiv T.hom V').injective
  rw [baseChangeUnitsEquiv_ofActPoints, Gm.baseChangeUnitsEquiv_naturality,
    baseChangeUnitsEquiv_ofActPoints, testPointsEquiv_naturality, hφ]

/-- The character over `T` determined by a natural action on character-valued points. -/
def ofAct {T : Over S}
    (φ : ∀ V : Over T.left, (Multiplicative M →* (Γ(V.left, ⊤))ˣ) →* (Γ(V.left, ⊤))ˣ)
    (hφ : IsNaturalAct φ) : (characters (model S M)).obj (op T) :=
  Additive.ofMul (homOfPoints (ofActPoints φ) (fun b x => ofActPoints_naturality φ hφ b x))

lemma comp_ofAct {T : Over S}
    (φ : ∀ V : Over T.left, (Multiplicative M →* (Γ(V.left, ⊤))ˣ) →* (Γ(V.left, ⊤))ˣ)
    (hφ : IsNaturalAct φ) (V : Over T.left) (x : V ⟶ (testBaseChange T (model S M)).X) :
    x ≫ (Additive.toMul (ofAct φ hφ)).hom.hom = ofActPoints φ V x :=
  comp_homOfPoints (ofActPoints φ) (fun b x => ofActPoints_naturality φ hφ b x) V x

lemma act_ofAct {T : Over S}
    (φ : ∀ V : Over T.left, (Multiplicative M →* (Γ(V.left, ⊤))ˣ) →* (Γ(V.left, ⊤))ˣ)
    (hφ : IsNaturalAct φ) (V : Over T.left) (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    act (ofAct φ hφ) V t = φ V t := by
  rw [act_apply, comp_ofAct, baseChangeUnitsEquiv_ofActPoints, MulEquiv.apply_symm_apply]

lemma ofAct_act {T : Over S} (χ : (characters (model S M)).obj (op T)) :
    ofAct (act χ) (isNaturalAct_act χ) = χ :=
  act_ext fun V t => act_ofAct _ _ V t

end Langlands.GroupScheme.Cartier.DiagonalizableCharacters

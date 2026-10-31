import Langlands.Shimura.PEL.HarrisTaylorCMCentralTrace
import Langlands.Shimura.PEL.RationalLieDeterminantBaseChange
import Langlands.Shimura.PEL.HarrisTaylorLieBaseChange

/-! # Joint normalized determinant and numerical classes over the actual CM base -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry Opposite
open Langlands.AbelianScheme

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    {S T : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

omit [IsCMField F] in
/-- The normalized determinant pulls back along the actual CM structure map. -/
theorem harrisTaylorCMRationalLieDeterminantCondition_baseChange_of_naturality
    (f : T ⟶ S) (naturality : LieBaseChangeNaturalityStatement S)
    (h : D.HarrisTaylorCMRationalLieDeterminantCondition C p B i) :
    D.HarrisTaylorCMRationalLieDeterminantCondition C (f ≫ p)
      ((baseChange f).obj B) ((rationalBaseChangeEnd f B).comp i) := by
  apply (D.harrisTaylorCMRationalLieDeterminantCondition_iff C (f ≫ p)
    ((baseChange f).obj B) ((rationalBaseChangeEnd f B).comp i)).mpr
  rw [D.harrisTaylorReflexStructure_comp C p f]
  exact D.harrisRationalLieDeterminantCondition_baseChange_of_naturality
    C hΦ (D.harrisTaylorReflexStructure C p) B i f naturality
    ((D.harrisTaylorCMRationalLieDeterminantCondition_iff C p B i).mp h)

omit [IsCMField F] in
/-- Pullback preserves the determinant and geometric dimension on the same representative. -/
theorem harrisTaylorCMDeterminantDimensionCondition_baseChange_of_naturality
    (f : T ⟶ S) (naturality : LieBaseChangeNaturalityStatement S)
    (h : D.HarrisTaylorCMDeterminantDimensionCondition C p B i) :
    D.HarrisTaylorCMDeterminantDimensionCondition C (f ≫ p)
      ((baseChange f).obj B) ((rationalBaseChangeEnd f B).comp i) :=
  ⟨D.harrisTaylorCMRationalLieDeterminantCondition_baseChange_of_naturality
      C p B i f naturality h.1,
    HarrisTaylor.prescribedRelativeDimension_baseChange E B n h.2 f⟩

/-- The normalized determinant predicate on actual equivariant rational action classes. -/
abbrev HarrisTaylorCMDeterminantClassCondition
    (q : RationalAlgebraAction.IsoClass S A) : Prop :=
  D.HarrisRationalLieDeterminantClassCondition C hΦ
    (D.harrisTaylorReflexStructure C p) q

omit [IsCMField F] in
@[simp]
theorem harrisTaylorCMDeterminantClassCondition_classOf
    (X : RationalAlgebraAction S A) :
    D.HarrisTaylorCMDeterminantClassCondition C p (RationalAlgebraAction.classOf X) ↔
      D.HarrisTaylorCMRationalLieDeterminantCondition C p X.abelianScheme X.action :=
  (D.harrisTaylorCMRationalLieDeterminantCondition_iff C p
    X.abelianScheme X.action).symm

omit [IsCMField F] in
/-- The normalized quotient predicate follows actual class pullback. -/
theorem harrisTaylorCMDeterminantClassCondition_baseChange_of_naturality
    (f : T ⟶ S) (naturality : LieBaseChangeNaturalityStatement S)
    (q : RationalAlgebraAction.IsoClass S A)
    (h : D.HarrisTaylorCMDeterminantClassCondition C p q) :
    D.HarrisTaylorCMDeterminantClassCondition C (f ≫ p)
      (RationalAlgebraAction.pullbackClass f q) := by
  change D.HarrisRationalLieDeterminantClassCondition C hΦ
    (D.harrisTaylorReflexStructure C (f ≫ p)) _
  rw [D.harrisTaylorReflexStructure_comp C p f]
  exact D.harrisRationalLieDeterminantClassCondition_baseChange_of_naturality
    C hΦ (D.harrisTaylorReflexStructure C p) f naturality q h

/-- A single actual representative satisfies both normalized determinant and dimension. -/
def HarrisTaylorCMActionClassCondition
    (q : RationalAlgebraAction.IsoClass S A) : Prop :=
  ∃ X : RationalAlgebraAction S A, RationalAlgebraAction.classOf X = q ∧
    D.HarrisTaylorCMDeterminantDimensionCondition C p X.abelianScheme X.action

/-- The same-representative image equals the determinant predicate and numerical image.
The determinant is invariant on every representative; dimension stays existential. -/
theorem harrisTaylorCMActionClassCondition_iff
    (q : RationalAlgebraAction.IsoClass S A) :
    D.HarrisTaylorCMActionClassCondition C p q ↔
      D.HarrisTaylorCMDeterminantClassCondition C p q ∧
        HarrisTaylor.NumericalActionClassCondition L F p n E q := by
  constructor
  · rintro ⟨X, hX, h⟩
    have hnum := (D.harrisTaylorCMDeterminantDimensionCondition_iff C p
      X.abelianScheme X.action).mp h
    refine ⟨?_, X, hX, hnum.2⟩
    rw [← hX]
    exact (D.harrisTaylorCMDeterminantClassCondition_classOf C p X).mpr h.1
  · rintro ⟨hdet, X, hX, hnum⟩
    refine ⟨X, hX, ?_, hnum.1⟩
    rw [← hX] at hdet
    exact (D.harrisTaylorCMDeterminantClassCondition_classOf C p X).mp hdet

/-- Every actual representative of a joint class satisfies the normalized determinant. -/
theorem harrisTaylorCMActionClassCondition_determinant
    (q : RationalAlgebraAction.IsoClass S A)
    (hq : D.HarrisTaylorCMActionClassCondition C p q)
    (X : RationalAlgebraAction S A) (hX : RationalAlgebraAction.classOf X = q) :
    D.HarrisTaylorCMRationalLieDeterminantCondition C p X.abelianScheme X.action := by
  have hdet := ((D.harrisTaylorCMActionClassCondition_iff C p q).mp hq).1
  rw [← hX] at hdet
  exact (D.harrisTaylorCMDeterminantClassCondition_classOf C p X).mp hdet

/-- Every actual representative of a joint class satisfies the all-scalar central trace. -/
theorem harrisTaylorCMActionClassCondition_centralTrace
    (q : RationalAlgebraAction.IsoClass S A)
    (hq : D.HarrisTaylorCMActionClassCondition C p q)
    (X : RationalAlgebraAction S A) (hX : RationalAlgebraAction.classOf X = q) :
    HarrisTaylor.CentralLieTraceCondition L p X.abelianScheme X.action n :=
  D.harrisTaylorCMRationalLieDeterminantCondition_centralTrace C p
    X.abelianScheme X.action
    (D.harrisTaylorCMActionClassCondition_determinant C p q hq X hX)

/-- Actual rational action classes admitting one joint satisfying representative. -/
def HarrisTaylorCMActionClass :=
  {q : RationalAlgebraAction.IsoClass S A // D.HarrisTaylorCMActionClassCondition C p q}

/-- An actual jointly satisfying action defines its actual rational-isomorphism class. -/
def harrisTaylorCMActionClassOf (X : RationalAlgebraAction S A)
    (hX : D.HarrisTaylorCMDeterminantDimensionCondition C p X.abelianScheme X.action) :
    D.HarrisTaylorCMActionClass C p :=
  ⟨RationalAlgebraAction.classOf X, X, rfl, hX⟩

omit [IsCMField F] in
@[simp]
theorem harrisTaylorCMActionClassOf_val (X : RationalAlgebraAction S A)
    (hX : D.HarrisTaylorCMDeterminantDimensionCondition C p X.abelianScheme X.action) :
    (D.harrisTaylorCMActionClassOf C p X hX).val = RationalAlgebraAction.classOf X := rfl

omit [IsCMField F] in
/-- Equality retains a two-sided rational isomorphism and the full algebra action equation. -/
theorem harrisTaylorCMActionClassOf_eq_iff_rationalIso
    (X Y : RationalAlgebraAction S A)
    (hX : D.HarrisTaylorCMDeterminantDimensionCondition C p X.abelianScheme X.action)
    (hY : D.HarrisTaylorCMDeterminantDimensionCondition C p Y.abelianScheme Y.action) :
    D.harrisTaylorCMActionClassOf C p X hX = D.harrisTaylorCMActionClassOf C p Y hY ↔
      ∃ e : Langlands.Rationalization.of X.abelianScheme ≅
          Langlands.Rationalization.of Y.abelianScheme,
        ∀ a : A, comp0 _ _ _ (X.action a) e.hom = comp0 _ _ _ e.hom (Y.action a) := by
  rw [Subtype.ext_iff]
  exact RationalAlgebraAction.classOf_eq_iff_rationalIso

omit [IsCMField F] in
/-- Every joint image class has an actual representative satisfying both tests. -/
theorem harrisTaylorCMActionClassOf_surjective (q : D.HarrisTaylorCMActionClass C p) :
    ∃ (X : RationalAlgebraAction S A)
      (hX : D.HarrisTaylorCMDeterminantDimensionCondition C p X.abelianScheme X.action),
      D.harrisTaylorCMActionClassOf C p X hX = q := by
  obtain ⟨X, hX, h⟩ := q.property
  exact ⟨X, h, Subtype.ext hX⟩

omit [IsCMField F] in
/-- Actual pullback preserves one jointly satisfying representative and its class. -/
theorem harrisTaylorCMActionClassCondition_baseChange_of_naturality
    (f : T ⟶ S) (naturality : LieBaseChangeNaturalityStatement S)
    (q : RationalAlgebraAction.IsoClass S A)
    (h : D.HarrisTaylorCMActionClassCondition C p q) :
    D.HarrisTaylorCMActionClassCondition C (f ≫ p)
      (RationalAlgebraAction.pullbackClass f q) := by
  obtain ⟨X, hX, h⟩ := h
  refine ⟨(RationalAlgebraAction.pullback f).obj X, ?_, ?_⟩
  · rw [← hX]
    rfl
  · exact D.harrisTaylorCMDeterminantDimensionCondition_baseChange_of_naturality
      C p X.abelianScheme X.action f naturality h

/-- The actual normalized determinant subfunctor over the CM spectrum. -/
def harrisTaylorCMDeterminantSubfunctor
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    Subfunctor (RationalAlgebraAction.isoClassOverPresheaf (Spec (.of F)) A) where
  obj X := {q | D.HarrisTaylorCMDeterminantClassCondition C X.unop.hom q}
  map {X Y} f q hq := by
    change D.HarrisTaylorCMDeterminantClassCondition C Y.unop.hom
      (RationalAlgebraAction.pullbackClass f.unop.left q)
    rw [← Over.w f.unop]
    exact D.harrisTaylorCMDeterminantClassCondition_baseChange_of_naturality
      C X.unop.hom f.unop.left (allNaturality X.unop.left) q hq

/-- The same-representative joint image is stable under actual geometric pullback. -/
def harrisTaylorCMActionSubfunctor
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    Subfunctor (RationalAlgebraAction.isoClassOverPresheaf (Spec (.of F)) A) where
  obj X := {q | D.HarrisTaylorCMActionClassCondition C X.unop.hom q}
  map {X Y} f q hq := by
    change D.HarrisTaylorCMActionClassCondition C Y.unop.hom
      (RationalAlgebraAction.pullbackClass f.unop.left q)
    rw [← Over.w f.unop]
    exact D.harrisTaylorCMActionClassCondition_baseChange_of_naturality
      C X.unop.hom f.unop.left (allNaturality X.unop.left) q hq

/-- The joint image agrees with the intersection only after the same-representative theorem. -/
theorem harrisTaylorCMActionSubfunctor_eq_inf
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    D.harrisTaylorCMActionSubfunctor C allNaturality =
      D.harrisTaylorCMDeterminantSubfunctor C allNaturality ⊓
        HarrisTaylor.numericalActionSubfunctor L F n E (A := A) allNaturality := by
  ext X q
  exact D.harrisTaylorCMActionClassCondition_iff C X.unop.hom q

/-- The normalized determinant moduli presheaf on actual schemes over the CM field. -/
def harrisTaylorCMDeterminantPresheaf
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    (Over (Spec (.of F)))ᵒᵖ ⥤ Type 1 :=
  (D.harrisTaylorCMDeterminantSubfunctor C allNaturality).toFunctor

/-- The joint determinant-and-dimension image as an actual moduli presheaf. -/
def harrisTaylorCMActionPresheaf
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    (Over (Spec (.of F)))ᵒᵖ ⥤ Type 1 :=
  (D.harrisTaylorCMActionSubfunctor C allNaturality).toFunctor

/-- The natural inclusion into actual rational algebra-action isomorphism classes. -/
def harrisTaylorCMActionPresheafInclusion
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    D.harrisTaylorCMActionPresheaf C allNaturality ⟶
      RationalAlgebraAction.isoClassOverPresheaf (Spec (.of F)) A :=
  (D.harrisTaylorCMActionSubfunctor C allNaturality).ι

/-- Forget the numerical restriction while retaining the normalized determinant. -/
def harrisTaylorCMActionPresheafToDeterminant
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    D.harrisTaylorCMActionPresheaf C allNaturality ⟶
      D.harrisTaylorCMDeterminantPresheaf C allNaturality :=
  Subfunctor.homOfLe (by
    intro X q h
    exact ((D.harrisTaylorCMActionClassCondition_iff C X.unop.hom q).mp h).1)

/-- Forget the determinant while retaining the actual numerical image class. -/
def harrisTaylorCMActionPresheafToNumerical
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    D.harrisTaylorCMActionPresheaf C allNaturality ⟶
      HarrisTaylor.numericalActionPresheaf L F n E (A := A) allNaturality :=
  Subfunctor.homOfLe (by
    intro X q h
    exact ((D.harrisTaylorCMActionClassCondition_iff C X.unop.hom q).mp h).2)

omit [IsCMField F] in
@[simp]
theorem harrisTaylorCMActionPresheaf_obj
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    (X : Over (Spec (.of F))) :
    (D.harrisTaylorCMActionPresheaf C allNaturality).obj (op X) =
      D.HarrisTaylorCMActionClass C X.hom := rfl

omit [IsCMField F] in
@[simp]
theorem harrisTaylorCMActionPresheaf_map_val
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    {X Y : Over (Spec (.of F))} (f : Y ⟶ X)
    (q : D.HarrisTaylorCMActionClass C X.hom) :
    ((D.harrisTaylorCMActionPresheaf C allNaturality).map f.op q).val =
      RationalAlgebraAction.pullbackClass f.left q.val := rfl

omit [IsCMField F] in
@[simp]
theorem harrisTaylorCMActionPresheaf_map_classOf_val
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    {X Y : Over (Spec (.of F))} (f : Y ⟶ X)
    (Z : RationalAlgebraAction X.left A)
    (hZ : D.HarrisTaylorCMDeterminantDimensionCondition C X.hom
      Z.abelianScheme Z.action) :
    ((D.harrisTaylorCMActionPresheaf C allNaturality).map f.op
      (D.harrisTaylorCMActionClassOf C X.hom Z hZ)).val =
        RationalAlgebraAction.classOf ((RationalAlgebraAction.pullback f.left).obj Z) := rfl

omit [IsCMField F] in
theorem harrisTaylorCMActionPresheafInclusion_injective
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    (X : Over (Spec (.of F))) :
    Function.Injective
      ((D.harrisTaylorCMActionPresheafInclusion C allNaturality).app (op X)) :=
  Subtype.val_injective

/-- Forgetting through numerical classes equals the ambient natural inclusion. -/
theorem harrisTaylorCMActionPresheafToNumerical_inclusion
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    D.harrisTaylorCMActionPresheafToNumerical C allNaturality ≫
        HarrisTaylor.numericalActionPresheafInclusion L F n E (A := A) allNaturality =
      D.harrisTaylorCMActionPresheafInclusion C allNaturality := by
  ext X q
  rfl

/-- Forgetting through determinant classes equals the same ambient inclusion. -/
theorem harrisTaylorCMActionPresheafToDeterminant_inclusion
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    D.harrisTaylorCMActionPresheafToDeterminant C allNaturality ≫
        (D.harrisTaylorCMDeterminantSubfunctor C allNaturality).ι =
      D.harrisTaylorCMActionPresheafInclusion C allNaturality := by
  ext X q
  rfl

end Langlands.Shimura.CentralSimpleUnitaryData

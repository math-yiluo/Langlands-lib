import Langlands.Algebra.NonUnitalTensorHomAdjunctionStatements
import Langlands.Algebra.NondegenerateModuleAdjunction

/-! # Proof of the original-action additive tensor-Hom equivalences -/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalTensorHomAdjunction

open MulOpposite
open NonUnitalModuleTensor
open NonUnitalBimoduleTensor (rightModule leftModule rightLift leftLift)
open NonUnitalBimoduleHomActions (rightSourceAction sourceAction)

universe uR uS uX uY uZ uX' uY' uZ'

/-- Whole additive inverse identities follow from the equivalence inverse laws. -/
theorem inverseIdentities {A : Type uX} {B : Type uY} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) : InverseIdentities E := by
  constructor
  · ext a
    exact E.symm_apply_apply a
  · ext b
    exact E.apply_symm_apply b

/-- The inverse naturality square follows from the forward square and inverse laws. -/
theorem inverse_naturality {A : Type uX} {B : Type uY} {A' : Type uX'} {B' : Type uY'}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    (E : A ≃+ B) (E' : A' ≃+ B') (P : A →+ A') (Q : B →+ B')
    (h : E'.toAddMonoidHom.comp P = Q.comp E.toAddMonoidHom) :
    E'.symm.toAddMonoidHom.comp Q = P.comp E.symm.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro b
  apply E'.injective
  change E' (E'.symm (Q b)) = E' (P (E.symm b))
  rw [E'.apply_symm_apply]
  have hb := DFunLike.congr_fun h (E.symm b)
  change E' (P (E.symm b)) = Q (E (E.symm b)) at hb
  rw [E.apply_symm_apply] at hb
  exact hb.symm

/-- Original Hom factorization through the actual part, as an additive equivalence. -/
def partEquivalence {A : Type uR} {M : Type uX} {N : Type uY}
    [NonUnitalRing A] [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    NonUnitalModuleHom A M N ≃+ NonUnitalModuleHom A M (nondegeneratePart hA N) where
  toFun := NonUnitalModuleHom.factorNondegeneratePart hA hM
  invFun f := (nondegeneratePart hA N).subtype.comp f
  left_inv f := by ext m; rfl
  right_inv f := by
    apply NonUnitalModuleHom.ext
    intro m
    apply Subtype.ext
    rfl
  map_add' f g := by
    apply NonUnitalModuleHom.ext
    intro m
    apply Subtype.ext
    rfl

namespace Right

section Triple

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
  [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
  (hY : ActionsCommute R S Y)

/-- Curry by evaluation on the original pure tensors. -/
def curry : TensorHom R S X Y Z hY →+ CurriedHom R S X Y Z hY := by
  letI := rightModule X hY
  letI := rightSourceAction (Z := Z) hY
  exact {
    toFun φ := {
      toFun x := {
        toFun y := φ (tmul R X Y x y)
        map_zero' := by simp
        map_add' y y' := by rw [tmul_add, φ.map_add]
        map_smul' s y := by
          change φ (tmul R X Y x (s • y)) = s • φ (tmul R X Y x y)
          rw [← NonUnitalBimoduleTensor.rightModule_smul_tmul X hY]
          exact φ.map_smul s _ }
      map_zero' := by ext y; simp
      map_add' x x' := by ext y; exact congrArg φ (add_tmul R X Y x x' y) |>.trans (φ.map_add _ _)
      map_smul' r x := by
        apply NonUnitalModuleHom.ext
        intro y
        change φ (tmul R X Y (r • x) y) = φ (tmul R X Y x (r.unop • y))
        exact congrArg φ (tmul_balanced R X Y r.unop x y) }
    map_zero' := by ext x y; rfl
    map_add' _ _ := by ext x y; rfl }

/-- Uncurry by the published original-linear quotient lift of evaluation. -/
def uncurry (ψ : CurriedHom R S X Y Z hY) : TensorHom R S X Y Z hY :=
  rightLift hY (evaluationPairing R S X Y Z hY ψ)
    (evaluationPairing_balanced R S X Y Z hY ψ) (fun s x y => (ψ x).map_smul s y)

/-- The actual original-action additive equivalence. -/
def equivalence : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY where
  toFun := curry R S X Y Z hY
  invFun := uncurry R S X Y Z hY
  left_inv φ := by
    let := rightModule X hY
    apply NonUnitalModuleHom.ext
    intro t
    exact DFunLike.congr_fun (hom_ext R (fun _ _ => rfl) :
      (uncurry R S X Y Z hY (curry R S X Y Z hY φ)).toAddMonoidHom = φ.toAddMonoidHom) t
  right_inv ψ := by
    let := rightSourceAction (Z := Z) hY
    ext x y
    rfl
  map_add' := (curry R S X Y Z hY).map_add

/-- All specified canonical clauses, including the whole inverse lift. -/
theorem equivalence_canonical : Canonical R S X Y Z hY (equivalence R S X Y Z hY) :=
  ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, inverseIdentities _⟩

/-- Compose the ambient equivalence with actual-part factorization. -/
def refinedEquivalence (hR : IsIdempotented R) (hX : IsNondegenerate Rᵐᵒᵖ X) :
    TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR := by
  letI := rightSourceAction (Z := Z) hY
  exact (equivalence R S X Y Z hY).trans (partEquivalence hR.op hX)

/-- Both whole-map comparisons with the ambient equivalence. -/
theorem refinedEquivalence_canonical (hR : IsIdempotented R)
    (hX : IsNondegenerate Rᵐᵒᵖ X) :
    RefinedCanonical R S X Y Z hY hR (equivalence R S X Y Z hY)
      (refinedEquivalence R S X Y Z hY hR hX) := by
  refine ⟨equivalence_canonical R S X Y Z hY, fun _ _ _ => rfl, ?_, ?_⟩
  · ext φ
    rfl
  · rfl

section Maps

variable {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
  [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
  [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
  [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
  (hY' : ActionsCommute R S Y')
  (f : NonUnitalModuleHom Rᵐᵒᵖ X' X)
  (g : NonUnitalBimoduleHom R S Y' Y)
  (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')

/-- Naturality in all three variables for any canonical witnesses. -/
theorem naturality
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY')
    (hE : Canonical R S X Y Z hY E) (hE' : Canonical R S X' Y' Z' hY' E') :
    Naturality R S X Y Z hY hY' f g k E E' := by
  let := rightModule X hY
  let := rightModule X' hY'
  let := rightSourceAction (Z := Z) hY
  let := rightSourceAction (Z := Z') hY'
  have hforward : E'.toAddMonoidHom.comp (tensorHomMap R S X Y Z hY hY' f g k) =
      (curriedHomMap R S X Y Z hY hY' f g k).comp E.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro φ
    apply NonUnitalModuleHom.ext
    intro x
    apply NonUnitalModuleHom.ext
    intro y
    change (E' (tensorHomMap R S X Y Z hY hY' f g k φ) x) y =
      k ((E φ (f x)) (g y))
    rw [hE'.1]
    change k (φ (NonUnitalBimoduleTensor.rightMap hY' hY f g (tmul R X' Y' x y))) = _
    rw [NonUnitalBimoduleTensor.rightMap_tmul, hE.1]
  exact ⟨hforward, inverse_naturality E E' _ _ hforward⟩

/-- Refined naturality uses the exact published restriction of the inner Hom map. -/
theorem refined_naturality (hR : IsIdempotented R)
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY')
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR)
    (End' : TensorHom R S X' Y' Z' hY' ≃+ RefinedHom R S X' Y' Z' hY' hR)
    (hEnd : RefinedCanonical R S X Y Z hY hR E End)
    (hEnd' : RefinedCanonical R S X' Y' Z' hY' hR E' End') :
    RefinedNaturality R S X Y Z hY hY' f g k hR End End' := by
  let := rightModule X hY
  let := rightModule X' hY'
  let := rightSourceAction (Z := Z) hY
  let := rightSourceAction (Z := Z') hY'
  have hforward : End'.toAddMonoidHom.comp (tensorHomMap R S X Y Z hY hY' f g k) =
      (refinedHomMap R S X Y Z hY hY' f g k hR).comp End.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro φ
    apply NonUnitalModuleHom.ext
    intro x
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro y
    change ((End' (tensorHomMap R S X Y Z hY hY' f g k φ) x).val) y =
      k (((End φ (f x)).val) (g y))
    rw [hEnd'.2.1]
    change k (φ (NonUnitalBimoduleTensor.rightMap hY' hY f g (tmul R X' Y' x y))) = _
    rw [NonUnitalBimoduleTensor.rightMap_tmul, hEnd.2.1]
  exact ⟨hforward, inverse_naturality End End' _ _ hforward⟩

end Maps

end Triple

/-- Closed unconditional existence at the full independent universes. -/
theorem existence : ExistenceTheorem.{uR, uS, uX, uY, uZ} := by
  intro R S X Y Z _ _ _ _ _ _ _ _ _ hY
  exact ⟨equivalence R S X Y Z hY, equivalence_canonical R S X Y Z hY⟩

/-- Closed whole-map naturality for arbitrary canonical witnesses. -/
theorem whole_naturality : NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} := by
  intro R S X Y Z X' Y' Z' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hY hY' f g k E E' hE hE'
  exact naturality R S X Y Z hY hY' f g k E E' hE hE'

/-- Closed existence through the actual nondegenerate Hom part. -/
theorem refined_existence : RefinedExistenceTheorem.{uR, uS, uX, uY, uZ} := by
  intro R S X Y Z _ _ _ _ _ _ _ _ _ hY hR hX
  exact ⟨equivalence R S X Y Z hY, refinedEquivalence R S X Y Z hY hR hX,
    refinedEquivalence_canonical R S X Y Z hY hR hX⟩

/-- Closed naturality for the published nondegenerate-part restrictions. -/
theorem whole_refined_naturality :
    RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} := by
  intro R S X Y Z X' Y' Z' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hY hY' hR f g k E E' End End'
    _hX _hX' hEnd hEnd'
  exact refined_naturality R S X Y Z hY hY' f g k hR E E' End End' hEnd hEnd'

end Right

namespace Left

section Triple

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule R X] [NonUnitalModule S Y]
  [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
  (hY : ActionsCommute S R Y)

/-- Curry directly with the original left action on X. -/
def curry : TensorHom R S X Y Z hY →+ CurriedHom R S X Y Z hY := by
  letI := leftModule hY X
  letI := sourceAction (Z := Z) hY
  exact {
    toFun φ := {
      toFun x := {
        toFun y := φ (tmul R Y X y x)
        map_zero' := by simp
        map_add' y y' := by rw [add_tmul, φ.map_add]
        map_smul' s y := by
          change φ (tmul R Y X (s • y) x) = s • φ (tmul R Y X y x)
          rw [← NonUnitalBimoduleTensor.leftModule_smul_tmul hY X]
          exact φ.map_smul s _ }
      map_zero' := by ext y; simp
      map_add' x x' := by ext y; exact congrArg φ (tmul_add R Y X y x x') |>.trans (φ.map_add _ _)
      map_smul' r x := by
        apply NonUnitalModuleHom.ext
        intro y
        change φ (tmul R Y X y (r • x)) = φ (tmul R Y X (op r • y) x)
        exact congrArg φ (tmul_balanced R Y X r y x).symm }
    map_zero' := by ext x y; rfl
    map_add' _ _ := by ext x y; rfl }

/-- Uncurry through the published left-linear lift of evaluation. -/
def uncurry (ψ : CurriedHom R S X Y Z hY) : TensorHom R S X Y Z hY :=
  leftLift hY (evaluationPairing R S X Y Z hY ψ)
    (evaluationPairing_balanced R S X Y Z hY ψ) (fun s y x => (ψ x).map_smul s y)

/-- The actual original-action additive equivalence. -/
def equivalence : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY where
  toFun := curry R S X Y Z hY
  invFun := uncurry R S X Y Z hY
  left_inv φ := by
    let := leftModule hY X
    apply NonUnitalModuleHom.ext
    intro t
    exact DFunLike.congr_fun (hom_ext R (fun _ _ => rfl) :
      (uncurry R S X Y Z hY (curry R S X Y Z hY φ)).toAddMonoidHom = φ.toAddMonoidHom) t
  right_inv ψ := by
    let := sourceAction (Z := Z) hY
    ext x y
    rfl
  map_add' := (curry R S X Y Z hY).map_add

/-- All specified canonical clauses, including the whole inverse lift. -/
theorem equivalence_canonical : Canonical R S X Y Z hY (equivalence R S X Y Z hY) :=
  ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, inverseIdentities _⟩

/-- Compose the ambient equivalence with actual-part factorization. -/
def refinedEquivalence (hR : IsIdempotented R) (hX : IsNondegenerate R X) :
    TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR := by
  letI := sourceAction (Z := Z) hY
  exact (equivalence R S X Y Z hY).trans (partEquivalence hR hX)

/-- Both whole-map comparisons with the ambient equivalence. -/
theorem refinedEquivalence_canonical (hR : IsIdempotented R)
    (hX : IsNondegenerate R X) :
    RefinedCanonical R S X Y Z hY hR (equivalence R S X Y Z hY)
      (refinedEquivalence R S X Y Z hY hR hX) := by
  refine ⟨equivalence_canonical R S X Y Z hY, fun _ _ _ => rfl, ?_, ?_⟩
  · ext φ
    rfl
  · rfl

section Maps

variable {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
  [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
  [NonUnitalModule R X'] [NonUnitalModule S Y']
  [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
  (hY' : ActionsCommute S R Y')
  (f : NonUnitalModuleHom R X' X)
  (g : NonUnitalBimoduleHom S R Y' Y)
  (k : NonUnitalModuleHom S Z Z')

/-- Naturality in all three variables for any canonical witnesses. -/
theorem naturality
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY')
    (hE : Canonical R S X Y Z hY E) (hE' : Canonical R S X' Y' Z' hY' E') :
    Naturality R S X Y Z hY hY' f g k E E' := by
  let := leftModule hY X
  let := leftModule hY' X'
  let := sourceAction (Z := Z) hY
  let := sourceAction (Z := Z') hY'
  have hforward : E'.toAddMonoidHom.comp (tensorHomMap R S X Y Z hY hY' f g k) =
      (curriedHomMap R S X Y Z hY hY' f g k).comp E.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro φ
    apply NonUnitalModuleHom.ext
    intro x
    apply NonUnitalModuleHom.ext
    intro y
    change (E' (tensorHomMap R S X Y Z hY hY' f g k φ) x) y =
      k ((E φ (f x)) (g y))
    rw [hE'.1]
    change k (φ (NonUnitalBimoduleTensor.leftMap hY' hY g f (tmul R Y' X' y x))) = _
    rw [NonUnitalBimoduleTensor.leftMap_tmul, hE.1]
  exact ⟨hforward, inverse_naturality E E' _ _ hforward⟩

/-- Refined naturality uses the exact published restriction of the inner Hom map. -/
theorem refined_naturality (hR : IsIdempotented R)
    (E : TensorHom R S X Y Z hY ≃+ CurriedHom R S X Y Z hY)
    (E' : TensorHom R S X' Y' Z' hY' ≃+ CurriedHom R S X' Y' Z' hY')
    (End : TensorHom R S X Y Z hY ≃+ RefinedHom R S X Y Z hY hR)
    (End' : TensorHom R S X' Y' Z' hY' ≃+ RefinedHom R S X' Y' Z' hY' hR)
    (hEnd : RefinedCanonical R S X Y Z hY hR E End)
    (hEnd' : RefinedCanonical R S X' Y' Z' hY' hR E' End') :
    RefinedNaturality R S X Y Z hY hY' f g k hR End End' := by
  let := leftModule hY X
  let := leftModule hY' X'
  let := sourceAction (Z := Z) hY
  let := sourceAction (Z := Z') hY'
  have hforward : End'.toAddMonoidHom.comp (tensorHomMap R S X Y Z hY hY' f g k) =
      (refinedHomMap R S X Y Z hY hY' f g k hR).comp End.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro φ
    apply NonUnitalModuleHom.ext
    intro x
    apply Subtype.ext
    apply NonUnitalModuleHom.ext
    intro y
    change ((End' (tensorHomMap R S X Y Z hY hY' f g k φ) x).val) y =
      k (((End φ (f x)).val) (g y))
    rw [hEnd'.2.1]
    change k (φ (NonUnitalBimoduleTensor.leftMap hY' hY g f (tmul R Y' X' y x))) = _
    rw [NonUnitalBimoduleTensor.leftMap_tmul, hEnd.2.1]
  exact ⟨hforward, inverse_naturality End End' _ _ hforward⟩

end Maps

end Triple

/-- Closed unconditional existence at the full independent universes. -/
theorem existence : ExistenceTheorem.{uR, uS, uX, uY, uZ} := by
  intro R S X Y Z _ _ _ _ _ _ _ _ _ hY
  exact ⟨equivalence R S X Y Z hY, equivalence_canonical R S X Y Z hY⟩

/-- Closed whole-map naturality for arbitrary canonical witnesses. -/
theorem whole_naturality : NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} := by
  intro R S X Y Z X' Y' Z' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hY hY' f g k E E' hE hE'
  exact naturality R S X Y Z hY hY' f g k E E' hE hE'

/-- Closed existence through the actual nondegenerate Hom part. -/
theorem refined_existence : RefinedExistenceTheorem.{uR, uS, uX, uY, uZ} := by
  intro R S X Y Z _ _ _ _ _ _ _ _ _ hY hR hX
  exact ⟨equivalence R S X Y Z hY, refinedEquivalence R S X Y Z hY hR hX,
    refinedEquivalence_canonical R S X Y Z hY hR hX⟩

/-- Closed naturality for the published nondegenerate-part restrictions. -/
theorem whole_refined_naturality :
    RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} := by
  intro R S X Y Z X' Y' Z' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hY hY' hR f g k E E' End End'
    _hX _hX' hEnd hEnd'
  exact refined_naturality R S X Y Z hY hY' f g k hR E E' End End' hEnd hEnd'

end Left

end Langlands.Algebra.NonUnitalTensorHomAdjunction

namespace Langlands.Algebra

open NonUnitalTensorHomAdjunction

universe uR uS uX uY uZ uX' uY' uZ'

/-- Both original-action equivalences, whole-map naturality and actual-part refinements. -/
theorem nonUnitalTensorHomAdjunction :
    NonUnitalTensorHomAdjunctionTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} :=
  ⟨Right.existence, Left.existence, Right.whole_naturality, Left.whole_naturality,
    Right.refined_existence, Left.refined_existence,
    Right.whole_refined_naturality, Left.whole_refined_naturality⟩

end Langlands.Algebra

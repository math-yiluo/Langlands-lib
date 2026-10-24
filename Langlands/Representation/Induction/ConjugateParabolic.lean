import Langlands.Representation.Exponents.ParabolicPair
import Langlands.Representation.Induction.Parabolic

/-!
# Normalized induction from actual conjugate block parabolics

For a concrete pair `P = (B, c)` the actual parabolic is `c * B.parabolic * c⁻¹`.
Conjugation by `c` identifies it with the standard upper block parabolic, which
transports the block Levi embedding and projection. Induction from the actual
conjugate parabolic uses the transported projection, and left translation by
`c⁻¹` is an equivalence from standard normalized parabolic induction.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]
variable {P Q : Subgroup G} {σ : Representation R P V} {τ : Representation R Q V}

/-- Left translation `x ↦ f (a * x)` carries smooth `P`-covariant functions to smooth
`Q`-covariant functions, where `e` identifies `P` with `Q = a⁻¹ * P * a`. -/
def translateSmoothFunction (a : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = a⁻¹ * p * a) (hστ : ∀ p : P, τ (e p) = σ p)
    (f : SmoothFunctions P σ) : SmoothFunctions Q τ :=
  ⟨⟨fun x => eval P σ f (a * x), by
    intro q x
    obtain ⟨p, rfl⟩ := e.surjective q
    change eval P σ f (a * ((e p : G) * x)) = τ (e p) (eval P σ f (a * x))
    rw [he p, hστ p]
    refine Eq.trans (congrArg (eval P σ f) ?_) (f.1.2 p (a * x))
    change a * (a⁻¹ * (p : G) * a * x) = (p : G) * (a * x)
    simp [mul_assoc]⟩, by
    obtain ⟨K, hK⟩ := f.property
    refine ⟨K, ?_⟩
    intro k
    apply Subtype.ext
    funext x
    change eval P σ f (a * (x * (k : G))) = eval P σ f (a * x)
    rw [← mul_assoc]
    exact congrArg (fun φ : EquivariantFunctions P σ => φ.1 (a * x)) (hK k)⟩

omit [IsTopologicalGroup G] in
@[simp]
theorem translateSmoothFunction_eval (a : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = a⁻¹ * p * a) (hστ : ∀ p : P, τ (e p) = σ p)
    (f : SmoothFunctions P σ) (x : G) :
    eval Q τ (translateSmoothFunction a e he hστ f) x = eval P σ f (a * x) := rfl

omit [IsTopologicalGroup G] in
/-- Each uniform open right stabilizer of `f` stabilizes its left translate. -/
theorem translateSmoothFunction_stabilizer (a : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = a⁻¹ * p * a) (hστ : ∀ p : P, τ (e p) = σ p)
    (f : SmoothFunctions P σ) (K : OpenSubgroup G)
    (hK : ∀ (k : K) (x : G), eval P σ f (x * (k : G)) = eval P σ f x)
    (k : K) (x : G) :
    eval Q τ (translateSmoothFunction a e he hστ f) (x * (k : G)) =
      eval Q τ (translateSmoothFunction a e he hστ f) x := by
  change eval P σ f (a * (x * (k : G))) = eval P σ f (a * x)
  rw [← mul_assoc]
  exact hK k (a * x)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Inner conjugation by `c` on subgroups, in the inverse direction. -/
private theorem conjugate_symm_apply (c : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = c * p * c⁻¹) (q : Q) :
    (e.symm q : G) = c⁻¹ * q * c := by
  have h := he (e.symm q)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  simp [mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem conjugate_apply_inv (c : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = c * p * c⁻¹) (p : P) :
    (e p : G) = c⁻¹⁻¹ * p * c⁻¹ := by
  rw [inv_inv]
  exact he p

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem conjugate_symm_rep (e : P ≃* Q) (hστ : ∀ p : P, τ (e p) = σ p) (q : Q) :
    σ (e.symm q) = τ q := by
  rw [← hστ, MulEquiv.apply_symm_apply]

/-- If `e` is inner conjugation `p ↦ c * p * c⁻¹` and matches the inducing
representations, left translation by `c⁻¹` is an equivalence of smooth inductions,
with inverse left translation by `c`. -/
def conjugateSmoothInducedEquiv (c : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = c * p * c⁻¹) (hστ : ∀ p : P, τ (e p) = σ p) :
    (smoothInduced P σ).Equiv (smoothInduced Q τ) where
  toFun := translateSmoothFunction c⁻¹ e (conjugate_apply_inv c e he) hστ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := translateSmoothFunction c e.symm (conjugate_symm_apply c e he)
    (conjugate_symm_rep e hστ)
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval P σ f (c⁻¹ * (c * x)) = eval P σ f x
    rw [inv_mul_cancel_left]
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval Q τ h (c * (c⁻¹ * x)) = eval Q τ h x
    rw [mul_inv_cancel_left]
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change eval P σ f (c⁻¹ * x * g) = eval P σ f (c⁻¹ * (x * g))
    rw [mul_assoc]

@[simp]
theorem conjugateSmoothInducedEquiv_eval (c : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = c * p * c⁻¹) (hστ : ∀ p : P, τ (e p) = σ p)
    (f : SmoothFunctions P σ) (x : G) :
    eval Q τ (conjugateSmoothInducedEquiv c e he hστ f) x = eval P σ f (c⁻¹ * x) := rfl

@[simp]
theorem conjugateSmoothInducedEquiv_symm_eval (c : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = c * p * c⁻¹) (hστ : ∀ p : P, τ (e p) = σ p)
    (h : SmoothFunctions Q τ) (x : G) :
    eval P σ ((conjugateSmoothInducedEquiv c e he hστ).symm h) x = eval Q τ h (c * x) := rfl

/-- The equivalence preserves exactly the uniform open right stabilizers. -/
theorem conjugateSmoothInducedEquiv_stabilizer_iff (c : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = c * p * c⁻¹) (hστ : ∀ p : P, τ (e p) = σ p)
    (f : SmoothFunctions P σ) (K : OpenSubgroup G) :
    (∀ (k : K) (x : G), eval Q τ (conjugateSmoothInducedEquiv c e he hστ f) (x * (k : G)) =
        eval Q τ (conjugateSmoothInducedEquiv c e he hστ f) x) ↔
      ∀ (k : K) (x : G), eval P σ f (x * (k : G)) = eval P σ f x := by
  constructor
  · intro h k x
    have hx := h k (c * x)
    change eval P σ f (c⁻¹ * (c * x * (k : G))) = eval P σ f (c⁻¹ * (c * x)) at hx
    simpa only [mul_assoc, inv_mul_cancel_left] using hx
  · exact translateSmoothFunction_stabilizer c⁻¹ e (conjugate_apply_inv c e he) hστ f K

/-- Postcomposition by an intertwiner commutes with conjugate transport. -/
theorem conjugateSmoothInducedEquiv_naturality {W : Type*} [AddCommGroup W] [Module R W]
    {σ' : Representation R P W} {τ' : Representation R Q W}
    (c : G) (e : P ≃* Q) (he : ∀ p : P, (e p : G) = c * p * c⁻¹)
    (hστ : ∀ p : P, τ (e p) = σ p) (hστ' : ∀ p : P, τ' (e p) = σ' p)
    (φ : σ.IntertwiningMap σ') (ψ : τ.IntertwiningMap τ')
    (hφψ : ∀ v : V, ψ v = φ v) :
    (smoothInducedMap Q ψ).comp (conjugateSmoothInducedEquiv c e he hστ).toIntertwiningMap =
      (conjugateSmoothInducedEquiv c e he hστ').toIntertwiningMap.comp
        (smoothInducedMap P φ) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact hφψ _

end Langlands.Induction

namespace Langlands.Exponents.ConjugateBlockPair

universe uR

variable {n : ℕ} {R : Type uR} [CommRing R] (P : ConjugateBlockPair n R)

/-- Membership in the actual conjugate parabolic `c * B.parabolic * c⁻¹`. -/
theorem mem_parabolic_iff (g : GeneralLinear n R) :
    g ∈ P.parabolic ↔ P.conjugator⁻¹ * g * P.conjugator ∈ P.shape.parabolic R := by
  unfold parabolic
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change P.conjugator⁻¹ * (P.conjugator * y * P.conjugator⁻¹) * P.conjugator ∈ _
    simpa [mul_assoc] using hy
  · intro h
    refine ⟨_, h, ?_⟩
    change P.conjugator * (P.conjugator⁻¹ * g * P.conjugator) * P.conjugator⁻¹ = g
    simp [mul_assoc]

/-- Conjugation `p ↦ c * p * c⁻¹` from the standard upper block parabolic onto the
actual conjugate parabolic, with inverse `q ↦ c⁻¹ * q * c`. -/
def parabolicEquiv : P.shape.parabolic R ≃* P.parabolic where
  toFun p := ⟨P.conjugator * p * P.conjugator⁻¹, by
    rw [mem_parabolic_iff]
    simp [mul_assoc]⟩
  invFun q := ⟨P.conjugator⁻¹ * q * P.conjugator, (P.mem_parabolic_iff q).mp q.property⟩
  left_inv p := by
    apply Subtype.ext
    change P.conjugator⁻¹ * (P.conjugator * p * P.conjugator⁻¹) * P.conjugator = p
    simp [mul_assoc]
  right_inv q := by
    apply Subtype.ext
    change P.conjugator * (P.conjugator⁻¹ * q * P.conjugator) * P.conjugator⁻¹ = q
    simp [mul_assoc]
  map_mul' p p' := by
    apply Subtype.ext
    change P.conjugator * ((p : GeneralLinear n R) * p') * P.conjugator⁻¹ =
      P.conjugator * p * P.conjugator⁻¹ * (P.conjugator * p' * P.conjugator⁻¹)
    simp [mul_assoc]

@[simp]
theorem parabolicEquiv_apply (p : P.shape.parabolic R) :
    (P.parabolicEquiv p : GeneralLinear n R) = P.conjugator * p * P.conjugator⁻¹ := rfl

@[simp]
theorem parabolicEquiv_symm_apply (q : P.parabolic) :
    (P.parabolicEquiv.symm q : GeneralLinear n R) = P.conjugator⁻¹ * q * P.conjugator := rfl

/-- The actual conjugate Levi embedding `m ↦ c * m * c⁻¹`. -/
def leviEmbedding : P.shape.Levi R →* GeneralLinear n R :=
  (MulAut.conj P.conjugator).toMonoidHom.comp (P.shape.leviEmbedding R)

@[simp]
theorem leviEmbedding_apply (m : P.shape.Levi R) :
    P.leviEmbedding m = P.conjugator * P.shape.leviEmbedding R m * P.conjugator⁻¹ := rfl

theorem leviEmbedding_injective : Function.Injective P.leviEmbedding :=
  (MulAut.conj P.conjugator).injective.comp (P.shape.leviEmbedding_injective R)

/-- The conjugate Levi embedding, valued in the actual conjugate parabolic. -/
def leviInParabolic : P.shape.Levi R →* P.parabolic :=
  P.parabolicEquiv.toMonoidHom.comp (P.shape.leviInParabolic R)

@[simp]
theorem leviInParabolic_val (m : P.shape.Levi R) :
    (P.leviInParabolic m : GeneralLinear n R) = P.leviEmbedding m := rfl

/-- The Levi projection of the conjugate parabolic: the standard block projection
of `c⁻¹ * q * c`. -/
def leviProjection : P.parabolic →* P.shape.Levi R :=
  (P.shape.leviProjection R).comp P.parabolicEquiv.symm.toMonoidHom

theorem leviProjection_apply (q : P.parabolic) :
    P.leviProjection q = P.shape.leviProjection R
      ⟨P.conjugator⁻¹ * q * P.conjugator, (P.mem_parabolic_iff q).mp q.property⟩ := rfl

@[simp]
theorem leviProjection_parabolicEquiv (p : P.shape.parabolic R) :
    P.leviProjection (P.parabolicEquiv p) = P.shape.leviProjection R p := by
  change P.shape.leviProjection R (P.parabolicEquiv.symm (P.parabolicEquiv p)) = _
  rw [MulEquiv.symm_apply_apply]

@[simp]
theorem leviProjection_section (m : P.shape.Levi R) :
    P.leviProjection (P.leviInParabolic m) = m := by
  change P.leviProjection (P.parabolicEquiv (P.shape.leviInParabolic R m)) = m
  rw [leviProjection_parabolicEquiv, GeneralLinear.BlockShape.leviProjection_section]

/-- The actual embedded Levi subgroup of the conjugate parabolic. -/
def leviSubgroup : Subgroup (GeneralLinear n R) :=
  P.leviEmbedding.range

theorem leviSubgroup_le_parabolic : P.leviSubgroup ≤ P.parabolic := by
  rintro _ ⟨m, rfl⟩
  exact (P.leviInParabolic m).property

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- Conjugation by `c` is a topological isomorphism of the parabolic subgroups. -/
def parabolicEquivContinuous : P.shape.parabolic R ≃ₜ* P.parabolic where
  toMulEquiv := P.parabolicEquiv
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- The conjugate Levi embedding is continuous. -/
def leviEmbeddingContinuous :
    ContinuousMonoidHom (P.shape.Levi R) (GeneralLinear n R) where
  toMonoidHom := P.leviEmbedding
  continuous_toFun :=
    (continuous_const.mul (P.shape.leviEmbeddingContinuous R).continuous).mul continuous_const

/-- The conjugate Levi projection is continuous. -/
def leviProjectionContinuous : ContinuousMonoidHom P.parabolic (P.shape.Levi R) where
  toMonoidHom := P.leviProjection
  continuous_toFun :=
    (P.shape.leviProjectionContinuous R).continuous.comp
      P.parabolicEquivContinuous.symm.continuous

/-- The conjugate Levi section is continuous for the subgroup topology. -/
def leviInParabolicContinuous : ContinuousMonoidHom (P.shape.Levi R) P.parabolic where
  toMonoidHom := P.leviInParabolic
  continuous_toFun := P.leviEmbeddingContinuous.continuous.subtype_mk _

end Topology

section Induction

universe uF uV uW uX

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable (Q : ConjugateBlockPair n F)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

/-- A smooth Levi character, inflated along the conjugate Levi projection. -/
def inflateCharacter (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F)) :
    Induction.SmoothCharacter ℂ Q.parabolic where
  toMonoidHom := χ.toMonoidHom.comp Q.leviProjection
  isOpen_ker := χ.isOpen_ker.preimage Q.leviProjectionContinuous.continuous

@[simp]
theorem inflateCharacter_apply (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (q : Q.parabolic) :
    (Q.inflateCharacter χ).toMonoidHom q = χ.toMonoidHom (Q.leviProjection q) := rfl

/-- The inducing representation of the conjugate parabolic: the Levi action inflated
along the conjugate projection and twisted by the inflated normalizing character. -/
abbrev inducingRepresentation (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V) : Representation ℂ Q.parabolic V :=
  twist (Q.inflateCharacter χ).toMonoidHom (σ.comp Q.leviProjection)

/-- Conjugation matches the conjugate inducing representation with the standard one. -/
theorem inducingRepresentation_parabolicEquiv
    (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V) (p : Q.shape.parabolic F) :
    Q.inducingRepresentation χ σ (Q.parabolicEquiv p) =
      Q.shape.inducingRepresentation χ σ p := by
  change (χ.toMonoidHom (Q.leviProjection (Q.parabolicEquiv p)) : ℂ) •
      σ (Q.leviProjection (Q.parabolicEquiv p)) =
    (χ.toMonoidHom (Q.shape.leviProjection F p) : ℂ) • σ (Q.shape.leviProjection F p)
  rw [leviProjection_parabolicEquiv]

/-- Normalized induction from the actual conjugate parabolic, for a supplied
normalizing Levi character. -/
def normalizedInducedOf (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V) :
    Representation ℂ (GeneralLinear n F)
      (Induction.SmoothFunctions Q.parabolic (Q.inducingRepresentation χ σ)) :=
  Induction.normalizedSmoothInduced Q.parabolic (Q.inflateCharacter χ)
    (σ.comp Q.leviProjection)

/-- The covariance `f (q g) = χ (m q) • σ (m q) (f g)`, where `m` is the conjugate
Levi projection. -/
theorem normalizedInducedOf_covariant (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V)
    (f : Induction.SmoothFunctions Q.parabolic (Q.inducingRepresentation χ σ))
    (q : Q.parabolic) (g : GeneralLinear n F) :
    Induction.eval Q.parabolic (Q.inducingRepresentation χ σ) f ((q : GeneralLinear n F) * g) =
      (χ.toMonoidHom (Q.leviProjection q) : ℂ) •
        σ (Q.leviProjection q)
          (Induction.eval Q.parabolic (Q.inducingRepresentation χ σ) f g) :=
  f.1.2 q g

/-- The group acts by right translation. -/
@[simp]
theorem normalizedInducedOf_apply (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V) (g : GeneralLinear n F)
    (f : Induction.SmoothFunctions Q.parabolic (Q.inducingRepresentation χ σ))
    (x : GeneralLinear n F) :
    Induction.eval Q.parabolic (Q.inducingRepresentation χ σ)
        (Q.normalizedInducedOf χ σ g f) x =
      Induction.eval Q.parabolic (Q.inducingRepresentation χ σ) f (x * g) := rfl

theorem isSmooth_normalizedInducedOf (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V) :
    IsSmooth (Q.normalizedInducedOf χ σ) :=
  Induction.smoothInduced_smooth _ _

/-- An actual Levi intertwiner, inflated and twisted to the conjugate inducing data. -/
def inducingMap (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    {σ : Representation ℂ (Q.shape.Levi F) V} {τ : Representation ℂ (Q.shape.Levi F) W}
    (f : σ.IntertwiningMap τ) :
    (Q.inducingRepresentation χ σ).IntertwiningMap (Q.inducingRepresentation χ τ) :=
  twistIntertwining _
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun q => f.isIntertwining' (Q.leviProjection q) }

/-- Conjugate normalized induction of an actual Levi intertwiner, by postcomposition. -/
def normalizedInducedOfMap (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    {σ : Representation ℂ (Q.shape.Levi F) V} {τ : Representation ℂ (Q.shape.Levi F) W}
    (f : σ.IntertwiningMap τ) :
    (Q.normalizedInducedOf χ σ).IntertwiningMap (Q.normalizedInducedOf χ τ) :=
  Induction.smoothInducedMap Q.parabolic (Q.inducingMap χ f)

@[simp]
theorem normalizedInducedOfMap_apply (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    {σ : Representation ℂ (Q.shape.Levi F) V} {τ : Representation ℂ (Q.shape.Levi F) W}
    (f : σ.IntertwiningMap τ)
    (φ : Induction.SmoothFunctions Q.parabolic (Q.inducingRepresentation χ σ))
    (x : GeneralLinear n F) :
    Induction.eval Q.parabolic (Q.inducingRepresentation χ τ)
        (Q.normalizedInducedOfMap χ f φ) x =
      f (Induction.eval Q.parabolic (Q.inducingRepresentation χ σ) φ x) := rfl

@[simp]
theorem normalizedInducedOfMap_id (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V) :
    Q.normalizedInducedOfMap χ (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (Q.normalizedInducedOf χ σ) := by
  ext φ x
  rfl

@[simp]
theorem normalizedInducedOfMap_comp (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    {σ : Representation ℂ (Q.shape.Levi F) V} {τ : Representation ℂ (Q.shape.Levi F) W}
    {υ : Representation ℂ (Q.shape.Levi F) X}
    (f : σ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    Q.normalizedInducedOfMap χ (g.comp f) =
      (Q.normalizedInducedOfMap χ g).comp (Q.normalizedInducedOfMap χ f) := by
  ext φ x
  rfl

/-- Conjugate normalized induction as a functor between the canonical smooth
categories of the actual Levi and the actual general linear group. -/
def normalizedInductionFunctorOf (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F)) :
    SmoothRep.{0, uF, uV} ℂ (Q.shape.Levi F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) where
  obj A := SmoothRep.of (Q.normalizedInducedOf χ A.representation)
    (Q.isSmooth_normalizedInducedOf χ A.representation)
  map f := SmoothRep.ofHom (Q.normalizedInducedOfMap χ (SmoothRep.hom f))
  map_id A := by
    ext φ x
    rfl
  map_comp f g := by
    ext φ x
    rfl

/-- Left translation by `c⁻¹` from standard normalized parabolic induction to
normalized induction from the actual conjugate parabolic, with inverse left
translation by `c`. -/
def conjugateInducedEquiv (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V) :
    (Q.shape.normalizedInducedOf χ σ).Equiv (Q.normalizedInducedOf χ σ) :=
  Induction.conjugateSmoothInducedEquiv Q.conjugator Q.parabolicEquiv Q.parabolicEquiv_apply
    (Q.inducingRepresentation_parabolicEquiv χ σ)

@[simp]
theorem conjugateInducedEquiv_eval (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V)
    (f : Induction.SmoothFunctions (Q.shape.parabolic F) (Q.shape.inducingRepresentation χ σ))
    (x : GeneralLinear n F) :
    Induction.eval Q.parabolic (Q.inducingRepresentation χ σ) (Q.conjugateInducedEquiv χ σ f) x =
      Induction.eval (Q.shape.parabolic F) (Q.shape.inducingRepresentation χ σ) f
        (Q.conjugator⁻¹ * x) := rfl

@[simp]
theorem conjugateInducedEquiv_symm_eval (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    (σ : Representation ℂ (Q.shape.Levi F) V)
    (h : Induction.SmoothFunctions Q.parabolic (Q.inducingRepresentation χ σ))
    (x : GeneralLinear n F) :
    Induction.eval (Q.shape.parabolic F) (Q.shape.inducingRepresentation χ σ)
        ((Q.conjugateInducedEquiv χ σ).symm h) x =
      Induction.eval Q.parabolic (Q.inducingRepresentation χ σ) h (Q.conjugator * x) := rfl

/-- Conjugate transport commutes with the induced maps of Levi intertwiners. -/
theorem conjugateInducedEquiv_naturality (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F))
    {σ : Representation ℂ (Q.shape.Levi F) V} {τ : Representation ℂ (Q.shape.Levi F) W}
    (f : σ.IntertwiningMap τ) :
    (Q.normalizedInducedOfMap χ f).comp (Q.conjugateInducedEquiv χ σ).toIntertwiningMap =
      (Q.conjugateInducedEquiv χ τ).toIntertwiningMap.comp
        (Q.shape.normalizedInducedOfMap χ f) := by
  ext φ x
  rfl

/-- Conjugate transport as a natural isomorphism of induction functors into the
canonical smooth category. -/
def conjugateInductionIso (χ : Induction.SmoothCharacter ℂ (Q.shape.Levi F)) :
    Q.shape.normalizedInductionFunctorOf χ ≅
      (Q.normalizedInductionFunctorOf χ : SmoothRep.{0, uF, uV} ℂ (Q.shape.Levi F) ⥤ _) :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (Q.conjugateInducedEquiv χ A.representation))
    (fun f => by
      ext φ
      rfl)

end Induction

end Langlands.Exponents.ConjugateBlockPair

namespace Langlands.PadicField.TopologicalData

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (P : Exponents.ConjugateBlockPair n F.Carrier)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The positive half `δ_B^(1/2)` of the published upper block modulus, transported
to the actual conjugate parabolic along its Levi projection. -/
def conjugateParabolicHalfModulus : P.parabolic →* ℂˣ :=
  (T.leviHalfModulus P.shape).comp P.leviProjection

@[simp]
theorem conjugateParabolicHalfModulus_apply (g : P.parabolic) :
    T.conjugateParabolicHalfModulus P g = T.leviHalfModulus P.shape (P.leviProjection g) := rfl

@[simp]
theorem conjugateParabolicHalfModulus_parabolicEquiv (g : P.shape.parabolic F.Carrier) :
    T.conjugateParabolicHalfModulus P (P.parabolicEquiv g) = T.parabolicHalfModulus P.shape g := by
  simp

@[simp]
theorem conjugateParabolicHalfModulus_section (m : P.shape.Levi F.Carrier) :
    T.conjugateParabolicHalfModulus P (P.leviInParabolic m) = T.leviHalfModulus P.shape m := by
  simp

theorem isOpen_ker_conjugateParabolicHalfModulus :
    letI := T.topology
    IsOpen ((T.conjugateParabolicHalfModulus P).ker : Set P.parabolic) := by
  let := T.topology
  let := T.isTopologicalRing
  exact (T.isOpen_ker_leviHalfModulus P.shape).preimage P.leviProjectionContinuous.continuous

/-- Normalized induction from the actual conjugate parabolic for an actual p-adic
field: smooth induction by right translation of the transported `δ_B^(1/2) ⊗ σ`. -/
def normalizedConjugateParabolicInduced (σ : Representation ℂ (P.shape.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  P.normalizedInducedOf (T.leviHalfCharacter P.shape) σ

/-- The covariance `f (q x) = δ_B(m)^(1/2) σ(m) f(x)` with `m` the conjugate Levi
projection of `q`. -/
theorem normalizedConjugateParabolicInduced_covariant
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)))
    (g : P.parabolic) (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
        f ((g : GeneralLinear n F.Carrier) * x) =
      (T.leviHalfModulus P.shape (P.leviProjection g) : ℂ) •
        σ (P.leviProjection g)
          (Induction.eval P.parabolic
            (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)) f x) :=
  f.1.2 g x

/-- The conjugate induced representation acts by right translation. -/
@[simp]
theorem normalizedConjugateParabolicInduced_apply
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (g : GeneralLinear n F.Carrier)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
        (T.normalizedConjugateParabolicInduced P σ g f) x =
      Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)) f (x * g) := rfl

theorem isSmooth_normalizedConjugateParabolicInduced
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedConjugateParabolicInduced P σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact P.isSmooth_normalizedInducedOf (T.leviHalfCharacter P.shape) σ

/-- The induced map of an actual Levi intertwiner. -/
def normalizedConjugateParabolicInducedMap {σ : Representation ℂ (P.shape.Levi F.Carrier) V}
    {τ : Representation ℂ (P.shape.Levi F.Carrier) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedConjugateParabolicInduced P σ).IntertwiningMap
      (T.normalizedConjugateParabolicInduced P τ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  P.normalizedInducedOfMap (T.leviHalfCharacter P.shape) f

/-- The induced map is postcomposition with the given Levi intertwiner. -/
@[simp]
theorem normalizedConjugateParabolicInducedMap_apply
    {σ : Representation ℂ (P.shape.Levi F.Carrier) V}
    {τ : Representation ℂ (P.shape.Levi F.Carrier) W} (f : σ.IntertwiningMap τ)
    (φ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (τ.comp P.leviProjection))
        (T.normalizedConjugateParabolicInducedMap P f φ) x =
      f (Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)) φ x) := rfl

@[simp]
theorem normalizedConjugateParabolicInducedMap_id
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedConjugateParabolicInducedMap P (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (T.normalizedConjugateParabolicInduced P σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact P.normalizedInducedOfMap_id (T.leviHalfCharacter P.shape) σ

@[simp]
theorem normalizedConjugateParabolicInducedMap_comp
    {σ : Representation ℂ (P.shape.Levi F.Carrier) V}
    {τ : Representation ℂ (P.shape.Levi F.Carrier) W}
    {υ : Representation ℂ (P.shape.Levi F.Carrier) X}
    (f : σ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedConjugateParabolicInducedMap P (g.comp f) =
      (T.normalizedConjugateParabolicInducedMap P g).comp
        (T.normalizedConjugateParabolicInducedMap P f) := by
  let := T.topology
  let := T.isTopologicalRing
  exact P.normalizedInducedOfMap_comp (T.leviHalfCharacter P.shape) f g

/-- Conjugate normalized induction as a functor of canonical smooth categories. -/
def normalizedConjugateParabolicInductionFunctor :
    letI := T.leviTopology P.shape
    letI := T.generalLinearTopology n
    SmoothRep.{0, uF, uV} ℂ (P.shape.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := T.isTopologicalRing
  P.normalizedInductionFunctorOf (T.leviHalfCharacter P.shape)

/-- Left translation `f ↦ (x ↦ f (c⁻¹ * x))` from standard normalized parabolic
induction to normalized induction from the actual conjugate parabolic. -/
def conjugateParabolicInducedEquiv (σ : Representation ℂ (P.shape.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced P.shape σ).Equiv (T.normalizedConjugateParabolicInduced P σ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  P.conjugateInducedEquiv (T.leviHalfCharacter P.shape) σ

@[simp]
theorem conjugateParabolicInducedEquiv_eval (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
        (T.conjugateParabolicInducedEquiv P σ f) x =
      Induction.eval (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier)))
        f (P.conjugator⁻¹ * x) := rfl

@[simp]
theorem conjugateParabolicInducedEquiv_symm_eval
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (h : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier)))
        ((T.conjugateParabolicInducedEquiv P σ).symm h) x =
      Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
        h (P.conjugator * x) := rfl

/-- The translated function is covariant for the actual conjugate parabolic. -/
theorem conjugateParabolicInducedEquiv_covariant
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier))))
    (g : P.parabolic) (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
        (T.conjugateParabolicInducedEquiv P σ f) ((g : GeneralLinear n F.Carrier) * x) =
      (T.leviHalfModulus P.shape (P.leviProjection g) : ℂ) •
        σ (P.leviProjection g)
          (Induction.eval P.parabolic
            (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
            (T.conjugateParabolicInducedEquiv P σ f) x) :=
  T.normalizedConjugateParabolicInduced_covariant P σ _ g x

theorem conjugateParabolicInducedEquiv_symm_apply_apply
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier)))) :
    (T.conjugateParabolicInducedEquiv P σ).symm (T.conjugateParabolicInducedEquiv P σ f) = f :=
  Representation.Equiv.symm_apply_apply _ f

theorem conjugateParabolicInducedEquiv_apply_symm_apply
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (h : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))) :
    T.conjugateParabolicInducedEquiv P σ ((T.conjugateParabolicInducedEquiv P σ).symm h) = h :=
  Representation.Equiv.apply_symm_apply _ h

/-- The transport intertwines the ambient right-translation actions. -/
theorem conjugateParabolicInducedEquiv_intertwining
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V) (g : GeneralLinear n F.Carrier)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier)))) :
    T.conjugateParabolicInducedEquiv P σ (T.normalizedParabolicInduced P.shape σ g f) =
      T.normalizedConjugateParabolicInduced P σ g (T.conjugateParabolicInducedEquiv P σ f) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (T.conjugateParabolicInducedEquiv P σ).toIntertwiningMap g f

/-- The equivalence preserves exactly the uniform open right stabilizers. -/
theorem conjugateParabolicInducedEquiv_stabilizer_iff
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier))))
    (K : letI := T.generalLinearTopology n
      OpenSubgroup (GeneralLinear n F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (∀ (k : K) (x : GeneralLinear n F.Carrier),
        Induction.eval P.parabolic
            (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
            (T.conjugateParabolicInducedEquiv P σ f) (x * (k : GeneralLinear n F.Carrier)) =
          Induction.eval P.parabolic
            (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
            (T.conjugateParabolicInducedEquiv P σ f) x) ↔
      ∀ (k : K) (x : GeneralLinear n F.Carrier),
        Induction.eval (P.shape.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier)))
            f (x * (k : GeneralLinear n F.Carrier)) =
          Induction.eval (P.shape.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier)))
            f x := by
  let := T.topology
  let := T.isTopologicalRing
  exact Induction.conjugateSmoothInducedEquiv_stabilizer_iff P.conjugator P.parabolicEquiv
    P.parabolicEquiv_apply (P.inducingRepresentation_parabolicEquiv (T.leviHalfCharacter P.shape) σ)
    f K

/-- Conjugate transport commutes with the induced maps of Levi intertwiners. -/
theorem conjugateParabolicInducedEquiv_naturality
    {σ : Representation ℂ (P.shape.Levi F.Carrier) V}
    {τ : Representation ℂ (P.shape.Levi F.Carrier) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedConjugateParabolicInducedMap P f).comp
        (T.conjugateParabolicInducedEquiv P σ).toIntertwiningMap =
      (T.conjugateParabolicInducedEquiv P τ).toIntertwiningMap.comp
        (T.normalizedParabolicInducedMap P.shape f) := by
  let := T.topology
  let := T.isTopologicalRing
  exact P.conjugateInducedEquiv_naturality (T.leviHalfCharacter P.shape) f

/-- Conjugate transport as a natural isomorphism of p-adic induction functors. -/
def conjugateParabolicInductionIso :
    letI := T.leviTopology P.shape
    letI := T.generalLinearTopology n
    T.normalizedParabolicInductionFunctor P.shape ≅
      (T.normalizedConjugateParabolicInductionFunctor P :
        SmoothRep.{0, uF, uV} ℂ (P.shape.Levi F.Carrier) ⥤ _) :=
  letI := T.topology
  letI := T.isTopologicalRing
  P.conjugateInductionIso (T.leviHalfCharacter P.shape)

end Langlands.PadicField.TopologicalData

namespace Langlands.PadicField

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {n : ℕ} (P : Exponents.ConjugateBlockPair n F.Carrier)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Conjugate normalized induction for the canonical realization of every algebraic
p-adic field. -/
abbrev canonicalNormalizedConjugateParabolicInduced
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V) :=
  F.canonicalTopologicalData.normalizedConjugateParabolicInduced P σ

/-- The canonical conjugate normalized induction functor. -/
abbrev canonicalNormalizedConjugateParabolicInductionFunctor :
    letI := F.canonicalLeviTopology P.shape
    letI := F.canonicalGeneralLinearTopology n
    SmoothRep.{0, uF, uV} ℂ (P.shape.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.normalizedConjugateParabolicInductionFunctor P

/-- The canonical conjugate transport equivalence. -/
abbrev canonicalConjugateParabolicInducedEquiv
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V) :=
  F.canonicalTopologicalData.conjugateParabolicInducedEquiv P σ

end Langlands.PadicField

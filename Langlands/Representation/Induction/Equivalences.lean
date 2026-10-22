import Langlands.Representation.Induction.Parabolic

/-!
# Transport of smooth induction along representation equivalences

Postcomposition by an equivalence transports smooth induced functions, including
between independent carrier universes. Normalized parabolic induction specializes
this construction after inflation and the common character twist.
-/

noncomputable section

namespace Langlands.Induction

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Postcomposition by an injective intertwiner is injective on smooth induction. -/
theorem smoothInducedMap_injective (P : Subgroup G)
    {σ : Representation R P V} {τ : Representation R P W}
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) :
    Function.Injective (smoothInducedMap P f) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply hf
  exact congrArg (fun z => eval P τ z g) h

/-- Smooth induction of an equivalence acts by postcomposition, with inverse
postcomposition by the inverse equivalence. -/
def smoothInducedEquiv (P : Subgroup G)
    {σ : Representation R P V} {τ : Representation R P W}
    (e : σ.Equiv τ) : (smoothInduced P σ).Equiv (smoothInduced P τ) where
  toLinearMap := (smoothInducedMap P e.toIntertwiningMap).toLinearMap
  invFun := smoothInducedMap P e.symm.toIntertwiningMap
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change e.symm (e (eval P σ f g)) = eval P σ f g
    exact e.symm_apply_apply _
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change e (e.symm (eval P τ f g)) = eval P τ f g
    exact e.apply_symm_apply _
  isIntertwining' := (smoothInducedMap P e.toIntertwiningMap).isIntertwining'

@[simp]
theorem smoothInducedEquiv_eval (P : Subgroup G)
    {σ : Representation R P V} {τ : Representation R P W}
    (e : σ.Equiv τ) (f : SmoothFunctions P σ) (g : G) :
    eval P τ (smoothInducedEquiv P e f) g = e (eval P σ f g) := rfl

end Langlands.Induction

namespace Langlands.PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- An injective Levi map remains injective after normalized parabolic induction. -/
theorem normalizedParabolicInducedMap_injective
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Function.Injective (T.normalizedParabolicInducedMap B f) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply hf
  exact congrArg (fun z => z.1.1 g) h

/-- Normalize, inflate, and induce an actual Levi equivalence. The two Levi
representation carriers may lie in independent universes. -/
def normalizedParabolicInducedEquiv
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (e : σ.Equiv τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B σ).Equiv (T.normalizedParabolicInduced B τ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.smoothInducedEquiv (B.parabolic F.Carrier)
    (twistEquiv (T.parabolicHalfModulus B)
      (Representation.Equiv.mk e.toLinearEquiv
        (fun g => e.isIntertwining' (B.leviProjection F.Carrier g))))

@[simp]
theorem normalizedParabolicInducedEquiv_eval
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (e : σ.Equiv τ)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))))
    (g : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (T.normalizedParabolicInducedEquiv B e f) g =
      e (Induction.eval _ _ f g) := rfl

end Langlands.PadicField.TopologicalData

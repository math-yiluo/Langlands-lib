import Langlands.Representation.Derivative.MirabolicCharacter
import Langlands.Representation.Category.Twist
import Langlands.Representation.Twist.RealPower
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Group.GL.NormalizedCharacter

/-!
# Mirabolic minus localization functors

The unnormalized Bernstein–Zelevinsky functors `Ψ⁻ : P_(n+1) → GL_n` and
`Φ⁻ : P_(n+2) → P_(n+1)` act on the actual character-localized quotients by the
actual radicals. Their determinant-normalized versions twist the descended action by
the inverse half power of the residue-normalized determinant character. No Haar
automorphism modulus is identified with that character here.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uR uG uH uV uF

section Pullback

variable {R : Type uR} {G : Type uG} {H : Type uH} [CommRing R]
variable [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The same intertwiner, viewed between the restrictions along `φ`. -/
def continuousPullbackMap (φ : H →* G) {V W : Type uV} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {ρ : Representation R G V} {σ : Representation R G W}
    (f : ρ.IntertwiningMap σ) :
    Representation.IntertwiningMap (ρ.comp φ) (σ.comp φ) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := f.isIntertwining' (φ h)

/-- Restriction of a smooth representation along a continuous homomorphism. -/
abbrev continuousPullback (φ : H →* G) (hφ : Continuous φ)
    (A : SmoothRep.{uR, uG, uV} R G) : SmoothRep.{uR, uH, uV} R H :=
  SmoothRep.of (A.representation.comp φ) (isSmooth_comp φ hφ A.isSmooth)

/-- Restriction along a continuous homomorphism, with unchanged carriers and linear maps. -/
def continuousPullbackFunctor (φ : H →* G) (hφ : Continuous φ) :
    SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uH, uV} R H where
  obj A := continuousPullback φ hφ A
  map f := SmoothRep.ofHom (continuousPullbackMap φ (SmoothRep.hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

end Pullback

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Unnormalized Psi-minus -/

/-- Unnormalized `Ψ⁻`: localize at the trivial character of `V_(n+1)`, then restrict
the descended Levi action along `GL_n ≃ₜ* leviSubgroup n`. -/
def psiMinusUnnormalized (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  exact Jacquet.Localization.smoothFunctor (radical n F.Carrier) 1 (leviSubgroup n F.Carrier)
      leviSubgroup_le_normalizer
      (Jacquet.Localization.isInvariant_one _ _ leviSubgroup_le_normalizer) ⋙
    continuousPullbackFunctor (leviContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
      (leviContinuousEquiv (n := n) (F := F.Carrier)).continuous

/-- The canonical quotient map onto the actual `Ψ⁻` carrier. -/
abbrev psiMinusQuotient (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      A →ₗ[ℂ] Jacquet.Localization.Coinvariants A.representation (radical n F.Carrier) 1 := by
  letI := T.topology
  exact fun A => Jacquet.Localization.mk A.representation (radical n F.Carrier) 1

/-- The object carrier is the actual coinvariant quotient by `V_(n+1)`. -/
theorem psiMinusUnnormalized_obj_carrier (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      ((psiMinusUnnormalized T n).obj A : Type uV) =
        Jacquet.Localization.Coinvariants A.representation (radical n F.Carrier) 1 := by
  intros
  rfl

/-- The object action is the descended Levi-range action composed with `leviEquiv`. -/
theorem psiMinusUnnormalized_obj_representation (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      ((psiMinusUnnormalized T n).obj A).representation =
        (Jacquet.Localization.action A.representation (radical n F.Carrier) 1
          (leviSubgroup n F.Carrier) leviSubgroup_le_normalizer
          (Jacquet.Localization.isInvariant_one _ _ leviSubgroup_le_normalizer)).comp
          (leviEquiv (n := n) (F := F.Carrier)).toMonoidHom := by
  intros
  rfl

theorem psiMinusQuotient_surjective (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      Function.Surjective (psiMinusQuotient T n A) := by
  let := T.topology
  intro A
  exact Jacquet.Localization.mk_surjective A.representation (radical n F.Carrier) 1

theorem ker_psiMinusQuotient (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      LinearMap.ker (psiMinusQuotient T n A) =
        Jacquet.Localization.relations A.representation (radical n F.Carrier) 1 := by
  let := T.topology
  intro A
  exact Jacquet.Localization.ker_mk A.representation (radical n F.Carrier) 1

/-- Radical elements act trivially on `Ψ⁻` quotient classes. -/
theorem psiMinusQuotient_radical (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (u : radical n F.Carrier) (v : A),
      psiMinusQuotient T n A (A.representation (u : mirabolic n F.Carrier) v) =
        psiMinusQuotient T n A v := by
  let := T.topology
  intro A u v
  rw [Jacquet.Localization.mk_apply_subgroup]
  simp

/-- `g • q(v) = q(levi g • v)` for unnormalized `Ψ⁻`. -/
theorem psiMinusUnnormalized_action (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : GeneralLinear n F.Carrier)
      (v : A),
      ((psiMinusUnnormalized T n).obj A).representation g (psiMinusQuotient T n A v) =
        psiMinusQuotient T n A (A.representation (levi g) v) := by
  intros
  rfl

theorem psiMinusUnnormalized_isSmooth (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      IsSmooth ((psiMinusUnnormalized T n).obj A).representation := by
  let := T.topology
  intro A
  exact ((psiMinusUnnormalized T n).obj A).isSmooth

/-- On quotient classes, the induced map sends `q_A(v)` to `q_B(f v)`. -/
theorem psiMinusUnnormalized_map_quotient (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : A ⟶ B) (v : A),
      SmoothRep.hom ((psiMinusUnnormalized T n).map f) (psiMinusQuotient T n A v) =
        psiMinusQuotient T n B (SmoothRep.hom f v) := by
  intros
  rfl

theorem psiMinusUnnormalized_map_equivariant (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : A ⟶ B)
      (g : GeneralLinear n F.Carrier) (w : (psiMinusUnnormalized T n).obj A),
      SmoothRep.hom ((psiMinusUnnormalized T n).map f)
          (((psiMinusUnnormalized T n).obj A).representation g w) =
        ((psiMinusUnnormalized T n).obj B).representation g
          (SmoothRep.hom ((psiMinusUnnormalized T n).map f) w) := by
  let := T.topology
  intro A B f g w
  exact Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom ((psiMinusUnnormalized T n).map f)) g w

theorem psiMinusUnnormalized_map_id (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      (psiMinusUnnormalized T n).map (𝟙 A) = 𝟙 ((psiMinusUnnormalized T n).obj A) := by
  let := T.topology
  intro A
  exact (psiMinusUnnormalized T n).map_id A

theorem psiMinusUnnormalized_map_comp (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B C : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : A ⟶ B) (g : B ⟶ C),
      (psiMinusUnnormalized T n).map (f ≫ g) =
        (psiMinusUnnormalized T n).map f ≫ (psiMinusUnnormalized T n).map g := by
  let := T.topology
  intro A B C f g
  exact (psiMinusUnnormalized T n).map_comp f g

/-! ## Unnormalized Phi-minus -/

/-- Unnormalized `Φ⁻`: localize at `θ_ψ` on `V_(n+2)`, then restrict the descended
successor action along `P_(n+1) ≃ₜ* successorSubgroup n`. -/
def phiMinusUnnormalized (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact Jacquet.Localization.smoothFunctor (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n)
      (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer
      (theta_isInvariant ψ n) ⋙
    continuousPullbackFunctor (successorContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
      (successorContinuousEquiv (n := n) (F := F.Carrier)).continuous

/-- The canonical quotient map onto the actual `Φ⁻` carrier. -/
abbrev phiMinusQuotient (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)) →
      A →ₗ[ℂ] Jacquet.Localization.Coinvariants A.representation (radical (n + 1) F.Carrier)
        (T.mirabolicTheta ψ n) := by
  letI := T.topology
  exact fun A => Jacquet.Localization.mk A.representation (radical (n + 1) F.Carrier)
    (T.mirabolicTheta ψ n)

/-- The object carrier is the actual `θ_ψ`-localized quotient by `V_(n+2)`. -/
theorem phiMinusUnnormalized_obj_carrier (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      ((phiMinusUnnormalized T ψ n).obj A : Type uV) =
        Jacquet.Localization.Coinvariants A.representation (radical (n + 1) F.Carrier)
          (T.mirabolicTheta ψ n) := by
  intros
  rfl

/-- The object action is the descended successor-range action composed with
`successorEquiv`. -/
theorem phiMinusUnnormalized_obj_representation (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      ((phiMinusUnnormalized T ψ n).obj A).representation =
        (Jacquet.Localization.action A.representation (radical (n + 1) F.Carrier)
          (T.mirabolicTheta ψ n) (successorSubgroup n F.Carrier)
          successorSubgroup_le_normalizer (theta_isInvariant ψ n)).comp
          (successorEquiv (n := n) (F := F.Carrier)).toMonoidHom := by
  intros
  rfl

theorem phiMinusQuotient_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      Function.Surjective (phiMinusQuotient T ψ n A) := by
  let := T.topology
  intro A
  exact Jacquet.Localization.mk_surjective A.representation (radical (n + 1) F.Carrier) _

theorem ker_phiMinusQuotient (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      LinearMap.ker (phiMinusQuotient T ψ n A) =
        Jacquet.Localization.relations A.representation (radical (n + 1) F.Carrier)
          (T.mirabolicTheta ψ n) := by
  let := T.topology
  intro A
  exact Jacquet.Localization.ker_mk A.representation (radical (n + 1) F.Carrier) _

/-- Radical elements act on `Φ⁻` quotient classes through `θ_ψ`. -/
theorem phiMinusQuotient_radical (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
      (u : radical (n + 1) F.Carrier) (v : A),
      phiMinusQuotient T ψ n A (A.representation (u : mirabolic (n + 1) F.Carrier) v) =
        (T.mirabolicTheta ψ n u : ℂ) • phiMinusQuotient T ψ n A v := by
  let := T.topology
  intro A u v
  exact Jacquet.Localization.mk_apply_subgroup A.representation _ _ u v

/-- `h • q(v) = q(successor h • v)` for unnormalized `Φ⁻`. -/
theorem phiMinusUnnormalized_action (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
      (h : mirabolic n F.Carrier) (v : A),
      ((phiMinusUnnormalized T ψ n).obj A).representation h (phiMinusQuotient T ψ n A v) =
        phiMinusQuotient T ψ n A (A.representation (successor h) v) := by
  intros
  rfl

theorem phiMinusUnnormalized_isSmooth (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      IsSmooth ((phiMinusUnnormalized T ψ n).obj A).representation := by
  let := T.topology
  intro A
  exact ((phiMinusUnnormalized T ψ n).obj A).isSmooth

/-- On quotient classes, the induced map sends `q_A(v)` to `q_B(f v)`. -/
theorem phiMinusUnnormalized_map_quotient (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)} (f : A ⟶ B) (v : A),
      SmoothRep.hom ((phiMinusUnnormalized T ψ n).map f) (phiMinusQuotient T ψ n A v) =
        phiMinusQuotient T ψ n B (SmoothRep.hom f v) := by
  intros
  rfl

theorem phiMinusUnnormalized_map_equivariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)} (f : A ⟶ B)
      (h : mirabolic n F.Carrier) (w : (phiMinusUnnormalized T ψ n).obj A),
      SmoothRep.hom ((phiMinusUnnormalized T ψ n).map f)
          (((phiMinusUnnormalized T ψ n).obj A).representation h w) =
        ((phiMinusUnnormalized T ψ n).obj B).representation h
          (SmoothRep.hom ((phiMinusUnnormalized T ψ n).map f) w) := by
  let := T.topology
  intro A B f h w
  exact Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom ((phiMinusUnnormalized T ψ n).map f)) h w

theorem phiMinusUnnormalized_map_id (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      (phiMinusUnnormalized T ψ n).map (𝟙 A) = 𝟙 ((phiMinusUnnormalized T ψ n).obj A) := by
  let := T.topology
  intro A
  exact (phiMinusUnnormalized T ψ n).map_id A

theorem phiMinusUnnormalized_map_comp (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {A B C : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)} (f : A ⟶ B)
      (g : B ⟶ C),
      (phiMinusUnnormalized T ψ n).map (f ≫ g) =
        (phiMinusUnnormalized T ψ n).map f ≫ (phiMinusUnnormalized T ψ n).map g := by
  let := T.topology
  intro A B C f g
  exact (phiMinusUnnormalized T ψ n).map_comp f g

/-! ## Determinant normalization -/

/-- The explicit `Ψ⁻` normalization character `|det|^(-1/2)` on `GL_n`. -/
abbrev psiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    GeneralLinear n F.Carrier →* ℂˣ :=
  realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ))

/-- The explicit `Φ⁻` normalization character `|det|^(-1/2)` on `P_(n+1)`. -/
abbrev phiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    mirabolic n F.Carrier →* ℂˣ :=
  realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
    (-(1 / 2 : ℝ))

theorem isOpen_ker_psiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((psiMinusCharacter T n).ker : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact isOpen_ker_realPowerCharacter _ (T.isOpen_ker_determinantNorm n) _

theorem isOpen_ker_phiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((phiMinusCharacter T n).ker : Set (mirabolic n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1)
  apply isOpen_ker_realPowerCharacter
  exact (T.isOpen_ker_determinantNorm (n + 1)).preimage continuous_subtype_val

/-- Determinant-normalized `Ψ⁻`: unnormalized `Ψ⁻` twisted by `|det|^(-1/2)`. -/
def psiMinus (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  exact psiMinusUnnormalized T n ⋙
    SmoothRep.twistFunctor (psiMinusCharacter T n) (isOpen_ker_psiMinusCharacter T n)

/-- Determinant-normalized `Φ⁻`: unnormalized `Φ⁻` twisted by `|det|^(-1/2)`. -/
def phiMinus (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact phiMinusUnnormalized T ψ n ⋙
    SmoothRep.twistFunctor (phiMinusCharacter T n) (isOpen_ker_phiMinusCharacter T n)

theorem psiMinus_eq (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    psiMinus.{uV} T n = psiMinusUnnormalized T n ⋙
      SmoothRep.twistFunctor (psiMinusCharacter T n) (isOpen_ker_psiMinusCharacter T n) :=
  rfl

theorem phiMinus_eq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    phiMinus.{uV} T ψ n = phiMinusUnnormalized T ψ n ⋙
      SmoothRep.twistFunctor (phiMinusCharacter T n) (isOpen_ker_phiMinusCharacter T n) :=
  rfl

/-- The normalized carrier is still the actual coinvariant quotient. -/
theorem psiMinus_obj_carrier (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      ((psiMinus T n).obj A : Type uV) =
        Jacquet.Localization.Coinvariants A.representation (radical n F.Carrier) 1 := by
  intros
  rfl

/-- `g • q(v) = |det g|^(-1/2) q(levi g • v)` for normalized `Ψ⁻`. -/
theorem psiMinus_action (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : GeneralLinear n F.Carrier)
      (v : A),
      ((psiMinus T n).obj A).representation g (psiMinusQuotient T n A v) =
        (realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) g : ℂ) •
          psiMinusQuotient T n A (A.representation (levi g) v) := by
  intros
  rfl

/-- The normalized action is the character value times the unnormalized action. -/
theorem psiMinus_action_eq_smul (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : GeneralLinear n F.Carrier)
      (w : (psiMinusUnnormalized T n).obj A),
      ((psiMinus T n).obj A).representation g w =
        (realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) g : ℂ) •
          ((psiMinusUnnormalized T n).obj A).representation g w := by
  intros
  rfl

/-- The normalized functor keeps the quotient-induced linear maps. -/
theorem psiMinus_map_quotient (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : A ⟶ B) (v : A),
      SmoothRep.hom ((psiMinus T n).map f) (psiMinusQuotient T n A v) =
        psiMinusQuotient T n B (SmoothRep.hom f v) := by
  intros
  rfl

theorem psiMinus_isSmooth (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      IsSmooth ((psiMinus T n).obj A).representation := by
  let := T.topology
  intro A
  exact ((psiMinus T n).obj A).isSmooth

theorem psiMinus_map_equivariant (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : A ⟶ B)
      (g : GeneralLinear n F.Carrier) (w : (psiMinus T n).obj A),
      SmoothRep.hom ((psiMinus T n).map f) (((psiMinus T n).obj A).representation g w) =
        ((psiMinus T n).obj B).representation g (SmoothRep.hom ((psiMinus T n).map f) w) := by
  let := T.topology
  intro A B f g w
  exact Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom ((psiMinus T n).map f)) g w

theorem psiMinus_map_id (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      (psiMinus T n).map (𝟙 A) = 𝟙 ((psiMinus T n).obj A) := by
  let := T.topology
  intro A
  exact (psiMinus T n).map_id A

theorem psiMinus_map_comp (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B C : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : A ⟶ B) (g : B ⟶ C),
      (psiMinus T n).map (f ≫ g) = (psiMinus T n).map f ≫ (psiMinus T n).map g := by
  let := T.topology
  intro A B C f g
  exact (psiMinus T n).map_comp f g

/-- The normalized carrier is still the actual `θ_ψ`-localized quotient. -/
theorem phiMinus_obj_carrier (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      ((phiMinus T ψ n).obj A : Type uV) =
        Jacquet.Localization.Coinvariants A.representation (radical (n + 1) F.Carrier)
          (T.mirabolicTheta ψ n) := by
  intros
  rfl

/-- `h • q(v) = |det h|^(-1/2) q(successor h • v)` for normalized `Φ⁻`. -/
theorem phiMinus_action (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
      (h : mirabolic n F.Carrier) (v : A),
      ((phiMinus T ψ n).obj A).representation h (phiMinusQuotient T ψ n A v) =
        (realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
            (-(1 / 2 : ℝ)) h : ℂ) •
          phiMinusQuotient T ψ n A (A.representation (successor h) v) := by
  intros
  rfl

/-- The normalized action is the character value times the unnormalized action. -/
theorem phiMinus_action_eq_smul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
      (h : mirabolic n F.Carrier) (w : (phiMinusUnnormalized T ψ n).obj A),
      ((phiMinus T ψ n).obj A).representation h w =
        (realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
            (-(1 / 2 : ℝ)) h : ℂ) •
          ((phiMinusUnnormalized T ψ n).obj A).representation h w := by
  intros
  rfl

/-- The normalized functor keeps the quotient-induced linear maps. -/
theorem phiMinus_map_quotient (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)} (f : A ⟶ B) (v : A),
      SmoothRep.hom ((phiMinus T ψ n).map f) (phiMinusQuotient T ψ n A v) =
        phiMinusQuotient T ψ n B (SmoothRep.hom f v) := by
  intros
  rfl

theorem phiMinus_isSmooth (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      IsSmooth ((phiMinus T ψ n).obj A).representation := by
  let := T.topology
  intro A
  exact ((phiMinus T ψ n).obj A).isSmooth

theorem phiMinus_map_equivariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)} (f : A ⟶ B)
      (h : mirabolic n F.Carrier) (w : (phiMinus T ψ n).obj A),
      SmoothRep.hom ((phiMinus T ψ n).map f) (((phiMinus T ψ n).obj A).representation h w) =
        ((phiMinus T ψ n).obj B).representation h
          (SmoothRep.hom ((phiMinus T ψ n).map f) w) := by
  let := T.topology
  intro A B f h w
  exact Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom ((phiMinus T ψ n).map f)) h w

theorem phiMinus_map_id (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      (phiMinus T ψ n).map (𝟙 A) = 𝟙 ((phiMinus T ψ n).obj A) := by
  let := T.topology
  intro A
  exact (phiMinus T ψ n).map_id A

theorem phiMinus_map_comp (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {A B C : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)} (f : A ⟶ B)
      (g : B ⟶ C),
      (phiMinus T ψ n).map (f ≫ g) = (phiMinus T ψ n).map f ≫ (phiMinus T ψ n).map g := by
  let := T.topology
  intro A B C f g
  exact (phiMinus T ψ n).map_comp f g

end Langlands.Derivative.Mirabolic

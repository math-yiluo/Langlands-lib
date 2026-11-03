import Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistStatement
import Langlands.Representation.Derivative.MirabolicDeterminant

/-!
# Proof that general-linear derivatives commute with determinant twists

A character of the ambient group that is trivial on the localizing subgroup leaves the
character-localization relations unchanged, so localization carries the twist to the
restricted character. Restriction along a continuous homomorphism carries a twist to the
pulled-back character, and twists by two characters commute. The determinant is one on
each mirabolic radical and is preserved by the Levi and successor embeddings, so
`|det|^s` passes through restriction, through each normalized `Φ⁻` and `Ψ⁻`, and through
the rank transports, with the same exponent `s` throughout.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uF uV uG uH

namespace DeterminantTwist

/-! ## Pasting commutation squares -/

section Pasting

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Paste two commutation squares `a ⋙ L₁ ≅ L₁ ⋙ b` and `b ⋙ L₂ ≅ L₂ ⋙ c`. -/
def pasteIso {a : C ⥤ C} {b : D ⥤ D} {c : E ⥤ E} {L₁ : C ⥤ D} {L₂ : D ⥤ E}
    (e₁ : a ⋙ L₁ ≅ L₁ ⋙ b) (e₂ : b ⋙ L₂ ≅ L₂ ⋙ c) :
    a ⋙ (L₁ ⋙ L₂) ≅ (L₁ ⋙ L₂) ⋙ c :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ L₂ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L₁ e₂ ≪≫
    (Functor.associator _ _ _).symm

end Pasting

/-! ## Twists, localization and restriction -/

section General

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]

theorem smoothRep_hom_ext {A B : SmoothRep.{0, uG, uV} ℂ G} {f g : A ⟶ B}
    (h : ∀ x, SmoothRep.hom f x = SmoothRep.hom g x) : f = g := by
  have e : SmoothRep.hom f = SmoothRep.hom g :=
    Representation.IntertwiningMap.ext (LinearMap.ext h)
  calc f = SmoothRep.ofHom (SmoothRep.hom f) := rfl
    _ = SmoothRep.ofHom (SmoothRep.hom g) := by rw [e]
    _ = g := rfl

/-- Twists by equal characters are the same functor. -/
def twistCongrIso {χ η : G →* ℂˣ} (h : χ = η) (hχ : IsOpen (χ.ker : Set G))
    (hη : IsOpen (η.ker : Set G)) :
    SmoothRep.twistFunctor.{0, uG, uV} χ hχ ≅ SmoothRep.twistFunctor η hη := by
  subst h
  exact Iso.refl _

/-- Twists by two characters commute. -/
def twistCommIso (χ η : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hη : IsOpen (η.ker : Set G)) :
    SmoothRep.twistFunctor.{0, uG, uV} χ hχ ⋙ SmoothRep.twistFunctor η hη ≅
      SmoothRep.twistFunctor η hη ⋙ SmoothRep.twistFunctor χ hχ :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (equivOfRepresentationEq (by
      change twist η (twist χ A.representation) = twist χ (twist η A.representation)
      rw [twist_twist, twist_twist]
      congr 1
      apply MonoidHom.ext
      intro g
      exact mul_comm (η g) (χ g))))
    (fun _ => smoothRep_hom_ext fun _ => rfl)

/-- Restriction along a continuous homomorphism carries a twist to the pulled-back
character. -/
def pullbackTwistIso (φ : H →* G) (hφ : Continuous φ) (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) (hχφ : IsOpen ((χ.comp φ).ker : Set H)) :
    SmoothRep.twistFunctor.{0, uG, uV} χ hχ ⋙ Mirabolic.continuousPullbackFunctor φ hφ ≅
      Mirabolic.continuousPullbackFunctor φ hφ ⋙ SmoothRep.twistFunctor (χ.comp φ) hχφ :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] in
/-- A character trivial on `U` does not change the `θ`-localization relations. -/
theorem relations_twist (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (χ : G →* ℂˣ) (hU : U ≤ χ.ker) :
    Jacquet.Localization.relations (twist χ ρ) U θ = Jacquet.Localization.relations ρ U θ := by
  have hfun : (fun uv : U × V => twist χ ρ uv.1 uv.2 - (θ uv.1 : ℂ) • uv.2) =
      fun uv : U × V => ρ uv.1 uv.2 - (θ uv.1 : ℂ) • uv.2 := by
    funext uv
    rw [Jacquet.twist_apply_of_le_ker χ ρ hU]
  change Submodule.span ℂ (Set.range _) = Submodule.span ℂ (Set.range _)
  rw [hfun]

/-- The localized quotient of a twist is the twist of the localized quotient by the
restricted character. -/
def localizationTwistEquiv (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
    (hθ : Jacquet.Localization.IsInvariant U M hMU θ) (χ : G →* ℂˣ) (hU : U ≤ χ.ker) :
    (Jacquet.Localization.action (twist χ ρ) U θ M hMU hθ).Equiv
      (twist (χ.comp M.subtype) (Jacquet.Localization.action ρ U θ M hMU hθ)) :=
  Representation.Equiv.mk (Submodule.quotEquivOfEq _ _ (relations_twist ρ U θ χ hU))
    fun m => by
      apply Jacquet.Localization.hom_ext
      refine LinearMap.ext fun v => ?_
      change Jacquet.Localization.mk ρ U θ ((χ m : ℂ) • ρ m v) =
        (χ m : ℂ) • Jacquet.Localization.mk ρ U θ (ρ m v)
      exact map_smul _ _ _

/-- Character localization commutes naturally with a twist trivial on `U`. -/
def localizationTwistIso (U : Subgroup G) (θ : U →* ℂˣ) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (hθ : Jacquet.Localization.IsInvariant U M hMU θ)
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) (hU : U ≤ χ.ker)
    (hχM : IsOpen ((χ.comp M.subtype).ker : Set M)) :
    SmoothRep.twistFunctor.{0, uG, uV} χ hχ ⋙
        Jacquet.Localization.smoothFunctor U θ M hMU hθ ≅
      Jacquet.Localization.smoothFunctor U θ M hMU hθ ⋙
        SmoothRep.twistFunctor (χ.comp M.subtype) hχM :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (localizationTwistEquiv A.representation U θ M hMU hθ χ hU))
    (fun _ => smoothRep_hom_ext fun x => Submodule.Quotient.induction_on _ x fun _ => rfl)

/-- Localization followed by restriction to `H` along `e : H → M` carries a twist trivial
on `U` to any character equal to its restriction to `H`. -/
def localizationPullbackTwistIso (U : Subgroup G) (θ : U →* ℂˣ) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (hθ : Jacquet.Localization.IsInvariant U M hMU θ)
    (e : H →* M) (he : Continuous e)
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) (hU : U ≤ χ.ker)
    (η : H →* ℂˣ) (hη : IsOpen (η.ker : Set H)) (hηχ : (χ.comp M.subtype).comp e = η) :
    SmoothRep.twistFunctor.{0, uG, uV} χ hχ ⋙
        (Jacquet.Localization.smoothFunctor U θ M hMU hθ ⋙
          Mirabolic.continuousPullbackFunctor e he) ≅
      (Jacquet.Localization.smoothFunctor U θ M hMU hθ ⋙
          Mirabolic.continuousPullbackFunctor e he) ⋙
        SmoothRep.twistFunctor η hη :=
  pasteIso
    (localizationTwistIso U θ M hMU hθ χ hχ hU (hχ.preimage continuous_subtype_val))
    (pullbackTwistIso e he (χ.comp M.subtype) (hχ.preimage continuous_subtype_val)
        ((hχ.preimage continuous_subtype_val).preimage he) ≪≫
      Functor.isoWhiskerLeft _ (twistCongrIso hηχ _ hη))

end General

/-! ## Determinant-power characters -/

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The character `|det|^s` of `GL_(n+1)`, restricted to the actual mirabolic subgroup. -/
abbrev mirabolicPowerCharacter (T : F.TopologicalData) (n : ℕ) (s : ℝ) :
    mirabolic n F.Carrier →* ℂˣ :=
  (T.determinantPowerCharacter (n + 1) s).comp (mirabolic n F.Carrier).subtype

theorem isOpen_ker_mirabolicPowerCharacter (T : F.TopologicalData) (n : ℕ) (s : ℝ) :
    letI := T.topology
    IsOpen ((mirabolicPowerCharacter T n s).ker : Set (mirabolic n F.Carrier)) := by
  let _ := T.topology
  exact (T.isOpen_ker_determinantPowerCharacter (n + 1) s).preimage continuous_subtype_val

/-- `|det g|^s` depends only on the determinant, whatever the ranks. -/
theorem determinantPowerCharacter_eq_of_determinant_eq (T : F.TopologicalData) (s : ℝ)
    {m m' : ℕ} {g : GeneralLinear m F.Carrier} {g' : GeneralLinear m' F.Carrier}
    (h : GeneralLinear.determinant g = GeneralLinear.determinant g') :
    T.determinantPowerCharacter m s g = T.determinantPowerCharacter m' s g' := by
  have hn : T.determinantNorm m g = T.determinantNorm m' g' := by
    change T.normalizedAbsUnits (GeneralLinear.determinant g) =
      T.normalizedAbsUnits (GeneralLinear.determinant g')
    rw [h]
  change realPowerCharacter (T.determinantNorm m) s g =
    realPowerCharacter (T.determinantNorm m') s g'
  simp only [realPowerCharacter, MonoidHom.comp_apply, hn]

/-- Every element of the actual mirabolic radical has determinant one. -/
theorem determinant_radical {n : ℕ} (u : radical n F.Carrier) :
    GeneralLinear.determinant
      ((u : mirabolic n F.Carrier) : GeneralLinear (n + 1) F.Carrier) = 1 := by
  have hu : ((u : mirabolic n F.Carrier) : GeneralLinear (n + 1) F.Carrier) ∈
      GeneralLinear.upperUnipotent (n + 1) F.Carrier :=
    radical_le_upperUnipotent u.property
  apply Units.ext
  change Matrix.det (u : mirabolic n F.Carrier).val.val = 1
  rw [Matrix.det_of_isUpperTriangular hu.1]
  exact Finset.prod_eq_one fun i _ => hu.2 i

theorem radical_le_ker_mirabolicPowerCharacter (T : F.TopologicalData) (n : ℕ) (s : ℝ) :
    radical n F.Carrier ≤ (mirabolicPowerCharacter T n s).ker := by
  intro u hu
  exact T.ker_determinant_le_ker_determinantPowerCharacter (n + 1) s
    (determinant_radical (⟨u, hu⟩ : radical n F.Carrier))

/-- Through the Levi equivalence, the mirabolic character is `|det|^s` on `GL_n`. -/
theorem mirabolicPowerCharacter_levi (T : F.TopologicalData) (n : ℕ) (s : ℝ) :
    letI := T.topology
    ((mirabolicPowerCharacter T n s).comp (leviSubgroup n F.Carrier).subtype).comp
        (leviContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom =
      T.determinantPowerCharacter n s := by
  let _ := T.topology
  apply MonoidHom.ext
  intro g
  exact determinantPowerCharacter_eq_of_determinant_eq T s
    (JacquetNormalization.determinant_levi g)

/-- Through the successor equivalence, the rank `n + 1` mirabolic character is the rank
`n` mirabolic character. -/
theorem mirabolicPowerCharacter_successor (T : F.TopologicalData) (n : ℕ) (s : ℝ) :
    letI := T.topology
    ((mirabolicPowerCharacter T (n + 1) s).comp (successorSubgroup n F.Carrier).subtype).comp
        (successorContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom =
      mirabolicPowerCharacter T n s := by
  let _ := T.topology
  apply MonoidHom.ext
  intro h
  exact determinantPowerCharacter_eq_of_determinant_eq T s
    (JacquetNormalization.determinant_successor h)

/-! ## The minus functors -/

/-- Unnormalized `Ψ⁻` carries `|det|^s` on `P_(n+1)` to `|det|^s` on `GL_n`. -/
def psiMinusUnnormalizedTwistIso (T : F.TopologicalData) (n : ℕ) (s : ℝ) :
    letI := T.topology
    SmoothRep.twistFunctor (mirabolicPowerCharacter T n s)
        (isOpen_ker_mirabolicPowerCharacter T n s) ⋙
        Mirabolic.psiMinusUnnormalized.{uV} T n ≅
      Mirabolic.psiMinusUnnormalized T n ⋙
        SmoothRep.twistFunctor (T.determinantPowerCharacter n s)
          (T.isOpen_ker_determinantPowerCharacter n s) := by
  letI := T.topology
  exact localizationPullbackTwistIso (radical n F.Carrier) 1 (leviSubgroup n F.Carrier)
    leviSubgroup_le_normalizer
    (Jacquet.Localization.isInvariant_one _ _ leviSubgroup_le_normalizer)
    (leviContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
    (leviContinuousEquiv (n := n) (F := F.Carrier)).continuous
    (mirabolicPowerCharacter T n s) (isOpen_ker_mirabolicPowerCharacter T n s)
    (radical_le_ker_mirabolicPowerCharacter T n s)
    (T.determinantPowerCharacter n s) (T.isOpen_ker_determinantPowerCharacter n s)
    (mirabolicPowerCharacter_levi T n s)

/-- Unnormalized `Φ⁻` carries `|det|^s` on `P_(n+2)` to `|det|^s` on `P_(n+1)`. -/
def phiMinusUnnormalizedTwistIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) (s : ℝ) :
    letI := T.topology
    SmoothRep.twistFunctor (mirabolicPowerCharacter T (n + 1) s)
        (isOpen_ker_mirabolicPowerCharacter T (n + 1) s) ⋙
        Mirabolic.phiMinusUnnormalized.{uV} T ψ n ≅
      Mirabolic.phiMinusUnnormalized T ψ n ⋙
        SmoothRep.twistFunctor (mirabolicPowerCharacter T n s)
          (isOpen_ker_mirabolicPowerCharacter T n s) := by
  letI := T.topology
  exact localizationPullbackTwistIso (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n)
    (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer
    (Mirabolic.theta_isInvariant ψ n)
    (successorContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
    (successorContinuousEquiv (n := n) (F := F.Carrier)).continuous
    (mirabolicPowerCharacter T (n + 1) s) (isOpen_ker_mirabolicPowerCharacter T (n + 1) s)
    (radical_le_ker_mirabolicPowerCharacter T (n + 1) s)
    (mirabolicPowerCharacter T n s) (isOpen_ker_mirabolicPowerCharacter T n s)
    (mirabolicPowerCharacter_successor T n s)

/-- Normalized `Ψ⁻` commutes with `|det|^s`; its normalization twist commutes with it. -/
def psiMinusTwistIso (T : F.TopologicalData) (n : ℕ) (s : ℝ) :
    letI := T.topology
    SmoothRep.twistFunctor (mirabolicPowerCharacter T n s)
        (isOpen_ker_mirabolicPowerCharacter T n s) ⋙ Mirabolic.psiMinus.{uV} T n ≅
      Mirabolic.psiMinus T n ⋙
        SmoothRep.twistFunctor (T.determinantPowerCharacter n s)
          (T.isOpen_ker_determinantPowerCharacter n s) := by
  letI := T.topology
  exact pasteIso (psiMinusUnnormalizedTwistIso T n s)
    (twistCommIso (T.determinantPowerCharacter n s) (Mirabolic.psiMinusCharacter T n)
      (T.isOpen_ker_determinantPowerCharacter n s) (Mirabolic.isOpen_ker_psiMinusCharacter T n))

/-- Normalized `Φ⁻` commutes with `|det|^s`; its normalization twist commutes with it. -/
def phiMinusTwistIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) (s : ℝ) :
    letI := T.topology
    SmoothRep.twistFunctor (mirabolicPowerCharacter T (n + 1) s)
        (isOpen_ker_mirabolicPowerCharacter T (n + 1) s) ⋙ Mirabolic.phiMinus.{uV} T ψ n ≅
      Mirabolic.phiMinus T ψ n ⋙
        SmoothRep.twistFunctor (mirabolicPowerCharacter T n s)
          (isOpen_ker_mirabolicPowerCharacter T n s) := by
  letI := T.topology
  exact pasteIso (phiMinusUnnormalizedTwistIso T ψ n s)
    (twistCommIso (mirabolicPowerCharacter T n s) (Mirabolic.phiMinusCharacter T n)
      (isOpen_ker_mirabolicPowerCharacter T n s) (Mirabolic.isOpen_ker_phiMinusCharacter T n))

/-! ## Iteration, restriction and rank transport -/

/-- `(Φ⁻)^k` commutes with `|det|^s`, by induction on `k`. -/
def phiMinusIterateTwistIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (s : ℝ) (n : ℕ) :
    (k : ℕ) →
      letI := T.topology
      SmoothRep.twistFunctor (mirabolicPowerCharacter T (n + k) s)
          (isOpen_ker_mirabolicPowerCharacter T (n + k) s) ⋙
          phiMinusIterate.{uF, uV} T ψ n k ≅
        phiMinusIterate T ψ n k ⋙
          SmoothRep.twistFunctor (mirabolicPowerCharacter T n s)
            (isOpen_ker_mirabolicPowerCharacter T n s)
  | 0 => letI := T.topology; Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  | k + 1 => letI := T.topology
      pasteIso (phiMinusTwistIso T ψ (n + k) s) (phiMinusIterateTwistIso T ψ s n k)

/-- The mirabolic derivative `Ψ⁻ ∘ (Φ⁻)^k` commutes with `|det|^s`. -/
def mirabolicDerivativeTwistIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (s : ℝ) (n k : ℕ) :
    letI := T.topology
    SmoothRep.twistFunctor (mirabolicPowerCharacter T (n + k) s)
        (isOpen_ker_mirabolicPowerCharacter T (n + k) s) ⋙
        mirabolicDerivative.{uF, uV} T ψ n k ≅
      mirabolicDerivative T ψ n k ⋙
        SmoothRep.twistFunctor (T.determinantPowerCharacter n s)
          (T.isOpen_ker_determinantPowerCharacter n s) := by
  letI := T.topology
  exact pasteIso (phiMinusIterateTwistIso T ψ s n k) (psiMinusTwistIso T n s)

/-- Restriction from `GL_(n+1)` to `P_(n+1)` carries `|det|^s` to its restriction. -/
def generalLinearRestrictionTwistIso (T : F.TopologicalData) (n : ℕ) (s : ℝ) :
    letI := T.topology
    SmoothRep.twistFunctor (T.determinantPowerCharacter (n + 1) s)
        (T.isOpen_ker_determinantPowerCharacter (n + 1) s) ⋙
        generalLinearRestriction.{uF, uV} T n ≅
      generalLinearRestriction T n ⋙
        SmoothRep.twistFunctor (mirabolicPowerCharacter T n s)
          (isOpen_ker_mirabolicPowerCharacter T n s) := by
  letI := T.topology
  exact pullbackTwistIso (mirabolic n F.Carrier).subtype continuous_subtype_val
    (T.determinantPowerCharacter (n + 1) s) (T.isOpen_ker_determinantPowerCharacter (n + 1) s)
    (isOpen_ker_mirabolicPowerCharacter T n s)

/-- The positive derivative `Ψ⁻ ∘ (Φ⁻)^k ∘ Res` commutes with `|det|^s`. -/
def generalLinearDerivativePositiveTwistIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (s : ℝ) (n k : ℕ) :
    letI := T.topology
    SmoothRep.twistFunctor (T.determinantPowerCharacter (n + k + 1) s)
        (T.isOpen_ker_determinantPowerCharacter (n + k + 1) s) ⋙
        generalLinearDerivativePositive.{uF, uV} T ψ n k ≅
      generalLinearDerivativePositive T ψ n k ⋙
        SmoothRep.twistFunctor (T.determinantPowerCharacter n s)
          (T.isOpen_ker_determinantPowerCharacter n s) := by
  letI := T.topology
  exact pasteIso (generalLinearRestrictionTwistIso T (n + k) s)
    (mirabolicDerivativeTwistIso T ψ s n k)

/-- The rank transport along `a = b` carries `|det|^s` on `GL_a` to `|det|^s` on `GL_b`. -/
def generalLinearRankCastTwistIso (T : F.TopologicalData) (s : ℝ) {a b : ℕ} (h : a = b) :
    letI := T.topology
    SmoothRep.twistFunctor (T.determinantPowerCharacter a s)
        (T.isOpen_ker_determinantPowerCharacter a s) ⋙
        generalLinearRankCast.{uF, uV} T h ≅
      generalLinearRankCast T h ⋙
        SmoothRep.twistFunctor (T.determinantPowerCharacter b s)
          (T.isOpen_ker_determinantPowerCharacter b s) := by
  letI := T.topology
  subst h
  exact Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- Every feasible general-linear derivative commutes naturally with `|det|^s`. -/
def generalLinearDerivativeTwistIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (s : ℝ) (N : ℕ) :
    (k : ℕ) → (hk : k ≤ N) →
      letI := T.topology
      SmoothRep.twistFunctor (T.determinantPowerCharacter N s)
          (T.isOpen_ker_determinantPowerCharacter N s) ⋙
          generalLinearDerivative.{uF, uV} T ψ N k hk ≅
        generalLinearDerivative T ψ N k hk ⋙
          SmoothRep.twistFunctor (T.determinantPowerCharacter (N - k) s)
            (T.isOpen_ker_determinantPowerCharacter (N - k) s)
  | 0, _ => letI := T.topology; Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  | k + 1, hk => letI := T.topology
      pasteIso (generalLinearRankCastTwistIso T s (rank_eq_of_succ_le hk))
        (generalLinearDerivativePositiveTwistIso T ψ s (N - (k + 1)) k)

end DeterminantTwist

/-- The actual general-linear derivatives commute naturally with every real
determinant-power twist, with the same exponent on both groups. -/
theorem generalLinearDerivativeDeterminantTwist {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    GeneralLinearDerivativeDeterminantTwistStatement.{uF, uV} F T := by
  let _ := T.topology
  intro ψ N k hk s
  exact ⟨DeterminantTwist.generalLinearDerivativeTwistIso T ψ s N k hk⟩

end Langlands.Derivative

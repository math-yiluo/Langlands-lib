import Langlands.Representation.Derivative.TopLocalizationRestriction

/-! # The terminal mirabolic full upper quotient -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.TopLocalization

open GeneralLinear Jacquet.Localization

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- On the rank-one mirabolic group the two actual localizing subgroups agree. -/
theorem mirabolicZero_upper_eq_radical :
    Mirabolic.upperUnipotent 0 F.Carrier = Mirabolic.radical 0 F.Carrier :=
  Subsingleton.elim _ _

/-- The terminal full upper quotient is the actual normalized `Ψ⁻` quotient. -/
def mirabolicZeroEquiv (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (mirabolic 0 F.Carrier)) →
      ((mirabolicUpperCoinvariantsFunctor ψ 0).obj A).representation.Equiv
        ((Mirabolic.psiMinus T 0).obj A).representation := by
  letI := T.topology
  intro A
  refine
    { toLinearEquiv := transportEquiv A.representation A.representation _ _ _ _
        (MulEquiv.subgroupCongr mirabolicZero_upper_eq_radical)
        (LinearEquiv.refl ℂ _) (fun _ _ => rfl) ?_
      isIntertwining' := ?_ }
  · intro u
    have hu : u = 1 := Subsingleton.elim _ _
    subst u
    simp
  · intro g
    have hg : g = 1 := Subsingleton.elim _ _
    rw [hg]
    ext q
    simp

@[simp] theorem mirabolicZeroEquiv_mk (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (mirabolic 0 F.Carrier)) (v : A),
      mirabolicZeroEquiv T ψ A
        (mk A.representation (Mirabolic.upperUnipotent 0 F.Carrier)
          (mirabolicUpperCharacter ψ 0) v) =
      Mirabolic.psiMinusQuotient T 0 A v := by
  intros
  rfl

@[simp] theorem mirabolicZeroEquiv_symm_mk
    (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (mirabolic 0 F.Carrier)) (v : A),
      (mirabolicZeroEquiv T ψ A).symm (Mirabolic.psiMinusQuotient T 0 A v) =
      mk A.representation (Mirabolic.upperUnipotent 0 F.Carrier)
        (mirabolicUpperCharacter ψ 0) v := by
  intros
  rfl

/-- The terminal comparison is natural in every smooth `P₁` intertwiner. -/
def mirabolicZeroIso (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ) :
    letI := T.topology
    mirabolicUpperCoinvariantsFunctor.{uF,uV} ψ 0 ≅ Mirabolic.psiMinus T 0 := by
  letI := T.topology
  refine NatIso.ofComponents (fun A => SmoothRep.mkIso (mirabolicZeroEquiv T ψ A)) ?_
  intro A B f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply hom_ext
  ext v
  rfl

end Langlands.Derivative.TopLocalization

import Langlands.Representation.Derivative.PartialDerivativeTensorLocalization
import Langlands.Representation.Jacquet.LocalizationTransport

/-! # Restricting full upper localization to the actual mirabolic group -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.TopLocalization

open GeneralLinear Jacquet.Localization

universe uF uV

variable {F : Type uF} [CommRing F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The same entrywise character on the actual mirabolic upper group. -/
def mirabolicUpperCharacter (ψ : AddChar F ℂ) (n : ℕ) :
    Mirabolic.upperUnipotent n F →* ℂˣ :=
  (Whittaker.entrywiseCharacter ψ (n + 1)).comp
    Mirabolic.upperUnipotentEquiv.toMonoidHom

/-- Restriction to the mirabolic group changes only subgroup certificates in
the full upper-unipotent quotient. -/
def upperRestrictionLinearEquiv (ψ : AddChar F ℂ)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V) :
    Coinvariants ρ (upperUnipotent (n + 1) F)
        (Whittaker.entrywiseCharacter ψ (n + 1)) ≃ₗ[ℂ]
      Coinvariants (ρ.comp (mirabolic n F).subtype)
        (Mirabolic.upperUnipotent n F) (mirabolicUpperCharacter ψ n) :=
  transportEquiv ρ (ρ.comp (mirabolic n F).subtype) _ _ _ _
    Mirabolic.upperUnipotentEquiv.symm (LinearEquiv.refl ℂ V)
    (fun _ _ => rfl) (fun _ => rfl)

@[simp] theorem upperRestrictionLinearEquiv_mk (ψ : AddChar F ℂ)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V) (v : V) :
    upperRestrictionLinearEquiv ψ ρ
      (mk ρ (upperUnipotent (n + 1) F)
        (Whittaker.entrywiseCharacter ψ (n + 1)) v) =
      mk (ρ.comp (mirabolic n F).subtype)
        (Mirabolic.upperUnipotent n F) (mirabolicUpperCharacter ψ n) v := rfl

@[simp] theorem upperRestrictionLinearEquiv_symm_mk (ψ : AddChar F ℂ)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V) (v : V) :
    (upperRestrictionLinearEquiv ψ ρ).symm
      (mk (ρ.comp (mirabolic n F).subtype)
        (Mirabolic.upperUnipotent n F) (mirabolicUpperCharacter ψ n) v) =
      mk ρ (upperUnipotent (n + 1) F)
        (Whittaker.entrywiseCharacter ψ (n + 1)) v := rfl

section Smooth

variable [TopologicalSpace F]

/-- Full upper localization of a mirabolic representation, keeping the whole
quotient module as a trivial representation of `GL₀`. -/
def mirabolicUpperCoinvariantsFunctor (ψ : AddChar F ℂ) (n : ℕ) :
    SmoothRep.{0,uF,uV} ℂ (mirabolic n F) ⥤
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear 0 F) where
  obj A := SmoothRep.of
    (1 : Representation ℂ (GeneralLinear 0 F)
      (Coinvariants A.representation (Mirabolic.upperUnipotent n F)
        (mirabolicUpperCharacter ψ n)))
    (fun _ => ⟨⊤, fun _ => rfl⟩)
  map f := SmoothRep.ofHom
    { toLinearMap := mapLinear (Mirabolic.upperUnipotent n F)
        (mirabolicUpperCharacter ψ n) (SmoothRep.hom f)
      isIntertwining' _ := rfl }
  map_id A := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact hom_ext rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact hom_ext rfl

end Smooth

section Padic

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p}

/-- The actual `GL_(n+1)` and mirabolic full upper quotients are naturally
isomorphic, with identity maps on original representatives. -/
def upperRestrictionIso (T : K.TopologicalData) (ψ : AddChar K.Carrier ℂ) (n : ℕ) :
    letI := T.topology
    PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ (n + 1) ≅
      generalLinearRestriction T n ⋙ mirabolicUpperCoinvariantsFunctor ψ n := by
  letI := T.topology
  refine NatIso.ofComponents (fun A => SmoothRep.mkIso
    { toLinearEquiv := upperRestrictionLinearEquiv ψ A.representation
      isIntertwining' := fun _ => rfl }) ?_
  intro A B f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply hom_ext
  ext v
  rfl

end Padic

end Langlands.Derivative.TopLocalization

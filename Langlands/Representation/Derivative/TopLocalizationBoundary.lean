import Langlands.Representation.Derivative.PartialDerivativeTensorLocalization

/-! # The rank-zero and rank-one top-localization comparisons -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.TopLocalization

open GeneralLinear Jacquet.Localization

universe uF uV

private theorem singleton_relations {G : Type uF} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (hu : ∀ u : U, u = 1) :
    relations ρ U θ = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  simp [hu u]

private def singletonQuotientEquiv {G : Type uF} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (hu : ∀ u : U, u = 1) :
    Coinvariants ρ U θ ≃ₗ[ℂ] V :=
  (relations ρ U θ).quotEquivOfEqBot (singleton_relations ρ U θ hu)

section Zero

variable {F : Type uF} [CommRing F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- At rank zero the full upper-unipotent quotient retains the original module. -/
def upperZeroEquiv (ψ : AddChar F ℂ)
    (ρ : Representation ℂ (GeneralLinear 0 F) V) :
    (1 : Representation ℂ (GeneralLinear 0 F)
      (Coinvariants ρ (upperUnipotent 0 F) (Whittaker.entrywiseCharacter ψ 0))).Equiv ρ where
  toLinearEquiv := singletonQuotientEquiv ρ _ _ (fun _ => Subsingleton.elim _ _)
  isIntertwining' g := by
    rw [show g = 1 from Subsingleton.elim _ _]
    ext q
    simp only [map_one, LinearMap.comp_apply, Module.End.one_apply]

@[simp] theorem upperZeroEquiv_mk (ψ : AddChar F ℂ)
    (ρ : Representation ℂ (GeneralLinear 0 F) V) (v : V) :
    upperZeroEquiv ψ ρ
      (mk ρ (upperUnipotent 0 F) (Whittaker.entrywiseCharacter ψ 0) v) = v := rfl

variable [TopologicalSpace F]

/-- The rank-zero comparison is natural for every smooth intertwiner. -/
def upperCoinvariantsZeroIso (ψ : AddChar F ℂ) :
    PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun A => SmoothRep.mkIso (upperZeroEquiv ψ A.representation)) (by
    intro A B f
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply hom_ext
    ext v
    rfl)

end Zero

section One

variable {F : Type uF} [CommRing F]

private theorem upperOne_eq_one (u : upperUnipotent 1 F) : u = 1 := by
  apply Subtype.ext
  exact congrArg (fun x : GeneralLinear.mirabolic 0 F => x.val)
    (GeneralLinear.Mirabolic.rankOne_eq_one
      ⟨u.val, upperUnipotent_le_mirabolic u.property⟩)

end One

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The normalized top derivative at rank one is the actual first minus quotient. -/
theorem topDerivative_one (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    topDerivative.{uF,uV} T ψ 1 =
      generalLinearRestriction T 0 ⋙ Mirabolic.psiMinus T 0 := by
  let := T.topology
  rw [topDerivative_eq, generalLinearDerivative_one_one]
  rfl

/-- The upper quotient at rank one is the normalized `Ψ⁻` quotient of the
restricted representation, with no replacement of its module carrier. -/
def upperOneEquiv (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier)) →
      ((PartialTensor.upperCoinvariantsFunctor ψ 1).obj A).representation.Equiv
        ((generalLinearRestriction T 0 ⋙ Mirabolic.psiMinus T 0).obj A).representation := by
  letI := T.topology
  intro A
  refine
    { toLinearEquiv :=
        (singletonQuotientEquiv A.representation _ _ upperOne_eq_one).trans
          (singletonQuotientEquiv
            ((generalLinearRestriction T 0).obj A).representation
            (GeneralLinear.Mirabolic.radical 0 F.Carrier) 1
            (fun _ => Subsingleton.elim _ _)).symm
      isIntertwining' := ?_ }
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  rw [hg]
  ext q
  simp

/-- Both maps are the identity on original representatives. -/
@[simp] theorem upperOneEquiv_mk (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier)) (v : A),
      upperOneEquiv T ψ A
        (mk A.representation (upperUnipotent 1 F.Carrier)
          (Whittaker.entrywiseCharacter ψ 1) v) =
        Mirabolic.psiMinusQuotient T 0 ((generalLinearRestriction T 0).obj A) v := by
  intros
  rfl

/-- The rank-one quotient comparison is natural in the original `GL₁` representation. -/
def upperCoinvariantsOneIso (T : F.TopologicalData) (ψ : AddChar F.Carrier ℂ) :
    letI := T.topology
    PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ 1 ≅
      generalLinearRestriction T 0 ⋙ Mirabolic.psiMinus T 0 := by
  letI := T.topology
  exact NatIso.ofComponents (fun A => SmoothRep.mkIso (upperOneEquiv T ψ A)) (by
    intro A B f
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply hom_ext
    ext v
    rfl)

/-- The exact rank-zero boundary for the published top derivative. -/
def topLocalizationZeroIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ.complex 0 ≅ topDerivative T ψ 0 := by
  letI := T.topology
  exact upperCoinvariantsZeroIso ψ.complex ≪≫ (eqToIso (topDerivative_zero T ψ)).symm

/-- The exact rank-one boundary for the published normalized top derivative. -/
def topLocalizationOneIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ.complex 1 ≅ topDerivative T ψ 1 := by
  letI := T.topology
  exact upperCoinvariantsOneIso T ψ.complex ≪≫ (eqToIso (topDerivative_one T ψ)).symm

end Padic

end Langlands.Derivative.TopLocalization

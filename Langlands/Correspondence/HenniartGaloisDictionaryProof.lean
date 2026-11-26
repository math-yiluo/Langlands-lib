import Langlands.VirtualRepresentation.Weil.GroupTransport
import Langlands.Correspondence.HenniartGaloisPullback

/-!
# The finite-image Weil–Galois orbit dictionary

This file proves `Langlands.Henniart.WeilGaloisDictionaryStatement` and its four conjuncts
for every nonarchimedean local field `K`, of either characteristic, and every separable
closure `Ω` of `K`. It also proves that the Artin and Swan exponents and the torsion number
of an irreducible Weil class are invariant under unramified twists.
-/

noncomputable section

namespace Langlands.Henniart.LocalNumerical

open Langlands.VirtualRepresentation Langlands.FiniteRepresentation
open Langlands.Weil.Local.SepClosed

universe uK uΩ uW

section Twists

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Unramified twists of Weil classes commute. -/
theorem weilUnramifiedTwist_comm (k : ℕ) (y z : ℂˣ)
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) :
    weilUnramifiedTwist K Ω k y (weilUnramifiedTwist K Ω k z σ) =
      weilUnramifiedTwist K Ω k z (weilUnramifiedTwist K Ω k y σ) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have h1 := Equiv.congr_fun (continuousIrreducibleTwistEquiv_mul
    (localUnramifiedCharacter K Ω y) (localUnramifiedCharacter K Ω z) (k + 1)) σ
  have h2 := Equiv.congr_fun (continuousIrreducibleTwistEquiv_mul
    (localUnramifiedCharacter K Ω z) (localUnramifiedCharacter K Ω y) (k + 1)) σ
  have hc : localUnramifiedCharacter K Ω z * localUnramifiedCharacter K Ω y =
      localUnramifiedCharacter K Ω y * localUnramifiedCharacter K Ω z := by
    change Weil.Local.unramifiedCharacterHom (localDegree K Ω) z *
        Weil.Local.unramifiedCharacterHom (localDegree K Ω) y =
      Weil.Local.unramifiedCharacterHom (localDegree K Ω) y *
        Weil.Local.unramifiedCharacterHom (localDegree K Ω) z
    rw [← map_mul, ← map_mul, mul_comm]
  rw [hc] at h2
  exact h1.trans h2.symm

/-- The unramified twist by `z⁻¹` undoes the twist by `z`. -/
theorem weilUnramifiedTwist_inv_apply (k : ℕ) (z : ℂˣ)
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) :
    weilUnramifiedTwist K Ω k z⁻¹ (weilUnramifiedTwist K Ω k z σ) = σ :=
  continuousIrreducibleUnramifiedTwistEquiv_inv_apply _ z (k + 1) σ

/-- The torsion number of a Weil class is invariant under unramified twists. -/
theorem weilTorsionNumber_weilUnramifiedTwist {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) (z : ℂˣ) :
    weilTorsionNumber K Ω (weilUnramifiedTwist K Ω k z σ) = weilTorsionNumber K Ω σ := by
  unfold weilTorsionNumber
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by
    rw [weilUnramifiedTwist_comm]
    exact (weilUnramifiedTwist K Ω k z).injective.eq_iff)

private theorem conductor_congr {J : Type*} [Monoid J] {V : Type*} [AddCommGroup V]
    [Module ℂ V] {p : Representation ℂ J V → Prop} (F : (ρ : Representation ℂ J V) → p ρ → ℚ)
    {ρ₁ ρ₂ : Representation ℂ J V} (h : ρ₁ = ρ₂) (h₁ : p ρ₁) (h₂ : p ρ₂) :
    F ρ₁ h₁ = F ρ₂ h₂ := by
  subst h
  rfl

/-- An unramified twist of a Weil class keeps its Artin exponents: a finite inertia
presentation of a representative serves for the twisted representative. -/
theorem HasArtinConductor.weilUnramifiedTwist {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat} {a : ℕ}
    (h : HasArtinConductor K Ω σ a) (z : ℂˣ) :
    HasArtinConductor K Ω (weilUnramifiedTwist K Ω k z σ) a := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨A, P, hsurj, hA, ha⟩ := h
  let χ := (localUnramifiedCharacter K Ω z).toMonoidHom
  have hrep : ∀ w : localInertia K Ω,
      (FiniteRepresentation.twist χ A).representation w = A.representation w := by
    intro w
    change ((χ w : ℂˣ) : ℂ) • A.representation w = A.representation w
    rw [show χ w = 1 from localUnramifiedCharacter_on_inertia K Ω z w.property, Units.val_one,
      one_smul]
  have hrep' : Ramification.Local.SepClosed.localInertiaRepresentation K Ω
      (FiniteRepresentation.twist χ A) =
      Ramification.Local.SepClosed.localInertiaRepresentation K Ω A :=
    MonoidHom.ext hrep
  let P' : Ramification.Local.SepClosed.FiniteInertiaPresentation K Ω
      (FiniteRepresentation.twist χ A) :=
    ⟨P.extension, fun w hw => by
      have h := P.kernel_le hw
      change A.representation w = 1 at h
      change (FiniteRepresentation.twist χ A).representation w = 1
      rw [hrep]
      exact h⟩
  refine ⟨FiniteRepresentation.twist χ A, P', hsurj, ?_, ?_⟩
  · refine Eq.trans ?_
      (forget_continuousIrreducibleTwistEquiv (localUnramifiedCharacter K Ω z) (k + 1) σ).symm
    change classOf (FiniteRepresentation.twist χ A) = twistClass χ (weilClassForget K Ω σ)
    rw [← hA]
    rfl
  · rw [← ha]
    exact conductor_congr (fun ρ hρ => Ramification.Local.artinConductorOfQuotient _ K
      (Ramification.Local.SepClosed.weilInertiaRestriction K Ω P.extension).toMonoidHom hsurj
      ρ hρ) hrep' P'.kernel_le P.kernel_le

/-- The Artin exponents of a Weil class are those of its unramified twists. -/
theorem hasArtinConductor_weilUnramifiedTwist_iff {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) (z : ℂˣ) (a : ℕ) :
    HasArtinConductor K Ω (weilUnramifiedTwist K Ω k z σ) a ↔ HasArtinConductor K Ω σ a := by
  refine ⟨fun h => ?_, fun h => h.weilUnramifiedTwist K Ω z⟩
  have := h.weilUnramifiedTwist K Ω z⁻¹
  rwa [weilUnramifiedTwist_inv_apply] at this

/-- The Swan exponents of a Weil class are those of its unramified twists. -/
theorem hasWeilSwan_weilUnramifiedTwist_iff {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) (z : ℂˣ) (s : ℕ) :
    HasWeilSwan K Ω (weilUnramifiedTwist K Ω k z σ) s ↔ HasWeilSwan K Ω σ s := by
  unfold HasWeilSwan
  simp only [hasArtinConductor_weilUnramifiedTwist_iff]

end Twists

section Dictionary

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]

local notation "Γ" => (Ω ≃ₐ[K] Ω)

/-- The ranks of a Weil pullback and its Galois class agree. -/
theorem IsGaloisPullbackBasis.fst_eq {b : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)}
    {c : Weil.IrreducibleBasis.{uΩ, uW} Γ} (h : IsGaloisPullbackBasis K Ω b c) : b.1 = c.1 := by
  apply PNat.coe_injective
  have h1 : classRank (Weil.underlyingClass _ b) = b.1 := b.2.property
  have h2 : classRank (Weil.underlyingClass _ c) = c.1 := c.2.property
  rw [← h1, ← h2, h, Langlands.FiniteRepresentation.classRank_restrictClass]

/-- Unramified twists of rank-tagged Weil classes compose multiplicatively. -/
theorem twistBasisEquiv_localUnramifiedCharacter_mul (x y : ℂˣ)
    (b : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)) :
    Weil.twistBasisEquiv (localUnramifiedCharacter K Ω x)
        (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω y) b) =
      Weil.twistBasisEquiv (localUnramifiedCharacter K Ω (x * y)) b := by
  rw [← Equiv.trans_apply, Weil.twistBasisEquiv_mul]
  congr 2
  exact (map_mul (Weil.Local.unramifiedCharacterHom (localDegree K Ω)) x y).symm

/-- The unramified twist with parameter `1` is the identity. -/
theorem twistBasisEquiv_localUnramifiedCharacter_one
    (b : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)) :
    Weil.twistBasisEquiv (localUnramifiedCharacter K Ω 1) b = b := by
  rw [show localUnramifiedCharacter K Ω 1 = 1 from
    map_one (Weil.Local.unramifiedCharacterHom (localDegree K Ω)), Weil.twistBasisEquiv_one]
  rfl

omit [IsSepClosed Ω] in
/-- Galois classes are in the same unramified orbit exactly when an unramified Galois
character carries one to the other. -/
theorem galoisUnramifiedOrbitClass_eq_iff (a b : Weil.IrreducibleBasis.{uΩ, uW} Γ) :
    galoisUnramifiedOrbitClass K Ω a = galoisUnramifiedOrbitClass K Ω b ↔
      ∃ χ : galoisUnramifiedCharacters K Ω, Weil.twistBasisEquiv χ.val b = a := by
  show Quotient.mk _ a = Quotient.mk _ b ↔ _
  exact Quotient.eq

omit [IsSepClosed Ω] in
/-- An unramified twist does not change the Galois orbit. -/
theorem galoisUnramifiedOrbitClass_twist (χ : galoisUnramifiedCharacters K Ω)
    (c : Weil.IrreducibleBasis.{uΩ, uW} Γ) :
    galoisUnramifiedOrbitClass K Ω (Weil.twistBasisEquiv χ.val c) =
      galoisUnramifiedOrbitClass K Ω c :=
  (galoisUnramifiedOrbitClass_eq_iff K Ω _ _).mpr ⟨χ, rfl⟩

/-- An unramified twist does not change the Weil orbit. -/
theorem unramifiedOrbitClass_twist (z : ℂˣ)
    (b : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)) :
    Weil.unramifiedOrbitClass (localDegree K Ω)
        (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z) b) =
      Weil.unramifiedOrbitClass (localDegree K Ω) b :=
  (Weil.unramifiedOrbitClass_eq_iff _ _ _).mpr ⟨z, rfl⟩

/-- Galois-type twists of Weil classes in one unramified orbit have Galois classes in one
unramified orbit. -/
theorem galoisUnramifiedOrbitClass_eq_of_twist
    {b b' : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)}
    {c c' : Weil.IrreducibleBasis.{uΩ, uW} Γ} {z z' : ℂˣ}
    (h : IsGaloisPullbackBasis K Ω (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z) b) c)
    (h' : IsGaloisPullbackBasis K Ω
      (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z') b') c')
    (hb : Weil.unramifiedOrbitClass (localDegree K Ω) b =
      Weil.unramifiedOrbitClass (localDegree K Ω) b') :
    galoisUnramifiedOrbitClass K Ω c = galoisUnramifiedOrbitClass K Ω c' := by
  obtain ⟨y, hy⟩ := (Weil.unramifiedOrbitClass_eq_iff _ _ _).mp hb
  have hy : Weil.twistBasisEquiv (localUnramifiedCharacter K Ω y) b' = b := hy
  have htw : Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z') b' =
      Weil.twistBasisEquiv (localUnramifiedCharacter K Ω (z' * (z * y)⁻¹))
        (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z) b) := by
    rw [← hy, twistBasisEquiv_localUnramifiedCharacter_mul,
      twistBasisEquiv_localUnramifiedCharacter_mul, mul_assoc, inv_mul_cancel_right]
  obtain ⟨χ, -, hχ⟩ := h.exists_galoisUnramified_of_twist K Ω h' _ htw
  rw [hχ, galoisUnramifiedOrbitClass_twist]

/-- The Galois orbit attached to a Weil class: the orbit of the Galois class of a chosen
Galois-type unramified twist. -/
def galoisOrbitOfWeil (b : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)) :
    GaloisUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω :=
  galoisUnramifiedOrbitClass K Ω (exists_twist_isGaloisPullbackBasis K Ω b).choose_spec.choose

/-- `galoisOrbitOfWeil` is the Galois orbit of the Galois class of any Galois-type twist. -/
theorem galoisOrbitOfWeil_eq {b : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)}
    {c : Weil.IrreducibleBasis.{uΩ, uW} Γ} {z : ℂˣ}
    (h : IsGaloisPullbackBasis K Ω (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z) b) c) :
    galoisOrbitOfWeil K Ω b = galoisUnramifiedOrbitClass K Ω c :=
  galoisUnramifiedOrbitClass_eq_of_twist K Ω
    (exists_twist_isGaloisPullbackBasis K Ω b).choose_spec.choose_spec h rfl

/-- The Weil orbit attached to a Galois class: the orbit of its Weil pullback. -/
def weilOrbitOfGalois (c : Weil.IrreducibleBasis.{uΩ, uW} Γ) :
    Weil.UnramifiedOrbitClasses.{uΩ, uW} (localDegree K Ω) :=
  Weil.unramifiedOrbitClass (localDegree K Ω) (exists_isGaloisPullbackBasis K Ω c).choose

/-- `weilOrbitOfGalois` is the Weil orbit of any Weil pullback. -/
theorem weilOrbitOfGalois_eq {b : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)}
    {c : Weil.IrreducibleBasis.{uΩ, uW} Γ} (h : IsGaloisPullbackBasis K Ω b c) :
    weilOrbitOfGalois K Ω c = Weil.unramifiedOrbitClass (localDegree K Ω) b := by
  unfold weilOrbitOfGalois
  rw [(exists_isGaloisPullbackBasis K Ω c).choose_spec.weil_unique K Ω h]

/-- The equivalence between unramified-twist orbits of irreducible Weil classes and
unramified-twist orbits of irreducible Galois classes. -/
def weilGaloisOrbitEquiv :
    Weil.UnramifiedOrbitClasses.{uΩ, uW} (localDegree K Ω) ≃
      GaloisUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω where
  toFun := Quotient.lift (galoisOrbitOfWeil K Ω) fun a b hab => by
    have hb : Weil.unramifiedOrbitClass (localDegree K Ω) a =
        Weil.unramifiedOrbitClass (localDegree K Ω) b := Quotient.sound hab
    exact galoisUnramifiedOrbitClass_eq_of_twist K Ω
      (exists_twist_isGaloisPullbackBasis K Ω a).choose_spec.choose_spec
      (exists_twist_isGaloisPullbackBasis K Ω b).choose_spec.choose_spec hb
  invFun := Quotient.lift (weilOrbitOfGalois K Ω) fun a b hab => by
    have hc : galoisUnramifiedOrbitClass K Ω a = galoisUnramifiedOrbitClass K Ω b :=
      Quotient.sound hab
    obtain ⟨χ, hχ⟩ := (galoisUnramifiedOrbitClass_eq_iff K Ω _ _).mp hc
    have hpb := (exists_isGaloisPullbackBasis K Ω b).choose_spec.twist K Ω χ
    rw [hχ] at hpb
    rw [weilOrbitOfGalois_eq K Ω hpb, unramifiedOrbitClass_twist]
    rfl
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h b =>
      obtain ⟨z, c, h⟩ := exists_twist_isGaloisPullbackBasis K Ω b
      change Quotient.lift (weilOrbitOfGalois K Ω) _ (galoisOrbitOfWeil K Ω b) =
        Weil.unramifiedOrbitClass (localDegree K Ω) b
      rw [galoisOrbitOfWeil_eq K Ω h]
      change weilOrbitOfGalois K Ω c = _
      rw [weilOrbitOfGalois_eq K Ω h, unramifiedOrbitClass_twist]
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h c =>
      obtain ⟨b, h⟩ := exists_isGaloisPullbackBasis K Ω c
      change Quotient.lift (galoisOrbitOfWeil K Ω) _ (weilOrbitOfGalois K Ω c) =
        galoisUnramifiedOrbitClass K Ω c
      rw [weilOrbitOfGalois_eq K Ω h]
      change galoisOrbitOfWeil K Ω b = _
      have h1 : IsGaloisPullbackBasis K Ω
          (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω 1) b) c := by
        rw [twistBasisEquiv_localUnramifiedCharacter_one]
        exact h
      exact galoisOrbitOfWeil_eq K Ω h1

/-- The orbit equivalence sends the orbit of a Weil class to the orbit of the Galois class of
any of its Galois-type unramified twists. -/
theorem weilGaloisOrbitEquiv_apply_of_twist
    {b : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)}
    {c : Weil.IrreducibleBasis.{uΩ, uW} Γ} {z : ℂˣ}
    (h : IsGaloisPullbackBasis K Ω (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z) b) c) :
    weilGaloisOrbitEquiv K Ω (Weil.unramifiedOrbitClass (localDegree K Ω) b) =
      galoisUnramifiedOrbitClass K Ω c :=
  galoisOrbitOfWeil_eq K Ω h

/-- The orbit equivalence sends the orbit of a Weil pullback to the orbit of its Galois
class. -/
theorem weilGaloisOrbitEquiv_apply {b : Weil.IrreducibleBasis.{uΩ, uW} (localWeilGroup K Ω)}
    {c : Weil.IrreducibleBasis.{uΩ, uW} Γ} (h : IsGaloisPullbackBasis K Ω b c) :
    weilGaloisOrbitEquiv K Ω (Weil.unramifiedOrbitClass (localDegree K Ω) b) =
      galoisUnramifiedOrbitClass K Ω c := by
  apply weilGaloisOrbitEquiv_apply_of_twist K Ω (z := 1)
  rw [twistBasisEquiv_localUnramifiedCharacter_one]
  exact h

/-- A Weil class of Galois type and its Galois class have the same torsion number. -/
theorem weilTorsionNumber_eq_galoisTorsionNumber {k : ℕ}
    {σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat}
    {ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat} (h : IsGaloisPullback K Ω σ ρ) :
    weilTorsionNumber K Ω σ = galoisTorsionNumber K Ω ρ := by
  have hb : IsGaloisPullbackBasis K Ω ⟨k.succPNat, σ⟩ ⟨k.succPNat, ρ⟩ := h
  let g : {χ : galoisUnramifiedCharacters K Ω // galoisUnramifiedTwist K Ω k χ ρ = ρ} →
      {z : ℂˣ // weilUnramifiedTwist K Ω k z σ = σ} := fun χ =>
    ⟨χ.1.val (localProjection K Ω (localGeometricFrobenius K Ω)), by
      have h1 := hb.twist K Ω χ.1
      have hρ : Weil.twistBasisEquiv χ.1.val (⟨k.succPNat, ρ⟩ : Weil.IrreducibleBasis Γ) =
          ⟨k.succPNat, ρ⟩ := congrArg (Sigma.mk k.succPNat) χ.2
      rw [hρ] at h1
      exact irreducibleBasis_mk_injective (h1.weil_unique K Ω hb)⟩
  have hinj : Function.Injective g := by
    intro χ χ' hχ
    have hv : χ.1.val (localProjection K Ω (localGeometricFrobenius K Ω)) =
        χ'.1.val (localProjection K Ω (localGeometricFrobenius K Ω)) := congrArg Subtype.val hχ
    have hc := galoisUnramifiedCharacter_comp_localProjection K Ω χ.1
    have hc' := galoisUnramifiedCharacter_comp_localProjection K Ω χ'.1
    rw [hv, ← hc'] at hc
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    exact congrFun ((localProjection_denseRange K Ω).equalizer χ.1.val.continuous
      χ'.1.val.continuous (funext fun w => DFunLike.congr_fun hc w)) g
  have hsurj : Function.Surjective g := by
    rintro ⟨z, hz⟩
    have hz' : (⟨k.succPNat, σ⟩ : Weil.IrreducibleBasis (localWeilGroup K Ω)) =
        Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z) ⟨k.succPNat, σ⟩ :=
      congrArg (Sigma.mk k.succPNat) hz.symm
    obtain ⟨χ, hχ, hρ⟩ := hb.exists_galoisUnramified_of_twist K Ω hb z hz'
    refine ⟨⟨χ, (irreducibleBasis_mk_injective hρ).symm⟩, Subtype.ext ?_⟩
    change (χ.val.comp (localProjection K Ω)) (localGeometricFrobenius K Ω) = z
    rw [hχ, localUnramifiedCharacter_geometricFrobenius]
  unfold weilTorsionNumber galoisTorsionNumber
  exact (Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)).symm

/-- The image of a Weil refined stratum under the orbit equivalence is the Galois refined
stratum with the same rank, Swan exponent and torsion number. -/
theorem weilGaloisOrbitEquiv_image_weilRefinedStratum (k s f : ℕ) :
    weilGaloisOrbitEquiv K Ω '' weilRefinedStratum.{uK, uΩ, uW} K Ω k s f =
      galoisRefinedStratum.{uK, uΩ, uW} K Ω k s f := by
  ext x
  constructor
  · rintro ⟨_, ⟨σ, rfl, hs, hf⟩, rfl⟩
    obtain ⟨z, ⟨n, ρ⟩, h⟩ := exists_twist_isGaloisPullbackBasis K Ω
      (⟨k.succPNat, σ⟩ : Weil.IrreducibleBasis (localWeilGroup K Ω))
    have hn : k.succPNat = n := h.fst_eq K Ω
    subst hn
    have hpb : IsGaloisPullback K Ω (weilUnramifiedTwist K Ω k z σ) ρ := h
    refine ⟨ρ, (weilGaloisOrbitEquiv_apply_of_twist K Ω h).symm,
      ⟨_, hpb, (hasWeilSwan_weilUnramifiedTwist_iff K Ω σ z s).mpr hs⟩, ?_⟩
    rw [← weilTorsionNumber_eq_galoisTorsionNumber K Ω hpb,
      weilTorsionNumber_weilUnramifiedTwist, hf]
  · rintro ⟨ρ, rfl, ⟨σ, hpb, hs⟩, hf⟩
    refine ⟨Weil.unramifiedOrbitClass (localDegree K Ω) ⟨k.succPNat, σ⟩,
      ⟨σ, rfl, hs, ?_⟩, weilGaloisOrbitEquiv_apply K Ω hpb⟩
    rw [weilTorsionNumber_eq_galoisTorsionNumber K Ω hpb, hf]

end Dictionary

end Langlands.Henniart.LocalNumerical

namespace Langlands.Henniart

open Langlands.VirtualRepresentation LocalNumerical Langlands.Weil.Local.SepClosed

universe uK uΩ uW

/-- Each irreducible Weil class has an unramified twist of Galois type
(Henniart 1980, §2.3, Corollary 3). -/
theorem weilGaloisTypeTwist : WeilGaloisTypeTwistStatement.{uK, uΩ, uW} := by
  intro K _ _ _ _ Ω _ _ _ k σ
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨z, ⟨n, ρ⟩, h⟩ := exists_twist_isGaloisPullbackBasis K Ω
    (⟨k.succPNat, σ⟩ : Weil.IrreducibleBasis (localWeilGroup K Ω))
  have hn : k.succPNat = n := h.fst_eq K Ω
  subst hn
  exact ⟨z, ρ, h⟩

/-- Each Galois class has a unique Weil pullback, which determines the Galois class
(Henniart 1980, §2.1). -/
theorem galoisPullbackBijection : GaloisPullbackBijectionStatement.{uK, uΩ, uW} := by
  intro K _ _ _ _ Ω _ _ _ k
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  refine ⟨fun ρ => ?_, fun σ ρ ρ' h h' => ?_⟩
  · obtain ⟨⟨n, σ⟩, h⟩ := exists_isGaloisPullbackBasis K Ω
      (⟨k.succPNat, ρ⟩ : Weil.IrreducibleBasis (Ω ≃ₐ[K] Ω))
    have hn : n = k.succPNat := h.fst_eq K Ω
    subst hn
    refine ⟨σ, h, fun σ' h' => ?_⟩
    have h'' : IsGaloisPullbackBasis K Ω ⟨k.succPNat, σ'⟩ ⟨k.succPNat, ρ⟩ := h'
    exact irreducibleBasis_mk_injective (h''.weil_unique K Ω h)
  · have hb : IsGaloisPullbackBasis K Ω ⟨k.succPNat, σ⟩ ⟨k.succPNat, ρ⟩ := h
    have hb' : IsGaloisPullbackBasis K Ω ⟨k.succPNat, σ⟩ ⟨k.succPNat, ρ'⟩ := h'
    exact irreducibleBasis_mk_injective (hb.galois_unique K Ω hb')

/-- Pullback preserves and reflects unramified twisting and preserves torsion numbers
(Henniart 1988, Proposition 2.2(a)). -/
theorem galoisPullbackTwist : GaloisPullbackTwistStatement.{uK, uΩ, uW} := by
  intro K _ _ _ _ Ω _ _ _ k
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  refine ⟨fun σ σ' ρ ρ' h h' => ⟨?_, ?_⟩, fun σ ρ h => weilTorsionNumber_eq_galoisTorsionNumber
    K Ω h⟩
  · rintro ⟨z, rfl⟩
    have hb : IsGaloisPullbackBasis K Ω ⟨k.succPNat, σ⟩ ⟨k.succPNat, ρ⟩ := h
    have hb' : IsGaloisPullbackBasis K Ω
        (Weil.twistBasisEquiv (localUnramifiedCharacter K Ω z) ⟨k.succPNat, σ⟩)
        ⟨k.succPNat, ρ'⟩ := h'
    obtain ⟨χ, -, hχ⟩ := hb.exists_galoisUnramified_of_twist K Ω hb' z rfl
    exact ⟨χ, irreducibleBasis_mk_injective hχ⟩
  · rintro ⟨χ, rfl⟩
    have hb : IsGaloisPullbackBasis K Ω ⟨k.succPNat, σ⟩ ⟨k.succPNat, ρ⟩ := h
    have hb' : IsGaloisPullbackBasis K Ω ⟨k.succPNat, σ'⟩
        (Weil.twistBasisEquiv χ.val ⟨k.succPNat, ρ⟩) := h'
    exact ⟨_, irreducibleBasis_mk_injective (hb'.weil_unique K Ω (hb.twist K Ω χ))⟩

/-- The unramified-orbit equivalence of irreducible Weil and Galois classes, compatible with
pullback and with the refined strata. -/
theorem weilGaloisOrbitDictionary : WeilGaloisOrbitDictionaryStatement.{uK, uΩ, uW} := by
  intro K _ _ _ _ Ω _ _ _
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  intro d
  exact ⟨weilGaloisOrbitEquiv K Ω, fun k σ ρ h => weilGaloisOrbitEquiv_apply K Ω h,
    weilGaloisOrbitEquiv_image_weilRefinedStratum K Ω⟩

/-- The class-level and orbit-level Weil–Galois dictionary for nonarchimedean local fields
of either characteristic. -/
theorem weilGaloisDictionary : WeilGaloisDictionaryStatement.{uK, uΩ, uW} :=
  ⟨weilGaloisTypeTwist, galoisPullbackBijection, galoisPullbackTwist,
    weilGaloisOrbitDictionary⟩

end Langlands.Henniart

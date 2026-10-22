import Langlands.VirtualRepresentation.ExactTwist
import Langlands.Weil.Local.DegreeCharacters
import Langlands.LocalFactor.Euler

/-!
# Spectral twists of continuous exact virtual representations

The character is pulled back from the discrete integer degree, with value
`q^(-s)` at geometric degree one. This is an actual automorphism of the exact
virtual group, without choosing a local constant system.
-/

noncomputable section

universe uG uV

namespace Langlands.LocalFactor

@[simp]
theorem spectralParameter_zero (q : ℝ) (hq : 0 < q) :
    spectralParameter q hq 0 = 1 := by
  apply Units.ext
  simp [spectralParameter]

theorem spectralParameter_add (q : ℝ) (hq : 0 < q) (s t : ℂ) :
    spectralParameter q hq (s + t) =
      spectralParameter q hq s * spectralParameter q hq t := by
  apply Units.ext
  simp only [spectralParameter, Units.val_mk0, Units.val_mul,
    neg_add, add_mul, Complex.exp_add]

namespace SpectralTwist

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable (d : G →ₜ* Weil.Degree) (q : ℝ) (hq : 0 < q)

/-- The existing degree character at the existing spectral parameter. -/
def character (s : ℂ) : G →ₜ* ℂˣ :=
  Weil.Local.unramifiedCharacter d (spectralParameter q hq s)

theorem character_apply (s : ℂ) (g : G) :
    (character d q hq s g : ℂ) =
      Complex.exp (-s * (Real.log q : ℂ)) ^ (d g).toAdd := by
  simp [character, Weil.Local.unramifiedCharacter_apply, spectralParameter]

/-- Every spectral character is trivial on the kernel of the supplied degree. -/
theorem character_on_kernel (s : ℂ) {g : G} (hg : g ∈ d.toMonoidHom.ker) :
    character d q hq s g = 1 :=
  Weil.Local.unramifiedCharacter_on_kernel d _ hg

/-- The geometric degree-one value has the required sign. -/
theorem character_degree_one (s : ℂ) {g : G}
    (hg : d g = Multiplicative.ofAdd (1 : ℤ)) :
    character d q hq s g = spectralParameter q hq s :=
  Weil.Local.unramifiedCharacter_degree_one d _ hg

@[simp]
theorem character_zero : character d q hq 0 = 1 := by
  ext g
  simp [character, Weil.Local.unramifiedCharacter_apply]

theorem character_add (s t : ℂ) :
    character d q hq (s + t) = character d q hq s * character d q hq t := by
  change Weil.Local.unramifiedCharacterHom d (spectralParameter q hq (s + t)) = _
  rw [spectralParameter_add, map_mul]
  rfl

/-- Spectral twisting of the actual finite-dimensional representation. -/
def representation (s : ℂ) (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    FiniteRepresentation.{0, uG, uV} ℂ G :=
  FiniteRepresentation.twist (character d q hq s).toMonoidHom A

theorem representation_isContinuous (s : ℂ)
    {A : FiniteRepresentation.{0, uG, uV} ℂ G} (hA : A.IsContinuous) :
    (representation d q hq s A).IsContinuous :=
  FiniteRepresentation.isContinuous_twist _ hA

/-- The already constructed exact quotient, specialized to continuous objects. -/
abbrev ContinuousVirtual :=
  VirtualRepresentation.ExactGrothendieckGroup
    (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)

/-- Spectral twisting is an actual automorphism of the continuous exact virtual
group. Its inverse twists by the inverse continuous character. -/
def virtual (s : ℂ) :
    ContinuousVirtual.{uG, uV} (G := G) ≃ₗ[ℤ] ContinuousVirtual.{uG, uV} (G := G) :=
  VirtualRepresentation.ExactGrothendieckGroup.continuousTwist (character d q hq s)

open VirtualRepresentation

theorem virtual_ofRepresentation (s : ℂ)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsContinuous}) :
    virtual.{uG, uV} d q hq s (ExactGrothendieckGroup.ofRepresentation
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) A) =
      ExactGrothendieckGroup.ofRepresentation
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
        ⟨representation d q hq s A.val, representation_isContinuous d q hq s A.property⟩ :=
  ExactGrothendieckGroup.twist_ofRepresentation _ _ _ _ A

theorem virtual_preserves_degree (s : ℂ) (x : ContinuousVirtual.{uG, uV} (G := G)) :
    ExactGrothendieckGroup.degree
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
        (virtual.{uG, uV} d q hq s x) =
      ExactGrothendieckGroup.degree
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) x :=
  ExactGrothendieckGroup.degree_twist _ _ _ _ x

/-- The zero spectral shift is identity on the exact quotient. -/
theorem virtual_zero :
    (virtual.{uG, uV} d q hq 0).toLinearMap = LinearMap.id := by
  apply ExactGrothendieckGroup.hom_ext (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change virtual.{uG, uV} d q hq 0 (ExactGrothendieckGroup.ofRepresentation
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) A) = _
    rw [virtual_ofRepresentation]
    apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
    change FiniteRepresentation.Equiv
      (FiniteRepresentation.twist (character d q hq 0).toMonoidHom A.val) A.val
    rw [character_zero]
    exact FiniteRepresentation.twistOneEquiv A.val

/-- Addition of spectral parameters composes the constructed automorphisms. -/
theorem virtual_add (s t : ℂ) :
    (virtual.{uG, uV} d q hq s).toLinearMap.comp (virtual.{uG, uV} d q hq t).toLinearMap =
      (virtual.{uG, uV} d q hq (s + t)).toLinearMap := by
  apply ExactGrothendieckGroup.hom_ext (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change virtual.{uG, uV} d q hq s
      (virtual.{uG, uV} d q hq t (ExactGrothendieckGroup.ofRepresentation
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) A)) =
        virtual.{uG, uV} d q hq (s + t) (ExactGrothendieckGroup.ofRepresentation
          (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) A)
    rw [virtual_ofRepresentation, virtual_ofRepresentation, virtual_ofRepresentation]
    apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
    change FiniteRepresentation.Equiv
      (FiniteRepresentation.twist (character d q hq s).toMonoidHom
        (FiniteRepresentation.twist (character d q hq t).toMonoidHom A.val))
      (FiniteRepresentation.twist (character d q hq (s + t)).toMonoidHom A.val)
    rw [character_add]
    exact FiniteRepresentation.twistMulEquiv _ _ A.val

/-- The same actual map acts on genuine virtual dimension-zero elements. -/
def virtualDegreeZero (s : ℂ) :
    ExactGrothendieckGroup.degreeZero
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) →ₗ[ℤ]
      ExactGrothendieckGroup.degreeZero
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) :=
  (virtual.{uG, uV} d q hq s).toLinearMap.restrict fun x hx => by
    change ExactGrothendieckGroup.degree
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
        (virtual.{uG, uV} d q hq s x) = 0
    rw [virtual_preserves_degree,
      (ExactGrothendieckGroup.mem_degreeZero
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) x).mp hx]

end SpectralTwist

end Langlands.LocalFactor

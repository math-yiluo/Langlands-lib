import Langlands.Geometry.FormalGroup.PolarizedFramedAffinePoints
import Langlands.Geometry.FormalGroup.RationalHeight

/-! # Height of the actual polarized framing section -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.RationalSection.HasHeightFunction

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {L : ModuleLaw O R υ}
variable {π : O} {q : ℕ} {U : Opens (PrimeSpectrum R)}
variable {f : RationalSection F M N U} {h : U → ℤ}

/-- Postcomposition by an actual integral isomorphism preserves the rational height function. -/
theorem postcompose_iso (hf : HasHeightFunction π q f h) (e : Iso N L) :
    HasHeightFunction π q (RationalSection.comp (RationalSection.ofHom e.hom U) f) h := by
  intro x
  obtain ⟨V, hx, i, P, hP⟩ := hf x
  let A := (coefficientStructurePresheaf R).obj (op V)
  let eV := e.map (IsScalarTower.toAlgHom O R A)
  let Q : HeightPresentation π q
      (RationalSection.restrict i (RationalSection.comp (RationalSection.ofHom e.hom U) f)) := {
    exponent := P.exponent
    representative := eV.hom.comp P.representative
    numeratorHeight := P.numeratorHeight
    denominatorHeight := P.denominatorHeight
    numerator := Hom.hasHeight_of_isoSquare P.representative _ (Iso.refl _) eV
      (by change (eV.hom.comp P.representative).comp (Hom.id _) = _; rw [Hom.comp_id])
      P.numerator
    denominator := P.denominator
    represents := by
      rw [restrict_comp_hom, restrict_ofHom, ← comp_smul, P.represents]
      exact comp_ofIntegral eV.hom P.representative }
  exact ⟨V, hx, i, Q, hP⟩

end Langlands.FormalGroup.ModuleLaw.RationalSection.HasHeightFunction

namespace Langlands.FormalGroup.PolarizedFramedAffinePoint

open CategoryTheory TopologicalSpace ModuleLaw Langlands.Shimura

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {prime : ℕ} [Fact prime.Prime]
variable {W : Type} [CommRing W] [Algebra ℤ_[prime] W] {π : W}
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}
variable {frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])}
variable {T : Nilp.{0, 0} W π}
variable {X Y : PolarizedFramedAffinePoint prime π frame T}

/-- The full open on the spectrum of the actual reduced affine test. -/
abbrev reducedTop (T : Nilp.{0, 0} W π) :
    Opens (PrimeSpectrum ((Nilp.reductionFunctor W π).obj T).obj) := ⊤

/-- Harris's raw p-height is the local difference of logarithmic kernel ranks
for the actual framing section. -/
def HasFramingHeight (X : PolarizedFramedAffinePoint prime π frame T)
    (h : reducedTop T → ℤ) : Prop :=
  RationalSection.HasHeightFunction (prime : ℤ_[prime]) prime X.rho h

/-- The same height function holds after a polarized framed isomorphism. -/
theorem Iso.hasFramingHeight (e : Iso X Y) {h : reducedTop T → ℤ} (hh : X.HasFramingHeight h) :
    Y.HasFramingHeight h := by
  let a := e.targetIso.orderIso.toModuleIso.map (Nilp.quotientO ℤ_[prime] T)
  have hheight : RationalSection.HasHeightFunction (prime : ℤ_[prime]) prime
      (RationalSection.comp (X.reducedIsometrySection e.targetIso) X.rho) h :=
    RationalSection.HasHeightFunction.postcompose_iso hh a
  rw [e.square] at hheight
  exact hheight

/-- The actual raw height relation descends to the isomorphism classes. -/
def framingHeightFunctions (x : IsomorphismClass (frame := frame) (T := T)) :
    Set (reducedTop T → ℤ) :=
  Quotient.lift (s := isoSetoid (frame := frame) (T := T))
    (fun X => {h | X.HasFramingHeight h}) (by
      intro X Y hXY
      change Nonempty (Iso X Y) at hXY
      obtain ⟨e⟩ := hXY
      exact Set.ext fun _ => ⟨e.hasFramingHeight, e.symm.hasFramingHeight⟩) x

/-- The normalized height relation with Harris's sign and the product of
division degree and inertia degree as denominator. -/
def normalizedHeightFunctions (d f : ℕ) (x : IsomorphismClass (frame := frame) (T := T)) :
    Set (reducedTop T → ℤ) :=
  { h | 0 < d * f ∧
    (fun y => ((d * f : ℕ) : ℤ) * h y) ∈ framingHeightFunctions x }

/-- Any verified normalized height is locally constant. -/
theorem isLocallyConstant_of_mem_normalizedHeightFunctions {d f : ℕ}
    {x : IsomorphismClass (frame := frame) (T := T)} {h : reducedTop T → ℤ}
    (hh : h ∈ normalizedHeightFunctions d f x) : IsLocallyConstant h := by
  induction x using Quotient.inductionOn with
  | _ X =>
    change 0 < d * f ∧ X.HasFramingHeight (fun y => ((d * f : ℕ) : ℤ) * h y) at hh
    have hne : ((d * f : ℕ) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hh.1.ne'
    have hraw := (show RationalSection.HasHeightFunction (prime : ℤ_[prime]) prime X.rho
      (fun y => ((d * f : ℕ) : ℤ) * h y) from hh.2).isLocallyConstant
    rw [IsLocallyConstant.iff_exists_open] at hraw ⊢
    intro y
    obtain ⟨V, hV, hy, hval⟩ := hraw y
    exact ⟨V, hV, hy, fun z hz => mul_left_cancel₀ hne (hval z hz)⟩

end Langlands.FormalGroup.PolarizedFramedAffinePoint

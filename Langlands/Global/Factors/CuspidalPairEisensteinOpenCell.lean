import Langlands.Global.Factors.CuspidalPairEisensteinSeries
import Langlands.Global.AdelesLocallyCompactProof
import Langlands.Representation.Shahidi.Geometry

/-! # The open Bruhat cell integral of a cuspidal-pair Eisenstein series

For the upper two-block parabolic `P = MU` of `GL_N`, `N = r + t + 2`, with Levi
`M = GL_(r+1) × GL_(t+1)`, this module defines the generic Whittaker coefficient of a
function along the upper unipotent subgroup `N_M = N_(r+1) × N_(t+1)` of the Levi, and the
integral over the open Bruhat cell `P w U'` that the generic Fourier coefficient of the
Eisenstein series unfolds to (Shahidi 1978, Lemma 2.1; Shahidi 1981, proof of Theorem 5.1).
Here `w = [[0, I_(r+1)], [I_(t+1), 0]]` is Shahidi's block Weyl representative and `U'` is
the upper unipotent radical of the parabolic with exchanged block sizes `(t + 1, r + 1)`.
See the paired Markdown for the conventions. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.CuspidalPairEisenstein

open MeasureTheory NumberField
open scoped CategoryTheory.MonObj

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

/-- The block-diagonal adelic matrix `diag(x, y)` of `GL_(r+t+2)(𝔸)`, for
`x ∈ GL_(r+1)(𝔸)` and `y ∈ GL_(t+1)(𝔸)`: the Levi embedding of the upper two-block
parabolic. -/
def leviPair (x : AdelicGL F (r + 1)) (y : AdelicGL F (t + 1)) : AdelicGL F (r + t + 2) :=
  (blockShape r t).leviEmbedding (Adeles F)
    ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) (Adeles F)).symm (x, y))

/-- The generic Whittaker coefficient of `f` along the upper unipotent subgroup
`N_M = N_(r+1) × N_(t+1)` of the Levi, at `g`:
`∫_{N_(r+1)(F) \ N_(r+1)(𝔸)} ∫_{N_(t+1)(F) \ N_(t+1)(𝔸)} f(diag(u₁, u₂) g)
  conj(ψ_(r+1)(u₁)) conj(ψ_(t+1)(u₂)) du₂ du₁`,
as the iterated Library global Whittaker coefficients of the two blocks for the generic
characters `ψ(n_(0,1) + ⋯)` and the measures of total mass one. -/
def leviWhittaker (ψ : AddChar (Adeles F) ℂ) (f : AdelicGL F (r + t + 2) → ℂ)
    (g : AdelicGL F (r + t + 2)) : ℂ :=
  generalLinearWhittakerFunction F r ψ (fun _ => 1)
    (fun x => generalLinearWhittakerFunction F t ψ (fun _ => 1)
      (fun y => f (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) x)
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * g)) 1) 1

/-- Shahidi's block Weyl representative `w = [[0, I_(r+1)], [I_(t+1), 0]]` as an adelic
matrix of size `r + t + 2`. -/
def openCellWeyl : AdelicGL F (r + t + 2) :=
  GeneralLinear.reindex (finCongr (by omega : r + 1 + (t + 1) = r + t + 2))
    (Shahidi.blockWeyl (r + 1) (t + 1) (Adeles F))

/-- The matrix `u'(Y) = [[I_(t+1), Y], [0, I_(r+1)]]` of the upper unipotent radical `U'` of
the parabolic with block sizes `(t + 1, r + 1)`, for an adelic `(t + 1) × (r + 1)` matrix `Y`,
as an adelic matrix of size `r + t + 2`. -/
def openCellUnipotent (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    AdelicGL F (r + t + 2) :=
  GeneralLinear.reindex (finCongr (by omega : r + 1 + (t + 1) = r + t + 2))
    (Shahidi.intertwiningUnipotent (r + 1) (t + 1) (Adeles F) Y)

/-- A Haar measure on the additive group `U'(𝔸) ≅ M_((t+1) × (r+1))(𝔸)`, for its Borel
σ-algebra (which is not made an instance). -/
def openCellHaar :
    @Measure (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))
      (borel (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))) :=
  letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
  haveI : BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Adeles F) := adeles_locallyCompactSpace F
  haveI : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (r + 1) → Adeles F))
  Measure.addHaar

/-- Entries of `u'(Y)`: the `(t + 1) × (t + 1)` and `(r + 1) × (r + 1)` diagonal blocks are
identities, the upper right block is `Y` and the lower left block is zero. -/
theorem openCellUnipotent_apply (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))
    (i j : Fin (r + t + 2)) :
    (openCellUnipotent F r t Y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) i j =
      (Shahidi.upper (t + 1) (r + 1) (Adeles F) Y :
        Matrix (Fin (t + 1 + (r + 1))) (Fin (t + 1 + (r + 1))) (Adeles F))
        (Fin.cast (by omega) i) (Fin.cast (by omega) j) :=
  rfl

/-- On the superdiagonal, `u'(Y)` has the single possibly nonzero entry `Y_(t,0)`, at the
junction `(t, t + 1)` of the two diagonal blocks. -/
theorem openCellUnipotent_superdiagonal (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))
    (i : Fin (r + t + 1)) :
    (openCellUnipotent F r t Y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
        i.castSucc i.succ = if (i : ℕ) = t then Y (Fin.last t) 0 else 0 := by
  rw [openCellUnipotent_apply]
  rcases lt_trichotomy (i : ℕ) t with hi | hi | hi
  · have h1 : (Fin.cast (by omega) i.castSucc : Fin (t + 1 + (r + 1))) =
        (⟨i, by omega⟩ : Fin (t + 1)).castAdd (r + 1) := Fin.ext rfl
    have h2 : (Fin.cast (by omega) i.succ : Fin (t + 1 + (r + 1))) =
        (⟨i + 1, by omega⟩ : Fin (t + 1)).castAdd (r + 1) := Fin.ext (by simp)
    rw [h1, h2, Shahidi.upper_first_first, ite_eq_right (show (i : ℕ) ≠ t by omega),
      ite_eq_right_iff]
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  · have h1 : (Fin.cast (by omega) i.castSucc : Fin (t + 1 + (r + 1))) =
        (Fin.last t).castAdd (r + 1) := Fin.ext (by simp [hi])
    have h2 : (Fin.cast (by omega) i.succ : Fin (t + 1 + (r + 1))) =
        (0 : Fin (r + 1)).natAdd (t + 1) := Fin.ext (by simp [hi])
    rw [h1, h2, Shahidi.upper_first_second, ite_eq_left hi]
  · have h1 : (Fin.cast (by omega) i.castSucc : Fin (t + 1 + (r + 1))) =
        (⟨i - (t + 1), by omega⟩ : Fin (r + 1)).natAdd (t + 1) := Fin.ext (by simp; omega)
    have h2 : (Fin.cast (by omega) i.succ : Fin (t + 1 + (r + 1))) =
        (⟨i + 1 - (t + 1), by omega⟩ : Fin (r + 1)).natAdd (t + 1) := Fin.ext (by simp; omega)
    rw [h1, h2, Shahidi.upper_second_second, ite_eq_right (show (i : ℕ) ≠ t by omega),
      ite_eq_right_iff]
    intro h
    exact absurd (congrArg Fin.val h) (by simp; omega)

/-- The generic character of `coeff` restricted to `U'(𝔸)`: the superdiagonal sum of `u'(Y)` is
the corner entry `Y_(t,0)`. -/
theorem openCellUnipotent_superdiagonal_sum
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    ∑ i : Fin (r + t + 1),
        (openCellUnipotent F r t Y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
          i.castSucc i.succ = Y (Fin.last t) 0 := by
  simp only [openCellUnipotent_superdiagonal]
  rw [Finset.sum_eq_single (⟨t, by omega⟩ : Fin (r + t + 1))]
  · simp
  · intro i _ hi
    rw [ite_eq_right]
    intro h
    exact hi (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {F r t}

/-- The open-cell integral
`∫_{U'(𝔸)} W_M(φ_s)(w u') conj(ψ_N(u')) du'`, where `φ_s = φ · H^s` is the section twisted by
Shahidi's power `H(g)^s` (`heightPower`), `W_M` is the generic Whittaker coefficient along the
Levi (`leviWhittaker`), and `ψ_N(u) = ψ(u_(0,1) + ⋯ + u_(N-2,N-1))` is the generic character of
the upper unipotent group of `GL_N` used in `coeff`. The measure is `openCellHaar`. -/
def openCellIntegral (ψ : AddChar (Adeles F) ℂ) (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) : ℂ :=
  letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
  ∫ Y, leviWhittaker F r t ψ (fun g => φ g * heightPower F r t s g)
      (openCellWeyl F r t * openCellUnipotent F r t Y) *
    starRingEnd ℂ (ψ (∑ i : Fin (r + t + 1),
      (openCellUnipotent F r t Y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
        i.castSucc i.succ)) ∂(openCellHaar F r t)

end Langlands.Global.CuspidalPairEisenstein

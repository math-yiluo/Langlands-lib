import Langlands.Global.RankinSelberg.UnequalIntegrals
import Langlands.Automorphic.PlaceCompactAction

/-! # Archimedean places for the global Rankin–Selberg integrals

Single-place inclusions `GL_n(ℝ) → GL_n(𝔸)` at a real place and `GL_n(ℂ) → GL_n(𝔸)` at a
complex place, through the mixed archimedean coordinates of the Library; the archimedean
restrictions `g ↦ W(ι_v(g) a)` of the global Whittaker functions `cuspWhittaker`, with `a` a
finite adelic point; and the scalar by which the central element `-1` at an infinite place
acts on a cuspidal realization, read off the compact action at that place. See the paired
Markdown.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance archimedeanPlacesSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance archimedeanPlacesSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Inclusions

variable (F : Type u) [Field F] (n : ℕ)

/-- Assemble a real matrix at every real place and a complex matrix at every complex place
into one matrix over the mixed space `F_∞ = ℝ^(r₁) × ℂ^(r₂)`. -/
def placeMatrixHom :
    (({v : InfinitePlace F // v.IsReal} → Matrix (Fin n) (Fin n) ℝ) ×
      ({v : InfinitePlace F // v.IsComplex} → Matrix (Fin n) (Fin n) ℂ)) →*
      ArchimedeanMatrix F n where
  toFun p i j := (fun v => p.1 v i j, fun v => p.2 v i j)
  map_one' := by
    apply Matrix.ext
    intro i j
    apply Prod.ext
    · funext v
      simp only [Prod.fst_one, Pi.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · funext v
      simp only [Prod.snd_one, Pi.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
  map_mul' p q := by
    apply Matrix.ext
    intro i j
    apply Prod.ext
    · funext v
      change _ = (RingHom.fst _ _)
        (∑ k, ((fun v => p.1 v i k, fun v => p.2 v i k) :
            mixedEmbedding.mixedSpace F) *
          (fun v => q.1 v k j, fun v => q.2 v k j)) v
      rw [map_sum, Finset.sum_apply]
      rfl
    · funext v
      change _ = (RingHom.snd _ _)
        (∑ k, ((fun v => p.1 v i k, fun v => p.2 v i k) :
            mixedEmbedding.mixedSpace F) *
          (fun v => q.1 v k j, fun v => q.2 v k j)) v
      rw [map_sum, Finset.sum_apply]
      rfl

/-- The invertible matrices at all infinite places, assembled in mixed coordinates:
`∏_(v real) GL_n(ℝ) × ∏_(v complex) GL_n(ℂ) → GL_n(F_∞)`. -/
def placeGL :
    (({v : InfinitePlace F // v.IsReal} → Matrix.GeneralLinearGroup (Fin n) ℝ) ×
      ({v : InfinitePlace F // v.IsComplex} → Matrix.GeneralLinearGroup (Fin n) ℂ)) →*
      ArchimedeanGL F n :=
  (Units.map (placeMatrixHom F n)).comp
    ((MulEquiv.prodUnits.symm.toMonoidHom).comp
      (MonoidHom.prodMap MulEquiv.piUnits.symm.toMonoidHom MulEquiv.piUnits.symm.toMonoidHom))

/-- `GL_n(ℝ)` at the real place `v`, with the identity at every other infinite place. -/
def realPlaceGL (v : {v : InfinitePlace F // v.IsReal}) :
    Matrix.GeneralLinearGroup (Fin n) ℝ →* ArchimedeanGL F n :=
  (placeGL F n).comp
    ((MonoidHom.mulSingle (fun _ : {v : InfinitePlace F // v.IsReal} =>
        Matrix.GeneralLinearGroup (Fin n) ℝ) v).prod 1)

/-- `GL_n(ℂ)` at the complex place `w`, with the identity at every other infinite place.
The complex coordinate at `w` is that of the mixed space, i.e. of
`InfinitePlace.Completion.ringEquivComplexOfIsComplex`. -/
def complexPlaceGL (w : {v : InfinitePlace F // v.IsComplex}) :
    Matrix.GeneralLinearGroup (Fin n) ℂ →* ArchimedeanGL F n :=
  (placeGL F n).comp
    ((1 : Matrix.GeneralLinearGroup (Fin n) ℂ →*
        ({v : InfinitePlace F // v.IsReal} → Matrix.GeneralLinearGroup (Fin n) ℝ)).prod
      (MonoidHom.mulSingle (fun _ : {v : InfinitePlace F // v.IsComplex} =>
        Matrix.GeneralLinearGroup (Fin n) ℂ) w))

variable [NumberField F]

/-- The adelic point with archimedean component `g` (in mixed coordinates) and finite
component `a`. -/
def adelicPoint (g : ArchimedeanGL F n) (a : FiniteAdelicGL F n) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm
    (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm g) a)

/-- The adelic point `ι_v(g)` of `g ∈ GL_n(ℝ)` at the real place `v`. -/
def realPlacePoint (v : {v : InfinitePlace F // v.IsReal})
    (g : Matrix.GeneralLinearGroup (Fin n) ℝ) : Points F n :=
  adelicPoint F n (realPlaceGL F n v g) 1

/-- The adelic point `ι_w(g)` of `g ∈ GL_n(ℂ)` at the complex place `w`. -/
def complexPlacePoint (w : {v : InfinitePlace F // v.IsComplex})
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) : Points F n :=
  adelicPoint F n (complexPlaceGL F n w g) 1

/-- The adelic point of a finite adelic matrix, with archimedean component `1`. -/
def finitePoint (a : FiniteAdelicGL F n) : Points F n :=
  adelicPoint F n 1 a

end Inclusions

section Whittaker

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- `W` is an archimedean restriction at the real place `v` of a global Whittaker function
of `T` for `χ`: `W(g) = W_x(ι_v(g) a)` for a vector `x` of `T` and a finite adelic point
`a`, where `W_x = cuspWhittaker F T χ x`. -/
def IsRealPlaceWhittaker {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (v : {v : InfinitePlace F // v.IsReal})
    (W : Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ → ℂ) : Prop :=
  ∃ (x : T.Space) (a : FiniteAdelicGL F (r + 1)),
    W = fun g => cuspWhittaker F T χ x (realPlacePoint F (r + 1) v g * finitePoint F (r + 1) a)

/-- `W` is an archimedean restriction at the complex place `w` of a global Whittaker
function of `T` for `χ`: `W(g) = W_x(ι_w(g) a)` for a vector `x` of `T` and a finite adelic
point `a`, where `W_x = cuspWhittaker F T χ x`. -/
def IsComplexPlaceWhittaker {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (w : {v : InfinitePlace F // v.IsComplex})
    (W : Matrix.GeneralLinearGroup (Fin (r + 1)) ℂ → ℂ) : Prop :=
  ∃ (x : T.Space) (a : FiniteAdelicGL F (r + 1)),
    W = fun g =>
      cuspWhittaker F T χ x (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) a)

end Whittaker

section MinusOne

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The scalar `ω_v(-1)` by which the central element `-1 ∈ O(n)` at the real place `v`
acts on a cuspidal realization `T` of `GL_(r+1)`, through the compact action at `v`; it is
`1` by convention if `-1` does not act by a scalar. -/
def realMinusOneScalar {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (v : {v : InfinitePlace F // v.IsReal}) : ℂ := by
  exact if h : ∃ c : ℂ, ∀ x : T.Space,
      T.realization.realPlaceCompactRepresentation v (-1) x = c • x then h.choose else 1

/-- The scalar `ω_w(-1)` by which the central element `-1 ∈ U(n)` at the complex place `w`
acts on a cuspidal realization `T` of `GL_(r+1)`, through the compact action at `w`; it is
`1` by convention if `-1` does not act by a scalar. -/
def complexMinusOneScalar {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex}) : ℂ := by
  exact if h : ∃ c : ℂ, ∀ x : T.Space,
      T.realization.complexPlaceCompactRepresentation w (-1) x = c • x then h.choose else 1

/-- When `-1` at `v` acts by a scalar, it acts by `realMinusOneScalar T v`. -/
theorem realMinusOneScalar_spec {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (v : {v : InfinitePlace F // v.IsReal})
    (h : ∃ c : ℂ, ∀ x : T.Space,
      T.realization.realPlaceCompactRepresentation v (-1) x = c • x) (x : T.Space) :
    T.realization.realPlaceCompactRepresentation v (-1) x = realMinusOneScalar T v • x := by
  unfold realMinusOneScalar
  split_ifs with h'
  · exact h'.choose_spec x
  · exact absurd h h'

/-- When `-1` at `w` acts by a scalar, it acts by `complexMinusOneScalar T w`. -/
theorem complexMinusOneScalar_spec {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex})
    (h : ∃ c : ℂ, ∀ x : T.Space,
      T.realization.complexPlaceCompactRepresentation w (-1) x = c • x) (x : T.Space) :
    T.realization.complexPlaceCompactRepresentation w (-1) x =
      complexMinusOneScalar T w • x := by
  unfold complexMinusOneScalar
  split_ifs with h'
  · exact h'.choose_spec x
  · exact absurd h h'

end MinusOne

end Langlands.Global.RankinSelbergGlobal

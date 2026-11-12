import Langlands.Shimura.Unitary.PlaceTensorDecomposition
import Langlands.Shimura.Unitary.HarrisSplitPrimePoints

/-!
# Harris's similitude group at a split prime as a product over places

Let `K/E` be a CM extension, `A` a `K`-algebra with an involution of the second kind and
`ι : F →+* K` an embedding of an imaginary quadratic field. If `𝔭` is a place of `F` above
the rational place `v` whose completion map `ℚ_v → F_𝔭` is bijective (for instance, `p`
splits in `F`), then
`GG(ℚ_v) ≅ Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ × ℚ_vˣ`,
the identification (4.2) of Harris (1999) and (A.1) of Harris (1998).
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura

open Global AdelicFunctoriality

section Place

variable {F : Type w} [Field F] [NumberField F]
variable (v : Global.FinitePlace ℚ) (𝔭 : FinitePlacesAbove F v)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v 𝔭.1))

/-- A degree-one completion: `ℚ_v ≃ F_𝔭` through the completion map. -/
def splitPlaceEquiv : FiniteCompletion ℚ v ≃+* 𝔭.1.adicCompletion F :=
  RingEquiv.ofBijective (FiniteExtension.completionMap v 𝔭.1) h𝔭

@[simp] theorem splitPlaceEquiv_apply (x : FiniteCompletion ℚ v) :
    splitPlaceEquiv v 𝔭 h𝔭 x = FiniteExtension.completionMap v 𝔭.1 x := rfl

/-- The embedding `F →+* ℚ_v` of a degree-one place: `F → F_𝔭 ≃ ℚ_v`. -/
def splitPlaceEmbedding : F →+* FiniteCompletion ℚ v :=
  (splitPlaceEquiv v 𝔭 h𝔭).symm.toRingHom.comp (algebraMap F (𝔭.1.adicCompletion F))

/-- With `ℚ_v` an `F`-algebra through `splitPlaceEmbedding`, the identification
`ℚ_v ≃ F_𝔭` is `F`-linear. -/
def splitPlaceAlgEquiv :
    letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
    FiniteCompletion ℚ v ≃ₐ[F] 𝔭.1.adicCompletion F :=
  letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
  AlgEquiv.ofRingEquiv (f := splitPlaceEquiv v 𝔭 h𝔭) fun t => by
    change splitPlaceEquiv v 𝔭 h𝔭 ((splitPlaceEquiv v 𝔭 h𝔭).symm _) = _
    rw [RingEquiv.apply_symm_apply]

end Place

section Harris

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F]
variable {A : Type z} [Ring A] [Algebra K A]

variable (ι : F →+* K) (v : Global.FinitePlace ℚ)

omit [NumberField K] [IsTotallyComplex K] [NumberField F] [IsCMField F] in
/-- The scalar tower `F → K → A` for the `F`-algebra structures through `ι`. -/
theorem imaginaryQuadraticAlgebra_isScalarTower :
    letI := ι.toAlgebra
    letI := imaginaryQuadraticAlgebra (A := A) ι
    IsScalarTower F K A :=
  letI := ι.toAlgebra
  letI := imaginaryQuadraticAlgebra (A := A) ι
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (𝔭 : FinitePlacesAbove F v)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v 𝔭.1))

variable (A) in
/-- The factor `ℚ_v ⊗[F] A` of `GG(ℚ_v)` at a degree-one place `𝔭` of `F`, for `ℚ_v` an
`F`-algebra through `splitPlaceEmbedding`, is `Π_{w ∣ 𝔭} K_w ⊗[K] A`. -/
def splitPlaceFactorEquiv :
    letI := ι.toAlgebra
    letI := imaginaryQuadraticAlgebra (A := A) ι
    letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
    FiniteCompletion ℚ v ⊗[F] A ≃+*
      (Π w : FinitePlacesAbove K 𝔭.1, w.1.adicCompletion K ⊗[K] A) :=
  letI := ι.toAlgebra
  letI := imaginaryQuadraticAlgebra (A := A) ι
  letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
  haveI := imaginaryQuadraticAlgebra_isScalarTower (A := A) ι
  (Algebra.TensorProduct.congr (splitPlaceAlgEquiv v 𝔭 h𝔭)
      (AlgEquiv.refl : A ≃ₐ[F] A)).toRingEquiv.trans
    (PlaceTensor.placeTensorEquiv (K := K) 𝔭.1 A)

omit [IsTotallyComplex K] [IsCMField F] in
theorem splitPlaceFactorEquiv_tmul (s : FiniteCompletion ℚ v) (a : A)
    (w : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) :
    letI := ι.toAlgebra
    letI := imaginaryQuadraticAlgebra (A := A) ι
    letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
    splitPlaceFactorEquiv A ι v 𝔭 h𝔭 (s ⊗ₜ[F] a) w =
      FiniteExtension.completionMap 𝔭.1 w.1 (FiniteExtension.completionMap v 𝔭.1 s) ⊗ₜ[K] a := by
  let := ι.toAlgebra
  let := imaginaryQuadraticAlgebra (A := A) ι
  let := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
  have := imaginaryQuadraticAlgebra_isScalarTower (A := A) ι
  exact PlaceTensor.placeTensorEquiv_tmul (K := K) 𝔭.1 A _ a w

variable [Algebra E A] [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A]
variable [Algebra.IsQuadraticExtension ℚ F]

/-- Harris's identification (4.2) at a degree-one place `𝔭` of the imaginary quadratic field
above `v`: `GG(ℚ_v) ≃ Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ × ℚ_vˣ`. The first component of a point is the
image of its algebra unit in the factors `K_w ⊗[K] A`, the second its multiplier. -/
def SecondKindInvolution.splitPlacePoints (σ : SecondKindInvolution E K A) :
    letI := ι.toAlgebra
    σ.rationalInvolution.Points (FiniteCompletion ℚ v) ≃*
      (Π w : FinitePlacesAbove K 𝔭.1, (w.1.adicCompletion K ⊗[K] A)ˣ) ×
        (FiniteCompletion ℚ v)ˣ :=
  letI := ι.toAlgebra
  (σ.splitPrimePoints ι v (splitPlaceEmbedding v 𝔭 h𝔭)).trans
    (MulEquiv.prodCongr
      ((Units.mapEquiv (splitPlaceFactorEquiv A ι v 𝔭 h𝔭).toMulEquiv).trans MulEquiv.piUnits)
      (MulEquiv.refl _))

omit [IsScalarTower E K A] in
theorem SecondKindInvolution.splitPlacePoints_fst (σ : SecondKindInvolution E K A)
    (g : σ.rationalInvolution.Points (FiniteCompletion ℚ v))
    (w : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) :
    letI := ι.toAlgebra
    letI := imaginaryQuadraticAlgebra (A := A) ι
    letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
    (((σ.splitPlacePoints ι v 𝔭 h𝔭 g).1 w : (w.1.adicCompletion K ⊗[K] A)ˣ) :
        w.1.adicCompletion K ⊗[K] A) =
      splitPlaceFactorEquiv A ι v 𝔭 h𝔭
        (ImaginaryQuadraticSplit.projection F A (FiniteCompletion ℚ v) g.1.1) w :=
  rfl

omit [IsScalarTower E K A] in
theorem SecondKindInvolution.splitPlacePoints_snd (σ : SecondKindInvolution E K A)
    (g : σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :
    (σ.splitPlacePoints ι v 𝔭 h𝔭 g).2 =
      AlgebraInvolution.Points.multiplier σ.rationalInvolution _ g :=
  rfl

end Harris

/-- At a rational place `v` where the imaginary quadratic field `F` has two places (`p` splits
in `F`), every completion map `ℚ_v → F_𝔭` above `v` is bijective. -/
theorem completionMap_bijective_of_split {F : Type w} [Field F] [NumberField F]
    [Algebra.IsQuadraticExtension ℚ F] (v : Global.FinitePlace ℚ)
    (hsplit : Fintype.card (FinitePlacesAbove F v) = 2) (𝔭 : FinitePlacesAbove F v) :
    Function.Bijective (FiniteExtension.completionMap v 𝔭.1) :=
  PlaceTensor.completionMap_bijective_of_le_card v
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two ℚ F, hsplit]) 𝔭

end Langlands.Shimura

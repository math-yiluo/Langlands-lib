import Langlands.Shimura.SplitLevelSpace
import Langlands.Shimura.Unitary.PointsSplit
import Langlands.Shimura.Unitary.HarrisLevels

/-! # Level towers away from the places dividing an integer

For a rational involution `σ` and `m ≠ 0`, the splitting
`GG(A_f) ≃ₜ* GG(∏_{v ∣ m} ℚ_v) × GG(A_f^{(m)})` identifies, for a fixed level `K₀` at the places
dividing `m`, the tower of level spaces of `GG(A_f)` at the levels `e⁻¹ (K₀ × K')` with the tower
of prime-to-`m` level spaces for the domain `X × GG(∏_{v ∣ m} ℚ_v) ⧸ K₀`. This is specialized to
the Harris unitary level tower. See `HarrisSplitTower.md`.
-/

noncomputable section

universe u v w z t r

namespace Langlands.Shimura

open CategoryTheory CategoryTheory.Limits Opposite CompactOpenLevel Langlands.Global
open scoped NumberField

namespace AlgebraInvolution

variable {A : Type u} [Ring A] [Algebra ℚ A]
variable (σ : AlgebraInvolution ℚ A) (m : ℕ)

/-- The diagonal homomorphism from the rational similitudes to the points over `∏_{v ∣ m} ℚ_v`. -/
abbrev dividingDiagonal : σ.similitudes →* σ.DividingPoints m :=
  σ.diagonalPoints _

/-- The diagonal homomorphism from the rational similitudes to the prime-to-`m` points. -/
abbrev primeToDiagonal : σ.similitudes →* σ.PrimeToPoints m :=
  σ.diagonalPoints _

variable (X : Type z) [MulAction σ.similitudes X]

/-- The domain `X × GG(∏_{v ∣ m} ℚ_v) ⧸ K₀` of the prime-to-`m` level spaces, on which the rational
similitudes act diagonally; on the coset factor by left multiplication through the diagonal
homomorphism. -/
abbrev PrimeToDomain (K₀ : CompactOpenLevel (σ.DividingPoints m)) : Type (max z u) :=
  LevelSpace.AwayDomain X (σ.dividingDiagonal m) K₀.subgroup

variable [Module.Finite ℚ A]

/-- The splitting sends the diagonal image of a rational point to its two diagonal images. -/
theorem finiteAdelicPointsSplit_finiteAdelicDiagonal (hm : m ≠ 0) (g : σ.similitudes) :
    σ.finiteAdelicPointsSplit m hm (σ.finiteAdelicDiagonal g) =
      (σ.dividingDiagonal m g, σ.primeToDiagonal m g) :=
  σ.finiteAdelicPointsSplit_diagonal m hm g

variable [TopologicalSpace X]

/-- The tower of prime-to-`m` level spaces `σ.similitudes \ ((X × GG(∏_{v ∣ m} ℚ_v) ⧸ K₀) ×
GG(A_f^{(m)})) / K'` over the levels `K'` of `GG(A_f^{(m)})`. -/
def primeToLevelTower (K₀ : CompactOpenLevel (σ.DividingPoints m)) :
    CompactOpenLevel (σ.PrimeToPoints m) ⥤ TopCat.{max u z} :=
  LevelSpace.tower (X := σ.PrimeToDomain m X K₀) (ι := σ.primeToDiagonal m)

variable (hm : m ≠ 0) (K₀ : CompactOpenLevel (σ.DividingPoints m))

/-- With the level `K₀` at the places dividing `m` fixed, the tower of level spaces of `GG(A_f)`
at the levels `e⁻¹ (K₀ × K')` is the tower of prime-to-`m` level spaces. -/
def primeToTowerIso :
    (awayOver (σ.finiteAdelicPointsSplit m hm) K₀).functor ⋙
        LevelSpace.tower (X := X) (ι := σ.finiteAdelicDiagonal) ≅
      σ.primeToLevelTower m X K₀ :=
  LevelSpace.awayTowerIso X (σ.finiteAdelicPointsSplit_finiteAdelicDiagonal m hm) K₀

@[simp] theorem primeToTowerIso_hom_app_mk (K' : CompactOpenLevel (σ.PrimeToPoints m))
    (x : X × σ.FiniteAdelicPoints) :
    (σ.primeToTowerIso m X hm K₀).hom.app K' (LevelSpace.mk _ x) =
      LevelSpace.mk _ (LevelSpace.awayPoint (σ.finiteAdelicPointsSplit m hm)
        (σ.dividingDiagonal m) K₀ x) :=
  rfl

variable {C : Type w} [Category.{r} C] (P : TopCat.{max u z}ᵒᵖ ⥤ C)

/-- For a presheaf `P` on spaces, the away tower at `K₀` of `K ↦ P (σ.similitudes \ (X × GG(A_f))
/ K)` is `P` on the prime-to-`m` level spaces. -/
def primeToPresheafIso :
    LevelColimit.awayTower (σ.finiteAdelicPointsSplit m hm) K₀
        ((LevelSpace.tower (X := X) (ι := σ.finiteAdelicDiagonal)).op ⋙ P) ≅
      (σ.primeToLevelTower m X K₀).op ⋙ P :=
  LevelSpace.awayTowerPresheafIso X (σ.finiteAdelicPointsSplit_finiteAdelicDiagonal m hm) K₀ P

/-- The colimit over the prime-to-`m` levels of the away tower at `K₀`, with its action of
`GG(A_f^{(m)})`, is the colimit of `P` on the prime-to-`m` level spaces. -/
def primeToActionIso [HasColimitsOfShape (Ordered (σ.PrimeToPoints m))ᵒᵖ C] :
    LevelColimit.action (LevelColimit.awayTower (σ.finiteAdelicPointsSplit m hm) K₀
        ((LevelSpace.tower (X := X) (ι := σ.finiteAdelicDiagonal)).op ⋙ P)) ≅
      LevelColimit.action ((σ.primeToLevelTower m X K₀).op ⋙ P) :=
  LevelSpace.awayActionIso X (σ.finiteAdelicPointsSplit_finiteAdelicDiagonal m hm) K₀ P

/-- For a presheaf of modules `P`, the smooth representation of `GG(A_f^{(m)})` on the colimit of
the away tower at `K₀` is the smooth representation on the colimit of `P` on the prime-to-`m`
level spaces. -/
def primeToSmoothRepIso {R : Type t} [CommRing R]
    [HasColimitsOfShape (Ordered σ.FiniteAdelicPoints)ᵒᵖ (ModuleCat.{w} R)]
    [HasColimitsOfShape (Ordered (σ.PrimeToPoints m))ᵒᵖ (ModuleCat.{w} R)]
    (P : TopCat.{max u z}ᵒᵖ ⥤ ModuleCat.{w} R) :
    LevelColimit.awaySmoothRep (σ.finiteAdelicPointsSplit m hm) K₀
        ((LevelSpace.tower (X := X) (ι := σ.finiteAdelicDiagonal)).op ⋙ P)
        (LevelSpace.isLevelTrivial_tower σ.finiteAdelicDiagonal P) ≅
      LevelColimit.smoothRep ((σ.primeToLevelTower m X K₀).op ⋙ P)
        (LevelSpace.isLevelTrivial_tower (σ.primeToDiagonal m) P) :=
  LevelSpace.awaySmoothRepIso X (σ.finiteAdelicPointsSplit_finiteAdelicDiagonal m hm) K₀ P

end AlgebraInvolution

section Harris

open NumberField _root_.Algebra

variable {E : Type v} {K : Type w} {A : Type u}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A] [Module.Finite ℚ A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    (h : HasHarrisSignature D.toSecondKindInvolution n)
    {F : Type z} [Field F] [NumberField F] [IsCMField F] [IsQuadraticExtension ℚ F]
    (ιF : F →+* K) (τ₀ : F →+* ℂ) (m : ℕ)

/-- The Harris level tower away from the places dividing `m`, at the level `K₀` of
`GG(∏_{v ∣ m} ℚ_v)`: the prime-to-`m` level spaces for the domain
`X × GG(∏_{v ∣ m} ℚ_v) ⧸ K₀`, where `X` is the CM-compatible Harris domain. -/
def harrisPrimeToLevelTower
    (K₀ : CompactOpenLevel (D.toSecondKindInvolution.rationalInvolution.DividingPoints m)) :
    CompactOpenLevel (D.toSecondKindInvolution.rationalInvolution.PrimeToPoints m) ⥤
      TopCat.{max u v} :=
  D.toSecondKindInvolution.rationalInvolution.primeToLevelTower m
    (HarrisSignatureCharts.ofSignature h (isCMSection_harrisCMSection E ιF τ₀)).Domain K₀

variable (hm : m ≠ 0)
    (K₀ : CompactOpenLevel (D.toSecondKindInvolution.rationalInvolution.DividingPoints m))

/-- Fixing the level `K₀` at the places dividing `m`, the Harris level tower at the levels
`e⁻¹ (K₀ × K')` is the Harris prime-to-`m` level tower. -/
def harrisPrimeToTowerIso :
    (awayOver (D.toSecondKindInvolution.rationalInvolution.finiteAdelicPointsSplit m hm)
        K₀).functor ⋙ harrisUnitaryLevelTower D h ιF τ₀ ≅
      harrisPrimeToLevelTower D h ιF τ₀ m K₀ :=
  D.toSecondKindInvolution.rationalInvolution.primeToTowerIso m
    (HarrisSignatureCharts.ofSignature h (isCMSection_harrisCMSection E ιF τ₀)).Domain hm K₀

variable {C : Type t} [Category.{r} C] (P : TopCat.{max u v}ᵒᵖ ⥤ C)

/-- For a presheaf `P` on spaces, the away tower at `K₀` of `P` on the Harris level tower is `P`
on the Harris prime-to-`m` level tower. -/
def harrisPrimeToPresheafIso :
    LevelColimit.awayTower (D.toSecondKindInvolution.rationalInvolution.finiteAdelicPointsSplit
        m hm) K₀ ((harrisUnitaryLevelTower D h ιF τ₀).op ⋙ P) ≅
      (harrisPrimeToLevelTower D h ιF τ₀ m K₀).op ⋙ P :=
  D.toSecondKindInvolution.rationalInvolution.primeToPresheafIso m
    (HarrisSignatureCharts.ofSignature h (isCMSection_harrisCMSection E ιF τ₀)).Domain hm K₀ P

/-- The colimit over the prime-to-`m` levels of the away tower at `K₀` of `P` on the Harris level
tower, with its action of `GG(A_f^{(m)})`, is the colimit of `P` on the Harris prime-to-`m`
level tower. -/
def harrisPrimeToActionIso
    [HasColimitsOfShape
      (Ordered (D.toSecondKindInvolution.rationalInvolution.PrimeToPoints m))ᵒᵖ C] :
    LevelColimit.action (LevelColimit.awayTower
        (D.toSecondKindInvolution.rationalInvolution.finiteAdelicPointsSplit m hm) K₀
        ((harrisUnitaryLevelTower D h ιF τ₀).op ⋙ P)) ≅
      LevelColimit.action ((harrisPrimeToLevelTower D h ιF τ₀ m K₀).op ⋙ P) :=
  D.toSecondKindInvolution.rationalInvolution.primeToActionIso m
    (HarrisSignatureCharts.ofSignature h (isCMSection_harrisCMSection E ιF τ₀)).Domain hm K₀ P

/-- For a presheaf of modules `P`, the smooth representation of `GG(A_f^{(m)})` on the colimit of
the away tower at `K₀` of `P` on the Harris level tower is the smooth representation on the
colimit of `P` on the Harris prime-to-`m` level tower. -/
def harrisPrimeToSmoothRepIso {R : Type t} [CommRing R]
    [HasColimitsOfShape
      (Ordered D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPoints)ᵒᵖ
      (ModuleCat.{r} R)]
    [HasColimitsOfShape
      (Ordered (D.toSecondKindInvolution.rationalInvolution.PrimeToPoints m))ᵒᵖ
      (ModuleCat.{r} R)]
    (P : TopCat.{max u v}ᵒᵖ ⥤ ModuleCat.{r} R) :
    LevelColimit.awaySmoothRep
        (D.toSecondKindInvolution.rationalInvolution.finiteAdelicPointsSplit m hm) K₀
        ((harrisUnitaryLevelTower D h ιF τ₀).op ⋙ P)
        (LevelSpace.isLevelTrivial_tower
          D.toSecondKindInvolution.rationalInvolution.finiteAdelicDiagonal P) ≅
      LevelColimit.smoothRep ((harrisPrimeToLevelTower D h ιF τ₀ m K₀).op ⋙ P)
        (LevelSpace.isLevelTrivial_tower
          (D.toSecondKindInvolution.rationalInvolution.primeToDiagonal m) P) :=
  D.toSecondKindInvolution.rationalInvolution.primeToSmoothRepIso m
    (HarrisSignatureCharts.ofSignature h (isCMSection_harrisCMSection E ιF τ₀)).Domain hm K₀ P

end Harris

end Langlands.Shimura

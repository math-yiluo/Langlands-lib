import Langlands.Algebra.UnitaryDiscriminant.Splitting
import Langlands.Algebra.UnitaryDiscriminant.Resize
import Langlands.Algebra.UnitaryDiscriminant.SplitCenter
import Langlands.Algebra.BrauerSemilinear
import Langlands.GaloisCohomology.Global.BrauerSequence.AlgebraicComparison
import Langlands.Shimura.Unitary.SplitCompletionChart
import Langlands.Shimura.Unitary.UnitaryLocalProfileRealizationStatement

/-! # The discriminant presentation and its split finite local invariants -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global.AdelicFunctoriality
open Langlands.Global (FiniteCompletion)
open Langlands.ClassFieldTheory.Local Langlands.GaloisCohomology Langlands.Galois
open Langlands.UnitaryDiscriminant
open scoped FiniteExtension

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  {A : CSA.{v, v} K} [Algebra E A] [IsScalarTower E K A] {m : ℕ}

/-- A finite Galois matrix splitting of the even-degree pair in the base field universe. -/
structure EvenDiscriminantPresentation (E : Type u) {K : Type v}
    [Field E] [Field K] [Algebra E K] (A : CSA.{v, v} K) (m : ℕ) where
  (pair : BaseUniversePair E A)
  [quadratic : IsQuadraticExtension E pair.center]
  splitting : GaloisSplitting E pair.center pair.algebra (2 * m)

attribute [instance] EvenDiscriminantPresentation.quadratic

namespace EvenDiscriminantPresentation

/-- Choose the finite Galois chart over the base field universe for the given degree. -/
def fromDimension (hA : Module.finrank K A = (2 * m) ^ 2) :
    EvenDiscriminantPresentation E A m := by
  let R := BaseUniversePair.ofFinite (F := E) A
  let : IsQuadraticExtension E R.center := ⟨R.center_finrank.trans (IsQuadraticExtension.finrank_eq_two E K)⟩
  exact ⟨R, galoisSplitting E R.center R.algebra (R.algebra_finrank.trans hA)⟩

variable (P : EvenDiscriminantPresentation E A m)

omit [NumberField E] [Algebra E A] [IsScalarTower E K A] in
/-- The nontrivial center action survives the change of universe. -/
theorem center_ne_one : P.pair.centerAutomorphism (cmConjugation E K) ≠ 1 :=
  P.pair.centerAutomorphism_ne_one (cmConjugation_ne_one E K)

omit [NumberField E] [IsScalarTower E K A] in
/-- The transported involution acts on the transported center. -/
theorem isUnitary (σ : SecondKindInvolution E K A) :
    IsUnitaryInvolution (P.pair.centerAutomorphism (cmConjugation E K))
      (P.pair.involution σ.involution) :=
  P.pair.isUnitaryInvolution ⟨σ.involution.apply_add, σ.involution.apply_mul,
    σ.involution.apply_apply, σ.onCenter⟩

/-- The discriminant Brauer class of the original unitary pair in its chosen splitting. -/
def brauerClass (σ : SecondKindInvolution E K A) : BrauerGroup.{u, u} E :=
  discriminantClass P.center_ne_one (P.isUnitary σ) P.splitting.chart

omit [NumberField E] [IsScalarTower E K A] in
theorem two_nsmul_brauerClass (σ : SecondKindInvolution E K A) :
    2 • P.brauerClass σ = 0 :=
  two_nsmul_discriminantClass P.center_ne_one (P.isUnitary σ) P.splitting.chart

end EvenDiscriminantPresentation

/-- A class of order dividing two has value zero or the rational half, distinguished by vanishing. -/
theorem halfClass_of_two_nsmul_eq_zero {x : RationalModIntegers} (hx : 2 • x = 0) :
    x = (by classical exact if x = 0 then 0 else rationalClass (1 / 2)) := by
  classical
  by_cases h : x = 0
  · simp [h]
  · obtain ⟨a, ha⟩ := (denominatorEquiv 2 (by decide)).surjective
      (⟨x, hx⟩ : denominatorSubgroup 2)
    have hval : (denominatorMap 2 (by decide) a : RationalModIntegers) = x :=
      congrArg Subtype.val ha
    have ha1 : a = 1 := by
      fin_cases a
      · exact (h (hval.symm.trans (map_zero _))).elim
      · rfl
    rw [ha1] at hval
    have hhalf : denominatorMap 2 (by decide) 1 = rationalClass (1 / 2) := by
      change (denominatorEquiv 2 (by decide) 1 : RationalModIntegers) = _
      simp [denominatorEquiv_one, reciprocalClass, one_div]
    rw [hhalf] at hval
    simpa [h] using hval.symm

attribute [local instance] FiniteExtension.local_finite

set_option maxRecDepth 8192 in
omit [IsScalarTower E K A] in
/-- The split finite localization is the half-degree multiple of the prescribed invariant
at the chosen actual upper place. -/
theorem localInvariant_discriminant_at_split (P : EvenDiscriminantPresentation E A m)
    (σ : SecondKindInvolution E K A) [Nonempty (Fin (2 * m))]
    (ι : PlaceEmbeddings E (AlgebraicClosure E)) (p : Langlands.Global.FinitePlace E)
    (hs : SplitPlaceIdentification E K p) (q : FinitePlacesAbove K p)
    (x : RationalModIntegers) (h : HasCompletedBrauerInvariant K A q.val x) :
    localInvariant ι p (brauerEquiv E (AlgebraicClosure E) (P.brauerClass σ)) = m • x := by
  classical
  let F := FiniteCompletion E p
  let Q := FiniteCompletion K q.val
  let j : F ≃ₐ[F] Q := hs.completionEquiv q
  let L := P.pair.center
  let B := P.pair.algebra
  let i : L →+* F := j.symm.toRingHom.comp ((algebraMap K Q).comp P.pair.centerEquiv.toRingHom)
  let : Algebra L F := i.toAlgebra
  let : IsScalarTower E L F := IsScalarTower.of_algebraMap_eq fun a => by
    apply j.injective
    change algebraMap F Q (algebraMap E F a) =
      j (j.symm (algebraMap K Q (P.pair.centerEquiv (algebraMap E L a))))
    rw [j.apply_symm_apply, P.pair.centerEquiv.commutes, ← IsScalarTower.algebraMap_apply E K Q,
      ← IsScalarTower.algebraMap_apply E F Q]
  let M := P.splitting.field
  let : FiniteDimensional L M := FiniteDimensional.right E L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois E L M
  let C := Brauer.baseChange F B
  let b := P.brauerClass σ
  have hb : Brauer.scalarExtension F b = m • Brauer.classOf C := by
    have ht := DFunLike.congr_fun (Brauer.scalarExtension_tower (K := E) L F) b
    change Brauer.scalarExtension F (Brauer.scalarExtension L b) = Brauer.scalarExtension F b at ht
    rw [← ht]
    change Brauer.scalarExtension F (Brauer.scalarExtension L
      (discriminantClass P.center_ne_one (P.isUnitary σ) P.splitting.chart)) = _
    rw [scalarExtension_discriminantClass, map_nsmul, Brauer.scalarExtension_classOf]
  obtain ⟨D, ⟨eD⟩, hD⟩ := h
  let e₀ : C ≃+* CompletedAlgebra K A q.val := Brauer.tensorSemilinearEquiv P.pair.centerEquiv.toRingEquiv
    j.toRingEquiv P.pair.algebraEquiv (fun l => j.apply_symm_apply _) P.pair.scalar_eq
  let e := e₀.trans eD.toRingEquiv
  have he (t : F) : e (algebraMap F C t) = algebraMap Q D (j t) := by
    change eD (j t ⊗ₜ[K] P.pair.algebraEquiv (1 : B)) = _
    rw [map_one]
    exact eD.commutes (j t)
  have hz₂ : 2 • (m • Brauer.classOf C) = 0 := by
    rw [← hb, ← map_nsmul, P.two_nsmul_brauerClass, map_zero]
  have hz₂' : 2 • (m • Brauer.classOf D) = 0 := by
    rw [← mul_smul]
    exact (Brauer.nsmul_classOf_eq_zero_iff_of_semilinear j.toRingEquiv e he (2 * m)).mp
      ((mul_smul 2 m (Brauer.classOf C)).trans hz₂)
  let y := localInvariant ι p (brauerEquiv E (AlgebraicClosure E) b)
  have hy₂ : 2 • y = 0 := by
    change 2 • localInvariant ι p (brauerEquiv E (AlgebraicClosure E) b) = 0
    rw [← map_nsmul, ← map_nsmul, P.two_nsmul_brauerClass, map_zero, map_zero]
  have hx₂ : 2 • (m • x) = 0 := by
    rw [← hD, ← map_nsmul, ← map_nsmul, hz₂', map_zero]
  have hy0 : y = 0 ↔ m • x = 0 := by
    let : ValuativeRel F := Langlands.Global.FiniteCompletion.valuativeRel p
    let : IsNonarchimedeanLocalField F := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField p
    change localInvariant ι p (brauerEquiv E (AlgebraicClosure E) b) = 0 ↔ _
    rw [localInvariant_brauerEquiv, hb, ← hD, ← map_nsmul,
      map_eq_zero_iff _ (localBrauerInvariant F).injective,
      map_eq_zero_iff _ (finiteBrauerInvariant K q.val).injective]
    exact Brauer.nsmul_classOf_eq_zero_iff_of_semilinear j.toRingEquiv e he m
  exact (halfClass_of_two_nsmul_eq_zero hy₂).trans
    ((if_congr hy0 rfl rfl).trans
      (halfClass_of_two_nsmul_eq_zero hx₂).symm)

end Langlands.Shimura.FiniteUnitary

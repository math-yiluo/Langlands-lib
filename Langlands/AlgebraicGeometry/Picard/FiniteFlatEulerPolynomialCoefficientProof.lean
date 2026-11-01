import Langlands.AlgebraicGeometry.Picard.FiniteFlatEulerPolynomialCoefficientStatement
import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomial
import Langlands.AlgebraicGeometry.Modules.LineBundleFiniteFreeEulerProof
import Langlands.AlgebraicGeometry.Modules.FiniteFlatPushforwardGenericBasisProof
import Langlands.AlgebraicGeometry.Picard.AffinePullbackTensorPowerEulerProof
import Langlands.Algebra.RationalPolynomialDifferenceComparisonProof

/-! # Native finite-flat rank in actual top Euler coefficients -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The actual coherent sequence for the free coefficient sheaf is the rank
multiple of the actual line-bundle Euler sequence. -/
theorem coherentEulerSequence_finiteFree {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of K)) [IsProper s]
    (L : LineBundle X) (r : ℕ)
    (hL : ∀ n, HasFiniteCohomology s (tensorPow L.obj n)) :
    coherentEulerSequence s
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
        (fun U => finiteFreeSections_finite X r U.1) L =
      fun n => (r : ℚ) * (eulerCharacteristic s (tensorPow L.obj n) (hL n) : ℚ) := by
  ext n
  let Ln : LineBundle X := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
  let F := SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle F Ln.obj Ln.property
  have hF : HasFiniteAffineSections F := fun U => finiteFreeSections_finite X r U.1
  let hFn := hasFiniteCohomology_of_coherent s (tensorObj F Ln.obj)
    (hF.tensor_lineBundle Ln.property)
  let hLnF := (lineBundleFiniteFreeEuler K X s Ln r (hL n)).1
  have hi := eulerCharacteristic_eq_of_iso s hFn hLnF (tensorComm F Ln.obj)
  have he := (lineBundleFiniteFreeEuler K X s Ln r (hL n)).2 hLnF
  change (eulerCharacteristic s (tensorObj F Ln.obj) hFn : ℚ) = _
  rw [hi, he]
  push_cast
  rfl

/-- Affine projection identifies the actual coherent pushforward sequence
with the actual Euler values of the pulled-back tensor powers. -/
theorem coherentEulerSequence_finitePushforward {K : Type u} [Field K]
    {X Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of K)) [IsProper s]
    (f : X ⟶ Y) [IsAffineHom f] (L : LineBundle Y)
    [((Scheme.Modules.pushforward f).obj (structureSheaf X)).IsQuasicoherent]
    (hP : HasFiniteAffineSections
      ((Scheme.Modules.pushforward f).obj (structureSheaf X)))
    (hF : ∀ n, HasFiniteCohomology (f ≫ s)
      (tensorPow ((Scheme.Modules.pullback f).obj L.obj) n)) :
    coherentEulerSequence s ((Scheme.Modules.pushforward f).obj (structureSheaf X)) hP L =
      fun n => (eulerCharacteristic (f ≫ s)
        (tensorPow ((Scheme.Modules.pullback f).obj L.obj) n) (hF n) : ℚ) := by
  ext n
  let P := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  have hLn := tensorPow_isLocallyFreeRankOne Y L n
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle P _ hLn
  let hPn := hasFiniteCohomology_of_coherent s (tensorObj P (tensorPow L.obj n))
    (hP.tensor_lineBundle hLn)
  let hLnP := hasFiniteCohomology_of_iso s (tensorComm P (tensorPow L.obj n)) hPn
  have hi := eulerCharacteristic_eq_of_iso s hPn hLnP (tensorComm P (tensorPow L.obj n))
  have he := (affinePullbackTensorPowerEuler K X Y f inferInstance s L n).2 (hF n) hLnP
  change (eulerCharacteristic s (tensorObj P (tensorPow L.obj n)) hPn : ℚ) = _
  rw [hi, ← he]

/-- On an integral proper target of dimension at most d, native finite-flat
rank gives equality of the d-th differences of actual Euler sequences. -/
theorem finiteFlat_topEulerDifference_eq_zero {K : Type u} [Field K]
    {X Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of K)) [IsProper s]
    [IsNoetherian Y] [Y.IsSeparated] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (d : ℕ)
    (hd : topologicalKrullDim Y ≤ d) (L : LineBundle Y)
    (hL : ∀ n, HasFiniteCohomology s (tensorPow L.obj n))
    (hF : ∀ n, HasFiniteCohomology (f ≫ s)
      (tensorPow ((Scheme.Modules.pullback f).obj L.obj) n)) (x : Y) :
    (fwdDiff 1)^[d]
      ((fun n => (eulerCharacteristic (f ≫ s)
          (tensorPow ((Scheme.Modules.pullback f).obj L.obj) n) (hF n) : ℚ)) -
        fun n => (f.finrank x : ℚ) *
          (eulerCharacteristic s (tensorPow L.obj n) (hL n) : ℚ)) = 0 := by
  let P := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  obtain ⟨hPQ, hPfin, _⟩ := finiteFlatPushforwardStructure X Y f inferInstance inferInstance
  have : P.IsQuasicoherent := hPQ
  have hP : HasFiniteAffineSections P := fun U => (hPfin U).1
  let F := SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin (f.finrank x)))
  have hFfin : HasFiniteAffineSections F :=
    fun U => finiteFreeSections_finite Y (f.finrank x) U.1
  obtain ⟨U, hUne, ⟨i⟩⟩ :=
    finiteFlatPushforwardGenericBasis X Y f inferInstance inferInstance
      inferInstance inferInstance x
  let T : IrreducibleCloseds Y :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  have hT : height T ≤ d := NoetherianVanishing.height_le_of_topologicalKrullDim_le hd T
  have hPT : QuasicoherentLocal.VanishesOn P
      ⟨(T : Set Y)ᶜ, T.isClosed.isOpen_compl⟩ := by
    apply (NoetherianVanishing.VanishesOn.bot P).mono
    intro y hy
    exact (hy (Set.mem_univ y)).elim
  have hFT : QuasicoherentLocal.VanishesOn F
      ⟨(T : Set Y)ᶜ, T.isClosed.isOpen_compl⟩ := by
    apply (NoetherianVanishing.VanishesOn.bot F).mono
    intro y hy
    exact (hy (Set.mem_univ y)).elim
  let e : P.restrict U.1.ι ≅ (Scheme.Modules.restrictFunctor U.1.ι).obj F :=
    i ≪≫ (restrictFiniteFreeIso U.1.ι (f.finrank x)).symm
  have he := iterate_fwdDiff_sub_of_irreducible s d F P hFfin hP L T hT
    U.1 U.2 (by obtain ⟨y, hy⟩ := hUne; exact ⟨y, Set.mem_univ y, hy⟩) hFT hPT e
  rw [coherentEulerSequence_finiteFree s L (f.finrank x) hL,
    coherentEulerSequence_finitePushforward s f L hP hF] at he
  exact he

/-- Actual native finite-flat rank compares the top coefficients of arbitrary
polynomials evaluating to the two Euler sequences. -/
theorem finiteFlat_eulerPolynomial_coeff {K : Type u} [Field K]
    {X Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of K)) [IsProper s]
    [IsNoetherian Y] [Y.IsSeparated] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (d : ℕ)
    (hd : topologicalKrullDim Y ≤ d) (L : LineBundle Y)
    (hL : ∀ n, HasFiniteCohomology s (tensorPow L.obj n))
    (hF : ∀ n, HasFiniteCohomology (f ≫ s)
      (tensorPow ((Scheme.Modules.pullback f).obj L.obj) n))
    (P Q : Polynomial ℚ)
    (hP : ∀ n : ℕ, P.eval (n : ℚ) =
      (eulerCharacteristic s (tensorPow L.obj n) (hL n) : ℚ))
    (hQ : ∀ n : ℕ, Q.eval (n : ℚ) = (eulerCharacteristic (f ≫ s)
      (tensorPow ((Scheme.Modules.pullback f).obj L.obj) n) (hF n) : ℚ))
    (x : Y) : Q.coeff d = (f.finrank x : ℚ) * P.coeff d := by
  apply Langlands.Algebra.RationalPolynomial.coeff_eq_of_iterate_fwdDiff_sub_eq_zero
  have he := finiteFlat_topEulerDifference_eq_zero s f d hd L hL hF x
  simpa only [← hP, ← hQ] using he

/-- The actual finite-flat top Euler coefficient theorem. -/
theorem finiteFlatEulerPolynomialCoefficient :
    FiniteFlatEulerPolynomialCoefficientStatement.{u} := by
  intro K _ X Y s hp hn hsep hint f hf hflat d hd L hL hF P Q hP hQ x
  let : IsProper s := hp
  let : IsNoetherian Y := hn
  let : Y.IsSeparated := hsep
  let : IsIntegral Y := hint
  let : IsFinite f := hf
  let : Flat f := hflat
  exact finiteFlat_eulerPolynomial_coeff s f d hd L hL hF P Q hP hQ x

end Langlands.AlgebraicGeometry.Picard

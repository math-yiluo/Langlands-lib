import Langlands.Representation.CuspidalSupport.LeviTensorFactorizationStatement
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.CuspidalSupport.LeviTensorReflectionProof
import Langlands.Representation.Smooth.SmallRealizationProof

/-! Small-universe tensor exhaustion for irreducible cuspidal standard Levis,
assembled from finite factorization, supercuspidality reflection, and small
realization. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uW uV

/-- Tensor the actual factor equivalences across independent carrier universes. -/
private def blockTensorEquiv {F : Type uF} [CommRing F] {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uW} {W : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)}
    (e : ∀ i, (ρ i).Equiv (τ i)) :
    (B.blockTensor ρ).Equiv (B.blockTensor τ) :=
  Representation.Equiv.mk (PiTensorProduct.congr (fun i => (e i).toLinearEquiv))
    (by
      intro g
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, BlockShape.blockTensor_tprod,
        PiTensorProduct.congr_tprod]
      congr 1
      funext i
      exact DFunLike.congr_fun ((e i).isIntertwining' (g i)) (v i))

/-- Every irreducible cuspidal standard Levi representation is equivalent to
the block tensor of irreducible supercuspidal representations in an
independently prescribed carrier universe. -/
theorem padicLeviCuspidalFactorization :
    PadicLeviCuspidalFactorizationStatement.{uF, uW, uV} := by
  classical
  intro p _ F T n hn B
  let := T.topology
  intro σ hσ hcuspidal
  obtain ⟨A, hAI, hAA, ⟨efactor⟩⟩ :=
    padicLeviAdmissibleFactorization.{uF, uW} p F T n hn B σ hσ hcuspidal.1
  have hquasi := (isLeviQuasicuspidal_iff_of_equiv B efactor).mp hcuspidal.2
  have hsuper := padicLeviTensorSupercuspidalReflection.{uF, uW}
    p F T n hn B A hAI hAA hquasi
  have hrealize := fun i =>
    padicIrreducibleSmoothSmallRealization.{uF, uW, uV} p F T (B.size i) (A i) (hAI i)
  choose C hC eC using hrealize
  let D : ∀ i : Fin B.length,
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i) :=
    fun i => ⟨C i, hC i, isSupercuspidal_of_equiv (eC i).some (hsuper i)⟩
  refine ⟨D, ⟨efactor.trans ?_⟩⟩
  exact blockTensorEquiv B (fun i => (eC i).some)

end Langlands.CuspidalSupport

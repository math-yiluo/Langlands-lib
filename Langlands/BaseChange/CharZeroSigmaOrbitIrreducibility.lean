import Langlands.BaseChange.SupercuspidalSigmaOrbitIrreducibility
import Langlands.Global.Factors.GLPoleRegionTransport
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.LocalField.SuppliedPadicExtension

/-! # Irreducibility of sigma-orbit products on characteristic-zero local fields -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v uW

namespace Langlands.BaseChange

open CharZeroLocalField GeneralLinear LocalField

set_option maxHeartbeats 1200000 in
/-- An irreducible supercuspidal representation of the original upper field
has an irreducible full normalized sigma-orbit product. -/
theorem sigmaOrbitProduct_irreducible_of_charZero
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E] [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) (s n : ℕ) (hn : 0 < n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P₁ : Representation ℂ (GeneralLinear n E) W) (hi : P₁.IsIrreducible)
    (hsc : IsSupercuspidal P₁) : (sigmaOrbitProduct σ s hn P₁).IsIrreducible := by
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let K := padicField F
  let T := topologicalData F
  let J := PadicField.ofField (p := p) E
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier E := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier E := (inferInstance : FiniteDimensional F E)
  let S : J.TopologicalData := suppliedPadicExtension T E
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))
  let : Algebra F J.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) F J.Carrier := (inferInstance : IsScalarTower (Padic p) F E)
  have horbit : (@sigmaOrbitProduct F _ E _ S.valuativeRel S.topology S.localField _
      σ s n hn W _ _ P₁).IsIrreducible := by
    have hcusp : @IsSupercuspidal E _ S.topology n W _ _ P₁ := hsc
    rw [S.eq_canonicalTopologicalData] at hcusp ⊢
    exact supercuspidalSigmaOrbitIrreducibility p J F σ s n hn W P₁ hi hcusp
  exact horbit

/-- Rank reindexing and representation equivalence preserve the irreducibility
of the original normalized orbit product. -/
theorem isIrreducible_of_sigmaOrbitProduct_equiv
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E] [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) {s n m : ℕ} (hn : 0 < n) (h : s * n = m)
    {W₁ W : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W] [Module ℂ W]
    {P₁ : Representation ℂ (GeneralLinear n E) W₁}
    {P : Representation ℂ (GeneralLinear m E) W}
    (hi : P₁.IsIrreducible) (hsc : IsSupercuspidal P₁)
    (e : P.Equiv ((sigmaOrbitProduct σ s hn P₁).comp
      (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) : P.IsIrreducible :=
  (isIrreducible_iff_of_equiv e).mpr ((CuspidalSupport.isIrreducible_comp_mulEquiv_iff _
    (GeneralLinear.reindex (R := E) (finCongr h)).symm).mpr
    (sigmaOrbitProduct_irreducible_of_charZero σ s n hn P₁ hi hsc))

end Langlands.BaseChange

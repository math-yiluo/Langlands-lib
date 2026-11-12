import Langlands.Shimura.Unitary.HarrisSplitPrimeLevels
import Langlands.Shimura.Unitary.InvolutionBaseChangeTower

/-!
# Harris's levels `K(N, m)` through an identification of `GG` and `GJ` away from `p`

An isomorphism of scalar-extended algebras intertwining the involutions gives an isomorphism of
topological point groups. For Harris's two inner forms `GG` and `GJ`, an identification
`GG(A_f^p) ≅ GJ(A_f^p)` of this kind transports a level `K(m)^p` of `GJ(A_f^p)` to `GG(A_f^p)`,
and the level `K(N, m) = K_p × K(m)^p` of `GG(A_f)` is formed with the split-prime level `K_p`.
-/

noncomputable section

open scoped TensorProduct NumberField
open NumberField

set_option autoImplicit false

universe u v w z z'

namespace Langlands.Shimura

open Global CompactOpenLevel

namespace AlgebraInvolution

variable {A : Type z} {B : Type z'} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]
variable (σ : AlgebraInvolution ℚ A) (τ : AlgebraInvolution ℚ B)
variable {S : Type w} [CommRing S] [Algebra ℚ S] [TopologicalSpace S]

/-- An isomorphism `S ⊗[ℚ] A ≃ S ⊗[ℚ] B` of `S`-algebras intertwining the scalar-extended
involutions induces an isomorphism of the topological point groups `σ.Points S ≃ τ.Points S`;
it preserves the multiplier. -/
def pointsHomeomorphOfEquiv (e : S ⊗[ℚ] A ≃ₐ[S] S ⊗[ℚ] B)
    (he : ∀ x, e (σ.baseChange S x) = τ.baseChange S (e x)) :
    σ.Points S ≃ₜ* τ.Points S where
  toMulEquiv := similitudesEquiv (σ.baseChange S) (τ.baseChange S) e he
  continuous_toFun := by
    let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S _
    let : TopologicalSpace (S ⊗[ℚ] B) := moduleTopology S _
    have := ModuleTopology.continuousAdd S (S ⊗[ℚ] B)
    have := ModuleTopology.continuousSMul S (S ⊗[ℚ] B)
    have hcont : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    exact (((hcont.units_map e.toRingHom.toMonoidHom).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
      ((continuous_id.units_map (RingHom.id S).toMonoidHom).comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun := by
    let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S _
    let : TopologicalSpace (S ⊗[ℚ] B) := moduleTopology S _
    have := ModuleTopology.continuousAdd S (S ⊗[ℚ] A)
    have := ModuleTopology.continuousSMul S (S ⊗[ℚ] A)
    have hcont : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    exact (((hcont.units_map e.symm.toRingHom.toMonoidHom).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
      ((continuous_id.units_map (RingHom.id S).toMonoidHom).comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _

@[simp] theorem pointsHomeomorphOfEquiv_unit (e : S ⊗[ℚ] A ≃ₐ[S] S ⊗[ℚ] B)
    (he : ∀ x, e (σ.baseChange S x) = τ.baseChange S (e x)) (g : σ.Points S) :
    ((pointsHomeomorphOfEquiv σ τ e he g).1.1 : S ⊗[ℚ] B) = e (g.1.1 : S ⊗[ℚ] A) := rfl

@[simp] theorem pointsHomeomorphOfEquiv_multiplier (e : S ⊗[ℚ] A ≃ₐ[S] S ⊗[ℚ] B)
    (he : ∀ x, e (σ.baseChange S x) = τ.baseChange S (e x)) (g : σ.Points S) :
    Points.multiplier τ S (pointsHomeomorphOfEquiv σ τ e he g) = Points.multiplier σ S g :=
  Units.ext rfl

end AlgebraInvolution

section Harris

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]
variable {B : Type z} [Ring B] [Algebra K B] [Algebra E B] [IsScalarTower E K B]
  [Algebra ℚ B] [IsScalarTower ℚ E B]
variable {D : Type z'} [Ring D] [Algebra K D] [Algebra E D] [IsScalarTower E K D]
  [Algebra ℚ D] [IsScalarTower ℚ E D]
variable (σB : SecondKindInvolution E K B) (σD : SecondKindInvolution E K D) (p : ℕ)

/-- Harris's identification `GJ(A_f^p) ≅ GG(A_f^p)`, induced by an isomorphism of the
scalar extensions of the two algebras to the prime-to-`p` finite adeles that intertwines the
involutions. -/
def SecondKindInvolution.innerFormPrimeToEquiv
    (e : PrimeToFiniteAdeles p ⊗[ℚ] D ≃ₐ[PrimeToFiniteAdeles p] PrimeToFiniteAdeles p ⊗[ℚ] B)
    (he : ∀ x, e (σD.rationalInvolution.baseChange _ x) =
      σB.rationalInvolution.baseChange _ (e x)) :
    σD.rationalInvolution.PrimeToPoints p ≃ₜ* σB.rationalInvolution.PrimeToPoints p :=
  AlgebraInvolution.pointsHomeomorphOfEquiv _ _ e he

variable [Module.Finite ℚ B] (ι : F →+* K) (hp : p.Prime)
  (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}) (u : F →+* FiniteCompletion ℚ v.1)

/-- Harris's level `K(N, m) = K_p × K(m)^p` of `GG(A_f)`: the split-prime level
`K_p = C × ℤ_vˣ` of `GG(ℚ_v)` and the transport of a level `K(m)^p` of `GJ(A_f^p)` through
`innerFormPrimeToEquiv`. -/
def SecondKindInvolution.innerFormAdelicLevel (C : CompactOpenLevel (SplitPrimeUnits B ι v.1 u))
    (e : PrimeToFiniteAdeles p ⊗[ℚ] D ≃ₐ[PrimeToFiniteAdeles p] PrimeToFiniteAdeles p ⊗[ℚ] B)
    (he : ∀ x, e (σD.rationalInvolution.baseChange _ x) =
      σB.rationalInvolution.baseChange _ (e x))
    (Km : CompactOpenLevel (σD.rationalInvolution.PrimeToPoints p)) :
    CompactOpenLevel σB.rationalInvolution.FiniteAdelicPoints :=
  σB.splitPrimeAdelicLevel ι p hp v u C (transport (σB.innerFormPrimeToEquiv σD p e he) Km)

omit [IsScalarTower E K B] [IsScalarTower E K D] in
/-- A finite adelic point of `GG` lies in `K(N, m)` exactly when its local image at `v` lies in
`K_p` and the image of its prime-to-`p` component in `GJ(A_f^p)` lies in `K(m)^p`. -/
theorem SecondKindInvolution.mem_innerFormAdelicLevel
    (C : CompactOpenLevel (SplitPrimeUnits B ι v.1 u))
    (e : PrimeToFiniteAdeles p ⊗[ℚ] D ≃ₐ[PrimeToFiniteAdeles p] PrimeToFiniteAdeles p ⊗[ℚ] B)
    (he : ∀ x, e (σD.rationalInvolution.baseChange _ x) =
      σB.rationalInvolution.baseChange _ (e x))
    (Km : CompactOpenLevel (σD.rationalInvolution.PrimeToPoints p))
    (g : σB.rationalInvolution.FiniteAdelicPoints) :
    g ∈ (σB.innerFormAdelicLevel σD p ι hp v u C e he Km).subgroup ↔
      σB.rationalInvolution.finiteLocalMap v.1 g ∈ (σB.splitPrimeLevel ι v.1 u C).subgroup ∧
        (σB.innerFormPrimeToEquiv σD p e he).symm
          (σB.rationalInvolution.finiteAdelicPointsSplit p hp.ne_zero g).2 ∈ Km.subgroup :=
  σB.mem_splitPrimeAdelicLevel ι p hp v u C _ g

section Tower

open CategoryTheory

variable [IsScalarTower ℚ K B] {n : ℕ} (DB : CentralSimpleUnitaryData E K B n)
  (h : HasHarrisSignature DB.toSecondKindInvolution n) (τ₀ : F →+* ℂ)
  (C : CompactOpenLevel (SplitPrimeUnits B ι v.1 u))
  (e : PrimeToFiniteAdeles p ⊗[ℚ] D ≃ₐ[PrimeToFiniteAdeles p] PrimeToFiniteAdeles p ⊗[ℚ] B)
  (he : ∀ x, e (σD.rationalInvolution.baseChange _ x) =
    DB.toSecondKindInvolution.rationalInvolution.baseChange _ (e x))

/-- The Harris tower over the levels `K(N, m) = K_p × K(m)^p` of `GG(A_f)`, indexed by the levels
`K(m)^p` of `GJ(A_f^p)`: the published tower away from `p` at `K_p`, precomposed with the
transport of levels through `innerFormPrimeToEquiv`. -/
def harrisInnerFormTower :
    CompactOpenLevel (σD.rationalInvolution.PrimeToPoints p) ⥤ TopCat.{max z u} :=
  transportFunctor (DB.toSecondKindInvolution.innerFormPrimeToEquiv σD p e he) ⋙
    harrisSplitPrimeTower DB h ι τ₀ p hp v u C

omit [IsScalarTower E K B] [IsScalarTower E K D] [IsScalarTower ℚ K B] in
/-- The level of `GG(A_f)` attached to a level `K(m)^p` of `GJ(A_f^p)` by the away functor at
`K_p` is `innerFormAdelicLevel`. -/
theorem innerForm_awayOver_obj (Km : CompactOpenLevel (σD.rationalInvolution.PrimeToPoints p)) :
    (transportFunctor (DB.toSecondKindInvolution.innerFormPrimeToEquiv σD p e he) ⋙
        (awayOver (DB.toSecondKindInvolution.rationalInvolution.finiteAdelicPointsSplit p
          hp.ne_zero) (DB.toSecondKindInvolution.splitPrimeDividingLevel ι p hp v u C)).functor).obj
        Km =
      DB.toSecondKindInvolution.innerFormAdelicLevel σD p ι hp v u C e he Km :=
  rfl

/-- The Harris level tower at the levels `K(N, m)`, as `K(m)^p` varies over the levels of
`GJ(A_f^p)`, is `harrisInnerFormTower`. -/
def harrisInnerFormTowerIso :
    transportFunctor (DB.toSecondKindInvolution.innerFormPrimeToEquiv σD p e he) ⋙
        (awayOver (DB.toSecondKindInvolution.rationalInvolution.finiteAdelicPointsSplit p
          hp.ne_zero) (DB.toSecondKindInvolution.splitPrimeDividingLevel ι p hp v u C)).functor ⋙
        harrisUnitaryLevelTower DB h ι τ₀ ≅
      harrisInnerFormTower σD p ι hp v u DB h τ₀ C e he :=
  Functor.isoWhiskerLeft _ (harrisSplitPrimeTowerIso DB h ι τ₀ p hp v u C)

end Tower

end Harris

end Langlands.Shimura

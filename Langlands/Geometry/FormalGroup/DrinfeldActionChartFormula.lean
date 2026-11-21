import Langlands.Geometry.FormalGroup.DrinfeldFramedAction
import Langlands.Geometry.FormalGroup.DrinfeldFramedChartTransition

/-! # The Drinfeld framing formula in normalized chart coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s w

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralSimple ModuleLaw

attribute [local instance] coefficientAlgebra coefficientScalarTower

section ChartNormalization

variable {O : Type u} [CommRing O] {S : Type v} [CommRing S] [Algebra O S]
variable {F : Type w} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O S σ} {P : ModuleLaw O S τ}
variable {T U : BasicAtlas O S υ}
variable {C : CommAlgCat.{v} S}

private def normalizedForward (M : ModuleLaw O S σ) (T : BasicAtlas O S υ)
    (ρ : BasicAtlas.RationalHom F (BasicAtlas.ofGlobalCover M T.opens T.covers) T rfl)
    (C : CommAlgCat.{v} S) (b : T.opens) (hb : IsUnit (algebraMap S C b.val)) :=
  ModuleLaw.RationalHom.comp
    (BasicAtlas.RationalHom.onChart (F := F) (X := BasicAtlas.ofGlobalCover M T.opens T.covers)
      (Y := T) (h := rfl) C b hb ρ)
    (ModuleLaw.RationalHom.ofHom (BasicAtlas.globalChartIso M b.val C hb).inv)

private theorem normalizedForward_congr (e : T = U)
    {ρ : BasicAtlas.RationalHom F (BasicAtlas.ofGlobalCover M T.opens T.covers) T rfl}
    {ρ' : BasicAtlas.RationalHom F (BasicAtlas.ofGlobalCover M U.opens U.covers) U rfl}
    (hρ : HEq ρ ρ') (b : T.opens) (b' : U.opens) (he : b.val = b'.val)
    (hb : IsUnit (algebraMap S C b.val)) (hb' : IsUnit (algebraMap S C b'.val)) :
    HEq (normalizedForward M T ρ C b hb) (normalizedForward M U ρ' C b' hb') := by
  subst U
  have : b = b' := Subtype.ext he
  subst b'
  cases eq_of_heq hρ
  rfl

private theorem normalizedForward_precomp
    (ρ : BasicAtlas.RationalHom F (BasicAtlas.ofGlobalCover P T.opens T.covers) T rfl)
    (f : ModuleLaw.RationalHom F M P) (b : T.opens) (hb : IsUnit (algebraMap S C b.val)) :
    normalizedForward M T (BasicAtlas.RationalHom.comp ρ (BasicAtlas.ofGlobalRationalHom T.opens T.covers f))
      C b hb = ModuleLaw.RationalHom.comp (normalizedForward P T ρ C b hb)
        (ModuleLaw.RationalHom.map (IsScalarTower.toAlgHom O S C) f) := by
  let i := BasicAtlas.globalChartIso M b.val C hb
  let j := BasicAtlas.globalChartIso P b.val C hb
  let r := BasicAtlas.RationalHom.onChart (F := F) (X := BasicAtlas.ofGlobalCover P T.opens T.covers)
    (Y := T) (h := rfl) C b hb ρ
  let fC := ModuleLaw.RationalHom.map (IsScalarTower.toAlgHom O S C) f
  let iHom := ModuleLaw.RationalHom.ofHom (F := F) i.hom
  let iInv := ModuleLaw.RationalHom.ofHom (F := F) i.inv
  let jInv := ModuleLaw.RationalHom.ofHom (F := F) j.inv
  have hId : ModuleLaw.RationalHom.comp iHom iInv = ModuleLaw.RationalHom.id _ := by
    change ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom i.hom)
      (ModuleLaw.RationalHom.ofHom i.inv) = _
    rw [← ModuleLaw.RationalHom.ofHom_comp, i.hom_inv]
    rfl
  have heval := BasicAtlas.RationalHom.onChart_comp ρ
    (BasicAtlas.ofGlobalRationalHom T.opens T.covers f) C b hb
  have hglobal := BasicAtlas.onChart_ofGlobalRationalHom f T.opens T.covers C b hb
  have hcomp := heval.trans (congrArg (ModuleLaw.RationalHom.comp r) hglobal)
  calc
    _ = ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.comp r
        (ModuleLaw.RationalHom.comp jInv (ModuleLaw.RationalHom.comp fC iHom))) iInv :=
      congrArg (fun q => ModuleLaw.RationalHom.comp q iInv) hcomp
    _ = _ := by
      change _ = ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.comp r jInv) fC
      simp only [ModuleLaw.RationalHom.comp_assoc, hId, ModuleLaw.RationalHom.comp_id]

end ChartNormalization

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {π : 𝒪[K]}
variable (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
variable (g : GL (Fin (reducedDegree K D)) K × Dˣ)
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
variable (c : Φ.val.MatrixCoordinates)

namespace DrinfeldResidue

variable {S : Type u} [CommRing S] [Algebra 𝒪[K] S] {a b : κ →ₐ[𝒪[K]] S}

/-- The three source factors of the printed formula, as one whole rational formal map. -/
def actionSourceHom (e : shift (DrinfeldAction.exponent K D g) b = a) :
    ModuleLaw.RationalHom K (Φ.val.formalModule.map a) (Φ.val.formalModule.map b) :=
  ModuleLaw.RationalHom.comp ((c.quasiIsogeny g.1⁻¹).map b).hom.val
    (ModuleLaw.RationalHom.comp (rationalAction K D (Φ.val.order.map b) ((g.2⁻¹ : Dˣ) : D))
      (signedFrameFrobenius Φ p hcard hFrob (DrinfeldAction.exponent K D g) e).hom.val)

end DrinfeldResidue

namespace DrinfeldFramedAtlas

variable {Φ}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable (X : DrinfeldFramedAtlas Φ A)
variable (hRank : ∀ j : ℕ, RelativeFrobeniusIsogenyStatement Φ.val.formalModule p (f * j))

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
/-- The underlying reduced atlas of the transformed target retains the original cover and transitions. -/
theorem actionReduction_atlas : (X.actionTarget g).val.reduction.atlas = X.target.val.reduction.atlas := by
  have h := congrArg SpecialAtlas.atlas (X.actionTarget_reduction g)
  exact h

set_option maxHeartbeats 1000000 in
/-- Restriction of the global source factors gives the whole transformed framing tensor. -/
theorem act_rho_precomp : HEq (X.act g p hcard hFrob hRank c).rho.hom.val
    (BasicAtlas.RationalHom.comp X.rho.hom.val
      (BasicAtlas.ofGlobalRationalHom X.target.val.reduction.atlas.opens X.target.val.reduction.atlas.covers
        (DrinfeldResidue.actionSourceHom Φ g p hcard hFrob c (b := X.residueMap) rfl))) := by
  refine (X.actionFraming_hom g p hcard hFrob c).trans (heq_of_eq ?_)
  let t := X.target.val.reduction.atlas.opens
  let ht := X.target.val.reduction.atlas.covers
  have hd : atlasRationalAction K D X.source.order ((g.2⁻¹ : Dˣ) : D) =
      BasicAtlas.ofGlobalRationalHom t ht (rationalAction K D (Φ.val.order.map X.residueMap) ((g.2⁻¹ : Dˣ) : D)) :=
    atlasRationalAction_ofGlobalCover _ _ _ _
  rw [hd]
  simp only [DrinfeldResidue.actionSourceHom, BasicAtlas.ofGlobalRationalHom_comp]
  rfl

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem chartFraming_hom_normalized
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : X.target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b.val)) :
    (X.chartFraming C b hb).hom.val =
      normalizedForward X.globalFrame.formalModule X.target.val.reduction.atlas X.rho.hom.val
        C b hb := rfl

set_option maxHeartbeats 500000 in
/-- On a test of an original reduced chart, the normalized transformed framing
precomposes the original normalized framing by the specified three source factors. -/
theorem chartFraming_act_hom
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : X.target.val.reduction.atlas.opens) (b' : (X.actionTarget g).val.reduction.atlas.opens)
    (eqGen : b'.val = b.val)
    (hb : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b.val))
    (hb' : IsUnit (algebraMap ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b'.val)) :
    HEq ((X.act g p hcard hFrob hRank c).chartFraming C b' hb').hom.val
      (ModuleLaw.RationalHom.comp (X.chartFraming C b hb).hom.val
        (ModuleLaw.RationalHom.map (IsScalarTower.toAlgHom 𝒪[K]
          ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C)
          (DrinfeldResidue.actionSourceHom Φ g p hcard hFrob c (b := X.residueMap) rfl))) := by
  have htransport := normalizedForward_congr (M := Φ.val.formalModule.map (X.actionResidueMap g))
    (X.actionReduction_atlas g)
    (X.act_rho_precomp g p hcard hFrob c hRank) b' b eqGen hb' hb
  have hpre := normalizedForward_precomp X.rho.hom.val
    (DrinfeldResidue.actionSourceHom Φ g p hcard hFrob c (b := X.residueMap) rfl) b hb
  have horiginal := X.chartFraming_hom_normalized C b hb
  have htransformed := (X.act g p hcard hFrob hRank c).chartFraming_hom_normalized C b' hb'
  exact (heq_of_eq htransformed).trans
    (htransport.trans (heq_of_eq (hpre.trans
      (congrArg (fun ρ => ModuleLaw.RationalHom.comp ρ _) horiginal.symm))))

end DrinfeldFramedAtlas

end Langlands.FormalGroup.LocalDivision

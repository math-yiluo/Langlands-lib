import Langlands.Geometry.FormalGroup.DrinfeldActionCoverBaseChange
import Langlands.Geometry.FormalGroup.DrinfeldActionSourceBaseChange
import Langlands.Geometry.FormalGroup.DrinfeldComparisonAction
import Langlands.Geometry.FormalGroup.DrinfeldFramedFrameNaturality
import Langlands.Geometry.FormalGroup.RelativeFrobeniusIsogenyProof
import Langlands.Geometry.FormalGroup.SpecialFrameFrobenius

/-! # Drinfeld's action by natural automorphisms of the framed Nilp functor -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open Langlands.FormalGroup.ModuleLaw.BasicAtlas.RationalHom
  (comp comp_assoc id_comp comp_id)

variable {O T F : Type*} [CommRing O] [IsDomain O] [CommRing T]
  [Algebra O T] [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ : Type} [Finite σ]
variable {X Y Z X' Y' Z' : BasicAtlas O T σ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}
variable {eX : X.opens = X'.opens} {eY : Y.opens = Y'.opens} {eZ : Z.opens = Z'.opens}
variable {h' : X'.opens = Y'.opens}

private theorem transport_precomp
    (r : RationalHom F X Y h) (q : RationalHom F Y Z k)
    (a : QuasiIsogeny F X X' eX) (b : QuasiIsogeny F Y Y' eY)
    (d : RationalHom F Z Z' eZ)
    (r' : RationalHom F X' Y' h')
    (hr : comp r' a.hom = comp b.hom r) :
    comp d (comp (comp q r) a.inv) = comp (comp d (comp q b.inv)) r' := by
  have hinv : comp r a.inv = comp b.inv r' := by
    calc
      comp r a.inv = comp (comp (comp b.inv b.hom) r) a.inv := by rw [b.inv_hom, id_comp]
      _ = comp b.inv (comp (comp b.hom r) a.inv) := by simp only [comp_assoc]
      _ = comp b.inv (comp (comp r' a.hom) a.inv) :=
        congrArg (fun t => comp b.inv (comp t a.inv)) hr.symm
      _ = comp b.inv r' := by rw [comp_assoc r', a.hom_inv, comp_id]
  rw [comp_assoc q, hinv]
  simp only [comp_assoc]

end Langlands.FormalGroup.ModuleLaw.BasicAtlas

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralSimple ModuleLaw
open BasicAtlas.RationalHom (comp ofHom baseChangeAlong)

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A B : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

private def baseChangeForward (M : SpecialModule K D ι κ)
    (ψ : κ →ₐ[𝒪[K]] ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (Y : BasicAtlas 𝒪[K] A.obj (Fin (reducedDegree K D))) (f : A ⟶ B)
    (r : BasicAtlas.RationalHom K
      (BasicAtlas.ofGlobalCover (M.formalModule.map ψ) Y.reduction.opens Y.reduction.covers)
      Y.reduction rfl) :
    let Y' := (Y.baseChangeAlong (Nilp.scalarMap 𝒪[K] f)).reduction (A := B)
    BasicAtlas.RationalHom K
      (BasicAtlas.ofGlobalCover (M.formalModule.map ((Nilp.reducedScalarMap 𝒪[K] f).comp ψ))
        Y'.opens Y'.covers)
      Y' rfl :=
  comp (ofHom (Y.reductionBaseChangeIso f).inv)
    (comp (baseChangeAlong (Nilp.reducedScalarMap 𝒪[K] f) r)
      (ofHom (SpecialAtlas.quotientFrameBaseChangeOnAtlasIso M ψ Y f).inv.val))

private theorem baseChangeForward_congr (M : SpecialModule K D ι κ)
    (ψ : κ →ₐ[𝒪[K]] ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    {Y Z : BasicAtlas 𝒪[K] A.obj (Fin (reducedDegree K D))} (f : A ⟶ B)
    {r : BasicAtlas.RationalHom K
      (BasicAtlas.ofGlobalCover (M.formalModule.map ψ) Y.reduction.opens Y.reduction.covers)
      Y.reduction rfl}
    {s : BasicAtlas.RationalHom K
      (BasicAtlas.ofGlobalCover (M.formalModule.map ψ) Z.reduction.opens Z.reduction.covers)
      Z.reduction rfl}
    (hY : Y = Z) (hρ : HEq r s) :
    HEq (baseChangeForward M ψ Y f r) (baseChangeForward M ψ Z f s) := by
  subst Z
  exact heq_of_eq (congrArg (baseChangeForward M ψ Y f) (eq_of_heq hρ))

set_option maxHeartbeats 800000 in
/-- The full underlying forward framing after extension is the original extended
tensor with the actual source and target inverse comparisons. -/
private theorem baseChange_rho_forward (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    (X.baseChange f).rho.hom.val =
      baseChangeForward Φ.val X.residueMap X.target.val.atlas f X.rho.hom.val := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let j := SpecialAtlas.quotientFrameBaseChangeIso Φ.val X.residueMap X.target.val f
  let t := X.target.val.reductionBaseChangeIso f
  have h := congrArg (fun q => q.hom.val) (X.baseChange_rho_formula f)
  change (X.baseChange f).rho.hom.val =
    comp (ofHom t.inv.val) (comp (X.rho.baseChangeAlong φ).hom.val (ofHom j.inv.val)) at h
  have ht : t.inv.val = (X.target.val.atlas.reductionBaseChangeIso f).inv :=
    BasicAtlas.OrderAction.reductionBaseChangeIso_inv_val X.target.val.order f
  have hr : (X.rho.baseChangeAlong φ).hom.val = baseChangeAlong φ X.rho.hom.val :=
    BasicAtlas.OrderAction.RationalHom.baseChangeAlong_val φ X.rho.hom
  exact h.trans (congrArg₂ (fun v r => comp (ofHom v) (comp r (ofHom j.inv.val))) ht hr)

variable [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (g : GL (Fin (reducedDegree K D)) K × Dˣ)
variable (p : ℕ) [ExpChar κ p] {n : ℕ} (hcard : Nat.card 𝓀[K] = p ^ n)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (n * j))
variable (hRank : ∀ j : ℕ, RelativeFrobeniusIsogenyStatement Φ.val.formalModule p (n * j))
variable (c : Φ.val.MatrixCoordinates)

set_option maxHeartbeats 1500000 in
/-- The two action and base-change routes have the same whole underlying framing. -/
theorem act_baseChange_forward (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    HEq ((X.act g p hcard hFrob hRank c).baseChange f).rho.hom.val
      ((X.baseChange f).act g p hcard hFrob hRank c).rho.hom.val := by
  let φ := Nilp.reducedScalarMap 𝒪[K] f
  let W := X.baseChange f
  let Y := X.act g p hcard hFrob hRank c
  let a := X.actionResidueMap g
  let b := X.residueMap
  let q := DrinfeldResidue.actionSourceHom Φ g p hcard hFrob c (b := b) rfl
  let q' := DrinfeldResidue.actionSourceHom Φ g p hcard hFrob c (b := W.residueMap) rfl
  let r := SpecialAtlas.restrictFrameHom Φ.val X.target.val a b q
  let r' := SpecialAtlas.restrictFrameHom Φ.val W.target.val (φ.comp a) (φ.comp b) q'
  let a₀ := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
    (SpecialAtlas.quotientFrameBaseChangeIso Φ.val a X.target.val f)).toAtlasQuasiIsogeny
  let b₀ := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K)
    (SpecialAtlas.quotientFrameBaseChangeIso Φ.val b X.target.val f)).toAtlasQuasiIsogeny
  let d := ofHom (F := K) (X.target.val.atlas.reductionBaseChangeIso f).inv
  have hq := DrinfeldResidue.actionSourceHom_map Φ p hcard hFrob φ g c (b := b) rfl
  have hr : comp r' a₀.hom = comp b₀.hom (baseChangeAlong φ r) :=
    SpecialAtlas.quotientFrameBaseChangeIso_rational_natural Φ.val X.target.val f a b q q' hq
  have htransport := baseChangeForward_congr Φ.val a f
    (Y := Y.target.val.atlas) (Z := X.target.val.atlas)
    (r := Y.rho.hom.val) (s := comp X.rho.hom.val r)
    rfl (X.act_rho_precomp g p hcard hFrob c hRank)
  have hbaseMap := BasicAtlas.RationalHom.baseChangeAlong_comp X.rho.hom.val r φ
  have hcomp := BasicAtlas.transport_precomp (baseChangeAlong φ r)
    (baseChangeAlong φ X.rho.hom.val) a₀ b₀ d r' hr
  have hρ := (congrArg (fun t => comp d (comp t a₀.inv)) hbaseMap).trans
    (hcomp.trans (congrArg (fun t => comp t r') (X.baseChange_rho_forward f).symm))
  exact (heq_of_eq (Y.baseChange_rho_forward f)).trans
    (htransport.trans ((heq_of_eq hρ).trans (W.act_rho_precomp g p hcard hFrob c hRank).symm))

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem eq_of_residue_target_forward {X Y : DrinfeldFramedAtlas Φ B}
    (he : X.residueMap = Y.residueMap) (ht : X.target = Y.target)
    (hρ : HEq X.rho.hom.val Y.rho.hom.val) : X = Y := by
  apply eq_of_residue_target_rho he ht
  rcases X with ⟨a, X, ρ, hX⟩
  rcases Y with ⟨b, Y, σ, hY⟩
  change a = b at he
  change X = Y at ht
  subst b
  subst Y
  exact heq_of_eq (BasicAtlas.OrderAction.QuasiIsogeny.ext_hom
    (BasicAtlas.OrderAction.RationalHom.ext (eq_of_heq hρ)))

set_option maxHeartbeats 500000 in
/-- The actual height-zero framed transformation commutes with every Nilp base extension. -/
theorem act_baseChange (X : DrinfeldFramedAtlas Φ A) (f : A ⟶ B) :
    (X.act g p hcard hFrob hRank c).baseChange f =
      (X.baseChange f).act g p hcard hFrob hRank c := by
  refine eq_of_residue_target_forward ?_ ?_ (act_baseChange_forward g p hcard hFrob hRank c X f)
  · exact DrinfeldResidue.comp_shift (Nilp.reducedScalarMap 𝒪[K] f) (DrinfeldAction.exponent K D g) X.residueMap
  · exact Subtype.ext (SpecialAtlas.twistDivisionUnit_baseChangeAlong X.target.val g.2 (Nilp.scalarMap 𝒪[K] f))

namespace ComparisonClass

/-- Drinfeld's action on the comparison classes commutes with each Nilp morphism. -/
theorem act_baseChange (q : ComparisonClass Φ A) (f : A ⟶ B) :
    (act p hcard hFrob hRank c g q).baseChange f =
      act p hcard hFrob hRank c g (q.baseChange f) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact congrArg comparisonClassOf (DrinfeldFramedAtlas.act_baseChange g p hcard hFrob hRank c X f)

end ComparisonClass

private def actionNatTrans :
    comparisonClassFunctor (R := R) Φ ⟶ comparisonClassFunctor Φ where
  app A := ↾(ComparisonClass.act p hcard hFrob hRank c g)
  naturality A B f := by
    apply ConcreteCategory.hom_ext
    intro q
    exact (ComparisonClass.act_baseChange g p hcard hFrob hRank c q f).symm

private def actionNatIso :
    comparisonClassFunctor (R := R) Φ ≅ comparisonClassFunctor Φ where
  hom := actionNatTrans (R := R) g p hcard hFrob hRank c
  inv := actionNatTrans (R := R) g⁻¹ p hcard hFrob hRank c
  hom_inv_id := by
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro q
    change ComparisonClass.act p hcard hFrob hRank c g⁻¹
      (ComparisonClass.act p hcard hFrob hRank c g q) = q
    rw [← ComparisonClass.act_mul, inv_mul_cancel, ComparisonClass.act_one]
  inv_hom_id := by
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro q
    change ComparisonClass.act p hcard hFrob hRank c g
      (ComparisonClass.act p hcard hFrob hRank c g⁻¹ q) = q
    rw [← ComparisonClass.act_mul, mul_inv_cancel, ComparisonClass.act_one]

/-- The matrix and division groups act on Drinfeld's framed comparison-class
functor. The relative Frobenius rank and inverse are supplied by the actual
isogeny and full-order quasi-isogeny theorems for the fixed frame. -/
def actionHom : GL (Fin (reducedDegree K D)) K × Dˣ →*
    Aut (comparisonClassFunctor (R := R) Φ) where
  toFun g := Aut.of (actionNatIso g p hcard
    (fun j => SpecialModule.relativeFrobeniusQuasiIsogeny Φ p (n * j))
    (fun j => ModuleLaw.relativeFrobeniusIsogeny Φ.val.formalModule p (n * j)) c)
  map_one' := by
    apply Aut.ext
    apply CategoryTheory.Iso.ext
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro q
    exact ComparisonClass.act_one p hcard _ _ c q
  map_mul' a b := by
    apply Aut.ext
    apply CategoryTheory.Iso.ext
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro q
    exact ComparisonClass.act_mul p hcard _ _ c a b q

/-- Evaluation of the natural action recovers the original descended action. -/
@[simp]
theorem actionHom_app (q : ComparisonClass Φ A) :
    (actionHom (R := R) p hcard c g).asIso.hom.app A q =
      ComparisonClass.act p hcard
        (fun j => SpecialModule.relativeFrobeniusQuasiIsogeny Φ p (n * j))
        (fun j => ModuleLaw.relativeFrobeniusIsogeny Φ.val.formalModule p (n * j)) c g q := rfl

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

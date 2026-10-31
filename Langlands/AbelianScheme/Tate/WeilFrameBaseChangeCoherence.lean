import Langlands.AbelianScheme.Tate.WeilFrameBaseChange
import Langlands.AbelianScheme.Tate.AdelicFrameCoherence

/-! # Identity and composition of actual Weil-compatible frame base change -/

universe u v w
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme Langlands.Shimura.PEL

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}

  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace (A).X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace (A).X.hom).obj (dualScheme A hA)))
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
    stability composition unitCoherence associativity comparison symmetry)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω]

section Full

local notation "FA" => WeilAdelicFrame (S := S) (A := A) preservation composition unitCoherence associativity
  comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
local notation "rA" => weilAdelicFrameRightAction (S := S) (A := A) preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ

/-- Transport a compatible frame along equality of its point. -/
def weilAdelicFramePointEq {s t : Spec (.of Ω) ⟶ S} (hst : s = t) :
    FA s ≃ FA t := by
  subst t
  exact Equiv.refl _

/-- Equality transport is the actual test-scheme comparison when that
comparison has identity underlying morphism. -/
theorem weilAdelicFramePointEq_underlying {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (e : Over.mk s ≅ Over.mk t) (he : e.hom.left = 𝟙 _)
    (eta : FA s) :
    letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
    (weilAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry stability
      hA geometryA MA evaluationA compatibility lam h i V ψ hst eta).1 =
      adelicFrameTestIso A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) e eta.1 := by
  let := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  subst t
  have heq : e = Iso.refl (Over.mk s) := by
    apply Iso.ext
    apply Over.OverMorphism.ext
    exact he
  subst e
  exact (adelicFrameTestIso_refl A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) eta.1).symm

/-- Point equality preserves right precomposition. -/
theorem weilAdelicFramePointEq_right {s t : Spec (.of Ω) ⟶ S} (hst : s = t) :
    letI := rA s
    letI := rA t
    ∀ (eta : FA s) (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ),
      weilAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry stability
        hA geometryA MA evaluationA compatibility lam h i V ψ hst (right eta g) = right (weilAdelicFramePointEq
        preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA
        evaluationA compatibility lam h i V ψ hst eta) g := by
  subst t
  intro eta g
  rfl

/-- Equality transport descends to arbitrary right subgroup orbits. -/
def weilAdelicFrameRightOrbitPointEq {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rA s
    letI := rA t
    RightOrbit (FA s) U ≃ RightOrbit (FA t) U := by
  let := rA s
  let := rA t
  exact RightOrbit.equiv U (weilAdelicFramePointEq preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hst)
    (weilAdelicFramePointEq_right preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hst)

section Identity
local notation "AI" => (baseChange (𝟙 S)).obj A
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})

  (hI : HasDualScheme ((baseChange (𝟙 S)).obj A)) (geometryI : DualSchemeGeometry ((baseChange (𝟙 S)).obj A) hI)
  (MI : LineBundle ((relativeSpace (((baseChange (𝟙 S)).obj A)).X.hom).obj (dualScheme ((baseChange (𝟙 S)).obj
    A) hI)))
  (evaluationI : tensorObj (poincareFamily ((baseChange (𝟙 S)).obj A) hI).obj.carrier MI.obj ≅
    structureSheaf ((relativeSpace (((baseChange (𝟙 S)).obj A)).X.hom).obj (dualScheme ((baseChange (𝟙 S)).obj
      A) hI)))

local notation "FI" => WeilAdelicFrame (S := S) (A := AI) preservation composition unitCoherence associativity
  comparison symmetry stability hI geometryI MI evaluationI compatibility (canonicalDualValuedBaseChange (𝟙 S) A
  preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA
  MA evaluationA hI geometryI MI evaluationI lam) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ
local notation "rI" => weilAdelicFrameRightAction (S := S) (A := AI) preservation composition unitCoherence
  associativity comparison symmetry stability hI geometryI MI evaluationI compatibility
  (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ
local notation "bcId" => weilAdelicFrameBaseChange (𝟙 S) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI
  compatibility lam h i V ψ

/-- Identity pullback comparison restricted to the actual compatible-frame
subtypes, with the canonically base-changed dual-valued map. -/
def weilAdelicFrameBaseChangeId (s : Spec (.of Ω) ⟶ S) :
    FI s ≃ FA s :=
  (bcId s).trans (weilAdelicFramePointEq preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.comp_id s))

/-- The restricted identity comparison has the existing canonical geometric
identity comparison as its underlying frame map. -/
theorem weilAdelicFrameBaseChangeId_underlying (s : Spec (.of Ω) ⟶ S)
    (eta : FI s) :
    letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
    (weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI s
      eta).1 =
      adelicFrameBaseChangeId A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) s eta.1 := by
  let := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  change (weilAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.comp_id s) (bcId s eta)).1 = _
  rw [weilAdelicFramePointEq_underlying preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.comp_id s)
    ((Over.mapId S).app (Over.mk s)) rfl]
  exact adelicFrameBaseChange_id A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) s eta.1

/-- In particular, its pointwise map is induced by baseChangeIdIso.hom. -/
@[simp] theorem weilAdelicFrameBaseChangeId_apply (s : Spec (.of Ω) ⟶ S)
    (eta : FI s) (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] V) :
    (weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI s
      eta).1 x =
      rationalMap (Over.mk s) (fun _ => True)
        (AbelianScheme.baseChangeIdIso A).hom (eta.1 x) := by
  let := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  rw [weilAdelicFrameBaseChangeId_underlying preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI
    evaluationI s eta]
  exact adelicFrameBaseChangeId_apply A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) s eta.1 x

/-- Identity base change is coherent after equality transport of the point. -/
theorem weilAdelicFrameBaseChange_id (s : Spec (.of Ω) ⟶ S) (eta : FI s) :
    weilAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry stability hA
      geometryA MA evaluationA compatibility lam h i V ψ (Category.comp_id s) (bcId s eta) =
      weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI
        s eta := rfl

/-- The actual identity comparison respects right precomposition. -/
theorem weilAdelicFrameBaseChangeId_right (s : Spec (.of Ω) ⟶ S) :
    letI := rI s
    letI := rA s
    ∀ (eta : FI s) (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ),
      weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI
        s (right eta g) = right (weilAdelicFrameBaseChangeId preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
        universality hI geometryI MI evaluationI s eta) g := by
  let := rI s
  let := rA s
  intro eta g
  change weilAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.comp_id s) (bcId s (right eta g))
    = _
  rw [weilAdelicFrameBaseChange_right (𝟙 S) A preservation composition unitCoherence associativity comparison
    symmetry stability universality hA geometryA MA evaluationA
      hI geometryI MI evaluationI compatibility lam h i V ψ s eta g]
  exact weilAdelicFramePointEq_right preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.comp_id s) (bcId s eta) g


/-- The actual identity comparison descends to every right subgroup orbit set. -/
def weilAdelicFrameRightOrbitBaseChangeId (s : Spec (.of Ω) ⟶ S)
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rI s
    letI := rA s
    RightOrbit (FI s) U ≃ RightOrbit (FA s) U := by
  let := rI s
  let := rA s
  exact RightOrbit.equiv U (weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI
    geometryI MI evaluationI s)
    (weilAdelicFrameBaseChangeId_right preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI
      s)

@[simp] theorem weilAdelicFrameRightOrbitBaseChangeId_mk (s : Spec (.of Ω) ⟶ S)
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rI s
    letI := rA s
    ∀ eta : FI s,
      weilAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI
        evaluationI s U (RightOrbit.mk U eta) =
        RightOrbit.mk U (weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI
          geometryI MI evaluationI s eta) := by
  intro eta
  rfl

/-- Identity comparison commutes with every permitted right Hecke translation. -/
theorem weilAdelicFrameRightOrbitBaseChangeId_translate (s : Spec (.of Ω) ⟶ S)
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)}
    (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    letI := rI s
    letI := rA s
    ∀ q : RightOrbit (FI s) U,
      weilAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI
        evaluationI s U' (RightOrbit.translate g hg q) =
        RightOrbit.translate g hg (weilAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence
          associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
          universality hI geometryI MI evaluationI s U q) := by
  let := rI s
  let := rA s
  intro q
  exact RightOrbit.map_translate (weilAdelicFrameBaseChangeId preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
    universality hI geometryI MI evaluationI s)
    (weilAdelicFrameBaseChangeId_right preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI
      s) g hg q

/-- The identity comparison also commutes with forgetting to a larger subgroup. -/
theorem weilAdelicFrameRightOrbitBaseChangeId_forget (s : Spec (.of Ω) ⟶ S)
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)} (hU : U ≤ U') :
    letI := rI s
    letI := rA s
    ∀ q : RightOrbit (FI s) U,
      weilAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI
        evaluationI s U'
          (RightOrbit.translate 1 (by intro u hu; simpa using hU hu) q) =
        RightOrbit.translate 1 (by intro u hu; simpa using hU hu)
          (weilAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity comparison
            symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI
            MI evaluationI s U q) := by
  intro q
  exact weilAdelicFrameRightOrbitBaseChangeId_translate preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI
    geometryI MI evaluationI s 1 _ q


/-- Identity coherence descends from actual frames to every right subgroup orbit set. -/
theorem weilAdelicFrameRightOrbitBaseChange_id (s : Spec (.of Ω) ⟶ S)
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rI s
    letI := rA (s ≫ 𝟙 S)
    letI := rA s
    ∀ q : RightOrbit (FI s) U,
      weilAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.comp_id s) U
        (weilAdelicFrameRightOrbitBaseChange (𝟙 S) A preservation composition unitCoherence associativity
          comparison symmetry stability universality hA geometryA MA evaluationA
          hI geometryI MI evaluationI compatibility lam h i V ψ s U q) =
        weilAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity comparison
          symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI
          evaluationI s U q := by
  let := rI s
  let := rA (s ≫ 𝟙 S)
  let := rA s
  intro q
  induction q using Quotient.inductionOn with
  | h eta => rfl

end Identity

section Composition
variable {S' S'' : Scheme.{u}} [QuasiSeparatedSpace S'] [QuasiSeparatedSpace S'']
  (b : S' ⟶ S) (c : S'' ⟶ S')
  (universality : PicardZeroUniversalBaseChangeStatement.{u})

  (hb : HasDualScheme ((baseChange b).obj A)) (geometryb : DualSchemeGeometry ((baseChange b).obj A) hb)
  (Mb : LineBundle ((relativeSpace (((baseChange b).obj A)).X.hom).obj (dualScheme ((baseChange b).obj A) hb)))
  (evaluationb : tensorObj (poincareFamily ((baseChange b).obj A) hb).obj.carrier Mb.obj ≅
    structureSheaf ((relativeSpace (((baseChange b).obj A)).X.hom).obj (dualScheme ((baseChange b).obj A) hb)))
  (hbc : HasDualScheme ((baseChange (c ≫ b)).obj A)) (geometrybc : DualSchemeGeometry ((baseChange (c ≫ b)).obj
    A) hbc)
  (Mbc : LineBundle ((relativeSpace (((baseChange (c ≫ b)).obj A)).X.hom).obj (dualScheme ((baseChange (c ≫
    b)).obj A) hbc)))
  (evaluationbc : tensorObj (poincareFamily ((baseChange (c ≫ b)).obj A) hbc).obj.carrier Mbc.obj ≅
    structureSheaf ((relativeSpace (((baseChange (c ≫ b)).obj A)).X.hom).obj (dualScheme ((baseChange (c ≫
      b)).obj A) hbc)))
  (hcb : HasDualScheme ((baseChange c).obj ((baseChange b).obj A))) (geometrycb : DualSchemeGeometry
    ((baseChange c).obj ((baseChange b).obj A)) hcb)
  (Mcb : LineBundle ((relativeSpace (((baseChange c).obj ((baseChange b).obj A))).X.hom).obj (dualScheme
    ((baseChange c).obj ((baseChange b).obj A)) hcb)))
  (evaluationcb : tensorObj (poincareFamily ((baseChange c).obj ((baseChange b).obj A)) hcb).obj.carrier Mcb.obj
    ≅
    structureSheaf ((relativeSpace (((baseChange c).obj ((baseChange b).obj A))).X.hom).obj (dualScheme
      ((baseChange c).obj ((baseChange b).obj A)) hcb)))

local notation "FD" => WeilAdelicFrame (S := S'') (A := ((baseChange (c ≫ b)).obj A)) preservation composition
  unitCoherence associativity comparison symmetry stability hbc geometrybc Mbc evaluationbc compatibility
  (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) h
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ
local notation "FC" => WeilAdelicFrame (S := S'') (A := ((baseChange c).obj ((baseChange b).obj A)))
  preservation composition unitCoherence associativity comparison symmetry stability hcb geometrycb Mcb
  evaluationcb compatibility (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition
  unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb
  geometrycb Mcb evaluationcb (canonicalDualValuedBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
  evaluationb lam)) h ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ψ
local notation "rB" => weilAdelicFrameRightAction (S := S') (A := ((baseChange b).obj A)) preservation
  composition unitCoherence associativity comparison symmetry stability hb geometryb Mb evaluationb
  compatibility (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb lam) h
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ
local notation "rD" => weilAdelicFrameRightAction (S := S'') (A := ((baseChange (c ≫ b)).obj A)) preservation
  composition unitCoherence associativity comparison symmetry stability hbc geometrybc Mbc evaluationbc
  compatibility (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) h
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ
local notation "rC" => weilAdelicFrameRightAction (S := S'') (A := ((baseChange c).obj ((baseChange b).obj A)))
  preservation composition unitCoherence associativity comparison symmetry stability hcb geometrycb Mcb
  evaluationcb compatibility (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition
  unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb
  geometrycb Mcb evaluationcb (canonicalDualValuedBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
  evaluationb lam)) h ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ψ
local notation "bcD" => weilAdelicFrameBaseChange (c ≫ b) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc
  compatibility lam h i V ψ
local notation "bcB" => weilAdelicFrameBaseChange b A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb
  compatibility lam h i V ψ
local notation "bcC" => weilAdelicFrameBaseChange c ((baseChange b).obj A) preservation composition
  unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb
  geometrycb Mcb evaluationcb compatibility (canonicalDualValuedBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hb
  geometryb Mb evaluationb lam) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ

/-- Direct pullback and successive pullback have canonically equivalent actual
Weil-compatible frames, for their respective canonically pulled-back maps. -/
def weilAdelicFrameBaseChangeComp (s : Spec (.of Ω) ⟶ S'') :
    FD s ≃ FC s :=
  (((bcD s).trans
      (weilAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry stability
        hA geometryA MA evaluationA compatibility lam h i V ψ (Category.assoc s c b).symm)).trans
        (bcB (s ≫ c)).symm).trans (bcC s).symm

/-- The composition square holds on the actual compatible-frame subtypes. -/
theorem weilAdelicFrameBaseChange_base_comp (s : Spec (.of Ω) ⟶ S'')
    (eta : FD s) :
    bcB (s ≫ c) (bcC s (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta)) =
      weilAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry stability
        hA geometryA MA evaluationA compatibility lam h i V ψ (Category.assoc s c b).symm (bcD s eta) := by
  simp only [weilAdelicFrameBaseChangeComp, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- The restricted composition comparison is the actual geometric
baseChangeCompIso comparison on underlying frames. -/
theorem weilAdelicFrameBaseChangeComp_underlying (s : Spec (.of Ω) ⟶ S'')
    (eta : FD s) :
    letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
    (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta).1 =
      adelicFrameBaseChangeComp A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) b c s eta.1 := by
  let := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  apply (adelicFrameBaseChange c ((baseChange b).obj A) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
    ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) s).injective
  apply (adelicFrameBaseChange b A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) (s ≫ c)).injective
  have square := congrArg Subtype.val
    (weilAdelicFrameBaseChange_base_comp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta)
  change adelicFrameBaseChange b A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) (s ≫ c)
    (adelicFrameBaseChange c ((baseChange b).obj A) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
      ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) s ((weilAdelicFrameBaseChangeComp preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c
      universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s
      eta).1)) = _ at square
  rw [weilAdelicFramePointEq_underlying preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.assoc s c b).symm
    ((Over.mapComp c b).app (Over.mk s)) rfl] at square
  rw [square]
  rw [weilAdelicFrameBaseChange_underlying (c ≫ b) A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA geometryA MA evaluationA
    hbc geometrybc Mbc evaluationbc compatibility lam h i V ψ s eta]
  apply LinearEquiv.ext
  intro x
  have value := finiteAdeleAlgebraBaseChange_base_comp A i h b c (Over.mk s) (fun _ => True)
    (finiteAdeleAlgebraBaseChangeComp A i h b c (Over.mk s) (fun _ => True) (eta.1 x))
  simp only [LinearEquiv.symm_apply_apply] at value
  simp only [finiteAdeleAlgebraBaseChange_apply, finiteAdeleAlgebraBaseChangeComp_apply,
    adelicFrameTestIso_apply, adelicFrameBaseChange_apply, adelicFrameBaseChangeComp_apply] at value ⊢
  convert value.symm using 1 <;> rfl

/-- Its pointwise map is induced by the actual abelian-scheme comparison. -/
@[simp] theorem weilAdelicFrameBaseChangeComp_apply (s : Spec (.of Ω) ⟶ S'')
    (eta : FD s) (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] V) :
    (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta).1 x =
      rationalMap (Over.mk s) (fun _ => True)
        (AbelianScheme.baseChangeCompIso b c A).hom (eta.1 x) := by
  let := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  rw [weilAdelicFrameBaseChangeComp_underlying preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
    evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta]
  exact adelicFrameBaseChangeComp_apply A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) b c s eta.1 x

/-- The actual composition comparison respects right precomposition. -/
theorem weilAdelicFrameBaseChangeComp_right (s : Spec (.of Ω) ⟶ S'') :
    letI := rD s
    letI := rC s
    ∀ (eta : FD s) (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ),
      weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
        evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s (right eta g) = right
        (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
        evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta) g := by
  let := rD s
  let := rC s
  intro eta g
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb evaluationb
    hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s (right eta g)).1 x =
    (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb evaluationb
    hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta).1 (g.1.1 x)
  rw [weilAdelicFrameBaseChangeComp_apply, weilAdelicFrameBaseChangeComp_apply]
  rfl

/-- The geometric composition comparison descends to arbitrary right subgroup orbits. -/
def weilAdelicFrameRightOrbitBaseChangeComp (s : Spec (.of Ω) ⟶ S'')
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rD s
    letI := rC s
    RightOrbit (FD s) U ≃ RightOrbit (FC s) U := by
  let := rD s
  let := rC s
  exact RightOrbit.equiv U (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb
    geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)
    (weilAdelicFrameBaseChangeComp_right preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)

@[simp] theorem weilAdelicFrameRightOrbitBaseChangeComp_mk (s : Spec (.of Ω) ⟶ S'')
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rD s
    letI := rC s
    ∀ eta : FD s,
      weilAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb
        Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U (RightOrbit.mk U eta)
        =
        RightOrbit.mk U (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality
          hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta) :=
          by
  intro eta
  rfl

/-- Composition comparison commutes with every permitted right Hecke translation. -/
theorem weilAdelicFrameRightOrbitBaseChangeComp_translate (s : Spec (.of Ω) ⟶ S'')
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)}
    (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    letI := rD s
    letI := rC s
    ∀ q : RightOrbit (FD s) U,
      weilAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb
        Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U'
        (RightOrbit.translate g hg q) =
        RightOrbit.translate g hg (weilAdelicFrameRightOrbitBaseChangeComp preservation composition
          unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
          lam h i V ψ b c universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb
          geometrycb Mcb evaluationcb s U q) := by
  let := rD s
  let := rC s
  intro q
  exact RightOrbit.map_translate (weilAdelicFrameBaseChangeComp preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c
    universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)
    (weilAdelicFrameBaseChangeComp_right preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s) g hg q

/-- The composition comparison commutes with forgetting to a larger subgroup. -/
theorem weilAdelicFrameRightOrbitBaseChangeComp_forget (s : Spec (.of Ω) ⟶ S'')
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)} (hU : U ≤ U') :
    letI := rD s
    letI := rC s
    ∀ q : RightOrbit (FD s) U,
      weilAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb
        Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U'
          (RightOrbit.translate 1 (by intro u hu; simpa using hU hu) q) =
        RightOrbit.translate 1 (by intro u hu; simpa using hU hu)
          (weilAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity
            comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality
            hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U q)
            := by
  intro q
  exact weilAdelicFrameRightOrbitBaseChangeComp_translate preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb
    geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s 1 _ q

/-- The actual composition square descends to arbitrary right subgroup orbits. -/
theorem weilAdelicFrameRightOrbitBaseChange_base_comp (s : Spec (.of Ω) ⟶ S'')
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    letI := rD s
    letI := rC s
    letI := rB (s ≫ c)
    letI := rA (s ≫ (c ≫ b))
    letI := rA ((s ≫ c) ≫ b)
    ∀ q : RightOrbit (FD s) U,
      weilAdelicFrameRightOrbitBaseChange b A preservation composition unitCoherence associativity comparison
        symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb compatibility
        lam h i V ψ (s ≫ c) U
        (weilAdelicFrameRightOrbitBaseChange c ((baseChange b).obj A) preservation composition unitCoherence
          associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb
          Mcb evaluationcb compatibility (canonicalDualValuedBaseChange b A preservation composition
          unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hb
          geometryb Mb evaluationb lam) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ s U
          (weilAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity
            comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality
            hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U q))
            =
        weilAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison
          symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.assoc s c b).symm U
          (weilAdelicFrameRightOrbitBaseChange (c ≫ b) A preservation composition unitCoherence associativity
            comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc
            evaluationbc compatibility lam h i V ψ s U q) := by
  let := rD s
  let := rC s
  let := rB (s ≫ c)
  let := rA (s ≫ (c ≫ b))
  let := rA ((s ≫ c) ≫ b)
  intro q
  induction q using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilAdelicFrameBaseChange_base_comp preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb
        Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta)

end Composition
end Full
section Away
variable {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

local notation "FA" => WeilPrimeToAdelicFrame (S := S) (A := A) preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
local notation "rA" => weilPrimeToAdelicFrameRightAction (S := S) (A := A) preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V
  ψ

/-- Transport a compatible frame along equality of its point. -/
def weilPrimeToAdelicFramePointEq {s t : Spec (.of Ω) ⟶ S} (hst : s = t) :
    FA s hAway ≃ FA t hAway := by
  subst t
  exact Equiv.refl _

/-- Equality transport is the actual test-scheme comparison when that
comparison has identity underlying morphism. -/
theorem weilPrimeToAdelicFramePointEq_underlying {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (e : Over.mk s ≅ Over.mk t) (he : e.hom.left = 𝟙 _)
    (eta : FA s hAway) :
    letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
    (weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst eta).1 =
      primeToAdelicFrameTestIso A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) e eta.1 := by
  let := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  subst t
  have heq : e = Iso.refl (Over.mk s) := by
    apply Iso.ext
    apply Over.OverMorphism.ext
    exact he
  subst e
  exact (primeToAdelicFrameTestIso_refl A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) eta.1).symm

/-- Point equality preserves right precomposition. -/
theorem weilPrimeToAdelicFramePointEq_right {s t : Spec (.of Ω) ⟶ S} (hst : s = t) :
    letI := rA s hAway
    letI := rA t hAway
    ∀ (eta : FA s hAway) (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ),
      weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst (right eta g) = right
        (weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst eta) g := by
  subst t
  intro eta g
  rfl

/-- Equality transport descends to arbitrary right subgroup orbits. -/
def weilPrimeToAdelicFrameRightOrbitPointEq {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rA s hAway
    letI := rA t hAway
    RightOrbit (FA s hAway) U ≃ RightOrbit (FA t hAway) U := by
  let := rA s hAway
  let := rA t hAway
  exact RightOrbit.equiv U (weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst)
    (weilPrimeToAdelicFramePointEq_right preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst)

section Identity
local notation "AI" => (baseChange (𝟙 S)).obj A
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})

  (hI : HasDualScheme ((baseChange (𝟙 S)).obj A)) (geometryI : DualSchemeGeometry ((baseChange (𝟙 S)).obj A) hI)
  (MI : LineBundle ((relativeSpace (((baseChange (𝟙 S)).obj A)).X.hom).obj (dualScheme ((baseChange (𝟙 S)).obj
    A) hI)))
  (evaluationI : tensorObj (poincareFamily ((baseChange (𝟙 S)).obj A) hI).obj.carrier MI.obj ≅
    structureSheaf ((relativeSpace (((baseChange (𝟙 S)).obj A)).X.hom).obj (dualScheme ((baseChange (𝟙 S)).obj
      A) hI)))

local notation "FI" => WeilPrimeToAdelicFrame (S := S) (A := AI) preservation composition unitCoherence
  associativity comparison symmetry stability hI geometryI MI evaluationI compatibility
  (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ
local notation "rI" => weilPrimeToAdelicFrameRightAction (S := S) (A := AI) preservation composition
  unitCoherence associativity comparison symmetry stability hI geometryI MI evaluationI compatibility
  (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ
local notation "bcId" => weilPrimeToAdelicFrameBaseChange (𝟙 S) A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hI geometryI MI
  evaluationI compatibility lam h i V ψ

/-- Identity pullback comparison restricted to the actual compatible-frame
subtypes, with the canonically base-changed dual-valued map. -/
def weilPrimeToAdelicFrameBaseChangeId (s : Spec (.of Ω) ⟶ S) :
    FI s hAway ≃ FA s hAway :=
  (bcId s hAway).trans (weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.comp_id
    s))

/-- The restricted identity comparison has the existing canonical geometric
identity comparison as its underlying frame map. -/
theorem weilPrimeToAdelicFrameBaseChangeId_underlying (s : Spec (.of Ω) ⟶ S)
    (eta : FI s hAway) :
    letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
    (weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI MI
      evaluationI s eta).1 =
      primeToAdelicFrameBaseChangeId A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) s eta.1 := by
  let := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  change (weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.comp_id s) (bcId s hAway
    eta)).1 = _
  rw [weilPrimeToAdelicFramePointEq_underlying preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.comp_id s)
    ((Over.mapId S).app (Over.mk s)) rfl]
  exact primeToAdelicFrameBaseChange_id A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) s eta.1

/-- In particular, its pointwise map is induced by baseChangeIdIso.hom. -/
@[simp] theorem weilPrimeToAdelicFrameBaseChangeId_apply (s : Spec (.of Ω) ⟶ S)
    (eta : FI s hAway) (x : (Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) :
    (weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI MI
      evaluationI s eta).1 x =
      rationalMap (Over.mk s) (fun n => Nat.Coprime n m)
        (AbelianScheme.baseChangeIdIso A).hom (eta.1 x) := by
  let := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  rw [weilPrimeToAdelicFrameBaseChangeId_underlying preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI
    geometryI MI evaluationI s eta]
  exact primeToAdelicFrameBaseChangeId_apply A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) s eta.1 x

/-- Identity base change is coherent after equality transport of the point. -/
theorem weilPrimeToAdelicFrameBaseChange_id (s : Spec (.of Ω) ⟶ S) (eta : FI s hAway) :
    weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.comp_id s) (bcId s hAway
      eta) =
      weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI
        MI evaluationI s eta := rfl

/-- The actual identity comparison respects right precomposition. -/
theorem weilPrimeToAdelicFrameBaseChangeId_right (s : Spec (.of Ω) ⟶ S) :
    letI := rI s hAway
    letI := rA s hAway
    ∀ (eta : FI s hAway) (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ),
      weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI
        MI evaluationI s (right eta g) = right (weilPrimeToAdelicFrameBaseChangeId preservation composition
        unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam
        h i V ψ hAway universality hI geometryI MI evaluationI s eta) g := by
  let := rI s hAway
  let := rA s hAway
  intro eta g
  change weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.comp_id s) (bcId s hAway
    (right eta g)) = _
  rw [weilPrimeToAdelicFrameBaseChange_right (𝟙 S) A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA geometryA MA evaluationA
      hI geometryI MI evaluationI compatibility lam h i V ψ s hAway eta g]
  exact weilPrimeToAdelicFramePointEq_right preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.comp_id s) (bcId s
    hAway eta) g


/-- The actual identity comparison descends to every right subgroup orbit set. -/
def weilPrimeToAdelicFrameRightOrbitBaseChangeId (s : Spec (.of Ω) ⟶ S)
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rI s hAway
    letI := rA s hAway
    RightOrbit (FI s hAway) U ≃ RightOrbit (FA s hAway) U := by
  let := rI s hAway
  let := rA s hAway
  exact RightOrbit.equiv U (weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
    universality hI geometryI MI evaluationI s)
    (weilPrimeToAdelicFrameBaseChangeId_right preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI
      MI evaluationI s)

@[simp] theorem weilPrimeToAdelicFrameRightOrbitBaseChangeId_mk (s : Spec (.of Ω) ⟶ S)
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rI s hAway
    letI := rA s hAway
    ∀ eta : FI s hAway,
      weilPrimeToAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality
        hI geometryI MI evaluationI s U (RightOrbit.mk U eta) =
        RightOrbit.mk U (weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality
          hI geometryI MI evaluationI s eta) := by
  intro eta
  rfl

/-- Identity comparison commutes with every permitted right Hecke translation. -/
theorem weilPrimeToAdelicFrameRightOrbitBaseChangeId_translate (s : Spec (.of Ω) ⟶ S)
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)}
    (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    letI := rI s hAway
    letI := rA s hAway
    ∀ q : RightOrbit (FI s hAway) U,
      weilPrimeToAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality
        hI geometryI MI evaluationI s U' (RightOrbit.translate g hg q) =
        RightOrbit.translate g hg (weilPrimeToAdelicFrameRightOrbitBaseChangeId preservation composition
          unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
          lam h i V ψ hAway universality hI geometryI MI evaluationI s U q) := by
  let := rI s hAway
  let := rA s hAway
  intro q
  exact RightOrbit.map_translate (weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
    universality hI geometryI MI evaluationI s)
    (weilPrimeToAdelicFrameBaseChangeId_right preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI
      MI evaluationI s) g hg q

/-- The identity comparison also commutes with forgetting to a larger subgroup. -/
theorem weilPrimeToAdelicFrameRightOrbitBaseChangeId_forget (s : Spec (.of Ω) ⟶ S)
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)} (hU : U ≤ U') :
    letI := rI s hAway
    letI := rA s hAway
    ∀ q : RightOrbit (FI s hAway) U,
      weilPrimeToAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality
        hI geometryI MI evaluationI s U'
          (RightOrbit.translate 1 (by intro u hu; simpa using hU hu) q) =
        RightOrbit.translate 1 (by intro u hu; simpa using hU hu)
          (weilPrimeToAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity
            comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
            universality hI geometryI MI evaluationI s U q) := by
  intro q
  exact weilPrimeToAdelicFrameRightOrbitBaseChangeId_translate preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
    universality hI geometryI MI evaluationI s 1 _ q


/-- Identity coherence descends from actual frames to every right subgroup orbit set. -/
theorem weilPrimeToAdelicFrameRightOrbitBaseChange_id (s : Spec (.of Ω) ⟶ S)
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rI s hAway
    letI := rA (s ≫ 𝟙 S) hAway
    letI := rA s hAway
    ∀ q : RightOrbit (FI s hAway) U,
      weilPrimeToAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.comp_id s) U
        (weilPrimeToAdelicFrameRightOrbitBaseChange (𝟙 S) A preservation composition unitCoherence associativity
          comparison symmetry stability universality hA geometryA MA evaluationA
          hI geometryI MI evaluationI compatibility lam h i V ψ s hAway U q) =
        weilPrimeToAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality
          hI geometryI MI evaluationI s U q := by
  let := rI s hAway
  let := rA (s ≫ 𝟙 S) hAway
  let := rA s hAway
  intro q
  induction q using Quotient.inductionOn with
  | h eta => rfl

end Identity

section Composition
variable {S' S'' : Scheme.{u}} [QuasiSeparatedSpace S'] [QuasiSeparatedSpace S'']
  (b : S' ⟶ S) (c : S'' ⟶ S')
  (universality : PicardZeroUniversalBaseChangeStatement.{u})

  (hb : HasDualScheme ((baseChange b).obj A)) (geometryb : DualSchemeGeometry ((baseChange b).obj A) hb)
  (Mb : LineBundle ((relativeSpace (((baseChange b).obj A)).X.hom).obj (dualScheme ((baseChange b).obj A) hb)))
  (evaluationb : tensorObj (poincareFamily ((baseChange b).obj A) hb).obj.carrier Mb.obj ≅
    structureSheaf ((relativeSpace (((baseChange b).obj A)).X.hom).obj (dualScheme ((baseChange b).obj A) hb)))
  (hbc : HasDualScheme ((baseChange (c ≫ b)).obj A)) (geometrybc : DualSchemeGeometry ((baseChange (c ≫ b)).obj
    A) hbc)
  (Mbc : LineBundle ((relativeSpace (((baseChange (c ≫ b)).obj A)).X.hom).obj (dualScheme ((baseChange (c ≫
    b)).obj A) hbc)))
  (evaluationbc : tensorObj (poincareFamily ((baseChange (c ≫ b)).obj A) hbc).obj.carrier Mbc.obj ≅
    structureSheaf ((relativeSpace (((baseChange (c ≫ b)).obj A)).X.hom).obj (dualScheme ((baseChange (c ≫
      b)).obj A) hbc)))
  (hcb : HasDualScheme ((baseChange c).obj ((baseChange b).obj A))) (geometrycb : DualSchemeGeometry
    ((baseChange c).obj ((baseChange b).obj A)) hcb)
  (Mcb : LineBundle ((relativeSpace (((baseChange c).obj ((baseChange b).obj A))).X.hom).obj (dualScheme
    ((baseChange c).obj ((baseChange b).obj A)) hcb)))
  (evaluationcb : tensorObj (poincareFamily ((baseChange c).obj ((baseChange b).obj A)) hcb).obj.carrier Mcb.obj
    ≅
    structureSheaf ((relativeSpace (((baseChange c).obj ((baseChange b).obj A))).X.hom).obj (dualScheme
      ((baseChange c).obj ((baseChange b).obj A)) hcb)))

local notation "FD" => WeilPrimeToAdelicFrame (S := S'') (A := ((baseChange (c ≫ b)).obj A)) preservation
  composition unitCoherence associativity comparison symmetry stability hbc geometrybc Mbc evaluationbc
  compatibility (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) h
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ
local notation "FC" => WeilPrimeToAdelicFrame (S := S'') (A := ((baseChange c).obj ((baseChange b).obj A)))
  preservation composition unitCoherence associativity comparison symmetry stability hcb geometrycb Mcb
  evaluationcb compatibility (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition
  unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb
  geometrycb Mcb evaluationcb (canonicalDualValuedBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
  evaluationb lam)) h ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ψ
local notation "rB" => weilPrimeToAdelicFrameRightAction (S := S') (A := ((baseChange b).obj A)) preservation
  composition unitCoherence associativity comparison symmetry stability hb geometryb Mb evaluationb
  compatibility (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb lam) h
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ
local notation "rD" => weilPrimeToAdelicFrameRightAction (S := S'') (A := ((baseChange (c ≫ b)).obj A))
  preservation composition unitCoherence associativity comparison symmetry stability hbc geometrybc Mbc
  evaluationbc compatibility (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc
  evaluationbc lam) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ
local notation "rC" => weilPrimeToAdelicFrameRightAction (S := S'') (A := ((baseChange c).obj ((baseChange
  b).obj A))) preservation composition unitCoherence associativity comparison symmetry stability hcb geometrycb
  Mcb evaluationcb compatibility (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation
  composition unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb
  hcb geometrycb Mcb evaluationcb (canonicalDualValuedBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
  evaluationb lam)) h ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ψ
local notation "bcD" => weilPrimeToAdelicFrameBaseChange (c ≫ b) A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc
  evaluationbc compatibility lam h i V ψ
local notation "bcB" => weilPrimeToAdelicFrameBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
  evaluationb compatibility lam h i V ψ
local notation "bcC" => weilPrimeToAdelicFrameBaseChange c ((baseChange b).obj A) preservation composition
  unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb
  geometrycb Mcb evaluationcb compatibility (canonicalDualValuedBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hb
  geometryb Mb evaluationb lam) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ

/-- Direct pullback and successive pullback have canonically equivalent actual
Weil-compatible frames, for their respective canonically pulled-back maps. -/
def weilPrimeToAdelicFrameBaseChangeComp (s : Spec (.of Ω) ⟶ S'') :
    FD s hAway ≃ FC s hAway :=
  (((bcD s hAway).trans
      (weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.assoc s c
        b).symm)).trans
        (bcB (s ≫ c) hAway).symm).trans (bcC s hAway).symm

/-- The composition square holds on the actual compatible-frame subtypes. -/
theorem weilPrimeToAdelicFrameBaseChange_base_comp (s : Spec (.of Ω) ⟶ S'')
    (eta : FD s hAway) :
    bcB (s ≫ c) hAway (bcC s hAway (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b
      c universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb
      s eta)) =
      weilPrimeToAdelicFramePointEq preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.assoc s c b).symm (bcD s
        hAway eta) := by
  simp only [weilPrimeToAdelicFrameBaseChangeComp, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- The restricted composition comparison is the actual geometric
baseChangeCompIso comparison on underlying frames. -/
theorem weilPrimeToAdelicFrameBaseChangeComp_underlying (s : Spec (.of Ω) ⟶ S'')
    (eta : FD s hAway) :
    letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
    (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta).1 =
      primeToAdelicFrameBaseChangeComp A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) b c s eta.1 := by
  let := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  apply (primeToAdelicFrameBaseChange c ((baseChange b).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd b
    A).comp i) ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) s).injective
  apply (primeToAdelicFrameBaseChange b A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) (s ≫ c)).injective
  have square := congrArg Subtype.val
    (weilPrimeToAdelicFrameBaseChange_base_comp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta)
  change primeToAdelicFrameBaseChange b A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) (s ≫ c)
    (primeToAdelicFrameBaseChange c ((baseChange b).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd b
      A).comp i) ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) s ((weilPrimeToAdelicFrameBaseChangeComp preservation
      composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility lam h i V ψ hAway b c universality hb geometryb Mb evaluationb hbc geometrybc Mbc
      evaluationbc hcb geometrycb Mcb evaluationcb s eta).1)) = _ at square
  rw [weilPrimeToAdelicFramePointEq_underlying preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.assoc s c b).symm
    ((Over.mapComp c b).app (Over.mk s)) rfl] at square
  rw [square]
  rw [weilPrimeToAdelicFrameBaseChange_underlying (c ≫ b) A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA geometryA MA evaluationA
    hbc geometrybc Mbc evaluationbc compatibility lam h i V ψ s hAway eta]
  apply LinearEquiv.ext
  intro x
  have value := primeToFiniteAdeleAlgebraBaseChange_base_comp A i hAway b c (Over.mk s)
    (primeToFiniteAdeleAlgebraBaseChangeComp A i hAway b c (Over.mk s) (eta.1 x))
  simp only [LinearEquiv.symm_apply_apply] at value
  simp only [primeToFiniteAdeleAlgebraBaseChange_apply, primeToFiniteAdeleAlgebraBaseChangeComp_apply,
    primeToAdelicFrameTestIso_apply, primeToAdelicFrameBaseChange_apply, primeToAdelicFrameBaseChangeComp_apply]
      at value ⊢
  convert value.symm using 1 <;> rfl

/-- Its pointwise map is induced by the actual abelian-scheme comparison. -/
@[simp] theorem weilPrimeToAdelicFrameBaseChangeComp_apply (s : Spec (.of Ω) ⟶ S'')
    (eta : FD s hAway) (x : (Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) :
    (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta).1 x =
      rationalMap (Over.mk s) (fun n => Nat.Coprime n m)
        (AbelianScheme.baseChangeCompIso b c A).hom (eta.1 x) := by
  let := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  rw [weilPrimeToAdelicFrameBaseChangeComp_underlying preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality
    hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta]
  exact primeToAdelicFrameBaseChangeComp_apply A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) b c s eta.1 x

/-- The actual composition comparison respects right precomposition. -/
theorem weilPrimeToAdelicFrameBaseChangeComp_right (s : Spec (.of Ω) ⟶ S'') :
    letI := rD s hAway
    letI := rC s hAway
    ∀ (eta : FD s hAway) (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ),
      weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
        geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s (right eta g)
        = right (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
        universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb
        s eta) g := by
  let := rD s hAway
  let := rC s hAway
  intro eta g
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb geometryb
    Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s (right eta g)).1 x =
    (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb geometryb
    Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta).1 (g.1.1 x)
  rw [weilPrimeToAdelicFrameBaseChangeComp_apply, weilPrimeToAdelicFrameBaseChangeComp_apply]
  rfl

/-- The geometric composition comparison descends to arbitrary right subgroup orbits. -/
def weilPrimeToAdelicFrameRightOrbitBaseChangeComp (s : Spec (.of Ω) ⟶ S'')
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rD s hAway
    letI := rC s hAway
    RightOrbit (FD s hAway) U ≃ RightOrbit (FC s hAway) U := by
  let := rD s hAway
  let := rC s hAway
  exact RightOrbit.equiv U (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
    universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)
    (weilPrimeToAdelicFrameBaseChangeComp_right preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)

@[simp] theorem weilPrimeToAdelicFrameRightOrbitBaseChangeComp_mk (s : Spec (.of Ω) ⟶ S'')
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rD s hAway
    letI := rC s hAway
    ∀ eta : FD s hAway,
      weilPrimeToAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
        universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb
        s U (RightOrbit.mk U eta) =
        RightOrbit.mk U (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence
          associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
          hAway b c universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb
          evaluationcb s eta) := by
  intro eta
  rfl

/-- Composition comparison commutes with every permitted right Hecke translation. -/
theorem weilPrimeToAdelicFrameRightOrbitBaseChangeComp_translate (s : Spec (.of Ω) ⟶ S'')
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)}
    (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    letI := rD s hAway
    letI := rC s hAway
    ∀ q : RightOrbit (FD s hAway) U,
      weilPrimeToAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
        universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb
        s U' (RightOrbit.translate g hg q) =
        RightOrbit.translate g hg (weilPrimeToAdelicFrameRightOrbitBaseChangeComp preservation composition
          unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
          lam h i V ψ hAway b c universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb
          geometrycb Mcb evaluationcb s U q) := by
  let := rD s hAway
  let := rC s hAway
  intro q
  exact RightOrbit.map_translate (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
    universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)
    (weilPrimeToAdelicFrameBaseChangeComp_right preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s) g hg q

/-- The composition comparison commutes with forgetting to a larger subgroup. -/
theorem weilPrimeToAdelicFrameRightOrbitBaseChangeComp_forget (s : Spec (.of Ω) ⟶ S'')
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)} (hU : U ≤ U') :
    letI := rD s hAway
    letI := rC s hAway
    ∀ q : RightOrbit (FD s hAway) U,
      weilPrimeToAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
        universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb
        s U'
          (RightOrbit.translate 1 (by intro u hu; simpa using hU hu) q) =
        RightOrbit.translate 1 (by intro u hu; simpa using hU hu)
          (weilPrimeToAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity
            comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
            universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb
            evaluationcb s U q) := by
  intro q
  exact weilPrimeToAdelicFrameRightOrbitBaseChangeComp_translate preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
    universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s 1
    _ q

/-- The actual composition square descends to arbitrary right subgroup orbits. -/
theorem weilPrimeToAdelicFrameRightOrbitBaseChange_base_comp (s : Spec (.of Ω) ⟶ S'')
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    letI := rD s hAway
    letI := rC s hAway
    letI := rB (s ≫ c) hAway
    letI := rA (s ≫ (c ≫ b)) hAway
    letI := rA ((s ≫ c) ≫ b) hAway
    ∀ q : RightOrbit (FD s hAway) U,
      weilPrimeToAdelicFrameRightOrbitBaseChange b A preservation composition unitCoherence associativity
        comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb
        compatibility lam h i V ψ (s ≫ c) hAway U
        (weilPrimeToAdelicFrameRightOrbitBaseChange c ((baseChange b).obj A) preservation composition
          unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb
          geometrycb Mcb evaluationcb compatibility (canonicalDualValuedBaseChange b A preservation composition
          unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hb
          geometryb Mb evaluationb lam) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ s hAway U
          (weilPrimeToAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity
            comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
            universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb
            evaluationcb s U q)) =
        weilPrimeToAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison
          symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.assoc s c
          b).symm U
          (weilPrimeToAdelicFrameRightOrbitBaseChange (c ≫ b) A preservation composition unitCoherence
            associativity comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc
            Mbc evaluationbc compatibility lam h i V ψ s hAway U q) := by
  let := rD s hAway
  let := rC s hAway
  let := rB (s ≫ c) hAway
  let := rA (s ≫ (c ≫ b)) hAway
  let := rA ((s ≫ c) ≫ b) hAway
  intro q
  induction q using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilPrimeToAdelicFrameBaseChange_base_comp preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
        universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb
        s eta)

end Composition
end Away
end Langlands.AbelianScheme.Tate

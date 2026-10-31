import Langlands.AbelianScheme.Tate.WeilFrameBaseChangeCoherence
import Langlands.AbelianScheme.Tate.WeilLevelBaseChange

/-! # Identity and composition of actual Weil-compatible fixed-level base change -/

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
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

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

private theorem inverse_level_comparison_square {X Y Z W T : Type*}
    (f : Y ≃ X) (g : Z ≃ Y) (d : T ≃ W) (t : W ≃ X) (c : T ≃ Z)
    (h : ∀ a, f (g (c a)) = t (d a)) (x : X) :
    c (d.symm (t.symm x)) = g.symm (f.symm x) := by
  apply g.injective
  apply f.injective
  simp only [h, Equiv.apply_symm_apply]

section Full
local notation "G" => ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ

/-- Equality of pointed fibres transports the actual fixed orbit sets. -/
def weilAdelicLevelPointEq {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (htor : TorsionFiniteEtaleStatement.{u})
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom] (U : Subgroup G) :
    WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
      compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i V ψ s hs htor hu (hμfin
      := hμfin) (hμet := hμet) U ≃
      WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
        compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i V ψ t ht htor hu (hμfin
        := hμfin) (hμet := hμet) U := by
  subst t
  exact Equiv.refl _

/-- The underlying orbit is the existing compatible-frame point transport. -/
@[simp] theorem weilAdelicLevelPointEq_val {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (htor : TorsionFiniteEtaleStatement.{u})
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom] (U : Subgroup G)
    (q : WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
      compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i V ψ s hs htor hu (hμfin
      := hμfin) (hμet := hμet) U) :
    (weilAdelicLevelPointEq preservation composition unitCoherence associativity comparison symmetry stability
      hA geometryA MA evaluationA compatibility lam h i V ψ hst hs ht htor hu U q).1 =
      weilAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ hst U q.1 := by
  subst t
  change q.1 = _
  induction q.1 using Quotient.inductionOn with
  | h eta => rfl

/-- Inverse point transport has the inverse underlying orbit comparison. -/
@[simp] theorem weilAdelicLevelPointEq_symm_val {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (htor : TorsionFiniteEtaleStatement.{u})
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom] (U : Subgroup G)
    (q : WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
      compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i V ψ t ht htor hu (hμfin
      := hμfin) (hμet := hμet) U) :
    ((weilAdelicLevelPointEq preservation composition unitCoherence associativity comparison symmetry stability
      hA geometryA MA evaluationA compatibility lam h i V ψ hst hs ht htor hu U).symm q).1 =
      (weilAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ hst U).symm q.1 := by
  apply (weilAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hst U).injective
  rw [Equiv.apply_symm_apply]
  rw [← weilAdelicLevelPointEq_val preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ hst hs ht htor hu U]
  rw [Equiv.apply_symm_apply]

section Identity
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})

  (hI : HasDualScheme ((baseChange (𝟙 S)).obj A)) (geometryI : DualSchemeGeometry ((baseChange (𝟙 S)).obj A) hI)
  (MI : LineBundle ((relativeSpace (((baseChange (𝟙 S)).obj A)).X.hom).obj (dualScheme ((baseChange (𝟙 S)).obj
    A) hI)))
  (evaluationI : tensorObj (poincareFamily ((baseChange (𝟙 S)).obj A) hI).obj.carrier MI.obj ≅
    structureSheaf ((relativeSpace (((baseChange (𝟙 S)).obj A)).X.hom).obj (dualScheme ((baseChange (𝟙 S)).obj
      A) hI)))
  (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]

local notation "FA" => WeilAdelicFrame (S := S) (A := A) preservation composition unitCoherence associativity
  comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ s
local notation "FI" => WeilAdelicFrame (S := S) (A := ((baseChange (𝟙 S)).obj A)) preservation composition
  unitCoherence associativity comparison symmetry stability hI geometryI MI evaluationI compatibility
  (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s
local notation "rA" => weilAdelicFrameRightAction (S := S) (A := A) preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ s
local notation "rI" => weilAdelicFrameRightAction (S := S) (A := ((baseChange (𝟙 S)).obj A)) preservation
  composition unitCoherence associativity comparison symmetry stability hI geometryI MI evaluationI
  compatibility (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s
local notation "mA" => weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i
  V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "mI" => weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hI geometryI MI evaluationI
  (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "kA" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i
  V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "kI" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hI geometryI MI evaluationI
  (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LA" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry
  stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i V ψ s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "LI" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry
  stability compatibility rationalWeilGeometricTransport hI geometryI MI evaluationI
  (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)

/-- The identity scheme comparison intertwines actual geometric monodromy. -/
theorem weilAdelicFrameBaseChangeId_monodromy :
    letI := mI
    letI := mA
    ∀ (g : FundamentalGroup s hs) (eta : FI),
      weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI
        s (g • eta) = g • weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI
        geometryI MI evaluationI s eta := by
  let := mI
  let := mA
  intro g eta
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI s
    (g • eta)).1 x =
    rationalMonodromy s hs htor A (fun _ => True) hu g ((weilAdelicFrameBaseChangeId preservation composition
      unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h
      i V ψ universality hI geometryI MI evaluationI s eta).1 x)
  simp only [weilAdelicFrameBaseChangeId_apply]
  exact (rationalMonodromy_map s hs htor (fun _ => True) hu
    (AbelianScheme.baseChangeIdIso A).hom g (eta.1 x)).symm

/-- Restrict the actual identity comparison to monodromy-fixed right orbits. -/
def weilAdelicLevelBaseChangeId (U : Subgroup G) : LI U ≃ LA U := by
  let := rI
  let := rA
  let := mI
  let := mA
  let := kI
  let := kA
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (weilAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI
      s) (weilAdelicFrameBaseChangeId_right preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI
      evaluationI s) (weilAdelicFrameBaseChangeId_monodromy preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI
      geometryI MI evaluationI s hs htor hu)

@[simp] theorem weilAdelicLevelBaseChangeId_val (U : Subgroup G) (q : LI U) :
    (weilAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI s
      hs htor hu U q).1 = weilAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
      universality hI geometryI MI evaluationI s U q.1 := rfl

@[simp] theorem weilAdelicLevelBaseChangeId_symm_val (U : Subgroup G) (q : LA U) :
    ((weilAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI s
      hs htor hu U).symm q).1 = (weilAdelicFrameRightOrbitBaseChangeId preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
      universality hI geometryI MI evaluationI s U).symm q.1 := rfl

/-- The fixed-level comparison commutes with every allowed Hecke map. -/
theorem weilAdelicLevelBaseChangeId_translate {U U' : Subgroup G} (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (q : LI U) :
    letI := rI
    letI := rA
    letI := mI
    letI := mA
    letI := kI
    letI := kA
    weilAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI s
      hs htor hu U' (InvariantOrbit.translate g hg q) =
      InvariantOrbit.translate g hg (weilAdelicLevelBaseChangeId preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
        universality hI geometryI MI evaluationI s hs htor hu U q) := by
  let := rI
  let := rA
  let := mI
  let := mA
  let := kI
  let := kA
  apply Subtype.ext
  exact weilAdelicFrameRightOrbitBaseChangeId_translate preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI
    geometryI MI evaluationI s g hg q.1

/-- Forgetting a finer subgroup commutes with the identity comparison. -/
theorem weilAdelicLevelBaseChangeId_forget {U U' : Subgroup G} (hU : U ≤ U') (q : LI U) :
    letI := rI
    letI := rA
    letI := mI
    letI := mA
    letI := kI
    letI := kA
    weilAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI s
      hs htor hu U' (InvariantOrbit.forget hU q) =
      InvariantOrbit.forget hU (weilAdelicLevelBaseChangeId preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI
        geometryI MI evaluationI s hs htor hu U q) := by
  exact weilAdelicLevelBaseChangeId_translate preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI
    evaluationI s hs htor hu 1 _ q

/-- Identity pullback agrees with point transport after the canonical comparison. -/
theorem weilAdelicLevelBaseChange_id
    (hs' : ∀ Y : Cover S, Finite (Fiber (s ≫ 𝟙 S) Y))
    (U : Subgroup G) (q : WeilAdelicLevel preservation composition unitCoherence associativity comparison
      symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i V ψ (s
      ≫ 𝟙 S) hs' htor hu (hμfin := hμfin) (hμet := hμet) U) :
    weilAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI geometryI MI evaluationI s
      hs htor hu U (weilAdelicLevelBaseChange (𝟙 S) A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI
      compatibility lam h i V ψ s hs hs' htor hu hu (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin) (hμet' :=
      hμet) U q) =
      weilAdelicLevelPointEq preservation composition unitCoherence associativity comparison symmetry stability
        hA geometryA MA evaluationA compatibility lam h i V ψ (Category.comp_id s) hs' hs htor hu U q := by
  apply Subtype.ext
  rw [weilAdelicLevelBaseChangeId_val, weilAdelicLevelBaseChange_val, weilAdelicLevelPointEq_val]
  have square := weilAdelicFrameRightOrbitBaseChange_id preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ universality hI
    geometryI MI evaluationI s U
    ((weilAdelicFrameRightOrbitBaseChange (𝟙 S) A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI
      compatibility lam h i V ψ s U).symm q.1)
  rw [Equiv.apply_symm_apply] at square
  exact square.symm

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
  (s : Spec (.of Ω) ⟶ S'')
  (hs : ∀ Y : Cover S'', Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu'' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S'', ⊤)))
  [hμfin'' : ∀ n : Index (fun _ => True), IsFinite (mu S'' n.val).X.hom]
  [hμet'' : ∀ n : Index (fun _ => True), Etale (mu S'' n.val).X.hom]

local notation "FD" => WeilAdelicFrame (S := S'') (A := ((baseChange (c ≫ b)).obj A)) preservation composition
  unitCoherence associativity comparison symmetry stability hbc geometrybc Mbc evaluationbc compatibility
  (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) h
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s
local notation "FC" => WeilAdelicFrame (S := S'') (A := ((baseChange c).obj ((baseChange b).obj A)))
  preservation composition unitCoherence associativity comparison symmetry stability hcb geometrycb Mcb
  evaluationcb compatibility (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition
  unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb
  geometrycb Mcb evaluationcb (canonicalDualValuedBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
  evaluationb lam)) h ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ψ s
local notation "rD" => weilAdelicFrameRightAction (S := S'') (A := ((baseChange (c ≫ b)).obj A)) preservation
  composition unitCoherence associativity comparison symmetry stability hbc geometrybc Mbc evaluationbc
  compatibility (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) h
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s
local notation "rC" => weilAdelicFrameRightAction (S := S'') (A := ((baseChange c).obj ((baseChange b).obj A)))
  preservation composition unitCoherence associativity comparison symmetry stability hcb geometrycb Mcb
  evaluationcb compatibility (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition
  unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb
  geometrycb Mcb evaluationcb (canonicalDualValuedBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
  evaluationb lam)) h ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ψ s
local notation "mD" => weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hbc geometrybc Mbc evaluationbc
  (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) h
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet :=
  hμet'')
local notation "mC" => weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition unitCoherence associativity
  comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity comparison symmetry
  stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb lam)) h
  ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b
  A).comp i)) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet := hμet'')
local notation "kD" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hbc geometrybc Mbc evaluationbc
  (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) h
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet :=
  hμet'')
local notation "kC" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition unitCoherence associativity
  comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity comparison symmetry
  stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb lam)) h
  ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b
  A).comp i)) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet := hμet'')
local notation "LD" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry
  stability compatibility rationalWeilGeometricTransport hbc geometrybc Mbc evaluationbc
  (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) h
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet :=
  hμet'')
local notation "LC" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry
  stability compatibility rationalWeilGeometricTransport hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition unitCoherence associativity
  comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity comparison symmetry
  stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb lam)) h
  ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b
  A).comp i)) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet := hμet'')

/-- The composition scheme comparison intertwines actual geometric monodromy. -/
theorem weilAdelicFrameBaseChangeComp_monodromy :
    letI := mD
    letI := mC
    ∀ (g : FundamentalGroup s hs) (eta : FD),
      weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
        evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s (g • eta) = g •
        weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
        evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta := by
  let := mD
  let := mC
  intro g eta
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb evaluationb
    hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s (g • eta)).1 x =
    rationalMonodromy s hs htor ((baseChange c).obj ((baseChange b).obj A)) (fun _ => True) hu'' g
      ((weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
        evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta).1 x)
  simp only [weilAdelicFrameBaseChangeComp_apply]
  exact (rationalMonodromy_map s hs htor (fun _ => True) hu''
    (AbelianScheme.baseChangeCompIso b c A).hom g (eta.1 x)).symm

/-- Restrict the actual direct-to-successive comparison to fixed orbit classes. -/
def weilAdelicLevelBaseChangeComp (U : Subgroup G) : LD U ≃ LC U := by
  let := rD
  let := rC
  let := mD
  let := mC
  let := kD
  let := kC
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (weilAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)
      (weilAdelicFrameBaseChangeComp_right preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)
      (weilAdelicFrameBaseChangeComp_monodromy preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'')

@[simp] theorem weilAdelicLevelBaseChangeComp_val (U : Subgroup G) (q : LD U) :
    (weilAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' U q).1 =
      weilAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U q.1 := rfl

@[simp] theorem weilAdelicLevelBaseChangeComp_symm_val (U : Subgroup G) (q : LC U) :
    ((weilAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' U).symm q).1 =
      (weilAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U).symm q.1 := rfl

/-- The fixed-level comparison commutes with all permitted Hecke maps. -/
theorem weilAdelicLevelBaseChangeComp_translate {U U' : Subgroup G} (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (q : LD U) :
    letI := rD
    letI := rC
    letI := mD
    letI := mC
    letI := kD
    letI := kC
    weilAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' U'
      (InvariantOrbit.translate g hg q) =
      InvariantOrbit.translate g hg (weilAdelicLevelBaseChangeComp preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c
        universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb
        s hs htor hu'' U q) := by
  let := rD
  let := rC
  let := mD
  let := mC
  let := kD
  let := kC
  apply Subtype.ext
  exact weilAdelicFrameRightOrbitBaseChangeComp_translate preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb
    geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s g hg q.1

/-- Forgetting a finer subgroup commutes with the composition comparison. -/
theorem weilAdelicLevelBaseChangeComp_forget {U U' : Subgroup G} (hU : U ≤ U') (q : LD U) :
    letI := rD
    letI := rC
    letI := mD
    letI := mC
    letI := kD
    letI := kC
    weilAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' U'
      (InvariantOrbit.forget hU q) =
      InvariantOrbit.forget hU (weilAdelicLevelBaseChangeComp preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c
        universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb
        s hs htor hu'' U q) := by
  exact weilAdelicLevelBaseChangeComp_translate preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
    evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' 1 _ q

variable (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S', ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]
  [hμfin' : ∀ n : Index (fun _ => True), IsFinite (mu S' n.val).X.hom]
  [hμet' : ∀ n : Index (fun _ => True), Etale (mu S' n.val).X.hom]

/-- Direct pullback agrees with successive pointed pullback after the actual
composition comparison and the necessary point-associativity transport. -/
theorem weilAdelicLevelBaseChange_comp
    (hc : ∀ Y : Cover S', Finite (Fiber (s ≫ c) Y))
    (hbpt : ∀ Y : Cover S, Finite (Fiber ((s ≫ c) ≫ b) Y))
    (hbcpt : ∀ Y : Cover S, Finite (Fiber (s ≫ (c ≫ b)) Y))
    (U : Subgroup G) (q : WeilAdelicLevel preservation composition unitCoherence associativity comparison
      symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i V ψ
      ((s ≫ c) ≫ b) hbpt htor hu (hμfin := hμfin) (hμet := hμet) U) :
    weilAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' U
      (weilAdelicLevelBaseChange (c ≫ b) A preservation composition unitCoherence associativity comparison
        symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc
        compatibility lam h i V ψ s hs hbcpt htor hu hu'' (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin'')
        (hμet' := hμet'') U
        ((weilAdelicLevelPointEq preservation composition unitCoherence associativity comparison symmetry
          stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.assoc s c b).symm hbcpt hbpt
          htor hu U).symm q)) =
      weilAdelicLevelBaseChange c ((baseChange b).obj A) preservation composition unitCoherence associativity
        comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb evaluationcb
        compatibility (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity
        comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb lam)
        h ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ s hs hc htor hu' hu'' (hμfin := hμfin') (hμet
        := hμet') (hμfin' := hμfin'') (hμet' := hμet'') U
        (weilAdelicLevelBaseChange b A preservation composition unitCoherence associativity comparison symmetry
          stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb compatibility lam h i V
          ψ (s ≫ c) hc hbpt htor hu hu' (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') U q)
          := by
  let := weilAdelicFrameRightAction (S := S) (A := A) preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ ((s ≫ c) ≫ b)
  let := weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry
    stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i V ψ ((s ≫ c) ≫ b)
    hbpt htor hu (hμfin := hμfin) (hμet := hμet)
  let := weilAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry
    stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam h i V ψ ((s ≫ c) ≫ b)
    hbpt htor hu (hμfin := hμfin) (hμet := hμet)
  apply Subtype.ext
  rw [weilAdelicLevelBaseChangeComp_val]
  rw [weilAdelicLevelBaseChange_val (c ≫ b) A preservation composition unitCoherence associativity comparison
    symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc compatibility
    lam h i V ψ s hs hbcpt htor hu hu'' (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin'') (hμet' := hμet'') U]
  rw [weilAdelicLevelPointEq_symm_val preservation composition unitCoherence associativity comparison symmetry
    stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.assoc s c b).symm hbcpt hbpt htor
    hu U]
  exact inverse_level_comparison_square
    (weilAdelicFrameRightOrbitBaseChange b A preservation composition unitCoherence associativity comparison
      symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb compatibility lam
      h i V ψ (s ≫ c) U)
    (weilAdelicFrameRightOrbitBaseChange c ((baseChange b).obj A) preservation composition unitCoherence
      associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb
      evaluationcb compatibility (canonicalDualValuedBaseChange b A preservation composition unitCoherence
      associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
      evaluationb lam) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ s U)
    (weilAdelicFrameRightOrbitBaseChange (c ≫ b) A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc
      compatibility lam h i V ψ s U)
    (weilAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ (Category.assoc s c b).symm U)
    (weilAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb geometryb Mb
      evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U)
    (weilAdelicFrameRightOrbitBaseChange_base_comp preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U) q.1

end Composition
end Full
section Away
variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
local notation "G" => ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ

/-- Equality of pointed fibres transports the actual fixed orbit sets. -/
def weilPrimeToAdelicLevelPointEq {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (htor : TorsionFiniteEtaleStatement.{u})
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom] (U : Subgroup G) :
    WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
      compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam hAway i V ψ s hs htor hu
      (hμfin := hμfin) (hμet := hμet) U ≃
      WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
        compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam hAway i V ψ t ht htor hu
        (hμfin := hμfin) (hμet := hμet) U := by
  subst t
  exact Equiv.refl _

/-- The underlying orbit is the existing compatible-frame point transport. -/
@[simp] theorem weilPrimeToAdelicLevelPointEq_val {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (htor : TorsionFiniteEtaleStatement.{u})
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom] (U : Subgroup G)
    (q : WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry
      stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam hAway i V ψ s hs
      htor hu (hμfin := hμfin) (hμet := hμet) U) :
    (weilPrimeToAdelicLevelPointEq preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst hs ht htor hu U q).1 =
      weilPrimeToAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst U q.1 := by
  subst t
  change q.1 = _
  induction q.1 using Quotient.inductionOn with
  | h eta => rfl

/-- Inverse point transport has the inverse underlying orbit comparison. -/
@[simp] theorem weilPrimeToAdelicLevelPointEq_symm_val {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (htor : TorsionFiniteEtaleStatement.{u})
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom] (U : Subgroup G)
    (q : WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry
      stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam hAway i V ψ t ht
      htor hu (hμfin := hμfin) (hμet := hμet) U) :
    ((weilPrimeToAdelicLevelPointEq preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst hs ht htor hu U).symm q).1 =
      (weilPrimeToAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst U).symm q.1 := by
  apply (weilPrimeToAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst U).injective
  rw [Equiv.apply_symm_apply]
  rw [← weilPrimeToAdelicLevelPointEq_val preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway hst hs ht htor hu U]
  rw [Equiv.apply_symm_apply]

section Identity
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})

  (hI : HasDualScheme ((baseChange (𝟙 S)).obj A)) (geometryI : DualSchemeGeometry ((baseChange (𝟙 S)).obj A) hI)
  (MI : LineBundle ((relativeSpace (((baseChange (𝟙 S)).obj A)).X.hom).obj (dualScheme ((baseChange (𝟙 S)).obj
    A) hI)))
  (evaluationI : tensorObj (poincareFamily ((baseChange (𝟙 S)).obj A) hI).obj.carrier MI.obj ≅
    structureSheaf ((relativeSpace (((baseChange (𝟙 S)).obj A)).X.hom).obj (dualScheme ((baseChange (𝟙 S)).obj
      A) hI)))
  (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

local notation "FA" => WeilPrimeToAdelicFrame (S := S) (A := A) preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ s hAway
local notation "FI" => WeilPrimeToAdelicFrame (S := S) (A := ((baseChange (𝟙 S)).obj A)) preservation
  composition unitCoherence associativity comparison symmetry stability hI geometryI MI evaluationI
  compatibility (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s hAway
local notation "rA" => weilPrimeToAdelicFrameRightAction (S := S) (A := A) preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V
  ψ s hAway
local notation "rI" => weilPrimeToAdelicFrameRightAction (S := S) (A := ((baseChange (𝟙 S)).obj A)) preservation
  composition unitCoherence associativity comparison symmetry stability hI geometryI MI evaluationI
  compatibility (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) h
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s hAway
local notation "mA" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA
  evaluationA lam hAway i V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "mI" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport hI geometryI MI
  evaluationI (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) hAway
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "kA" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam
  hAway i V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "kI" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hI geometryI MI evaluationI
  (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) hAway
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LA" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison
  symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam hAway i V ψ s
  hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LI" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison
  symmetry stability compatibility rationalWeilGeometricTransport hI geometryI MI evaluationI
  (canonicalDualValuedBaseChange (𝟙 S) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI lam) hAway
  ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)

/-- The identity scheme comparison intertwines actual geometric monodromy. -/
theorem weilPrimeToAdelicFrameBaseChangeId_monodromy :
    letI := mI
    letI := mA
    ∀ (g : FundamentalGroup s hs) (eta : FI),
      weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI
        MI evaluationI s (g • eta) = g • weilPrimeToAdelicFrameBaseChangeId preservation composition
        unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam
        h i V ψ hAway universality hI geometryI MI evaluationI s eta := by
  let := mI
  let := mA
  intro g eta
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI MI
    evaluationI s (g • eta)).1 x =
    rationalMonodromy s hs htor A (fun n => Nat.Coprime n m) hu g ((weilPrimeToAdelicFrameBaseChangeId
      preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA
      evaluationA compatibility lam h i V ψ hAway universality hI geometryI MI evaluationI s eta).1 x)
  simp only [weilPrimeToAdelicFrameBaseChangeId_apply]
  exact (rationalMonodromy_map s hs htor (fun n => Nat.Coprime n m) hu
    (AbelianScheme.baseChangeIdIso A).hom g (eta.1 x)).symm

/-- Restrict the actual identity comparison to monodromy-fixed right orbits. -/
def weilPrimeToAdelicLevelBaseChangeId (U : Subgroup G) : LI U ≃ LA U := by
  let := rI
  let := rA
  let := mI
  let := mA
  let := kI
  let := kA
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (weilPrimeToAdelicFrameBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI MI
      evaluationI s) (weilPrimeToAdelicFrameBaseChangeId_right preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
      universality hI geometryI MI evaluationI s) (weilPrimeToAdelicFrameBaseChangeId_monodromy preservation
      composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility lam h i V ψ hAway universality hI geometryI MI evaluationI s hs htor hu)

@[simp] theorem weilPrimeToAdelicLevelBaseChangeId_val (U : Subgroup G) (q : LI U) :
    (weilPrimeToAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI MI
      evaluationI s hs htor hu U q).1 = weilPrimeToAdelicFrameRightOrbitBaseChangeId preservation composition
      unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h
      i V ψ hAway universality hI geometryI MI evaluationI s U q.1 := rfl

@[simp] theorem weilPrimeToAdelicLevelBaseChangeId_symm_val (U : Subgroup G) (q : LA U) :
    ((weilPrimeToAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI
      MI evaluationI s hs htor hu U).symm q).1 = (weilPrimeToAdelicFrameRightOrbitBaseChangeId preservation
      composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility lam h i V ψ hAway universality hI geometryI MI evaluationI s U).symm q.1 := rfl

/-- The fixed-level comparison commutes with every allowed Hecke map. -/
theorem weilPrimeToAdelicLevelBaseChangeId_translate {U U' : Subgroup G} (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (q : LI U) :
    letI := rI
    letI := rA
    letI := mI
    letI := mA
    letI := kI
    letI := kA
    weilPrimeToAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI MI
      evaluationI s hs htor hu U' (InvariantOrbit.translate g hg q) =
      InvariantOrbit.translate g hg (weilPrimeToAdelicLevelBaseChangeId preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
        universality hI geometryI MI evaluationI s hs htor hu U q) := by
  let := rI
  let := rA
  let := mI
  let := mA
  let := kI
  let := kA
  apply Subtype.ext
  exact weilPrimeToAdelicFrameRightOrbitBaseChangeId_translate preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
    universality hI geometryI MI evaluationI s g hg q.1

/-- Forgetting a finer subgroup commutes with the identity comparison. -/
theorem weilPrimeToAdelicLevelBaseChangeId_forget {U U' : Subgroup G} (hU : U ≤ U') (q : LI U) :
    letI := rI
    letI := rA
    letI := mI
    letI := mA
    letI := kI
    letI := kA
    weilPrimeToAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI MI
      evaluationI s hs htor hu U' (InvariantOrbit.forget hU q) =
      InvariantOrbit.forget hU (weilPrimeToAdelicLevelBaseChangeId preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
        universality hI geometryI MI evaluationI s hs htor hu U q) := by
  exact weilPrimeToAdelicLevelBaseChangeId_translate preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI
    geometryI MI evaluationI s hs htor hu 1 _ q

/-- Identity pullback agrees with point transport after the canonical comparison. -/
theorem weilPrimeToAdelicLevelBaseChange_id
    (hs' : ∀ Y : Cover S, Finite (Fiber (s ≫ 𝟙 S) Y))
    (U : Subgroup G) (q : WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison
      symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam hAway i V
      ψ (s ≫ 𝟙 S) hs' htor hu (hμfin := hμfin) (hμet := hμet) U) :
    weilPrimeToAdelicLevelBaseChangeId preservation composition unitCoherence associativity comparison symmetry
      stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway universality hI geometryI MI
      evaluationI s hs htor hu U (weilPrimeToAdelicLevelBaseChange (𝟙 S) A preservation composition
      unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hI
      geometryI MI evaluationI compatibility lam h i V ψ s hs hs' htor hAway hu hu (hμfin := hμfin) (hμet :=
      hμet) (hμfin' := hμfin) (hμet' := hμet) U q) =
      weilPrimeToAdelicLevelPointEq preservation composition unitCoherence associativity comparison symmetry
        stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.comp_id s) hs' hs htor
        hu U q := by
  apply Subtype.ext
  rw [weilPrimeToAdelicLevelBaseChangeId_val, weilPrimeToAdelicLevelBaseChange_val,
    weilPrimeToAdelicLevelPointEq_val]
  have square := weilPrimeToAdelicFrameRightOrbitBaseChange_id preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
    universality hI geometryI MI evaluationI s U
    ((weilPrimeToAdelicFrameRightOrbitBaseChange (𝟙 S) A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hI geometryI MI evaluationI
      compatibility lam h i V ψ s hAway U).symm q.1)
  rw [Equiv.apply_symm_apply] at square
  exact square.symm

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
  (s : Spec (.of Ω) ⟶ S'')
  (hs : ∀ Y : Cover S'', Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu'' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S'', ⊤)))
  [hμfin'' : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S'' n.val).X.hom]
  [hμet'' : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S'' n.val).X.hom]

local notation "FD" => WeilPrimeToAdelicFrame (S := S'') (A := ((baseChange (c ≫ b)).obj A)) preservation
  composition unitCoherence associativity comparison symmetry stability hbc geometrybc Mbc evaluationbc
  compatibility (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) h
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s hAway
local notation "FC" => WeilPrimeToAdelicFrame (S := S'') (A := ((baseChange c).obj ((baseChange b).obj A)))
  preservation composition unitCoherence associativity comparison symmetry stability hcb geometrycb Mcb
  evaluationcb compatibility (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition
  unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb
  geometrycb Mcb evaluationcb (canonicalDualValuedBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
  evaluationb lam)) h ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ψ s hAway
local notation "rD" => weilPrimeToAdelicFrameRightAction (S := S'') (A := ((baseChange (c ≫ b)).obj A))
  preservation composition unitCoherence associativity comparison symmetry stability hbc geometrybc Mbc
  evaluationbc compatibility (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc
  evaluationbc lam) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s hAway
local notation "rC" => weilPrimeToAdelicFrameRightAction (S := S'') (A := ((baseChange c).obj ((baseChange
  b).obj A))) preservation composition unitCoherence associativity comparison symmetry stability hcb geometrycb
  Mcb evaluationcb compatibility (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation
  composition unitCoherence associativity comparison symmetry stability universality hb geometryb Mb evaluationb
  hcb geometrycb Mcb evaluationcb (canonicalDualValuedBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
  evaluationb lam)) h ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp
  ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ψ s hAway
local notation "mD" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport hbc geometrybc Mbc
  evaluationbc (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam)
  hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet :=
  hμet'')
local notation "mC" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport hcb geometrycb Mcb
  evaluationcb (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition unitCoherence
  associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb
  evaluationcb (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity
  comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb lam)) hAway
  ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b
  A).comp i)) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet := hμet'')
local notation "kD" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hbc geometrybc Mbc evaluationbc
  (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) hAway
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet :=
  hμet'')
local notation "kC" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition unitCoherence associativity
  comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity comparison symmetry
  stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb lam)) hAway
  ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b
  A).comp i)) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet := hμet'')
local notation "LD" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison
  symmetry stability compatibility rationalWeilGeometricTransport hbc geometrybc Mbc evaluationbc
  (canonicalDualValuedBaseChange (c ≫ b) A preservation composition unitCoherence associativity comparison
  symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc lam) hAway
  ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet :=
  hμet'')
local notation "LC" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison
  symmetry stability compatibility rationalWeilGeometricTransport hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange c ((baseChange b).obj A) preservation composition unitCoherence associativity
  comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb evaluationcb
  (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity comparison symmetry
  stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb lam)) hAway
  ((AbelianScheme.rationalBaseChangeEnd c ((baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b
  A).comp i)) V ψ s hs htor hu'' (hμfin := hμfin'') (hμet := hμet'')

/-- The composition scheme comparison intertwines actual geometric monodromy. -/
theorem weilPrimeToAdelicFrameBaseChangeComp_monodromy :
    letI := mD
    letI := mC
    ∀ (g : FundamentalGroup s hs) (eta : FD),
      weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
        geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s (g • eta) = g
        • weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
        geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta := by
  let := mD
  let := mC
  intro g eta
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb geometryb
    Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s (g • eta)).1 x =
    rationalMonodromy s hs htor ((baseChange c).obj ((baseChange b).obj A)) (fun n => Nat.Coprime n m) hu'' g
      ((weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
        geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s eta).1 x)
  simp only [weilPrimeToAdelicFrameBaseChangeComp_apply]
  exact (rationalMonodromy_map s hs htor (fun n => Nat.Coprime n m) hu''
    (AbelianScheme.baseChangeCompIso b c A).hom g (eta.1 x)).symm

/-- Restrict the actual direct-to-successive comparison to fixed orbit classes. -/
def weilPrimeToAdelicLevelBaseChangeComp (U : Subgroup G) : LD U ≃ LC U := by
  let := rD
  let := rC
  let := mD
  let := mC
  let := kD
  let := kC
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (weilPrimeToAdelicFrameBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)
      (weilPrimeToAdelicFrameBaseChangeComp_right preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality
      hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s)
      (weilPrimeToAdelicFrameBaseChangeComp_monodromy preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality
      hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor
      hu'')

@[simp] theorem weilPrimeToAdelicLevelBaseChangeComp_val (U : Subgroup G) (q : LD U) :
    (weilPrimeToAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' U
      q).1 = weilPrimeToAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality
      hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U q.1 := rfl

@[simp] theorem weilPrimeToAdelicLevelBaseChangeComp_symm_val (U : Subgroup G) (q : LC U) :
    ((weilPrimeToAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu''
      U).symm q).1 = (weilPrimeToAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b
      c universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb
      s U).symm q.1 := rfl

/-- The fixed-level comparison commutes with all permitted Hecke maps. -/
theorem weilPrimeToAdelicLevelBaseChangeComp_translate {U U' : Subgroup G} (g : G)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (q : LD U) :
    letI := rD
    letI := rC
    letI := mD
    letI := mC
    letI := kD
    letI := kC
    weilPrimeToAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' U'
      (InvariantOrbit.translate g hg q) =
      InvariantOrbit.translate g hg (weilPrimeToAdelicLevelBaseChangeComp preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
        b c universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb
        evaluationcb s hs htor hu'' U q) := by
  let := rD
  let := rC
  let := mD
  let := mC
  let := kD
  let := kC
  apply Subtype.ext
  exact weilPrimeToAdelicFrameRightOrbitBaseChangeComp_translate preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c
    universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s g
    hg q.1

/-- Forgetting a finer subgroup commutes with the composition comparison. -/
theorem weilPrimeToAdelicLevelBaseChangeComp_forget {U U' : Subgroup G} (hU : U ≤ U') (q : LD U) :
    letI := rD
    letI := rC
    letI := mD
    letI := mC
    letI := kD
    letI := kC
    weilPrimeToAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' U'
      (InvariantOrbit.forget hU q) =
      InvariantOrbit.forget hU (weilPrimeToAdelicLevelBaseChangeComp preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway
        b c universality hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb
        evaluationcb s hs htor hu'' U q) := by
  exact weilPrimeToAdelicLevelBaseChangeComp_translate preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality
    hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' 1
    _ q

variable (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S', ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]
  [hμfin' : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S' n.val).X.hom]
  [hμet' : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S' n.val).X.hom]

/-- Direct pullback agrees with successive pointed pullback after the actual
composition comparison and the necessary point-associativity transport. -/
theorem weilPrimeToAdelicLevelBaseChange_comp
    (hc : ∀ Y : Cover S', Finite (Fiber (s ≫ c) Y))
    (hbpt : ∀ Y : Cover S, Finite (Fiber ((s ≫ c) ≫ b) Y))
    (hbcpt : ∀ Y : Cover S, Finite (Fiber (s ≫ (c ≫ b)) Y))
    (U : Subgroup G) (q : WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison
      symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam hAway i V
      ψ ((s ≫ c) ≫ b) hbpt htor hu (hμfin := hμfin) (hμet := hμet) U) :
    weilPrimeToAdelicLevelBaseChangeComp preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality hb
      geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s hs htor hu'' U
      (weilPrimeToAdelicLevelBaseChange (c ≫ b) A preservation composition unitCoherence associativity
        comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc
        compatibility lam h i V ψ s hs hbcpt htor hAway hu hu'' (hμfin := hμfin) (hμet := hμet) (hμfin' :=
        hμfin'') (hμet' := hμet'') U
        ((weilPrimeToAdelicLevelPointEq preservation composition unitCoherence associativity comparison symmetry
          stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.assoc s c b).symm
          hbcpt hbpt htor hu U).symm q)) =
      weilPrimeToAdelicLevelBaseChange c ((baseChange b).obj A) preservation composition unitCoherence
        associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb
        evaluationcb compatibility (canonicalDualValuedBaseChange b A preservation composition unitCoherence
        associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
        evaluationb lam) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ s hs hc htor hAway hu' hu''
        (hμfin := hμfin') (hμet := hμet') (hμfin' := hμfin'') (hμet' := hμet'') U
        (weilPrimeToAdelicLevelBaseChange b A preservation composition unitCoherence associativity comparison
          symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb compatibility
          lam h i V ψ (s ≫ c) hc hbpt htor hAway hu hu' (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin')
          (hμet' := hμet') U q) := by
  let := weilPrimeToAdelicFrameRightAction (S := S) (A := A) preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ ((s ≫ c) ≫
    b) hAway
  let := weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison
    symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam hAway i V ψ
    ((s ≫ c) ≫ b) hbpt htor hu (hμfin := hμfin) (hμet := hμet)
  let := weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity comparison
    symmetry stability compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA lam hAway i V ψ
    ((s ≫ c) ≫ b) hbpt htor hu (hμfin := hμfin) (hμet := hμet)
  apply Subtype.ext
  rw [weilPrimeToAdelicLevelBaseChangeComp_val]
  rw [weilPrimeToAdelicLevelBaseChange_val (c ≫ b) A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc
    compatibility lam h i V ψ s hs hbcpt htor hAway hu hu'' (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin'')
    (hμet' := hμet'') U]
  rw [weilPrimeToAdelicLevelPointEq_symm_val preservation composition unitCoherence associativity comparison
    symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.assoc s c b).symm
    hbcpt hbpt htor hu U]
  exact inverse_level_comparison_square
    (weilPrimeToAdelicFrameRightOrbitBaseChange b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb evaluationb
      compatibility lam h i V ψ (s ≫ c) hAway U)
    (weilPrimeToAdelicFrameRightOrbitBaseChange c ((baseChange b).obj A) preservation composition unitCoherence
      associativity comparison symmetry stability universality hb geometryb Mb evaluationb hcb geometrycb Mcb
      evaluationcb compatibility (canonicalDualValuedBaseChange b A preservation composition unitCoherence
      associativity comparison symmetry stability universality hA geometryA MA evaluationA hb geometryb Mb
      evaluationb lam) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ψ s hAway U)
    (weilPrimeToAdelicFrameRightOrbitBaseChange (c ≫ b) A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hbc geometrybc Mbc evaluationbc
      compatibility lam h i V ψ s hAway U)
    (weilPrimeToAdelicFrameRightOrbitPointEq preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway (Category.assoc s c b).symm
      U)
    (weilPrimeToAdelicFrameRightOrbitBaseChangeComp preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality
      hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U)
    (weilPrimeToAdelicFrameRightOrbitBaseChange_base_comp preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ hAway b c universality
      hb geometryb Mb evaluationb hbc geometrybc Mbc evaluationbc hcb geometrycb Mcb evaluationcb s U) q.1

end Composition
end Away
end Langlands.AbelianScheme.Tate

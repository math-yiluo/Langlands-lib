import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelBaseChange
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelIsogeny

/-! # Pointed base change and rational isogenies of actual Weil level towers -/

universe u v w
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

section Intertwining
variable {S S' : Scheme.{u}} (b : S' ⟶ S) {A B : AbelianScheme S}
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] End0 A) (iB : D →ₐ[ℚ] End0 B)
  (e : Rationalization.of A ≅ Rationalization.of B)
  (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
    Rationalization.comp A B B e.hom (iB d))

include he

/-- Actual rational pullback preserves intertwining of algebra actions. -/
theorem rationalIntertwines_baseChange (d : D) :
    Rationalization.comp _ _ _ (((rationalBaseChangeEnd b A).comp iA) d)
        (rationalBaseChangeIso b e).hom =
      Rationalization.comp _ _ _ (rationalBaseChangeIso b e).hom
        (((rationalBaseChangeEnd b B).comp iB) d) := by
  simpa only [rationalBaseChangeHom_comp, AlgHom.comp_apply,
    rationalBaseChangeEnd_apply, rationalBaseChangeIso_hom] using
    congrArg (rationalBaseChangeHom b) (he d)
end Intertwining

variable {S S' : Scheme.{u}} (b : S' ⟶ S) [QuasiSeparatedSpace S]
  [QuasiSeparatedSpace S'] {A B : AbelianScheme S}
  (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (lamA : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (hB : HasDualScheme B) (geometryB : DualSchemeGeometry B hB)
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (lamB : B ⟶ dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
    evaluationB stability composition unitCoherence associativity comparison symmetry)

set_option quotPrecheck false in
local notation "Ab" => (baseChange b).obj A
set_option quotPrecheck false in
local notation "Bb" => (baseChange b).obj B

variable
  (hAb : HasDualScheme ((baseChange b).obj A))
  (geometryAb : DualSchemeGeometry ((baseChange b).obj A) hAb)
  (MAb : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hAb)))
  (evaluationAb : tensorObj (poincareFamily ((baseChange b).obj A) hAb).obj.carrier
    MAb.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hAb)))
  (hBb : HasDualScheme ((baseChange b).obj B))
  (geometryBb : DualSchemeGeometry ((baseChange b).obj B) hBb)
  (MBb : LineBundle ((relativeSpace ((baseChange b).obj B).X.hom).obj
    (dualScheme ((baseChange b).obj B) hBb)))
  (evaluationBb : tensorObj (poincareFamily ((baseChange b).obj B) hBb).obj.carrier
    MBb.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj B).X.hom).obj
      (dualScheme ((baseChange b).obj B) hBb)))
  (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)
  (additivityb : DualSchemeMapAdditivity preservation stability
    ((baseChange b).obj A) ((baseChange b).obj B) hAb hBb)
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] End0 A) (iB : D →ₐ[ℚ] End0 B)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S')

local notation "lamAb" => canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity comparison symmetry stability
  universality hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb lamA
set_option quotPrecheck false in
local notation "iAb" => (rationalBaseChangeEnd b A).comp iA
local notation "lamBb" => canonicalDualValuedBaseChange b B preservation composition unitCoherence associativity comparison symmetry stability
  universality hB geometryB MB evaluationB hBb geometryBb MBb evaluationBb lamB
set_option quotPrecheck false in
local notation "iBb" => (rationalBaseChangeEnd b B).comp iB

local notation "multiple" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability
  hA hB geometryA geometryB MA evaluationA MB evaluationB additivity
local notation "multipleb" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability
  hAb hBb geometryAb geometryBb MAb evaluationAb MBb evaluationBb additivityb

variable (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
  (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
    Rationalization.comp A B B e.hom (iB d))
  (hqe : IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability
    hA hB geometryA geometryB MA evaluationA MB evaluationB additivity (q : ℚ) e.hom
    (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
  (hqeb : IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability
    hAb hBb geometryAb geometryBb MAb evaluationAb MBb evaluationBb additivityb
    (q : ℚ) (rationalBaseChangeIso b e).hom
    (Rationalization.ofHom (canonicalDualValuedBaseChange b A preservation composition unitCoherence associativity comparison symmetry stability
      universality hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb lamA))
    (Rationalization.ofHom (canonicalDualValuedBaseChange b B preservation composition unitCoherence associativity comparison symmetry stability
      universality hB geometryB MB evaluationB hBb geometryBb MBb evaluationBb lamB)))

local notation "eb" => rationalBaseChangeIso b e
local notation "heb" => rationalIntertwines_baseChange b iA iB e he

section Full
local notation "FrameA" => WeilAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability
  hA geometryA MA evaluationA compatibility lamA h iA V ψ (s ≫ b)
local notation "rightA" => weilAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability
  hA geometryA MA evaluationA compatibility lamA h iA V ψ (s ≫ b)
local notation "FrameB" => WeilAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability
  hB geometryB MB evaluationB compatibility lamB h iB V ψ (s ≫ b)
local notation "rightB" => weilAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability
  hB geometryB MB evaluationB compatibility lamB h iB V ψ (s ≫ b)
local notation "FrameAb" => WeilAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability
  hAb geometryAb MAb evaluationAb compatibility lamAb h iAb V ψ s
local notation "rightAb" => weilAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability
  hAb geometryAb MAb evaluationAb compatibility lamAb h iAb V ψ s
local notation "FrameBb" => WeilAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability
  hBb geometryBb MBb evaluationBb compatibility lamBb h iBb V ψ s
local notation "rightBb" => weilAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability
  hBb geometryBb MBb evaluationBb compatibility lamBb h iBb V ψ s
local notation "bcA" => weilAdelicFrameBaseChange b A preservation composition unitCoherence associativity comparison symmetry stability
  universality hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb
  compatibility lamA h iA V ψ s
local notation "bcB" => weilAdelicFrameBaseChange b B preservation composition unitCoherence associativity comparison symmetry stability
  universality hB geometryB MB evaluationB hBb geometryBb MBb evaluationBb
  compatibility lamB h iB V ψ s
local notation "iso" => weilAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB
  compatibility rationalWeilFunctoriality h iA iB V ψ (s ≫ b) q e he hqe
local notation "isob" => weilAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hAb hBb geometryAb geometryBb MAb evaluationAb MBb evaluationBb additivityb lamAb lamBb
  compatibility rationalWeilFunctoriality h iAb iBb V ψ s q eb heb hqeb

/-- Actual rational Tate naturality gives the base-change/isogeny square on frames. -/
theorem weilAdelicFrameIsogeny_baseChange (eta : FrameAb) :
    bcB (isob eta) = iso (bcA eta) := by
  apply Subtype.ext
  ext x
  exact rationalBaseChange_iso b (Over.mk s) (fun _ => True) e (eta.1 x)

/-- The inverse base-change direction used to pull level structures back. -/
theorem weilAdelicFrameIsogeny_baseChange_symm (eta : FrameA) :
    isob ((bcA).symm eta) = (bcB).symm (iso eta) := by
  apply (bcB).injective
  rw [weilAdelicFrameIsogeny_baseChange, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Mixed comparison: actual isogeny transport followed by inverse Tate base change. -/
def weilAdelicFrameIsogenyBaseChange : FrameA ≃ FrameBb :=
  (iso).trans (bcB).symm

/-- Equivalently pull the frame back first and then use the pulled-back isogeny. -/
theorem weilAdelicFrameIsogenyBaseChange_eq :
    weilAdelicFrameIsogenyBaseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hBb geometryBb MBb evaluationBb additivity compatibility h iA iB V ψ s q e he hqe =
      (bcA).symm.trans isob := by
  apply Equiv.ext
  intro eta
  exact (weilAdelicFrameIsogeny_baseChange_symm b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb eta).symm

section Levels
variable (ht : ∀ Y : Cover S', Finite (Fiber s Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  (hub : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S', ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]
  [hμfinb : ∀ n : Index (fun _ => True), IsFinite (mu S' n.val).X.hom]
  [hμetb : ∀ n : Index (fun _ => True), Etale (mu S' n.val).X.hom]

local notation "G" => ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ
local notation "LevelA" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA
  lamA h iA V ψ (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "TowerA" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability
  compatibility hA geometryA MA evaluationA lamA h iA V ψ (s ≫ b)
  hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelB" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hB geometryB MB evaluationB
  lamB h iB V ψ (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "TowerB" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability
  compatibility hB geometryB MB evaluationB lamB h iB V ψ (s ≫ b)
  hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelAb" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hAb geometryAb MAb evaluationAb
  lamAb h iAb V ψ s ht htor hub (hμfin := hμfinb) (hμet := hμetb)
local notation "TowerAb" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability
  compatibility hAb geometryAb MAb evaluationAb lamAb h iAb V ψ s
  ht htor hub (hμfin := hμfinb) (hμet := hμetb)
local notation "LevelBb" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hBb geometryBb MBb evaluationBb
  lamBb h iBb V ψ s ht htor hub (hμfin := hμfinb) (hμet := hμetb)
local notation "TowerBb" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability
  compatibility hBb geometryBb MBb evaluationBb lamBb h iBb V ψ s
  ht htor hub (hμfin := hμfinb) (hμet := hμetb)
local notation "levelBCA" => weilAdelicLevelBaseChange b A preservation composition unitCoherence associativity comparison symmetry stability
  universality hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb
  compatibility lamA h iA V ψ s ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfinb) (hμet' := hμetb)
local notation "towerBCA" => weilAdelicCompactOpenLevelBaseChange b A preservation composition unitCoherence associativity comparison symmetry stability
  universality hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb
  compatibility lamA h iA V ψ s ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfinb) (hμet' := hμetb)
local notation "levelBCB" => weilAdelicLevelBaseChange b B preservation composition unitCoherence associativity comparison symmetry stability
  universality hB geometryB MB evaluationB hBb geometryBb MBb evaluationBb
  compatibility lamB h iB V ψ s ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfinb) (hμet' := hμetb)
local notation "towerBCB" => weilAdelicCompactOpenLevelBaseChange b B preservation composition unitCoherence associativity comparison symmetry stability
  universality hB geometryB MB evaluationB hBb geometryBb MBb evaluationBb
  compatibility lamB h iB V ψ s ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfinb) (hμet' := hμetb)
local notation "levelIso" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hA hB geometryA geometryB MA evaluationA MB evaluationB
  additivity lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport
  h iA iB V ψ (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "towerIso" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hA geometryA MA evaluationA lamA
  hB geometryB MB evaluationB lamB
  additivity compatibility h iA iB V ψ (s ≫ b) hs htor hu
  (hμfin := hμfin) (hμet := hμet) q e he hqe
local notation "levelIsob" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hAb hBb geometryAb geometryBb MAb evaluationAb MBb evaluationBb
  additivityb lamAb lamBb compatibility rationalWeilFunctoriality rationalWeilGeometricTransport
  h iAb iBb V ψ s ht htor hub (hμfin := hμfinb) (hμet := hμetb)
local notation "towerIsob" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hAb geometryAb MAb evaluationAb lamAb
  hBb geometryBb MBb evaluationBb lamBb
  additivityb compatibility h iAb iBb V ψ s ht htor hub
  (hμfin := hμfinb) (hμet := hμetb) q eb heb hqeb

/-- Pointed pullback and actual rational-isogeny transport commute on fixed orbits. -/
theorem weilAdelicLevelIsogeny_baseChange (U : Subgroup G) (x : LevelA U) :
    levelBCB U (levelIso U q e he hqe x) =
      levelIsob U q eb heb hqeb (levelBCA U x) := by
  let := rightA
  let := rightB
  let := rightAb
  let := rightBb
  apply Subtype.ext
  simp only [weilAdelicLevelBaseChange_val, weilAdelicLevelIsogeny,
    InvariantOrbit.equiv, Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilAdelicFrameIsogeny_baseChange_symm b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb eta).symm

/-- Mixed level transport is the old isogeny followed by pointed pullback. -/
def weilAdelicLevelIsogenyBaseChange (U : Subgroup G) : LevelA U → LevelBb U :=
  fun x => levelBCB U (levelIso U q e he hqe x)

/-- The same level map is obtained by pulling back before applying the new isogeny. -/
theorem weilAdelicLevelIsogenyBaseChange_eq (U : Subgroup G) :
    weilAdelicLevelIsogenyBaseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hBb geometryBb MBb evaluationBb additivity compatibility h iA iB V ψ s q e he hqe ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb) U =
      fun x => levelIsob U q eb heb hqeb (levelBCA U x) := by
  funext x
  exact weilAdelicLevelIsogeny_baseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb) U x

/-- Mixed transport is natural in compact-open level and every transporter arrow. -/
def weilAdelicCompactOpenLevelIsogenyBaseChange : TowerA ⟶ TowerBb :=
  (towerIso).hom ≫ towerBCB

local notation "mixed" => weilAdelicCompactOpenLevelIsogenyBaseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hBb geometryBb MBb evaluationBb additivity compatibility h iA iB V ψ s q e he hqe ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb)

/-- The two routes form the same natural transformation of actual level towers. -/
theorem weilAdelicCompactOpenLevelIsogeny_baseChange :
    (towerIso).hom ≫ towerBCB = towerBCA ≫ (towerIsob).hom := by
  ext K x
  exact weilAdelicLevelIsogeny_baseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb) K.toSubgroup x

/-- Reverse-route expression for mixed tower transport. -/
theorem weilAdelicCompactOpenLevelIsogenyBaseChange_eq :
    mixed = towerBCA ≫ (towerIsob).hom :=
  weilAdelicCompactOpenLevelIsogeny_baseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb)

end Levels
end Full

section Away
variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

local notation "FrameA" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability
  hA geometryA MA evaluationA compatibility lamA h iA V ψ (s ≫ b) hAway
local notation "rightA" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability
  hA geometryA MA evaluationA compatibility lamA h iA V ψ (s ≫ b) hAway
local notation "FrameB" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability
  hB geometryB MB evaluationB compatibility lamB h iB V ψ (s ≫ b) hAway
local notation "rightB" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability
  hB geometryB MB evaluationB compatibility lamB h iB V ψ (s ≫ b) hAway
local notation "FrameAb" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability
  hAb geometryAb MAb evaluationAb compatibility lamAb h iAb V ψ s hAway
local notation "rightAb" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability
  hAb geometryAb MAb evaluationAb compatibility lamAb h iAb V ψ s hAway
local notation "FrameBb" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability
  hBb geometryBb MBb evaluationBb compatibility lamBb h iBb V ψ s hAway
local notation "rightBb" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability
  hBb geometryBb MBb evaluationBb compatibility lamBb h iBb V ψ s hAway
local notation "bcA" => weilPrimeToAdelicFrameBaseChange b A preservation composition unitCoherence associativity comparison symmetry stability
  universality hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb
  compatibility lamA h iA V ψ s hAway
local notation "bcB" => weilPrimeToAdelicFrameBaseChange b B preservation composition unitCoherence associativity comparison symmetry stability
  universality hB geometryB MB evaluationB hBb geometryBb MBb evaluationBb
  compatibility lamB h iB V ψ s hAway
local notation "iso" => weilPrimeToAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB
  compatibility rationalWeilFunctoriality h iA iB V ψ (s ≫ b) hAway q e he hqe
local notation "isob" => weilPrimeToAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hAb hBb geometryAb geometryBb MAb evaluationAb MBb evaluationBb additivityb lamAb lamBb
  compatibility rationalWeilFunctoriality h iAb iBb V ψ s hAway q eb heb hqeb

/-- Actual rational Tate naturality gives the base-change/isogeny square on frames. -/
theorem weilPrimeToAdelicFrameIsogeny_baseChange (eta : FrameAb) :
    bcB (isob eta) = iso (bcA eta) := by
  apply Subtype.ext
  ext x
  exact rationalBaseChange_iso b (Over.mk s) (fun n => Nat.Coprime n m) e (eta.1 x)

/-- The inverse base-change direction used to pull level structures back. -/
theorem weilPrimeToAdelicFrameIsogeny_baseChange_symm (eta : FrameA) :
    isob ((bcA).symm eta) = (bcB).symm (iso eta) := by
  apply (bcB).injective
  rw [weilPrimeToAdelicFrameIsogeny_baseChange, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Mixed comparison: actual isogeny transport followed by inverse Tate base change. -/
def weilPrimeToAdelicFrameIsogenyBaseChange : FrameA ≃ FrameBb :=
  (iso).trans (bcB).symm

/-- Equivalently pull the frame back first and then use the pulled-back isogeny. -/
theorem weilPrimeToAdelicFrameIsogenyBaseChange_eq :
    weilPrimeToAdelicFrameIsogenyBaseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hBb geometryBb MBb evaluationBb additivity compatibility h iA iB V ψ s q e he hqe hAway =
      (bcA).symm.trans isob := by
  apply Equiv.ext
  intro eta
  exact (weilPrimeToAdelicFrameIsogeny_baseChange_symm b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb hAway eta).symm

section Levels
variable (ht : ∀ Y : Cover S', Finite (Fiber s Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  (hub : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S', ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]
  [hμfinb : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S' n.val).X.hom]
  [hμetb : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S' n.val).X.hom]

local notation "G" => ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ
local notation "LevelA" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hA geometryA MA evaluationA
  lamA hAway iA V ψ (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "TowerA" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability
  compatibility hA geometryA MA evaluationA lamA hAway iA V ψ (s ≫ b)
  hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelB" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hB geometryB MB evaluationB
  lamB hAway iB V ψ (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "TowerB" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability
  compatibility hB geometryB MB evaluationB lamB hAway iB V ψ (s ≫ b)
  hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelAb" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hAb geometryAb MAb evaluationAb
  lamAb hAway iAb V ψ s ht htor hub (hμfin := hμfinb) (hμet := hμetb)
local notation "TowerAb" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability
  compatibility hAb geometryAb MAb evaluationAb lamAb hAway iAb V ψ s
  ht htor hub (hμfin := hμfinb) (hμet := hμetb)
local notation "LevelBb" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability
  compatibility rationalWeilGeometricTransport hBb geometryBb MBb evaluationBb
  lamBb hAway iBb V ψ s ht htor hub (hμfin := hμfinb) (hμet := hμetb)
local notation "TowerBb" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability
  compatibility hBb geometryBb MBb evaluationBb lamBb hAway iBb V ψ s
  ht htor hub (hμfin := hμfinb) (hμet := hμetb)
local notation "levelBCA" => weilPrimeToAdelicLevelBaseChange b A preservation composition unitCoherence associativity comparison symmetry stability
  universality hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb
  compatibility lamA h iA V ψ s ht hs htor hAway hu hub (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfinb) (hμet' := hμetb)
local notation "towerBCA" => weilPrimeToAdelicCompactOpenLevelBaseChange b A preservation composition unitCoherence associativity comparison symmetry stability
  universality hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb
  compatibility lamA h iA V ψ s ht hs htor hAway hu hub (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfinb) (hμet' := hμetb)
local notation "levelBCB" => weilPrimeToAdelicLevelBaseChange b B preservation composition unitCoherence associativity comparison symmetry stability
  universality hB geometryB MB evaluationB hBb geometryBb MBb evaluationBb
  compatibility lamB h iB V ψ s ht hs htor hAway hu hub (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfinb) (hμet' := hμetb)
local notation "towerBCB" => weilPrimeToAdelicCompactOpenLevelBaseChange b B preservation composition unitCoherence associativity comparison symmetry stability
  universality hB geometryB MB evaluationB hBb geometryBb MBb evaluationBb
  compatibility lamB h iB V ψ s ht hs htor hAway hu hub (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfinb) (hμet' := hμetb)
local notation "levelIso" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hA hB geometryA geometryB MA evaluationA MB evaluationB
  additivity lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport
  h iA iB V ψ (s ≫ b) hs htor hAway hu (hμfin := hμfin) (hμet := hμet)
local notation "towerIso" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hA geometryA MA evaluationA lamA
  hB geometryB MB evaluationB lamB
  additivity compatibility h iA iB V ψ (s ≫ b) hs htor hAway hu
  (hμfin := hμfin) (hμet := hμet) q e he hqe
local notation "levelIsob" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hAb hBb geometryAb geometryBb MAb evaluationAb MBb evaluationBb
  additivityb lamAb lamBb compatibility rationalWeilFunctoriality rationalWeilGeometricTransport
  h iAb iBb V ψ s ht htor hAway hub (hμfin := hμfinb) (hμet := hμetb)
local notation "towerIsob" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability
  hAb geometryAb MAb evaluationAb lamAb
  hBb geometryBb MBb evaluationBb lamBb
  additivityb compatibility h iAb iBb V ψ s ht htor hAway hub
  (hμfin := hμfinb) (hμet := hμetb) q eb heb hqeb

/-- Pointed pullback and actual rational-isogeny transport commute on fixed orbits. -/
theorem weilPrimeToAdelicLevelIsogeny_baseChange (U : Subgroup G) (x : LevelA U) :
    levelBCB U (levelIso U q e he hqe x) =
      levelIsob U q eb heb hqeb (levelBCA U x) := by
  let := rightA
  let := rightB
  let := rightAb
  let := rightBb
  apply Subtype.ext
  simp only [weilPrimeToAdelicLevelBaseChange_val, weilPrimeToAdelicLevelIsogeny,
    InvariantOrbit.equiv, Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilPrimeToAdelicFrameIsogeny_baseChange_symm b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb hAway eta).symm

/-- Mixed level transport is the old isogeny followed by pointed pullback. -/
def weilPrimeToAdelicLevelIsogenyBaseChange (U : Subgroup G) : LevelA U → LevelBb U :=
  fun x => levelBCB U (levelIso U q e he hqe x)

/-- The same level map is obtained by pulling back before applying the new isogeny. -/
theorem weilPrimeToAdelicLevelIsogenyBaseChange_eq (U : Subgroup G) :
    weilPrimeToAdelicLevelIsogenyBaseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hBb geometryBb MBb evaluationBb additivity compatibility h iA iB V ψ s q e he hqe hAway ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb) U =
      fun x => levelIsob U q eb heb hqeb (levelBCA U x) := by
  funext x
  exact weilPrimeToAdelicLevelIsogeny_baseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb hAway ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb) U x

/-- Mixed transport is natural in compact-open level and every transporter arrow. -/
def weilPrimeToAdelicCompactOpenLevelIsogenyBaseChange : TowerA ⟶ TowerBb :=
  (towerIso).hom ≫ towerBCB

local notation "mixed" => weilPrimeToAdelicCompactOpenLevelIsogenyBaseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hBb geometryBb MBb evaluationBb additivity compatibility h iA iB V ψ s q e he hqe hAway ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb)

/-- The two routes form the same natural transformation of actual level towers. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogeny_baseChange :
    (towerIso).hom ≫ towerBCB = towerBCA ≫ (towerIsob).hom := by
  ext K x
  exact weilPrimeToAdelicLevelIsogeny_baseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb hAway ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb) K.toSubgroup x

/-- Reverse-route expression for mixed tower transport. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogenyBaseChange_eq :
    mixed = towerBCA ≫ (towerIsob).hom :=
  weilPrimeToAdelicCompactOpenLevelIsogeny_baseChange b preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hAb geometryAb MAb evaluationAb hBb geometryBb MBb evaluationBb additivity additivityb compatibility h iA iB V ψ s q e he hqe hqeb hAway ht hs htor hu hub (hμfin := hμfin) (hμet := hμet) (hμfinb := hμfinb) (hμetb := hμetb)

end Levels
end Away

end Langlands.AbelianScheme.Tate

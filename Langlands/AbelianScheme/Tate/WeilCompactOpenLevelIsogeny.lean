import Langlands.AbelianScheme.Tate.WeilLevelIsogenyCoherence
import Langlands.AbelianScheme.Tate.WeilRationalFunctorialityProof
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevels

/-! # Natural isogeny comparisons of actual compact-open Weil level towers -/

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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
open GroupScheme.Tate (Index)
open Langlands.GroupScheme Langlands.Shimura Langlands.Shimura.PEL

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A B C : AbelianScheme S}
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
  (hC : HasDualScheme C) (geometryC : DualSchemeGeometry C hC)
  (MC : LineBundle ((relativeSpace C.X.hom).obj (dualScheme C hC)))
  (evaluationC : tensorObj (poincareFamily C hC).obj.carrier MC.obj ≅
    structureSheaf ((relativeSpace C.X.hom).obj (dualScheme C hC)))
  (lamC : C ⟶ dualAbelianSchemeFromEvaluation C hC geometryC preservation MC
    evaluationC stability composition unitCoherence associativity comparison symmetry)
  (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
  (additivityAB : DualSchemeMapAdditivity preservation stability A B hA hB)
  (additivityBC : DualSchemeMapAdditivity preservation stability B C hB hC)
  (additivityAC : DualSchemeMapAdditivity preservation stability A C hA hC)
  (additivityBA : DualSchemeMapAdditivity preservation stability B A hB hA)
  (additivityBB : DualSchemeMapAdditivity preservation stability B B hB hB)
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)
  (iC : D →ₐ[ℚ] Rationalization.End C)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})


section Full
variable (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]

local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "multipleBC" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC
local notation "isogenyAA" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA additivityAA lamA lamA compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iA V ψ s hs htor hu
local notation "isogenyAB" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s hs htor hu
local notation "isogenyBC" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC lamB lamC compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iB iC V ψ s hs htor hu
local notation "isogenyAC" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hC geometryA geometryC MA evaluationA MC evaluationC additivityAC lamA lamC compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iC V ψ s hs htor hu
local notation "isogenyBA" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA additivityBA lamB lamA compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iB iA V ψ s hs htor hu
local notation "isogenyComp" => weilAdelicLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB iC V ψ s hs htor hu
local notation "isogenyInverse" => weilAdelicLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s hs htor hu

local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "TowerA" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA h iA V ψ s hs htor hu
local notation "TowerB" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB h iB V ψ s hs htor hu
local notation "TowerC" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hC geometryC MC evaluationC lamC h iC V ψ s hs htor hu

/-- Actual rational-isogeny equivalences assemble naturally in compact-open level. -/
def weilAdelicCompactOpenLevelIsogeny (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    TowerA ≅ TowerB :=
  NatIso.ofComponents (fun K => (isogenyAB K.toSubgroup q e he hqe).toIso) (by
    intro K L f
    ext x
    exact weilAdelicLevelIsogeny_translate preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s hs htor hu
      q e he hqe f.element f.respects x)

local notation "towerIsogenyAA" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hA geometryA MA evaluationA lamA additivityAA compatibility h iA iA V ψ s hs htor hu

local notation "towerIsogenyAB" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility h iA iB V ψ s hs htor hu

local notation "towerIsogenyBC" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityBC compatibility h iB iC V ψ s hs htor hu

local notation "towerIsogenyAC" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hC geometryC MC evaluationC lamC additivityAC compatibility h iA iC V ψ s hs htor hu

local notation "towerIsogenyBA" => weilAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB lamB hA geometryA MA evaluationA lamA additivityBA compatibility h iB iA V ψ s hs htor hu

/-- The forward component is the published fixed-level isogeny equivalence. -/
@[simp] theorem weilAdelicCompactOpenLevelIsogeny_hom_app (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerA).obj K) :
    (towerIsogenyAB q e he hqe).hom.app K x = isogenyAB K.toSubgroup q e he hqe x := rfl

/-- The inverse component is the inverse published fixed-level equivalence. -/
@[simp] theorem weilAdelicCompactOpenLevelIsogeny_inv_app (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerB).obj K) :
    (towerIsogenyAB q e he hqe).inv.app K x =
      (isogenyAB K.toSubgroup q e he hqe).symm x := rfl

/-- Isogeny transport commutes with every compact-open transporter arrow. -/
theorem weilAdelicCompactOpenLevelIsogeny_arrow (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    {K L : LevelIndex} (f : K ⟶ L) (x : (TowerA).obj K) :
    (towerIsogenyAB q e he hqe).hom.app L ((TowerA).map f x) =
      (TowerB).map f ((towerIsogenyAB q e he hqe).hom.app K x) :=
  (towerIsogenyAB q e he hqe).hom.naturality_apply f x

/-- The identity rational isogeny induces the identity natural isomorphism. -/
@[simp] theorem weilAdelicCompactOpenLevelIsogeny_refl :
    towerIsogenyAA 1 (Iso.refl _) (rationalIntertwines_identity iA)
        (IsRationalDualPullbackMultiple.id preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
          additivityAA (Rationalization.ofHom lamA)) = Iso.refl (TowerA) := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x) (weilAdelicLevelIsogeny_refl preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA additivityAA compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA V ψ s hs htor hu K.toSubgroup)

/-- Direct composite transport uses the geometrically derived product multiplier. -/
def weilAdelicCompactOpenLevelIsogenyComp (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) : TowerA ≅ TowerC :=
  towerIsogenyAC (q * r) (e.trans f)
    (rationalIntertwines_comp iA iB iC e.hom f.hom he hf)
    (IsRationalDualPullbackMultiple.comp preservation composition unitCoherence associativity comparison symmetry stability
      hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      hC geometryC MC evaluationC additivityBC additivityAC (q : ℚ) (r : ℚ) e.hom f.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)
      (Rationalization.ofHom lamC) hqe hrf)

local notation "towerIsogenyComp" => weilAdelicCompactOpenLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility h iA iB iC V ψ s hs htor hu

/-- Direct composite transport equals successive natural isomorphisms. -/
theorem weilAdelicCompactOpenLevelIsogenyComp_eq_trans (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) :
    towerIsogenyComp q r e f he hf hqe hrf =
      towerIsogenyAB q e he hqe ≪≫ towerIsogenyBC r f hf hrf := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x)
    (weilAdelicLevelIsogenyComp_eq_trans preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB iC V ψ s hs htor hu K.toSubgroup q r e f he hf hqe hrf)

/-- Direct inverse-isogeny transport uses the derived reciprocal multiplier. -/
def weilAdelicCompactOpenLevelIsogenyInverse (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerB ≅ TowerA :=
  towerIsogenyBA q⁻¹ e.symm (rationalIntertwines_inverse iA iB e he)
    (IsRationalDualPullbackMultiple.inv preservation composition unitCoherence associativity comparison symmetry stability
      hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      additivityBA additivityBB q e (Rationalization.ofHom lamA)
      (Rationalization.ofHom lamB) hqe)

local notation "towerIsogenyInverse" => weilAdelicCompactOpenLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility h iA iB V ψ s hs htor hu

/-- Reversing the rational isogeny inverts the natural tower comparison. -/
theorem weilAdelicCompactOpenLevelIsogeny_symm (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    (towerIsogenyAB q e he hqe).symm = towerIsogenyInverse q e he hqe := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x)
    (weilAdelicLevelIsogeny_symm preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s hs htor hu K.toSubgroup q e he hqe)

end Full

section Away
variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
variable (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "multipleBC" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC
local notation "isogenyAA" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA additivityAA lamA lamA compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iA V ψ s hs htor hAway hu
local notation "isogenyAB" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s hs htor hAway hu
local notation "isogenyBC" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC lamB lamC compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iB iC V ψ s hs htor hAway hu
local notation "isogenyAC" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hC geometryA geometryC MA evaluationA MC evaluationC additivityAC lamA lamC compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iC V ψ s hs htor hAway hu
local notation "isogenyBA" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA additivityBA lamB lamA compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iB iA V ψ s hs htor hAway hu
local notation "isogenyComp" => weilPrimeToAdelicLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB iC V ψ s hs htor hAway hu
local notation "isogenyInverse" => weilPrimeToAdelicLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s hs htor hAway hu

local notation "LevelIndex" => PrimeToScalarExtensionLevel D V ψ m
local notation "TowerA" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lamA hAway iA V ψ s hs htor hu
local notation "TowerB" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hB geometryB MB evaluationB lamB hAway iB V ψ s hs htor hu
local notation "TowerC" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity comparison symmetry stability compatibility hC geometryC MC evaluationC lamC hAway iC V ψ s hs htor hu

/-- Actual rational-isogeny equivalences assemble naturally in compact-open level. -/
def weilPrimeToAdelicCompactOpenLevelIsogeny (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    TowerA ≅ TowerB :=
  NatIso.ofComponents (fun K => (isogenyAB K.toSubgroup q e he hqe).toIso) (by
    intro K L f
    ext x
    exact weilPrimeToAdelicLevelIsogeny_translate preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s hs htor hAway hu
      q e he hqe f.element f.respects x)

local notation "towerIsogenyAA" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hA geometryA MA evaluationA lamA additivityAA compatibility h iA iA V ψ s hs htor hAway hu

local notation "towerIsogenyAB" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB compatibility h iA iB V ψ s hs htor hAway hu

local notation "towerIsogenyBC" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityBC compatibility h iB iC V ψ s hs htor hAway hu

local notation "towerIsogenyAC" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hC geometryC MC evaluationC lamC additivityAC compatibility h iA iC V ψ s hs htor hAway hu

local notation "towerIsogenyBA" => weilPrimeToAdelicCompactOpenLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB lamB hA geometryA MA evaluationA lamA additivityBA compatibility h iB iA V ψ s hs htor hAway hu

/-- The forward component is the published fixed-level isogeny equivalence. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelIsogeny_hom_app (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerA).obj K) :
    (towerIsogenyAB q e he hqe).hom.app K x = isogenyAB K.toSubgroup q e he hqe x := rfl

/-- The inverse component is the inverse published fixed-level equivalence. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelIsogeny_inv_app (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (K : LevelIndex) (x : (TowerB).obj K) :
    (towerIsogenyAB q e he hqe).inv.app K x =
      (isogenyAB K.toSubgroup q e he hqe).symm x := rfl

/-- Isogeny transport commutes with every compact-open transporter arrow. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogeny_arrow (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    {K L : LevelIndex} (f : K ⟶ L) (x : (TowerA).obj K) :
    (towerIsogenyAB q e he hqe).hom.app L ((TowerA).map f x) =
      (TowerB).map f ((towerIsogenyAB q e he hqe).hom.app K x) :=
  (towerIsogenyAB q e he hqe).hom.naturality_apply f x

/-- The identity rational isogeny induces the identity natural isomorphism. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelIsogeny_refl :
    towerIsogenyAA 1 (Iso.refl _) (rationalIntertwines_identity iA)
        (IsRationalDualPullbackMultiple.id preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
          additivityAA (Rationalization.ofHom lamA)) = Iso.refl (TowerA) := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x) (weilPrimeToAdelicLevelIsogeny_refl preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA additivityAA compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA V ψ s hs htor hAway hu K.toSubgroup)

/-- Direct composite transport uses the geometrically derived product multiplier. -/
def weilPrimeToAdelicCompactOpenLevelIsogenyComp (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) : TowerA ≅ TowerC :=
  towerIsogenyAC (q * r) (e.trans f)
    (rationalIntertwines_comp iA iB iC e.hom f.hom he hf)
    (IsRationalDualPullbackMultiple.comp preservation composition unitCoherence associativity comparison symmetry stability
      hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      hC geometryC MC evaluationC additivityBC additivityAC (q : ℚ) (r : ℚ) e.hom f.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)
      (Rationalization.ofHom lamC) hqe hrf)

local notation "towerIsogenyComp" => weilPrimeToAdelicCompactOpenLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility h iA iB iC V ψ s hs htor hAway hu

/-- Direct composite transport equals successive natural isomorphisms. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogenyComp_eq_trans (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) :
    towerIsogenyComp q r e f he hf hqe hrf =
      towerIsogenyAB q e he hqe ≪≫ towerIsogenyBC r f hf hrf := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x)
    (weilPrimeToAdelicLevelIsogenyComp_eq_trans preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB iC V ψ s hs htor hAway hu K.toSubgroup q r e f he hf hqe hrf)

/-- Direct inverse-isogeny transport uses the derived reciprocal multiplier. -/
def weilPrimeToAdelicCompactOpenLevelIsogenyInverse (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : TowerB ≅ TowerA :=
  towerIsogenyBA q⁻¹ e.symm (rationalIntertwines_inverse iA iB e he)
    (IsRationalDualPullbackMultiple.inv preservation composition unitCoherence associativity comparison symmetry stability
      hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      additivityBA additivityBB q e (Rationalization.ofHom lamA)
      (Rationalization.ofHom lamB) hqe)

local notation "towerIsogenyInverse" => weilPrimeToAdelicCompactOpenLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility h iA iB V ψ s hs htor hAway hu

/-- Reversing the rational isogeny inverts the natural tower comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelIsogeny_symm (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    (towerIsogenyAB q e he hqe).symm = towerIsogenyInverse q e he hqe := by
  apply Iso.ext
  ext K x
  exact congrArg (fun e => e x)
    (weilPrimeToAdelicLevelIsogeny_symm preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility rationalWeilFunctoriality rationalWeilGeometricTransport h iA iB V ψ s hs htor hAway hu K.toSubgroup q e he hqe)

end Away

end Langlands.AbelianScheme.Tate

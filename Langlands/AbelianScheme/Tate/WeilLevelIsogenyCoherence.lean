import Langlands.AbelianScheme.Tate.WeilLevelIsogeny
import Langlands.AbelianScheme.Tate.WeilFrameIsogenyCoherence

/-! # Coherence of actual Weil-compatible fixed-level isogenies -/

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
open Langlands.GroupScheme Langlands.Shimura.PEL

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
  (functoriality : RationalWeilFunctorialityStatement.{u})
  (geometricCompatibility : RationalWeilGeometricTransportStatement.{u})
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

local notation "G" => ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ
local notation "LevelA" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ s hs htor hu
local notation "rightA" => weilAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lamA h iA V ψ s
local notation "leftA" => weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "commA" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelB" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ s hs htor hu
local notation "rightB" => weilAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB compatibility lamB h iB V ψ s
local notation "leftB" => weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "commB" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelC" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hC geometryC MC evaluationC lamC h iC V ψ s hs htor hu
local notation "rightC" => weilAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hC geometryC MC evaluationC compatibility lamC h iC V ψ s
local notation "leftC" => weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hC geometryC MC evaluationC lamC h iC V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "commC" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hC geometryC MC evaluationC lamC h iC V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "multipleBC" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC
local notation "isogenyAA" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA additivityAA lamA lamA compatibility functoriality geometricCompatibility h iA iA V ψ s hs htor hu
local notation "isogenyAB" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hu
local notation "isogenyBC" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC lamB lamC compatibility functoriality geometricCompatibility h iB iC V ψ s hs htor hu
local notation "isogenyAC" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hC geometryA geometryC MA evaluationA MC evaluationC additivityAC lamA lamC compatibility functoriality geometricCompatibility h iA iC V ψ s hs htor hu
local notation "isogenyBA" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA additivityBA lamB lamA compatibility functoriality geometricCompatibility h iB iA V ψ s hs htor hu

/-- The actual identity isogeny induces the identity on geometrically fixed orbits. -/
@[simp] theorem weilAdelicLevelIsogeny_refl (U : Subgroup G) :
    isogenyAA U 1 (Iso.refl _) (rationalIntertwines_identity iA)
        (IsRationalDualPullbackMultiple.id preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA additivityAA (Rationalization.ofHom lamA)) = Equiv.refl (LevelA U) := by
  let := rightA
  let := leftA
  let := commA
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilAdelicLevelIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.refl_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (weilAdelicFrameIsogeny_refl preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA additivityAA compatibility functoriality h iA V ψ s))

/-- Direct transport along a composite uses its derived product multiplier. -/
def weilAdelicLevelIsogenyComp (U : Subgroup G) (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) : LevelA U ≃ LevelC U :=
  isogenyAC U (q * r) (e.trans f)
    (rationalIntertwines_comp iA iB iC e.hom f.hom he hf)
    (IsRationalDualPullbackMultiple.comp preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      hC geometryC MC evaluationC additivityBC additivityAC (q : ℚ) (r : ℚ) e.hom f.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)
      (Rationalization.ofHom lamC) hqe hrf)

local notation "isogenyComp" => weilAdelicLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility functoriality geometricCompatibility h iA iB iC V ψ s hs htor hu

/-- Direct composite transport equals successive transport on fixed orbit classes. -/
theorem weilAdelicLevelIsogenyComp_eq_trans (U : Subgroup G) (q r : ℚˣ)
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
    isogenyComp U q r e f he hf hqe hrf =
      (isogenyAB U q e he hqe).trans (isogenyBC U r f hf hrf) := by
  let := rightA
  let := leftA
  let := commA
  let := rightB
  let := leftB
  let := commB
  let := rightC
  let := leftC
  let := commC
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilAdelicLevelIsogenyComp, weilAdelicLevelIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.trans_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (weilAdelicFrameIsogenyComp_eq_trans preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility functoriality h iA iB iC V ψ s q r e f he hf hqe hrf))

/-- Direct inverse-isogeny transport uses its derived reciprocal multiplier. -/
def weilAdelicLevelIsogenyInverse (U : Subgroup G) (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : LevelB U ≃ LevelA U :=
  isogenyBA U q⁻¹ e.symm (rationalIntertwines_inverse iA iB e he)
    (IsRationalDualPullbackMultiple.inv preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      additivityBA additivityBB q e (Rationalization.ofHom lamA)
      (Rationalization.ofHom lamB) hqe)

local notation "isogenyInverse" => weilAdelicLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hu

/-- Reversing the isogeny induces the inverse equivalence of fixed orbit sets. -/
theorem weilAdelicLevelIsogeny_symm (U : Subgroup G) (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    (isogenyAB U q e he hqe).symm = isogenyInverse U q e he hqe := by
  let := rightA
  let := leftA
  let := commA
  let := rightB
  let := leftB
  let := commB
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilAdelicLevelIsogenyInverse, weilAdelicLevelIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (weilAdelicFrameIsogeny_symm preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility functoriality h iA iB V ψ s q e he hqe))

end Full

section Away
variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
variable (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

local notation "G" => ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ
local notation "LevelA" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ s hs htor hu
local notation "rightA" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lamA h iA V ψ s hAway
local notation "leftA" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "commA" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelB" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ s hs htor hu
local notation "rightB" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB compatibility lamB h iB V ψ s hAway
local notation "leftB" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "commB" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelC" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hC geometryC MC evaluationC lamC hAway iC V ψ s hs htor hu
local notation "rightC" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hC geometryC MC evaluationC compatibility lamC h iC V ψ s hAway
local notation "leftC" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hC geometryC MC evaluationC lamC hAway iC V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "commC" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hC geometryC MC evaluationC lamC hAway iC V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "multipleBC" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC
local notation "isogenyAA" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA additivityAA lamA lamA compatibility functoriality geometricCompatibility h iA iA V ψ s hs htor hAway hu
local notation "isogenyAB" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hAway hu
local notation "isogenyBC" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC lamB lamC compatibility functoriality geometricCompatibility h iB iC V ψ s hs htor hAway hu
local notation "isogenyAC" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hC geometryA geometryC MA evaluationA MC evaluationC additivityAC lamA lamC compatibility functoriality geometricCompatibility h iA iC V ψ s hs htor hAway hu
local notation "isogenyBA" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA additivityBA lamB lamA compatibility functoriality geometricCompatibility h iB iA V ψ s hs htor hAway hu

/-- The actual identity isogeny induces the identity on geometrically fixed orbits. -/
@[simp] theorem weilPrimeToAdelicLevelIsogeny_refl (U : Subgroup G) :
    isogenyAA U 1 (Iso.refl _) (rationalIntertwines_identity iA)
        (IsRationalDualPullbackMultiple.id preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA additivityAA (Rationalization.ofHom lamA)) = Equiv.refl (LevelA U) := by
  let := rightA
  let := leftA
  let := commA
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilPrimeToAdelicLevelIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.refl_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (weilPrimeToAdelicFrameIsogeny_refl preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA additivityAA compatibility functoriality h iA V ψ s hAway))

/-- Direct transport along a composite uses its derived product multiplier. -/
def weilPrimeToAdelicLevelIsogenyComp (U : Subgroup G) (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) : LevelA U ≃ LevelC U :=
  isogenyAC U (q * r) (e.trans f)
    (rationalIntertwines_comp iA iB iC e.hom f.hom he hf)
    (IsRationalDualPullbackMultiple.comp preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      hC geometryC MC evaluationC additivityBC additivityAC (q : ℚ) (r : ℚ) e.hom f.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)
      (Rationalization.ofHom lamC) hqe hrf)

local notation "isogenyComp" => weilPrimeToAdelicLevelIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility functoriality geometricCompatibility h iA iB iC V ψ s hs htor hAway hu

/-- Direct composite transport equals successive transport on fixed orbit classes. -/
theorem weilPrimeToAdelicLevelIsogenyComp_eq_trans (U : Subgroup G) (q r : ℚˣ)
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
    isogenyComp U q r e f he hf hqe hrf =
      (isogenyAB U q e he hqe).trans (isogenyBC U r f hf hrf) := by
  let := rightA
  let := leftA
  let := commA
  let := rightB
  let := leftB
  let := commB
  let := rightC
  let := leftC
  let := commC
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilPrimeToAdelicLevelIsogenyComp, weilPrimeToAdelicLevelIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val, Equiv.trans_apply]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (weilPrimeToAdelicFrameIsogenyComp_eq_trans preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility functoriality h iA iB iC V ψ s hAway q r e f he hf hqe hrf))

/-- Direct inverse-isogeny transport uses its derived reciprocal multiplier. -/
def weilPrimeToAdelicLevelIsogenyInverse (U : Subgroup G) (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : LevelB U ≃ LevelA U :=
  isogenyBA U q⁻¹ e.symm (rationalIntertwines_inverse iA iB e he)
    (IsRationalDualPullbackMultiple.inv preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      additivityBA additivityBB q e (Rationalization.ofHom lamA)
      (Rationalization.ofHom lamB) hqe)

local notation "isogenyInverse" => weilPrimeToAdelicLevelIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hAway hu

/-- Reversing the isogeny induces the inverse equivalence of fixed orbit sets. -/
theorem weilPrimeToAdelicLevelIsogeny_symm (U : Subgroup G) (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    (isogenyAB U q e he hqe).symm = isogenyInverse U q e he hqe := by
  let := rightA
  let := leftA
  let := commA
  let := rightB
  let := leftB
  let := commB
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [weilPrimeToAdelicLevelIsogenyInverse, weilPrimeToAdelicLevelIsogeny, InvariantOrbit.equiv, Equiv.symm,
    Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (congrArg (fun e => e eta) (weilPrimeToAdelicFrameIsogeny_symm preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility functoriality h iA iB V ψ s hAway q e he hqe))

end Away

end Langlands.AbelianScheme.Tate

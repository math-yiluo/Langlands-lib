import Langlands.AbelianScheme.Tate.WeilFrameIsogeny
import Langlands.AbelianScheme.Tate.WeilAdelicLevelTransport
import Langlands.AbelianScheme.Tate.WeilPrimeToAdelicLevelTransport

/-! # Rational-isogeny transport of actual Weil-compatible level orbits -/

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
open Langlands.GroupScheme Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)
  (lamA : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (lamB : B ⟶ dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
    evaluationB stability composition unitCoherence associativity comparison symmetry)
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (functoriality : RationalWeilFunctorialityStatement.{u})

  (geometricCompatibility : RationalWeilGeometricTransportStatement.{u})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})

local notation "multiple" => IsRationalDualPullbackMultiple preservation composition
  unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
  MA evaluationA MB evaluationB additivity


section Full
variable (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]

local notation "G" => ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ
local notation "frameIsogeny" => weilAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality h iA iB V ψ
local notation "isogenyRight" => weilAdelicFrameIsogeny_right preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality h iA iB V ψ

local notation "FrameA" => WeilAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lamA h iA V ψ
local notation "rightA" => weilAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lamA h iA V ψ
local notation "leftA" => weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ
local notation "commA" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ
local notation "LevelA" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ
local notation "translateA" => weilAdelicLevelTranslate preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ htor hu
local notation "forgetA" => weilAdelicLevelForget preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ htor hu
local notation "frameTransportA" => weilAdelicFrameTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ htor hu
local notation "levelTransportA" => weilAdelicLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA h iA V ψ htor hu

local notation "FrameB" => WeilAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB compatibility lamB h iB V ψ
local notation "rightB" => weilAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB compatibility lamB h iB V ψ
local notation "leftB" => weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ
local notation "commB" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ
local notation "LevelB" => WeilAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ
local notation "translateB" => weilAdelicLevelTranslate preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ htor hu
local notation "forgetB" => weilAdelicLevelForget preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ htor hu
local notation "frameTransportB" => weilAdelicFrameTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ htor hu
local notation "levelTransportB" => weilAdelicLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB h iB V ψ htor hu

/-- The restricted isogeny map intertwines actual geometric monodromy. -/
theorem weilAdelicFrameIsogeny_monodromy (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (gMon : FundamentalGroup s hs) (eta : FrameA s) :
    letI := leftA s hs htor hu (hμfin := hμfin) (hμet := hμet)
    letI := leftB s hs htor hu (hμfin := hμfin) (hμet := hμet)
    frameIsogeny s q e he hf (gMon • eta) = gMon • frameIsogeny s q e he hf eta := by
  apply Subtype.ext
  ext x
  exact (rationalMonodromy_iso s hs htor (fun _ => True) hu e gMon (eta.1 x)).symm


/-- Postcomposition transports geometrically fixed orbits of actual compatible frames. -/
def weilAdelicLevelIsogeny (U : Subgroup G) (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    LevelA s hs htor hu U ≃ LevelB s hs htor hu U := by
  letI := rightA s
  letI := leftA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := rightB s
  letI := leftB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (frameIsogeny s q e he hf) (isogenyRight s q e he hf)
    (weilAdelicFrameIsogeny_monodromy preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hu q e he hf)

local notation "levelIsogeny" => weilAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ

/-- Right Hecke translation commutes with the isogeny map. -/
theorem weilAdelicLevelIsogeny_translate {U U' : Subgroup G} (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (x : LevelA s hs htor hu U) :
    levelIsogeny s hs htor hu U' q e he hf (translateA g hg x) =
      translateB g hg (levelIsogeny s hs htor hu U q e he hf x) := by
  let := rightA s
  let := leftA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := rightB s
  let := leftB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.map_translate (MulEquiv.refl (FundamentalGroup s hs))
    (frameIsogeny s q e he hf) (isogenyRight s q e he hf)
    (weilAdelicFrameIsogeny_monodromy preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hu q e he hf) g hg x

/-- Isogeny transport commutes with forgetting a finer level. -/
theorem weilAdelicLevelIsogeny_forget {U U' : Subgroup G} (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hU : U ≤ U') (x : LevelA s hs htor hu U) :
    levelIsogeny s hs htor hu U' q e he hf (forgetA hU x) =
      forgetB hU (levelIsogeny s hs htor hu U q e he hf x) :=
  weilAdelicLevelIsogeny_translate preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hu q e he hf 1 _ x

variable {Ω' : Type u} [Field Ω'] {t : Spec (.of Ω') ⟶ S}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

/-- The frame isogeny map commutes with actual geometric path transport. -/
theorem weilAdelicFrameIsogeny_transport (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : FrameA s) :
    frameTransportB p (frameIsogeny s q e he hf eta) =
      frameIsogeny t q e he hf (frameTransportA p eta) := by
  apply Subtype.ext
  ext x
  exact rationalTransport_iso htor (fun _ => True) hu e p (eta.1 x)

/-- The isogeny/path square on fixed compatible level orbits. -/
theorem weilAdelicLevelIsogeny_transport (U : Subgroup G) (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : LevelA s hs htor hu U) :
    levelTransportB U p (levelIsogeny s hs htor hu U q e he hf x) =
      levelIsogeny t ht htor hu U q e he hf (levelTransportA U p x) := by
  let := rightA s
  let := leftA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := rightB s
  let := leftB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := rightA t
  let := leftA t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commA t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := rightB t
  let := leftB t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commB t ht htor hu (hμfin := hμfin) (hμet := hμet)
  apply Subtype.ext
  simp only [weilAdelicLevelIsogeny, weilAdelicLevelTransport, InvariantOrbit.equiv,
    Equiv.symm, Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilAdelicFrameIsogeny_transport preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hu q e he hf p eta)

end Full

section Away
variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
variable (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

local notation "G" => ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ
local notation "frameIsogeny" => weilPrimeToAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality h iA iB V ψ
local notation "isogenyRight" => weilPrimeToAdelicFrameIsogeny_right preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality h iA iB V ψ

local notation "FrameA" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lamA h iA V ψ
local notation "rightA" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lamA h iA V ψ
local notation "leftA" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ
local notation "commA" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ
local notation "LevelA" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ
local notation "translateA" => weilPrimeToAdelicLevelTranslate preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ htor hu
local notation "forgetA" => weilPrimeToAdelicLevelForget preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ htor hu
local notation "frameTransportA" => weilPrimeToAdelicFrameTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ htor hu
local notation "levelTransportA" => weilPrimeToAdelicLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hA geometryA MA evaluationA lamA hAway iA V ψ htor hu

local notation "FrameB" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB compatibility lamB h iB V ψ
local notation "rightB" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB compatibility lamB h iB V ψ
local notation "leftB" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ
local notation "commB" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ
local notation "LevelB" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ
local notation "translateB" => weilPrimeToAdelicLevelTranslate preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ htor hu
local notation "forgetB" => weilPrimeToAdelicLevelForget preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ htor hu
local notation "frameTransportB" => weilPrimeToAdelicFrameTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ htor hu
local notation "levelTransportB" => weilPrimeToAdelicLevelTransport preservation composition unitCoherence associativity comparison symmetry stability compatibility geometricCompatibility hB geometryB MB evaluationB lamB hAway iB V ψ htor hu

/-- The restricted isogeny map intertwines actual geometric monodromy. -/
theorem weilPrimeToAdelicFrameIsogeny_monodromy (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (gMon : FundamentalGroup s hs) (eta : FrameA s hAway) :
    letI := leftA s hs htor hu (hμfin := hμfin) (hμet := hμet)
    letI := leftB s hs htor hu (hμfin := hμfin) (hμet := hμet)
    frameIsogeny s hAway q e he hf (gMon • eta) = gMon • frameIsogeny s hAway q e he hf eta := by
  apply Subtype.ext
  ext x
  exact (rationalMonodromy_iso s hs htor (fun n => Nat.Coprime n m) hu e gMon (eta.1 x)).symm


/-- Postcomposition transports geometrically fixed orbits of actual compatible frames. -/
def weilPrimeToAdelicLevelIsogeny (U : Subgroup G) (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    LevelA s hs htor hu U ≃ LevelB s hs htor hu U := by
  letI := rightA s hAway
  letI := leftA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := rightB s hAway
  letI := leftB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  letI := commB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (frameIsogeny s hAway q e he hf) (isogenyRight s hAway q e he hf)
    (weilPrimeToAdelicFrameIsogeny_monodromy preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hAway hu q e he hf)

local notation "levelIsogeny" => weilPrimeToAdelicLevelIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ

/-- Right Hecke translation commutes with the isogeny map. -/
theorem weilPrimeToAdelicLevelIsogeny_translate {U U' : Subgroup G} (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (x : LevelA s hs htor hu U) :
    levelIsogeny s hs htor hAway hu U' q e he hf (translateA g hg x) =
      translateB g hg (levelIsogeny s hs htor hAway hu U q e he hf x) := by
  let := rightA s hAway
  let := leftA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := rightB s hAway
  let := leftB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  exact InvariantOrbit.map_translate (MulEquiv.refl (FundamentalGroup s hs))
    (frameIsogeny s hAway q e he hf) (isogenyRight s hAway q e he hf)
    (weilPrimeToAdelicFrameIsogeny_monodromy preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hAway hu q e he hf) g hg x

/-- Isogeny transport commutes with forgetting a finer level. -/
theorem weilPrimeToAdelicLevelIsogeny_forget {U U' : Subgroup G} (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hU : U ≤ U') (x : LevelA s hs htor hu U) :
    levelIsogeny s hs htor hAway hu U' q e he hf (forgetA hU x) =
      forgetB hU (levelIsogeny s hs htor hAway hu U q e he hf x) :=
  weilPrimeToAdelicLevelIsogeny_translate preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hAway hu q e he hf 1 _ x

variable {Ω' : Type u} [Field Ω'] {t : Spec (.of Ω') ⟶ S}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}

/-- The frame isogeny map commutes with actual geometric path transport. -/
theorem weilPrimeToAdelicFrameIsogeny_transport (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : FrameA s hAway) :
    frameTransportB p (frameIsogeny s hAway q e he hf eta) =
      frameIsogeny t hAway q e he hf (frameTransportA p eta) := by
  apply Subtype.ext
  ext x
  exact rationalTransport_iso htor (fun n => Nat.Coprime n m) hu e p (eta.1 x)

/-- The isogeny/path square on fixed compatible level orbits. -/
theorem weilPrimeToAdelicLevelIsogeny_transport (U : Subgroup G) (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : multiple (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : LevelA s hs htor hu U) :
    levelTransportB U p (levelIsogeny s hs htor hAway hu U q e he hf x) =
      levelIsogeny t ht htor hAway hu U q e he hf (levelTransportA U p x) := by
  let := rightA s hAway
  let := leftA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commA s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := rightB s hAway
  let := leftB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := commB s hs htor hu (hμfin := hμfin) (hμet := hμet)
  let := rightA t hAway
  let := leftA t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commA t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := rightB t hAway
  let := leftB t ht htor hu (hμfin := hμfin) (hμet := hμet)
  let := commB t ht htor hu (hμfin := hμfin) (hμet := hμet)
  apply Subtype.ext
  simp only [weilPrimeToAdelicLevelIsogeny, weilPrimeToAdelicLevelTransport, InvariantOrbit.equiv,
    Equiv.symm, Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction x.1 using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (weilPrimeToAdelicFrameIsogeny_transport preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivity lamA lamB compatibility functoriality geometricCompatibility h iA iB V ψ s hs htor hAway hu q e he hf p eta)

end Away

end Langlands.AbelianScheme.Tate

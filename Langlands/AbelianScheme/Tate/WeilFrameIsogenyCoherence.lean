import Langlands.AbelianScheme.Tate.WeilFrameIsogeny
import Langlands.AbelianScheme.Tate.WeilHom0PullbackCoherence

/-! # Coherence of actual Weil-compatible frame isogenies -/

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
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D]
  (iA : D →ₐ[ℚ] Rationalization.End A) (iB : D →ₐ[ℚ] Rationalization.End B)
  (iC : D →ₐ[ℚ] Rationalization.End C)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)

section Full

local notation "FrameA" => WeilAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lamA h iA V ψ s
local notation "FrameB" => WeilAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB compatibility lamB h iB V ψ s
local notation "FrameC" => WeilAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hC geometryC MC evaluationC compatibility lamC h iC V ψ s
local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "multipleBC" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC
local notation "isogenyAA" => weilAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA additivityAA lamA lamA compatibility functoriality h iA iA V ψ s
local notation "isogenyAB" => weilAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility functoriality h iA iB V ψ s
local notation "isogenyBC" => weilAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC lamB lamC compatibility functoriality h iB iC V ψ s
local notation "isogenyAC" => weilAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hC geometryA geometryC MA evaluationA MC evaluationC additivityAC lamA lamC compatibility functoriality h iA iC V ψ s
local notation "isogenyBA" => weilAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA additivityBA lamB lamA compatibility functoriality h iB iA V ψ s

/-- The actual rational identity acts identically on compatible frames. -/
@[simp] theorem weilAdelicFrameIsogeny_refl :
    isogenyAA 1 (Iso.refl _) (rationalIntertwines_identity iA)
        (IsRationalDualPullbackMultiple.id preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA additivityAA (Rationalization.ofHom lamA)) = Equiv.refl FrameA := by
  apply Equiv.ext
  intro eta
  apply Subtype.ext
  ext x
  exact LinearMap.congr_fun (rationalHomMap_identity (Over.mk s) (fun _ => True)) (eta.1 x)

/-- Direct compatible-frame transport for a composite, using the derived
product of its actual geometric multipliers. -/
def weilAdelicFrameIsogenyComp (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) : FrameA ≃ FrameC :=
  isogenyAC (q * r) (e.trans f)
    (rationalIntertwines_comp iA iB iC e.hom f.hom he hf)
    (IsRationalDualPullbackMultiple.comp preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      hC geometryC MC evaluationC additivityBC additivityAC (q : ℚ) (r : ℚ) e.hom f.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)
      (Rationalization.ofHom lamC) hqe hrf)

local notation "isogenyComp" => weilAdelicFrameIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility functoriality h iA iB iC V ψ s

/-- The direct composite agrees with successive compatible-frame transport. -/
theorem weilAdelicFrameIsogenyComp_eq_trans (q r : ℚˣ)
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
    isogenyComp q r e f he hf hqe hrf =
      (isogenyAB q e he hqe).trans (isogenyBC r f hf hrf) := by
  apply Equiv.ext
  intro eta
  apply Subtype.ext
  ext x
  exact LinearMap.congr_fun
    (rationalHomMap_comp (Over.mk s) (fun _ => True) e.hom f.hom) (eta.1 x)

/-- Transport for the inverse rational isogeny, with its derived inverse
geometric multiplier. -/
def weilAdelicFrameIsogenyInverse (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : FrameB ≃ FrameA :=
  isogenyBA q⁻¹ e.symm (rationalIntertwines_inverse iA iB e he)
    (IsRationalDualPullbackMultiple.inv preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      additivityBA additivityBB q e (Rationalization.ofHom lamA)
      (Rationalization.ofHom lamB) hqe)

local notation "isogenyInverse" => weilAdelicFrameIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility functoriality h iA iB V ψ s

/-- Reversing the rational isogeny gives the inverse frame equivalence. -/
theorem weilAdelicFrameIsogeny_symm (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    (isogenyAB q e he hqe).symm = isogenyInverse q e he hqe := by
  apply Equiv.ext
  intro eta
  apply Subtype.ext
  ext x
  rfl

end Full

section Away
variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

local notation "FrameA" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lamA h iA V ψ s hAway
local notation "FrameB" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB compatibility lamB h iB V ψ s hAway
local notation "FrameC" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity comparison symmetry stability hC geometryC MC evaluationC compatibility lamC h iC V ψ s hAway
local notation "multipleAB" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
local notation "multipleBC" => IsRationalDualPullbackMultiple preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC
local notation "isogenyAA" => weilPrimeToAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA additivityAA lamA lamA compatibility functoriality h iA iA V ψ s hAway
local notation "isogenyAB" => weilPrimeToAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB lamA lamB compatibility functoriality h iA iB V ψ s hAway
local notation "isogenyBC" => weilPrimeToAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC additivityBC lamB lamC compatibility functoriality h iB iC V ψ s hAway
local notation "isogenyAC" => weilPrimeToAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hA hC geometryA geometryC MA evaluationA MC evaluationC additivityAC lamA lamC compatibility functoriality h iA iC V ψ s hAway
local notation "isogenyBA" => weilPrimeToAdelicFrameIsogeny preservation composition unitCoherence associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA additivityBA lamB lamA compatibility functoriality h iB iA V ψ s hAway

/-- The actual rational identity acts identically on compatible frames. -/
@[simp] theorem weilPrimeToAdelicFrameIsogeny_refl :
    isogenyAA 1 (Iso.refl _) (rationalIntertwines_identity iA)
        (IsRationalDualPullbackMultiple.id preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA additivityAA (Rationalization.ofHom lamA)) = Equiv.refl FrameA := by
  apply Equiv.ext
  intro eta
  apply Subtype.ext
  ext x
  exact LinearMap.congr_fun (rationalHomMap_identity (Over.mk s) (fun n => Nat.Coprime n m)) (eta.1 x)

/-- Direct compatible-frame transport for a composite, using the derived
product of its actual geometric multipliers. -/
def weilPrimeToAdelicFrameIsogenyComp (q r : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hf : ∀ d, Rationalization.comp B B C (iB d) f.hom =
      Rationalization.comp B C C f.hom (iC d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB))
    (hrf : multipleBC (r : ℚ) f.hom
      (Rationalization.ofHom lamB) (Rationalization.ofHom lamC)) : FrameA ≃ FrameC :=
  isogenyAC (q * r) (e.trans f)
    (rationalIntertwines_comp iA iB iC e.hom f.hom he hf)
    (IsRationalDualPullbackMultiple.comp preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      hC geometryC MC evaluationC additivityBC additivityAC (q : ℚ) (r : ℚ) e.hom f.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)
      (Rationalization.ofHom lamC) hqe hrf)

local notation "isogenyComp" => weilPrimeToAdelicFrameIsogenyComp preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB hC geometryC MC evaluationC lamC additivityAB additivityBC additivityAC compatibility functoriality h iA iB iC V ψ s hAway

/-- The direct composite agrees with successive compatible-frame transport. -/
theorem weilPrimeToAdelicFrameIsogenyComp_eq_trans (q r : ℚˣ)
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
    isogenyComp q r e f he hf hqe hrf =
      (isogenyAB q e he hqe).trans (isogenyBC r f hf hrf) := by
  apply Equiv.ext
  intro eta
  apply Subtype.ext
  ext x
  exact LinearMap.congr_fun
    (rationalHomMap_comp (Over.mk s) (fun n => Nat.Coprime n m) e.hom f.hom) (eta.1 x)

/-- Transport for the inverse rational isogeny, with its derived inverse
geometric multiplier. -/
def weilPrimeToAdelicFrameIsogenyInverse (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) : FrameB ≃ FrameA :=
  isogenyBA q⁻¹ e.symm (rationalIntertwines_inverse iA iB e he)
    (IsRationalDualPullbackMultiple.inv preservation composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB additivityAB
      additivityBA additivityBB q e (Rationalization.ofHom lamA)
      (Rationalization.ofHom lamB) hqe)

local notation "isogenyInverse" => weilPrimeToAdelicFrameIsogenyInverse preservation composition unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA lamA hB geometryB MB evaluationB lamB additivityAB additivityBA additivityBB compatibility functoriality h iA iB V ψ s hAway

/-- Reversing the rational isogeny gives the inverse frame equivalence. -/
theorem weilPrimeToAdelicFrameIsogeny_symm (q : ℚˣ) (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (iA d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (hqe : multipleAB (q : ℚ) e.hom
      (Rationalization.ofHom lamA) (Rationalization.ofHom lamB)) :
    (isogenyAB q e he hqe).symm = isogenyInverse q e he hqe := by
  apply Equiv.ext
  intro eta
  apply Subtype.ext
  ext x
  rfl

end Away

end Langlands.AbelianScheme.Tate

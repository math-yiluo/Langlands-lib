import Langlands.Automorphic.TwoBlockConstantTermSmooth
import Langlands.Automorphic.FullOperatorRealization
import Langlands.Global.ArchimedeanOrbitDerivativeInterchange

/-! # Preservation of cuspidality under the actual enveloping action -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance cuspPreservationRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspPreservationContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspPreservationFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspPreservationStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspPreservationFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)]

private theorem isCuspidal_realGenerator (X : RealLieAlgebra F n)
    {f : FiniteSmoothRationalFunctions F n} (hf : IsCuspidal F n f.val) :
    IsCuspidal F n
      (finiteSmoothEnvelopingAction F n (envelopingGenerator F n (complexify F n X)) f).val := by
  intro a b h ha hb g
  let d := AdelicGL.finite F n g
  have hz : smoothConstantTermSlice F n h f d = 0 := by
    apply Subtype.ext
    funext x
    exact hf a b h ha hb (AdelicGL.pair F n x d)
  have hd := smoothDifferential_smoothConstantTermSlice F n h f d X (AdelicGL.infinite F n g)
  rw [hz, map_zero, AdelicGL.pair_projections] at hd
  exact hd.symm

/-- Every actual enveloping derivative of a finite-smooth cuspidal function is cuspidal. -/
theorem isCuspidal_finiteSmoothEnvelopingAction (a : EnvelopingAlgebra F n) :
    ∀ f : FiniteSmoothRationalFunctions F n, IsCuspidal F n f.val →
      IsCuspidal F n (finiteSmoothEnvelopingAction F n a f).val := by
  let P : Submodule ℂ (ContinuousRationalFunctions F n) := cuspidalSubrepresentation.toSubmodule
  induction a using enveloping_real_left_induction with
  | h1 => intro f hf; simpa only [map_one, Module.End.one_apply] using hf
  | hadd a b ha hb =>
    intro f hf
    simp only [map_add, LinearMap.add_apply]
    exact P.add_mem (ha f hf) (hb f hf)
  | hsmul z a ha =>
    intro f hf
    simp only [map_smul, LinearMap.smul_apply]
    exact P.smul_mem z (ha f hf)
  | hgen X a ha =>
    intro f hf
    simp only [map_mul, Module.End.mul_apply]
    exact isCuspidal_realGenerator X (ha f hf)

variable (F n) in
/-- The operator realization of all cuspidal forms inside the stable automorphic carrier. -/
def cuspidalOperatorRealization : OperatorRealization F n where
  toSubmodule := (cuspidalSubrepresentation (K := F) (n := n)).toSubmodule.comap
    ((finiteSmoothRationalSubrepresentation F n).toSubmodule.subtype.comp
      (automorphicOperatorCore F n).toSubmodule.subtype)
  apply_mem_toSubmodule a {f} hf := by
    let P := (cuspidalSubrepresentation (K := F) (n := n)).toSubmodule.comap
      (finiteSmoothRationalSubrepresentation F n).toSubmodule.subtype
    have hP := (operator_invariant_iff F n P).mpr
      ⟨fun d _ hx => cuspidalSubrepresentation.apply_mem_toSubmodule (AdelicGL.ofFinite F n d) hx,
        fun k _ hx => cuspidalSubrepresentation.apply_mem_toSubmodule
          (AdelicGL.ofInfinite F n k.val) hx,
        fun b q hq => isCuspidal_finiteSmoothEnvelopingAction b q hq⟩
    exact hP a f.val hf

@[simp]
theorem mem_cuspidalOperatorRealization (f : StableAutomorphicFunctions F n) :
    f ∈ cuspidalOperatorRealization F n ↔ IsCuspidal F n f.val.val := Iff.rfl

theorem cuspidalOperatorRealization_isCuspidal :
    (cuspidalOperatorRealization F n).IsCuspidal :=
  (cuspidalOperatorRealization F n).isCuspidal_iff.mpr fun f => f.property

end Langlands.Automorphic

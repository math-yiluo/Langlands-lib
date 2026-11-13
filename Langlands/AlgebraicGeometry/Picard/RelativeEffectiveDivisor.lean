import Langlands.AlgebraicGeometry.Picard.StructureKernelModule
import Langlands.AlgebraicGeometry.Picard.LineBundleDualSectionEvaluation
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Relative effective Cartier divisors as actual closed subschemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- An actual ideal defines an effective Cartier divisor when its kernel module
is locally free of rank one. -/
def IsEffectiveCartierIdeal {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  IsLocallyFreeRankOne (StructureKernelModule.kernelModule I.subschemeι)

/-- Effective Cartier divisors, identified by their actual ideal sheaves. -/
abbrev EffectiveCartierDivisor (X : Scheme.{u}) :=
  {I : X.IdealSheafData // IsEffectiveCartierIdeal I}

namespace EffectiveCartierDivisor

variable {X : Scheme.{u}}

/-- The actual ideal defining the closed subscheme. -/
abbrev ideal (D : EffectiveCartierDivisor X) : X.IdealSheafData := D.val

/-- The closed subscheme defined by the divisor ideal. -/
abbrev subscheme (D : EffectiveCartierDivisor X) : Scheme.{u} := D.ideal.subscheme

/-- The actual closed immersion of the divisor into the ambient scheme. -/
abbrev ι (D : EffectiveCartierDivisor X) : D.subscheme ⟶ X := D.ideal.subschemeι

@[ext]
lemma ext (D E : EffectiveCartierDivisor X) (h : D.ideal = E.ideal) : D = E :=
  Subtype.ext h

/-- The invertible ideal sheaf `O(-D)`, with its prescribed actual kernel module. -/
def idealLineBundle (D : EffectiveCartierDivisor X) : LineBundle X :=
  ⟨StructureKernelModule.kernelModule D.ι, D.property⟩

/-- The divisor line bundle `O(D)` is the internal dual of its ideal sheaf. -/
def lineBundle (D : EffectiveCartierDivisor X) : LineBundle X :=
  D.idealLineBundle.dual

/-- The canonical inclusion of the divisor ideal into the structure sheaf. -/
def idealInclusion (D : EffectiveCartierDivisor X) :
    D.idealLineBundle.obj ⟶ Langlands.SchemeModule.structureModule X :=
  StructureKernelModule.kernelModuleι D.ι

/-- The divisor ideal really is a submodule of the structure sheaf. -/
instance (D : EffectiveCartierDivisor X) : Mono D.idealInclusion :=
  mono_of_isLimit_fork (StructureKernelModule.kernelModuleIsKernel D.ι)

/-- The ideal sheaf is quasi-coherent, also without noetherian hypotheses. -/
lemma idealLineBundle_isQuasicoherent (D : EffectiveCartierDivisor X) :
    D.idealLineBundle.obj.IsQuasicoherent :=
  StructureKernelModule.kernelModule_isQuasicoherent D.ι

/-- The canonical global section of `O(D)` is the ideal inclusion, viewed in
the internal Hom sheaf. -/
def canonicalSection (D : EffectiveCartierDivisor X) : D.lineBundle.sections :=
  D.idealInclusion.over ⊤

/-- Evaluation of the canonical section is precisely the actual ideal inclusion. -/
@[simp]
lemma canonicalSection_eval (D : EffectiveCartierDivisor X)
    (a : Γ(D.idealLineBundle.obj, (⊤ : X.Opens))) :
    Langlands.Scheme.Modules.dualEval D.idealLineBundle.obj ⊤ D.canonicalSection a =
      D.idealInclusion.app ⊤ a := rfl

end EffectiveCartierDivisor

/-- A relative effective Cartier divisor has invertible actual ideal and its
closed subscheme is flat over the specified base. -/
def IsRelativeEffectiveCartierIdeal {S X : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) : Prop :=
  IsEffectiveCartierIdeal I ∧ Flat (I.subschemeι ≫ f)

/-- Relative effective Cartier divisors, with equality given by their actual
ideal sheaves. Base-change stability is a separate mathematical assertion. -/
abbrev RelativeEffectiveDivisor {S X : Scheme.{u}} (f : X ⟶ S) :=
  {I : X.IdealSheafData // IsRelativeEffectiveCartierIdeal f I}

namespace RelativeEffectiveDivisor

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The actual ideal of a relative effective divisor. -/
abbrev ideal (D : RelativeEffectiveDivisor f) : X.IdealSheafData := D.val

/-- Forget flatness over the base, retaining the actual effective divisor. -/
def toEffectiveCartierDivisor (D : RelativeEffectiveDivisor f) :
    EffectiveCartierDivisor X := ⟨D.ideal, D.property.1⟩

/-- The closed subscheme underlying a relative divisor. -/
abbrev subscheme (D : RelativeEffectiveDivisor f) : Scheme.{u} := D.ideal.subscheme

/-- The closed immersion of a relative divisor into its ambient scheme. -/
abbrev ι (D : RelativeEffectiveDivisor f) : D.subscheme ⟶ X := D.ideal.subschemeι

/-- The structural morphism of the divisor to the base. -/
abbrev toBase (D : RelativeEffectiveDivisor f) : D.subscheme ⟶ S := D.ι ≫ f

instance (D : RelativeEffectiveDivisor f) : Flat D.toBase := D.property.2

@[ext]
lemma ext (D E : RelativeEffectiveDivisor f) (h : D.ideal = E.ideal) : D = E :=
  Subtype.ext h

end RelativeEffectiveDivisor

end Langlands.AlgebraicGeometry.Picard

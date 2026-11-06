import Langlands.Shimura.PEL.HarrisTaylorCMConjugationSchemes
import Langlands.Shimura.LevelColimit
import Mathlib.CategoryTheory.Filtered.Final

/-! # Ordered sufficiently small levels for the actual CM tower -/

noncomputable section

universe u

open CategoryTheory

set_option autoImplicit false

namespace Langlands.Shimura.AlgebraInvolution

variable {B : Type u} [Ring B] [Algebra ℚ B]
  (σ : AlgebraInvolution ℚ B)

local notation "G" => σ.FiniteAdelicPointsᵐᵒᵖ

/-- Sufficiently small levels with only the inclusion order, for shrinking-level
limits and colimits. Transporter arrows belong to SmallLevelCategory instead. -/
abbrev OrderedSmallLevel :=
  {U : CompactOpenLevel.Ordered G // σ.LevelSufficientlySmall U}

/-- Forget the smallness certificate, retaining the ordered compact open level. -/
def orderedSmallLevelForget : σ.OrderedSmallLevel ⥤ CompactOpenLevel.Ordered G where
  obj U := U.val
  map f := homOfLE (leOfHom f)

/-- Include the ordered small levels in the genuine small transporter category. -/
def orderedSmallLevelToSmallLevelCategory : σ.OrderedSmallLevel ⥤ σ.SmallLevelCategory where
  obj U := ⟨U.val, U.property⟩
  map f := ObjectProperty.homMk (CompactOpenLevel.inclusion (leOfHom f))
  map_id U := by
    apply ObjectProperty.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply CompactOpenLevel.Arrow.ext
    exact (mul_one 1).symm

/-- Both routes to the whole transporter category preserve the actual inclusion
arrow, whose translating element is one. -/
theorem orderedSmallLevelToSmallLevelCategory_comp :
    σ.orderedSmallLevelToSmallLevelCategory ⋙ ObjectProperty.ι σ.LevelSufficientlySmall =
      σ.orderedSmallLevelForget ⋙ CompactOpenLevel.inclusionFunctor := rfl

/-- Ordered small levels are nonempty exactly when small transporter levels are. -/
theorem orderedSmallLevel_nonempty_iff :
    Nonempty σ.OrderedSmallLevel ↔ Nonempty σ.SmallLevelCategory := by
  constructor
  · rintro ⟨U⟩
    exact ⟨⟨U.val, U.property⟩⟩
  · rintro ⟨U⟩
    exact ⟨⟨U.obj, U.property⟩⟩

instance [Nonempty σ.SmallLevelCategory] : Nonempty σ.OrderedSmallLevel :=
  σ.orderedSmallLevel_nonempty_iff.mpr inferInstance

variable [Module.Finite ℚ B]

/-- Intersect a small level with any compact open level. Smallness is inherited
from the first factor, so no smallness premise is needed on the second. -/
def orderedSmallLevelRefinement (U : σ.OrderedSmallLevel) (V : CompactOpenLevel G) :
    σ.OrderedSmallLevel :=
  ⟨CompactOpenLevel.inf U.val V, U.property.mono (fun _ hx => hx.1)⟩

/-- The refinement forgets to the actual intersection of compact open levels. -/
@[simp] theorem orderedSmallLevelRefinement_val
    (U : σ.OrderedSmallLevel) (V : CompactOpenLevel G) :
    (σ.orderedSmallLevelRefinement U V).val = CompactOpenLevel.inf U.val V := rfl

/-- Every pair of small levels has an actual common smaller small level. -/
instance : IsDirected σ.OrderedSmallLevel (· ≥ ·) :=
  ⟨fun U V => ⟨σ.orderedSmallLevelRefinement U V.val,
    fun _ hx => hx.1, fun _ hx => hx.2⟩⟩

/-- The ordered small levels are cofiltered provided a small level exists. -/
instance [Nonempty σ.SmallLevelCategory] : IsCofiltered σ.OrderedSmallLevel :=
  isCofiltered_of_directed_ge_nonempty _

/-- Every compact open level admits a sufficiently small refinement whenever
one small level exists. This constructs the refinement by intersection. -/
theorem exists_orderedSmallLevel_le [Nonempty σ.SmallLevelCategory]
    (V : CompactOpenLevel G) :
    ∃ U : σ.OrderedSmallLevel, U.val.subgroup ≤ V.subgroup := by
  obtain ⟨U⟩ := (inferInstance : Nonempty σ.OrderedSmallLevel)
  exact ⟨σ.orderedSmallLevelRefinement U V, fun _ hx => hx.2⟩

/-- The ordered small-level inclusion is initial under the same explicit
nonemptiness premise; its opposite is therefore final for colimits. -/
instance orderedSmallLevelForget_initial [Nonempty σ.SmallLevelCategory] :
    σ.orderedSmallLevelForget.Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro V
    obtain ⟨U, hU⟩ := σ.exists_orderedSmallLevel_le V
    exact ⟨U, ⟨homOfLE hU⟩⟩
  · intro V U s t
    exact ⟨U, 𝟙 U, Subsingleton.elim _ _⟩

/-- Conjugation in the convention used by LevelColimit preserves the same
sufficient smallness predicate. -/
theorem LevelSufficientlySmall.conjLevel
    {U : CompactOpenLevel G} (hU : σ.LevelSufficientlySmall U) (g : G) :
    σ.LevelSufficientlySmall (CompactOpenLevel.conjLevel g U) := by
  exact hU.conjugate g⁻¹

/-- The ordered conjugate level has the underlying compact open subgroup
g U g⁻¹ used to define the generic colimit action. -/
def orderedSmallLevelConjugate (g : G) (U : σ.OrderedSmallLevel) :
    σ.OrderedSmallLevel :=
  ⟨CompactOpenLevel.conjLevel g U.val, U.property.conjLevel σ g⟩

/-- The underlying conjugate is precisely the generic colimit conjugate. -/
@[simp] theorem orderedSmallLevelConjugate_val (g : G) (U : σ.OrderedSmallLevel) :
    (σ.orderedSmallLevelConjugate g U).val = CompactOpenLevel.conjLevel g U.val := rfl

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)

/-- The actual CM sufficiently small levels with only inclusion arrows. -/
abbrev OrderedSmallCMLevel := D.rationalInvolution.OrderedSmallLevel

/-- The inclusion index for the actual CM scheme tower retains its exact
smallness certificate and genuine inclusion transporter arrow. -/
def orderedSmallCMLevelToSmallCMLevel : OrderedSmallCMLevel D ⥤ SmallCMLevel D :=
  D.rationalInvolution.orderedSmallLevelToSmallLevelCategory

/-- The ordered inclusion of CM levels into all compact open levels. -/
def orderedSmallCMLevelForget : OrderedSmallCMLevel D ⥤
    CompactOpenLevel.Ordered D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ :=
  D.rationalInvolution.orderedSmallLevelForget

omit [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The CM restriction has exactly the same underlying transporter arrows. -/
theorem orderedSmallCMLevelToSmallCMLevel_comp :
    orderedSmallCMLevelToSmallCMLevel D ⋙
        ObjectProperty.ι D.rationalInvolution.LevelSufficientlySmall =
      orderedSmallCMLevelForget D ⋙ CompactOpenLevel.inclusionFunctor := rfl

/-- Conditional CM cofilteredness uses the finite-dimensional algebra already
contained in D, and requires an actual small level. -/
instance [Nonempty (SmallCMLevel D)] : IsCofiltered (OrderedSmallCMLevel D) := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  infer_instance

/-- The opposite CM inclusion is final for shrinking-level colimits whenever
a small CM level exists. No unconditional small-level existence is inferred. -/
instance orderedSmallCMLevelForget_op_final [Nonempty (SmallCMLevel D)] :
    (orderedSmallCMLevelForget D).op.Final := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  change D.rationalInvolution.orderedSmallLevelForget.op.Final
  infer_instance

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

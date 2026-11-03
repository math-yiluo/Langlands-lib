import Langlands.BruhatTits.Cartan.CentralizerValuationConsequences
import Mathlib.GroupTheory.DoubleCoset

/-! # Restricted centralizer quotients and their representative maps -/

noncomputable section

universe u v

namespace Langlands.BruhatTits.Cartan

namespace RestrictedRightQuotient

variable {Z : Type u} [Group Z] (D : Set Z) (N : Subgroup Z)

/-- Restrict the right-coset relation to a set of representatives. No invariance
of the set under the subgroup, or normality of the subgroup, is required. -/
def setoid : Setoid D :=
  (QuotientGroup.rightRel N).comap Subtype.val

/-- The set quotient of `D` by `z' * z⁻¹ ∈ N`. This is not a quotient group. -/
def Quotient : Type u := _root_.Quotient (setoid D N)

/-- The class of an element of the restricted set. -/
def mk (z : D) : Quotient D N := _root_.Quotient.mk _ z

@[simp] theorem mk_eq_mk (z z' : D) :
    mk D N z = mk D N z' ↔ z'.val * z.val⁻¹ ∈ N := by
  exact _root_.Quotient.eq.trans QuotientGroup.rightRel_apply

variable {G : Type v} [Group G] (j : Z →* G) (H : Subgroup G)

/-- The exact well-definedness condition for sending a restricted class to
its representative's double coset. -/
def Respects : Prop :=
  ∀ z z' : D, z'.val * z.val⁻¹ ∈ N →
    DoubleCoset.mk H H (j z.val) = DoubleCoset.mk H H (j z'.val)

/-- The induced map, requiring the well-definedness proof explicitly. -/
def doubleCosetMap (h : Respects D N j H) :
    Quotient D N → DoubleCoset.Quotient (H : Set G) H :=
  _root_.Quotient.lift (fun z : D => DoubleCoset.mk H H (j z.val))
    (fun z z' hzz' => h z z' (QuotientGroup.rightRel_apply.mp hzz'))

@[simp] theorem doubleCosetMap_mk (h : Respects D N j H) (z : D) :
    doubleCosetMap D N j H h (mk D N z) = DoubleCoset.mk H H (j z.val) := rfl

/-- Coverage gives surjectivity, and the converse double-coset criterion gives
injectivity. Neither conclusion is inferred from coverage alone. -/
theorem doubleCosetMap_bijective (h : Respects D N j H)
    (hcover : ∀ g : G, ∃ z : D,
      DoubleCoset.mk H H (j z.val) = DoubleCoset.mk H H g)
    (hdetect : ∀ z z' : D,
      DoubleCoset.mk H H (j z.val) = DoubleCoset.mk H H (j z'.val) →
        z'.val * z.val⁻¹ ∈ N) :
    Function.Bijective (doubleCosetMap D N j H h) := by
  constructor
  · intro q q' heq
    induction q using _root_.Quotient.inductionOn with
    | h z =>
      induction q' using _root_.Quotient.inductionOn with
      | h z' => exact (mk_eq_mk D N z z').mpr (hdetect z z' heq)
  · intro q
    induction q using _root_.Quotient.inductionOn with
    | h g =>
      obtain ⟨z, hz⟩ := hcover g
      exact ⟨mk D N z, hz⟩

/-- The genuine quotient-to-double-coset equivalence obtained from coverage
and the full equality criterion. This is an elementary conditional constructor,
not an actual-group Cartan assertion. -/
def doubleCosetEquiv
    (hcover : ∀ g : G, ∃ z : D,
      DoubleCoset.mk H H (j z.val) = DoubleCoset.mk H H g)
    (hclassify : ∀ z z' : D,
      DoubleCoset.mk H H (j z.val) = DoubleCoset.mk H H (j z'.val) ↔
        z'.val * z.val⁻¹ ∈ N) :
    Quotient D N ≃ DoubleCoset.Quotient (H : Set G) H :=
  Equiv.ofBijective
    (doubleCosetMap D N j H (fun z z' hzz' => (hclassify z z').mpr hzz'))
    (doubleCosetMap_bijective D N j H _ hcover
      (fun z z' hzz' => (hclassify z z').mp hzz'))

@[simp] theorem doubleCosetEquiv_mk
    (hcover : ∀ g : G, ∃ z : D,
      DoubleCoset.mk H H (j z.val) = DoubleCoset.mk H H g)
    (hclassify : ∀ z z' : D,
      DoubleCoset.mk H H (j z.val) = DoubleCoset.mk H H (j z'.val) ↔
        z'.val * z.val⁻¹ ∈ N) (z : D) :
    doubleCosetEquiv D N j H hcover hclassify (mk D N z) =
      DoubleCoset.mk H H (j z.val) := rfl

end RestrictedRightQuotient

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- Equality of actual real valuations is precisely the right-coset relation
for the actual common norm kernel. -/
theorem centralizerValuation_eq_iff (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) (z z' : rationalPoints Z) :
    centralizerValuation s h z = centralizerValuation s h z' ↔
      z' * z⁻¹ ∈ rationalCommonNormKernel Z := by
  rw [← centralizerValuation_ker s h, ← div_eq_mul_inv,
    MonoidHom.div_mem_ker_iff, eq_comm]

/-- The dominant set quotiented by the common norm kernel `Z(F)^1`.
The KP parahoric quotient instead uses `Z(F)^0`. -/
abbrev DominantNormQuotient (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s)) :=
  RestrictedRightQuotient.Quotient (dominantCentralizer i ν s h)
    (rationalCommonNormKernel Z)

/-- The canonical value of a dominant norm-kernel class in the actual chamber. -/
def dominantNormValue (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s)) :
    DominantNormQuotient i ν s h → dominantValuationImage i ν s h :=
  _root_.Quotient.lift
    (fun z : dominantCentralizer i ν s h =>
      ⟨(centralizerValuation s h).rangeRestrict z.val, z.property⟩)
    (by
      intro z z' hzz'
      apply Subtype.ext
      apply Subtype.ext
      exact (centralizerValuation_eq_iff s h z.val z'.val).mpr
        (QuotientGroup.rightRel_apply.mp hzz'))

/-- The dominant norm quotient has exactly the actual chamber as its values. -/
theorem dominantNormValue_bijective (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s)) :
    Function.Bijective (dominantNormValue i ν s h) := by
  constructor
  · intro q q' heq
    induction q using _root_.Quotient.inductionOn with
    | h z =>
      induction q' using _root_.Quotient.inductionOn with
      | h z' =>
        apply (RestrictedRightQuotient.mk_eq_mk _ _ z z').mpr
        exact (centralizerValuation_eq_iff s h z.val z'.val).mp
          (congrArg (fun v => v.val.val) heq)
  · intro v
    obtain ⟨z, hz⟩ := v.val.property
    have hdom : z ∈ dominantCentralizer i ν s h := by
      change ∀ α ∈ positiveRelativeRoots i ν,
        0 ≤ RealTorusSpace.eval S α (centralizerValuation s h z).toAdd
      rw [hz]
      exact v.property
    refine ⟨RestrictedRightQuotient.mk _ _ ⟨z, hdom⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hz

/-- The intrinsic chamber parametrizes the actual dominant norm-kernel quotient.
No maximal-compact double-coset comparison enters this construction. -/
def dominantNormQuotientEquiv (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s)) :
    DominantNormQuotient i ν s h ≃ dominantValuationImage i ν s h :=
  Equiv.ofBijective _ (dominantNormValue_bijective i ν s h)

@[simp] theorem dominantNormQuotientEquiv_mk (i : S.toGrp ⟶ G)
    (ν : cocharacterLattice S) (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s))
    (z : dominantCentralizer i ν s h) :
    dominantNormQuotientEquiv i ν s h (RestrictedRightQuotient.mk _ _ z) =
      ⟨(centralizerValuation s h).rangeRestrict z.val, z.property⟩ := rfl

end Langlands.BruhatTits.Cartan

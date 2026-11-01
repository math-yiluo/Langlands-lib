import Langlands.AlgebraicGeometry.Picard.Functor
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AlgebraicGeometry.Picard.RelativeGeometry

/-! # The ordinary relative Picard presheaf -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativePicard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The ordinary relative Picard presheaf, with its actual abelian group structure. -/
def presheaf : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (relativeSpace f).op ⋙ Group.functor

/-- The underlying set-valued presheaf of ordinary line-bundle classes. -/
def classPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  presheaf f ⋙ forget AddCommGrpCat

@[simp]
lemma presheaf_obj (T : Over S) :
    (presheaf f).obj (op T) = AddCommGrpCat.of (Group ((relativeSpace f).obj T)) := rfl

@[simp]
lemma classPresheaf_obj (T : Over S) :
    (classPresheaf f).obj (op T) = Group ((relativeSpace f).obj T) := rfl

@[simp]
lemma presheaf_map_apply {T U : Over S} (h : T ⟶ U)
    (q : Group ((relativeSpace f).obj U)) :
    (presheaf f).map h.op q = Group.pullback ((relativeSpace f).map h) q := rfl

@[simp]
lemma classPresheaf_map_apply {T U : Over S} (h : T ⟶ U)
    (q : Group ((relativeSpace f).obj U)) :
    (classPresheaf f).map h.op q = Group.pullback ((relativeSpace f).map h) q := rfl

/-- The ordinary relative class of an actual line bundle on the fibre product. -/
def classOf (T : Over S) (L : LineBundle ((relativeSpace f).obj T)) :
    Group ((relativeSpace f).obj T) :=
  L.classOf

lemma classOf_eq_iff_iso (T : Over S) (L M : LineBundle ((relativeSpace f).obj T)) :
    classOf f T L = classOf f T M ↔ Nonempty (L ≅ M) :=
  LineBundle.classOf_eq_iff_iso L M

/-- Every presheaf section is represented by an actual line bundle. -/
lemma exists_representative (T : Over S) (q : (classPresheaf f).obj (op T)) :
    ∃ L : LineBundle ((relativeSpace f).obj T), classOf f T L = q :=
  ⟨Group.lineBundleRepresentative _ q, Group.classOf_lineBundleRepresentative _ q⟩

@[simp]
lemma map_classOf {T U : Over S} (h : T ⟶ U)
    (L : LineBundle ((relativeSpace f).obj U)) :
    (classPresheaf f).map h.op (classOf f U L) =
      classOf f T ((LineBundle.pullback ((relativeSpace f).map h)).obj L) :=
  Group.pullback_lineBundle_classOf _ L

@[simp]
lemma classOf_trivial (T : Over S) :
    classOf f T (LineBundle.trivial ((relativeSpace f).obj T)) = 0 :=
  LineBundle.classOf_trivial _

lemma classOf_tensor (T : Over S) (L M : LineBundle ((relativeSpace f).obj T)) :
    classOf f T (LineBundle.tensor
      Langlands.Scheme.Modules.pullbackTensorComparisonIsIso L M) =
      classOf f T L + classOf f T M :=
  LineBundle.classOf_tensor _ L M

@[simp]
lemma classOf_inverse (T : Over S) (L : LineBundle ((relativeSpace f).obj T)) :
    classOf f T L.inverse = -classOf f T L :=
  LineBundle.classOf_inverse L

end Langlands.AlgebraicGeometry.Picard.RelativePicard

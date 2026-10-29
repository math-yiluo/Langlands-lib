import Langlands.CategoryTheory.Renard.SimpleSupport
import Langlands.CategoryTheory.Renard.IndexedSubobjectSums

/-!
# Renard A.IX: the sum `E_S` of all supported subobjects

On printed page 268 / PDF page 274 of Renard's 9 July 2026 French edition,
`E_S` is the sum of all subobjects of `E` that lie in `M_S`. We take the
actual public sum `subobjectSum` of the family indexed by the full subtype of
supported subobjects of `X`: the image subobject of the map from the coproduct
of their underlying objects into `X`. The coproduct of this one family is an
explicit instance argument; images come from `[Abelian C]`.

Only the defining and order-theoretic laws of the sum are proved here. Support
of the sum, maximality among supported subobjects and all later A.IX
assertions are separate obligations.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Renard's `E_S`: the sum of all actual subobjects of `X` supported on `S`,
that is, the image subobject of the coproduct map out of the coproduct of the
underlying objects of all supported subobjects. -/
def simpleSupportSum (S : Set (ObjectClass C)) (X : C)
    [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)] :
    Subobject X :=
  subobjectSum (fun P : simpleSupportSubobjects S X => (P : Subobject X))

section Laws

variable (S : Set (ObjectClass C)) (X : C)
  [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)]

/-- The defining equation: `E_S` is the public sum of the family of all
supported subobjects. -/
theorem simpleSupportSum_def :
    simpleSupportSum S X =
      subobjectSum (fun P : simpleSupportSubobjects S X => (P : Subobject X)) :=
  rfl

/-- `E_S` is the subobject represented by the image inclusion of the coproduct
map `Sigma.desc fun P => (P : Subobject X).arrow`. -/
theorem simpleSupportSum_eq_mk :
    simpleSupportSum S X =
      Subobject.mk (image.ι (Sigma.desc fun P : simpleSupportSubobjects S X =>
        (P : Subobject X).arrow)) :=
  rfl

/-- Every supported subobject lies below `E_S`. -/
theorem le_simpleSupportSum {P : Subobject X} (hP : P ∈ simpleSupportSubobjects S X) :
    P ≤ simpleSupportSum S X :=
  le_subobjectSum (fun P : simpleSupportSubobjects S X => (P : Subobject X)) ⟨P, hP⟩

/-- `E_S` lies below every common upper bound of the supported subobjects. -/
theorem simpleSupportSum_le {G : Subobject X}
    (h : ∀ P ∈ simpleSupportSubobjects S X, P ≤ G) : simpleSupportSum S X ≤ G :=
  subobjectSum_le (fun P : simpleSupportSubobjects S X => (P : Subobject X))
    fun P => h P P.2

/-- `E_S` lies below `G` exactly when every supported subobject does. -/
theorem simpleSupportSum_le_iff {G : Subobject X} :
    simpleSupportSum S X ≤ G ↔ ∀ P ∈ simpleSupportSubobjects S X, P ≤ G :=
  ⟨fun h _ hP => (le_simpleSupportSum S X hP).trans h, simpleSupportSum_le S X⟩

/-- `E_S` is the least upper bound of the set of supported subobjects. -/
theorem isLUB_simpleSupportSum :
    IsLUB (simpleSupportSubobjects S X) (simpleSupportSum S X) :=
  ⟨fun _ hP => le_simpleSupportSum S X hP,
    fun _ hG => simpleSupportSum_le S X fun _ hP => hG hP⟩

/-- Any least upper bound of the set of supported subobjects is `E_S`. -/
theorem simpleSupportSum_eq_of_isLUB {U : Subobject X}
    (hU : IsLUB (simpleSupportSubobjects S X) U) : simpleSupportSum S X = U :=
  (isLUB_simpleSupportSum S X).unique hU

end Laws

/-- Enlarging `S` enlarges `E_S`, given the coproducts of both families. -/
theorem simpleSupportSum_mono {S T : Set (ObjectClass C)} (hST : S ⊆ T) (X : C)
    [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)]
    [HasCoproduct fun P : simpleSupportSubobjects T X => ((P : Subobject X) : C)] :
    simpleSupportSum S X ≤ simpleSupportSum T X :=
  simpleSupportSum_le S X fun _ hP =>
    le_simpleSupportSum T X (simpleSupportSubobjects_mono hST X hP)

end

end Langlands.Renard

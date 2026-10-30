import Langlands.CategoryTheory.Renard.SimpleSupportSum
import Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Canonical functoriality of Renard's supported sums

Internal construction from the actual supported sums of Renard A.IX,
printed268/PDF274 of the French edition dated 9 July 2026, and the public
epimorphism transport of simple subquotient classes. No support theorem for
the sum, source Grothendieck hypothesis or splitting assertion is assumed.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

section Map

variable (S : Set (ObjectClass C)) {X Y : C}
  [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)]
  [HasCoproduct fun P : simpleSupportSubobjects S Y => ((P : Subobject Y) : C)]

/-- Every supported subobject of `X` maps into the actual supported sum in `Y`.
This does not assume that either full supported sum itself is supported. -/
theorem simpleSupportSum_le_pullback (f : X ⟶ Y) :
    simpleSupportSum S X ≤ (Subobject.pullback f).obj (simpleSupportSum S Y) := by
  apply simpleSupportSum_le
  intro P hP
  let g : (P : C) ⟶ Y := P.arrow ≫ f
  have hIm : HasSimpleSupport S (imageSubobject g : C) := by
    intro q hq
    exact hP (simpleSubquotientClasses_subset_of_epi
      (factorThruImageSubobject g) hq)
  have hle : imageSubobject g ≤ simpleSupportSum S Y :=
    le_simpleSupportSum S Y hIm
  apply Subobject.le_pullback_of_comm f
    (factorThruImageSubobject g ≫ Subobject.ofLE _ _ hle)
  simp [g]

/-- The restriction of `f` to the actual supported sums, using their inclusions. -/
def simpleSupportSumMap (f : X ⟶ Y) :
    (simpleSupportSum S X : C) ⟶ (simpleSupportSum S Y : C) :=
  Subobject.ofLE _ _ (simpleSupportSum_le_pullback S f) ≫
    Subobject.pullbackπ f (simpleSupportSum S Y)

@[reassoc (attr := simp)]
theorem simpleSupportSumMap_arrow (f : X ⟶ Y) :
    simpleSupportSumMap S f ≫ (simpleSupportSum S Y).arrow =
      (simpleSupportSum S X).arrow ≫ f := by
  dsimp [simpleSupportSumMap]
  rw [Category.assoc, (Subobject.isPullback f (simpleSupportSum S Y)).w]
  simp

/-- The inclusion square uniquely determines the induced map. -/
theorem simpleSupportSumMap_unique (f : X ⟶ Y)
    (g : (simpleSupportSum S X : C) ⟶ (simpleSupportSum S Y : C))
    (h : g ≫ (simpleSupportSum S Y).arrow =
      (simpleSupportSum S X).arrow ≫ f) :
    g = simpleSupportSumMap S f := by
  apply (cancel_mono (simpleSupportSum S Y).arrow).1
  simpa only [simpleSupportSumMap_arrow] using h

end Map

/-- The canonical supported-sum map preserves identities. -/
@[simp]
theorem simpleSupportSumMap_id (S : Set (ObjectClass C)) (X : C)
    [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)] :
    simpleSupportSumMap S (𝟙 X) = 𝟙 (simpleSupportSum S X : C) := by
  apply (cancel_mono (simpleSupportSum S X).arrow).1
  simp

/-- The canonical supported-sum map preserves composition. -/
@[simp]
theorem simpleSupportSumMap_comp (S : Set (ObjectClass C)) {X Y Z : C}
    [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)]
    [HasCoproduct fun P : simpleSupportSubobjects S Y => ((P : Subobject Y) : C)]
    [HasCoproduct fun P : simpleSupportSubobjects S Z => ((P : Subobject Z) : C)]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    simpleSupportSumMap S (f ≫ g) = simpleSupportSumMap S f ≫ simpleSupportSumMap S g := by
  apply (cancel_mono (simpleSupportSum S Z).arrow).1
  simp [Category.assoc]

section Functor

variable (S : Set (ObjectClass C))
  [∀ X : C, HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)]

/-- The actual supported-sum endofunctor, given exactly its objectwise coproducts. -/
def simpleSupportSumFunctor : C ⥤ C where
  obj X := (simpleSupportSum S X : C)
  map f := simpleSupportSumMap S f
  map_id X := simpleSupportSumMap_id S X
  map_comp f g := simpleSupportSumMap_comp S f g

/-- The actual supported-sum inclusions form a natural transformation to identity. -/
def simpleSupportSumInclusion : simpleSupportSumFunctor S ⟶ 𝟭 C where
  app X := (simpleSupportSum S X).arrow
  naturality _ _ f := simpleSupportSumMap_arrow S f

@[simp]
theorem simpleSupportSumFunctor_obj (X : C) :
    (simpleSupportSumFunctor S).obj X = (simpleSupportSum S X : C) :=
  rfl

@[simp]
theorem simpleSupportSumFunctor_map {X Y : C} (f : X ⟶ Y) :
    (simpleSupportSumFunctor S).map f = simpleSupportSumMap S f :=
  rfl

@[simp]
theorem simpleSupportSumInclusion_app (X : C) :
    (simpleSupportSumInclusion S).app X = (simpleSupportSum S X).arrow :=
  rfl

instance simpleSupportSumInclusion_app_mono (X : C) :
    Mono ((simpleSupportSumInclusion S).app X) := by
  dsimp [simpleSupportSumInclusion]
  infer_instance

end Functor

end

end Langlands.Renard

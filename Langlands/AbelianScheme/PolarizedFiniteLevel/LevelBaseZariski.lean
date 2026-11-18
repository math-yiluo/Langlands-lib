import Langlands.AbelianScheme.PolarizedFiniteLevel.Base
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Yoneda

/-! # Zariski opens, sheaves and open charts on the level base category -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe v

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

namespace LevelBase

variable {n : ℕ}

/-- The level is a unit on every open subscheme of a level base. -/
theorem level_isUnit_open (S : LevelBase n) (U : S.obj.Opens) :
    IsUnit (n : Γ(U.toScheme, ⊤)) := by
  simpa only [map_natCast] using S.level_isUnit.map U.ι.appTop.hom

/-- An open subscheme of a level base, as an object of the level base category. -/
def ofOpen (S : LevelBase n) (U : S.obj.Opens) : LevelBase n :=
  ofScheme U.toScheme (S.level_isUnit_open U)

@[simp]
theorem ofOpen_obj (S : LevelBase n) (U : S.obj.Opens) :
    (S.ofOpen U).obj = U.toScheme :=
  rfl

/-- The inclusion of an open subscheme, as a morphism of level bases. -/
def openι (S : LevelBase n) (U : S.obj.Opens) : S.ofOpen U ⟶ S :=
  homMk U.ι

/-- The inclusion between two nested open subschemes. -/
def openLE (S : LevelBase n) {U V : S.obj.Opens} (h : U ≤ V) :
    S.ofOpen U ⟶ S.ofOpen V :=
  homMk (S.obj.homOfLE h)

@[reassoc (attr := simp)]
theorem openLE_openι (S : LevelBase n) {U V : S.obj.Opens} (h : U ≤ V) :
    S.openLE h ≫ S.openι V = S.openι U := by
  ext1
  exact Scheme.homOfLE_ι S.obj h

/-- The Zariski sheaf condition for a presheaf on the level base category:
compatible sections over an open cover of a level base glue uniquely. -/
def IsZariskiSheaf (F : (LevelBase n)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ (S : LevelBase n) (ι : Type) (U : ι → S.obj.Opens), iSup U = ⊤ →
    ∀ s : ∀ i, F.obj (op (S.ofOpen (U i))),
      (∀ i j, F.map (S.openLE (inf_le_left : U i ⊓ U j ≤ U i)).op (s i) =
        F.map (S.openLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j)) →
      ∃! t : F.obj (op S), ∀ i, F.map (S.openι (U i)).op t = s i

/-- `a` identifies the functor of points of `X` with an open subfunctor of `F`.
It is injective on every test object, and for every section `ξ` over `S`
there is an open `U` of `S` such that a pullback of `ξ` along `f : T ⟶ S`
lies in the subfunctor exactly when `f` factors set-theoretically through `U`. -/
def IsOpenChart {F : (LevelBase n)ᵒᵖ ⥤ Type 1} {X : LevelBase n}
    (a : uliftYoneda.{1}.obj X ⟶ F) : Prop :=
  (∀ T : (LevelBase n)ᵒᵖ, Function.Injective (a.app T)) ∧
    ∀ (S : LevelBase n) (ξ : F.obj (op S)), ∃ U : S.obj.Opens,
      ∀ (T : LevelBase n) (f : T ⟶ S),
        F.map f.op ξ ∈ Set.range (a.app (op T)) ↔
          Set.range f.hom.base ⊆ (U : Set S.obj)

/-- A family of charts covers `F`: every point of every base lies in the open
over which a given section belongs to one of the charts. -/
def IsOpenChartCover {F : (LevelBase n)ᵒᵖ ⥤ Type 1} {ι : Type} {X : ι → LevelBase n}
    (a : ∀ i, uliftYoneda.{1}.obj (X i) ⟶ F) : Prop :=
  ∀ (S : LevelBase n) (ξ : F.obj (op S)) (x : S.obj), ∃ (i : ι) (U : S.obj.Opens),
    x ∈ U ∧ ∀ (T : LevelBase n) (f : T ⟶ S),
      F.map f.op ξ ∈ Set.range ((a i).app (op T)) ↔
        Set.range f.hom.base ⊆ (U : Set S.obj)

end LevelBase

end Langlands.AbelianScheme.PolarizedFiniteLevel

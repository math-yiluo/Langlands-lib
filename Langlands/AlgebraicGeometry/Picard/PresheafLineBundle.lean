import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Yoneda

/-! # Coherent line bundles on presheaves of families -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}}

/-- An actual line bundle on every family of a presheaf, with cartesian
identifications satisfying the identity and composition laws. -/
structure PresheafLineBundle (F : (Over S)ᵒᵖ ⥤ Type v) where
  /-- The line bundle attached to an actual family. -/
  bundle (T : Over S) (x : F.obj (op T)) : LineBundle T.left
  /-- Identification along a morphism of families. -/
  pullbackIso {T U : Over S} (a : T ⟶ U)
      (x : F.obj (op U)) (y : F.obj (op T)) (h : F.map a.op x = y) :
      (LineBundle.pullback a.left).obj (bundle U x) ≅ bundle T y
  /-- Identity morphisms induce the canonical identity pullback comparison. -/
  pullbackIso_id (T : Over S) (x : F.obj (op T)) :
      pullbackIso (𝟙 T) x x (by simp) =
        (LineBundle.pullbackId T.left).app (bundle T x)
  /-- Composition of morphisms of families agrees with successive pullback. -/
  pullbackIso_comp {T U V : Over S} (a : T ⟶ U) (b : U ⟶ V)
      (x : F.obj (op V)) (y : F.obj (op U)) (z : F.obj (op T))
      (hb : F.map b.op x = y) (ha : F.map a.op y = z) :
      pullbackIso (a ≫ b) x z
          (by simpa using (congrArg (F.map a.op) hb).trans ha) =
        ((LineBundle.pullbackComp a.left b.left).app (bundle V x)).symm ≪≫
          (LineBundle.pullback a.left).mapIso (pullbackIso b x y hb) ≪≫
          pullbackIso a y z ha

namespace PresheafLineBundle

variable {F : (Over S)ᵒᵖ ⥤ Type v} (L : PresheafLineBundle F)

/-- Reindex a coherent line bundle along a natural transformation of families. -/
def reindex {G : (Over S)ᵒᵖ ⥤ Type v} (φ : G ⟶ F) : PresheafLineBundle G where
  bundle T x := L.bundle T (φ.app (op T) x)
  pullbackIso a x y h := L.pullbackIso a _ _ (by
    rw [← φ.naturality_apply a.op x, h])
  pullbackIso_id T x := L.pullbackIso_id T _
  pullbackIso_comp a b x y z hb ha := L.pullbackIso_comp a b _ _ _ _ _

/-- Restrict the parameter base of a coherent line bundle. -/
def baseChange {U : Scheme.{u}} (p : U ⟶ S) :
    PresheafLineBundle ((Over.map p).op ⋙ F) where
  bundle T x := L.bundle ((Over.map p).obj T) x
  pullbackIso a x y h := L.pullbackIso ((Over.map p).map a) x y h
  pullbackIso_id T x := L.pullbackIso_id ((Over.map p).obj T) x
  pullbackIso_comp a b x y z hb ha :=
    L.pullbackIso_comp ((Over.map p).map a) ((Over.map p).map b) x y z hb ha

/-- The line bundle on the universal family of a supplied representer. -/
def universal {M : Over S} (e : F.RepresentableBy M) : LineBundle M.left :=
  L.bundle M (e.homEquiv (𝟙 M))

/-- Every family classified by a representer has the pullback of its universal
line bundle, with its specified cartesian identification. -/
def universalPullbackIso {M : Over S} (e : F.RepresentableBy M)
    {T : Over S} (a : T ⟶ M) :
    (LineBundle.pullback a.left).obj (L.universal e) ≅ L.bundle T (e.homEquiv a) :=
  L.pullbackIso a _ _ (e.homEquiv_eq a).symm

/-- Matching restrictions identify the two actual pulled-back line bundles. -/
def transition {T U V : Over S} (a : T ⟶ U) (b : T ⟶ V)
    (x : F.obj (op U)) (y : F.obj (op V))
    (h : F.map a.op x = F.map b.op y) :
    (LineBundle.pullback a.left).obj (L.bundle U x) ≅
      (LineBundle.pullback b.left).obj (L.bundle V y) :=
  L.pullbackIso a x _ rfl ≪≫
    eqToIso (congrArg (L.bundle T) h) ≪≫ (L.pullbackIso b y _ rfl).symm

/-- The transition from a family to itself is the identity. -/
@[simp]
theorem transition_self {T U : Over S} (a : T ⟶ U) (x : F.obj (op U)) :
    L.transition a a x x rfl = Iso.refl _ := by
  simp [transition]

/-- Transitions on any common test scheme satisfy the cocycle law. -/
theorem transition_trans {T U V W : Over S}
    (a : T ⟶ U) (b : T ⟶ V) (c : T ⟶ W)
    (x : F.obj (op U)) (y : F.obj (op V)) (z : F.obj (op W))
    (hab : F.map a.op x = F.map b.op y) (hbc : F.map b.op y = F.map c.op z) :
    L.transition a b x y hab ≪≫ L.transition b c y z hbc =
      L.transition a c x z (hab.trans hbc) := by
  ext
  simp [transition]

end PresheafLineBundle

end Langlands.AlgebraicGeometry.Picard

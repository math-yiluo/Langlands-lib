import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.Finite
import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.TorsorCocycle

/-! # Local trivializations of split-torus cocycles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

open Langlands.Scheme.UnitCocycleDescent

/-- A coboundary expression for a cocycle over an open neighbourhood of a base point. -/
structure LocalTrivialization {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}
    (ξ : Cocycle G U) (y : S) where
  openSet : S.Opens
  mem_openSet : y ∈ openSet
  cochain : Over.mk ((U.hom ⁻¹ᵁ openSet).ι ≫ U.hom) ⟶ G.X
  coboundary : ∀ {Z : Over S}
    (a b : Z ⟶ Over.mk ((U.hom ⁻¹ᵁ openSet).ι ≫ U.hom)),
    ξ.toFun (a ≫ Over.homMk (U.hom ⁻¹ᵁ openSet).ι)
      (b ≫ Over.homMk (U.hom ⁻¹ᵁ openSet).ι) =
        (a ≫ cochain) * (b ≫ cochain)⁻¹

variable {S : Scheme.{u}} {I : Type u} [Finite I] {U : Over S}
  (ξ : Cocycle (splitTorus S I) U)

/-- Read one unit coordinate on any pair of maps with equal composite to the base. -/
def unitCoordinate (i : I) (Z : Scheme.{u}) (a b : Z ⟶ U.left)
    (h : a ≫ U.hom = b ≫ U.hom) : Γ(Z, ⊤)ˣ :=
  splitTorus.pointsEquiv I (Over.mk (a ≫ U.hom))
    (ξ.toFun (Over.homMk a) (Over.homMk b h.symm)) i

/-- The scheme-valued coordinate agrees with the original coordinate on an over-test. -/
theorem unitCoordinate_eq (i : I) (Z : Over S) (a b : Z.left ⟶ U.left)
    (ha : a ≫ U.hom = Z.hom) (hb : b ≫ U.hom = Z.hom)
    (h : a ≫ U.hom = b ≫ U.hom) :
    ξ.unitCoordinate i Z.left a b h =
      splitTorus.pointsEquiv I Z (ξ.toFun (Over.homMk a ha) (Over.homMk b hb)) i := by
  let t : Over.mk (a ≫ U.hom) ⟶ Z := Over.homMk (𝟙 Z.left) (by simpa using ha.symm)
  let a' : Over.mk (a ≫ U.hom) ⟶ U := Over.homMk a
  let b' : Over.mk (a ≫ U.hom) ⟶ U := Over.homMk b h.symm
  have hnat := ξ.naturality t (Over.homMk a ha) (Over.homMk b hb)
  have ha' : t ≫ Over.homMk a ha = a' := by ext; simp [t, a']
  have hb' : t ≫ Over.homMk b hb = b' := by ext; simp [t, b']
  rw [ha', hb'] at hnat
  change splitTorus.pointsEquiv I _ _ i = _
  rw [hnat, splitTorus.pointsEquiv_naturality]
  simp [splitTorus.unitsRestrict, t]

/-- Each unit coordinate of a split-torus cocycle is natural. -/
theorem unitCoordinate_isNatural (i : I) : IsNatural U.hom (ξ.unitCoordinate i) := by
  intro Z Z' t a b hab hab'
  let T : Over S := Over.mk (a ≫ U.hom)
  let T' : Over S := Over.mk ((t ≫ a) ≫ U.hom)
  let t' : T' ⟶ T := Over.homMk t (Category.assoc _ _ _).symm
  have h := ξ.naturality t' (Over.homMk a) (Over.homMk b hab.symm)
  change splitTorus.pointsEquiv I T' _ i = _
  rw [show ξ.toFun (Over.homMk (t ≫ a)) (Over.homMk (t ≫ b) hab'.symm) =
      t' ≫ ξ.toFun (Over.homMk a) (Over.homMk b hab.symm) from h,
    splitTorus.pointsEquiv_naturality]
  rfl

/-- Each unit coordinate satisfies the multiplicative cocycle equation. -/
theorem unitCoordinate_isMultiplicative (i : I) :
    IsMultiplicative U.hom (ξ.unitCoordinate i) := by
  intro Z a b d hab hbd had
  let T : Over S := Over.mk (a ≫ U.hom)
  change ξ.unitCoordinate i T.left a b hab * ξ.unitCoordinate i T.left b d hbd =
    ξ.unitCoordinate i T.left a d had
  rw [ξ.unitCoordinate_eq i T a b rfl hab.symm hab,
    ξ.unitCoordinate_eq i T b d hab.symm had.symm hbd,
    ξ.unitCoordinate_eq i T a d rfl had.symm had,
    ξ.cocycle (Over.homMk a : T ⟶ U) (Over.homMk b hab.symm)
      (Over.homMk d had.symm), map_mul]
  rfl

section Frame

variable {y : S} (F : FiniteLocalFrame U.hom ξ.unitCoordinate y)

/-- The cover restricted to the common open neighbourhood, still regarded over `S`. -/
abbrev frameCover : Over S :=
  Over.mk ((U.hom ⁻¹ᵁ F.openSet).ι ≫ U.hom)

/-- The open inclusion of the restricted cover into the original cover. -/
def frameCoverι : ξ.frameCover F ⟶ U :=
  Over.homMk (U.hom ⁻¹ᵁ F.openSet).ι

/-- The frame units read as global units of the restricted cover. -/
def frameUnit (i : I) : Γ((ξ.frameCover F).left, ⊤)ˣ :=
  Units.map ((U.hom ⁻¹ᵁ F.openSet).ι.appLE (U.hom ⁻¹ᵁ F.openSet) ⊤
    (U.hom ⁻¹ᵁ F.openSet).ι_preimage_self.ge).hom.toMonoidHom (F.unitSection i)

/-- Pulling back a frame unit agrees with pulling the original section back directly. -/
theorem frameUnit_pullback {Z : Over S} (a : Z ⟶ ξ.frameCover F) (i : I) :
    Units.map a.left.appTop.hom.toMonoidHom (ξ.frameUnit F i) =
      Units.map ((a ≫ ξ.frameCoverι F).left.appLE (U.hom ⁻¹ᵁ F.openSet) ⊤
        (by simp [frameCoverι])).hom.toMonoidHom
          (F.unitSection i) := by
  apply Units.ext
  change a.left.appTop
    ((U.hom ⁻¹ᵁ F.openSet).ι.appLE (U.hom ⁻¹ᵁ F.openSet) ⊤
      (U.hom ⁻¹ᵁ F.openSet).ι_preimage_self.ge (F.unitSection i).val) = _
  rw [appTop_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rfl

/-- The torus point with coordinates inverse to the frame units. -/
def frameCochain : ξ.frameCover F ⟶ (splitTorus S I).X :=
  (splitTorus.pointsEquiv I (ξ.frameCover F)).symm (fun i => (ξ.frameUnit F i)⁻¹)

/-- The frame law, expressed in units pulled back from the restricted cover. -/
theorem frameUnit_cocycle {Z : Over S} (a b : Z ⟶ ξ.frameCover F) (i : I) :
    splitTorus.pointsEquiv I Z
        (ξ.toFun (a ≫ ξ.frameCoverι F) (b ≫ ξ.frameCoverι F)) i *
      Units.map a.left.appTop.hom.toMonoidHom (ξ.frameUnit F i) =
      Units.map b.left.appTop.hom.toMonoidHom (ξ.frameUnit F i) := by
  rw [ξ.frameUnit_pullback F a i, ξ.frameUnit_pullback F b i]
  apply Units.ext
  let a' := a ≫ ξ.frameCoverι F
  let b' := b ≫ ξ.frameCoverι F
  have hab : a'.left ≫ U.hom = b'.left ≫ U.hom :=
    (Over.w a').trans (Over.w b').symm
  have h := F.isCocycleSection i Z.left a'.left b'.left hab ⊤
    (by simp [a', frameCoverι])
    (by simp [b', frameCoverι])
  rw [ξ.unitCoordinate_eq i Z a'.left b'.left (Over.w a') (Over.w b') hab] at h
  rw [show (Over.homMk a'.left (Over.w a') : Z ⟶ U) = a' from by ext; rfl,
    show (Over.homMk b'.left (Over.w b') : Z ⟶ U) = b' from by ext; rfl] at h
  simpa [a', b'] using h

/-- The inverse frame units trivialize the cocycle on the common neighbourhood. -/
theorem frameCochain_spec {Z : Over S} (a b : Z ⟶ ξ.frameCover F) :
    ξ.toFun (a ≫ ξ.frameCoverι F) (b ≫ ξ.frameCoverι F) =
      (a ≫ ξ.frameCochain F) * (b ≫ ξ.frameCochain F)⁻¹ := by
  apply (splitTorus.pointsEquiv I Z).injective
  funext i
  have h := ξ.frameUnit_cocycle F a b i
  simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply,
    splitTorus.pointsEquiv_naturality, frameCochain, MulEquiv.apply_symm_apply]
  change _ = (Units.map a.left.appTop.hom.toMonoidHom (ξ.frameUnit F i))⁻¹ *
    ((Units.map b.left.appTop.hom.toMonoidHom (ξ.frameUnit F i))⁻¹)⁻¹
  rw [inv_inv, ← h]
  rw [mul_left_comm, inv_mul_cancel, mul_one]

end Frame

/-- A split-torus cocycle on an affine faithfully flat cover has a local trivialization
at every base point, with the original all-test coboundary convention. -/
def localTrivialization [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom] (y : S) :
    ξ.LocalTrivialization y := by
  let F := finiteLocalFrame U.hom ξ.unitCoordinate ξ.unitCoordinate_isNatural
    ξ.unitCoordinate_isMultiplicative y
  exact {
    openSet := F.openSet
    mem_openSet := F.mem_openSet
    cochain := ξ.frameCochain F
    coboundary := ξ.frameCochain_spec F }

end Langlands.GroupScheme.Cocycle

import Langlands.Geometry.FormalGroup.DeligneRationalSheaf
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Actual stalk lattices for Deligne's framed determinant normalization -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {O : Type u} [CommRing O] (F : Type u) [Field F] [Algebra O F]
  (X : TopCat.{u})

/-- Scalar restriction commutes with the actual neighborhood colimit defining a stalk. -/
def restrictionStalkIso (N : X.Sheaf (ModuleCat.{u} F)) (x : X) :
    TopCat.Presheaf.stalk ((rationalRestriction F X).obj N).obj x ≅
      (ModuleCat.restrictScalars (algebraMap O F)).obj
        (TopCat.Presheaf.stalk N.obj x) :=
  (preservesColimitIso (ModuleCat.restrictScalars (algebraMap O F))
    ((OpenNhds.inclusion x).op ⋙ N.obj)).symm

/-- The actual integral-to-rational map on stalks, with its target's O-scalars explicit. -/
def integralRationalStalkMap (M : X.Sheaf (ModuleCat.{u} O)) (x : X) :
    TopCat.Presheaf.stalk M.obj x ⟶
      (ModuleCat.restrictScalars (algebraMap O F)).obj
        (TopCat.Presheaf.stalk ((rationalSheafFunctor F X).obj M).obj x) :=
  (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map (rationalUnit F X M).hom ≫
    (restrictionStalkIso F X ((rationalSheafFunctor F X).obj M) x).hom

set_option backward.isDefEq.respectTransparency false in
/-- A germ is sent to the germ of the same actual integral-to-rational section. -/
theorem integralRationalStalkMap_germ (M : X.Sheaf (ModuleCat.{u} O))
    (U : Opens X) (x : X) (hx : x ∈ U) :
    TopCat.Presheaf.germ M.obj U x hx ≫ integralRationalStalkMap F X M x =
      (rationalUnit F X M).hom.app (.op U) ≫
        (ModuleCat.restrictScalars (algebraMap O F)).map
          (TopCat.Presheaf.germ ((rationalSheafFunctor F X).obj M).obj U x hx) := by
  rw [integralRationalStalkMap, ← Category.assoc,
    TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
  congr 1
  exact ι_preservesColimitIso_inv
    (ModuleCat.restrictScalars (algebraMap O F))
    ((OpenNhds.inclusion x).op ⋙ ((rationalSheafFunctor F X).obj M).obj)
    (.op ⟨U, hx⟩)

variable (d : ℕ) [NeZero d] (π : O)

/-- The actual total rational stalk, retaining its F-module structure. -/
def rationalLatticeStalk (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (x : X) :
    ModuleCat.{u} F :=
  TopCat.Presheaf.stalk (rationalLattice F X d π M).obj x

namespace LatticePiSheaf

variable {d π X} (M : LatticePiSheaf d π X)

/-- The genuine rationalized inclusion of a homogeneous component. -/
def rationalInclusion (i : ZMod d) :
    M.rationalComponent F i ⟶ rationalLattice F X d π M.sheaf :=
  (rationalSheafFunctor F X).map (M.inclusion i)

/-- Each actual integral component stalk maps into the total rational stalk. -/
def componentRationalStalkMap (i : ZMod d) (x : X) :
    TopCat.Presheaf.stalk (M.component i).obj x ⟶
      (ModuleCat.restrictScalars (algebraMap O F)).obj
        (rationalLatticeStalk F X d π M.sheaf x) :=
  (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map (M.inclusion i).hom ≫
    integralRationalStalkMap F X (latticeScalarSheaf d π X M.sheaf) x

/-- The image of an actual integral component stalk is an O-submodule of total rational eta. -/
def componentStalkLattice (i : ZMod d) (x : X) :
    Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj
      (rationalLatticeStalk F X d π M.sheaf x)) :=
  LinearMap.range (M.componentRationalStalkMap F i x).hom

end LatticePiSheaf

namespace FramedLatticePiSheaf

variable {d π X} (M : FramedLatticePiSheaf d π X F)

/-- The actual rational frame followed by inclusion of degree zero into the total sheaf. -/
def frameToTotal :
    (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).obj
      (ModuleCat.of F (Fin d → F)) ⟶ rationalLattice F X d π M.lattice.sheaf :=
  M.frame.hom ≫ M.lattice.rationalInclusion F 0

/-- A constant vector gives a genuine germ through the sheafification unit and the frame. -/
def frameStalkMap (x : X) :
    ModuleCat.of F (Fin d → F) ⟶ rationalLatticeStalk F X d π M.lattice.sheaf x :=
  (toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of F (Fin d → F)))).app (.op ⊤) ≫
      (M.frameToTotal F).hom.app (.op ⊤) ≫
        TopCat.Presheaf.Γgerm (rationalLattice F X d π M.lattice.sheaf).obj x

/-- O-valued frame vectors map to the actual total rational stalk. -/
def integralFrameStalkMap (x : X) :
    (Fin d → O) →ₗ[O]
      ((ModuleCat.restrictScalars (algebraMap O F)).obj
        (rationalLatticeStalk F X d π M.lattice.sheaf x)) where
  toFun v := M.frameStalkMap F x (fun j => algebraMap O F (v j))
  map_add' v w := by
    have h : (fun j => algebraMap O F ((v + w) j)) =
        (fun j => algebraMap O F (v j)) + (fun j => algebraMap O F (w j)) := by
      funext j
      exact map_add (algebraMap O F) _ _
    rw [h]
    exact (M.frameStalkMap F x).hom.map_add _ _
  map_smul' a v := by
    change M.frameStalkMap F x (fun j => algebraMap O F ((a • v) j)) =
      algebraMap O F a • M.frameStalkMap F x (fun j => algebraMap O F (v j))
    have h : (fun j => algebraMap O F ((a • v) j)) =
        algebraMap O F a • (fun j => algebraMap O F (v j)) := by
      funext j
      exact map_mul (algebraMap O F) _ _
    rw [h]
    exact (M.frameStalkMap F x).hom.map_smul _ _

/-- The lattice r O^d inside the actual total rational stalk. -/
def frameStalkLattice (x : X) :
    Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj
      (rationalLatticeStalk F X d π M.lattice.sheaf x)) :=
  LinearMap.range (M.integralFrameStalkMap F x)

end FramedLatticePiSheaf

/-- The O-span of actual k-fold exterior products of vectors in an O-submodule of V. -/
def exteriorStalkLattice (k : ℕ) (V : ModuleCat.{u} F)
    (L : Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj V)) :
    Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj
      (ModuleCat.of F (⋀[F]^k V))) :=
  Submodule.span O
    (Set.range (fun v : Fin k → L =>
      exteriorPower.ιMulti F k (fun j => (show V from (v j).val))))

/-- Scalar multiplication of a determinant lattice, performed after taking exterior products. -/
def scaleStalkLattice (a : F) (V : ModuleCat.{u} F)
    (L : Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj V)) :
    Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj V) :=
  L.map (((ModuleCat.restrictScalars (algebraMap O F)).map
    (ModuleCat.ofHom (LinearMap.lsmul F V a))).hom)

/-- The rational total Pi automorphism on the actual stalk. -/
def rationalPiStalkAut (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (hπ : algebraMap O F π ≠ 0) (x : X) :
    Aut (rationalLatticeStalk F X d π M x) :=
  (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).mapIso
    ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).mapIso
      (rationalPiAut F X d π M hπ))

namespace FramedLatticePiSheaf

variable {d π X} (M : FramedLatticePiSheaf d π X F)

/-- The actual O-lattice Pi^n r O^d, for every integer n, including negative integers. -/
def translatedFrameStalkLattice (hπ : algebraMap O F π ≠ 0) (n : ℤ) (x : X) :
    Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj
      (rationalLatticeStalk F X d π M.lattice.sheaf x)) :=
  (M.frameStalkLattice F x).map
    (((ModuleCat.restrictScalars (algebraMap O F)).map
      ((rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ n).hom)).hom)

/-- The source's literal pi^(-n) wedge^d(Pi^n r O^d) in total rational eta. -/
def normalizedFrameDeterminant (hπ : algebraMap O F π ≠ 0) (n : ℤ) (x : X) :
    Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj
      (ModuleCat.of F (⋀[F]^d (rationalLatticeStalk F X d π M.lattice.sheaf x)))) :=
  scaleStalkLattice F (algebraMap O F π ^ (-n)) _
    (exteriorStalkLattice F d _ (M.translatedFrameStalkLattice F hπ n x))

end FramedLatticePiSheaf

open AlgebraicGeometry

namespace SheafPreDatum

variable {d π F} {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}
  (D : SheafPreDatum d π F φ)

/-- The actual degree-i determinant lattice, formed in the total rational stalk. -/
def componentDeterminant (i : ZMod d) (x : S) :
    Submodule O ((ModuleCat.restrictScalars (algebraMap O F)).obj
      (ModuleCat.of F (⋀[F]^d
        (rationalLatticeStalk F (S : TopCat) d π D.eta.lattice.sheaf x)))) :=
  exteriorStalkLattice F d _ (D.eta.lattice.componentStalkLattice F i x)

/-- Literal all-integer, stalkwise equality in Deligne's framed determinant condition (c). -/
def DeterminantNormalized (hπ : algebraMap O F π ≠ 0) : Prop :=
  ∀ (n : ℤ) (x : S), x ∈ D.tangent.graded.piZeroLocus (n : ZMod d) →
    D.componentDeterminant (n : ZMod d) x =
      D.eta.normalizedFrameDeterminant F hπ n x

end SheafPreDatum

end Langlands.DeligneFormalSpace

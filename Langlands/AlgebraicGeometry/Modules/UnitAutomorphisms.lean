import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback

/-! # The canonical action of global units on module sheaves -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Multiplication by a global unit, on an arbitrary actual module sheaf. -/
def unitAut (M : X.Modules) (r : Γ(X, ⊤)ˣ) : Aut M where
  hom := (r : Γ(X, ⊤)) • 𝟙 M
  inv := ((r⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) • 𝟙 M
  hom_inv_id := by simp [smul_smul]
  inv_hom_id := by simp [smul_smul]

@[simp]
lemma unitAut_hom (M : X.Modules) (r : Γ(X, ⊤)ˣ) :
    (unitAut M r).hom = (r : Γ(X, ⊤)) • 𝟙 M := rfl

@[simp]
lemma unitAut_inv (M : X.Modules) (r : Γ(X, ⊤)ˣ) :
    (unitAut M r).inv = ((r⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) • 𝟙 M := rfl

/-- The scalar automorphism acts by the restriction of the unit on every open. -/
lemma unitAut_hom_app (M : X.Modules) (r : Γ(X, ⊤)ˣ)
    (U : X.Opens) (s : Γ(M, U)) :
    (unitAut M r).hom.app U s = restrictScalar U (r : Γ(X, ⊤)) • s := by
  simp

/-- The global-unit action as a homomorphism to the actual automorphism group. -/
def unitAutHom (M : X.Modules) : Γ(X, ⊤)ˣ →* Aut M where
  toFun := unitAut M
  map_one' := by
    apply Aut.ext
    change (1 : Γ(X, ⊤)) • 𝟙 M = 𝟙 M
    simp
  map_mul' r s := by
    apply Aut.ext
    change ((r * s : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) • 𝟙 M =
      ((s : Γ(X, ⊤)) • 𝟙 M) ≫ ((r : Γ(X, ⊤)) • 𝟙 M)
    simp [smul_smul]

@[simp]
lemma unitAutHom_apply (M : X.Modules) (r : Γ(X, ⊤)ˣ) :
    unitAutHom M r = unitAut M r := rfl

/-- Scalar automorphisms commute with every module morphism. -/
@[reassoc]
lemma unitAut_naturality {M N : X.Modules} (φ : M ⟶ N) (r : Γ(X, ⊤)ˣ) :
    (unitAut M r).hom ≫ φ = φ ≫ (unitAut N r).hom := by simp

/-- Transport across an arbitrary module isomorphism preserves the scalar unit. -/
lemma unitAut_conjugate {M N : X.Modules} (e : M ≅ N) (r : Γ(X, ⊤)ˣ) :
    Aut.autMulEquivOfIso e (unitAut M r) = unitAut N r := by
  apply Aut.ext
  change e.inv ≫ ((r : Γ(X, ⊤)) • 𝟙 M) ≫ e.hom = _
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of multiplication by a unit uses the actual map on global functions. -/
lemma pullback_mapIso_unitAut (f : X ⟶ Y) (M : Y.Modules) (r : Γ(Y, ⊤)ˣ) :
    (Scheme.Modules.pullback f).mapIso (unitAut M r) =
      unitAut ((Scheme.Modules.pullback f).obj M)
        (Units.map f.appTop.hom.toMonoidHom r) := by
  apply Iso.ext
  change (Scheme.Modules.pullback f).map ((r : Γ(Y, ⊤)) • 𝟙 M) = _
  rw [pullback_map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- Naturality as an equality of homomorphisms, for every module sheaf. -/
lemma pullback_mapAut_unitAutHom (f : X ⟶ Y) (M : Y.Modules) :
    ((Scheme.Modules.pullback f).mapAut M).comp (unitAutHom M) =
      (unitAutHom ((Scheme.Modules.pullback f).obj M)).comp
        (Units.map f.appTop.hom.toMonoidHom) := by
  apply MonoidHom.ext
  intro r
  exact pullback_mapIso_unitAut f M r

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

variable {X Y : Scheme.{u}}

/-- The same unit automorphism in the category of actual line bundles. -/
def unitAut (L : LineBundle X) (r : Γ(X, ⊤)ˣ) : Aut L :=
  ObjectProperty.isoMk _ (Langlands.Scheme.Modules.unitAut L.obj r)

/-- The unit action on the actual line-bundle automorphism group. -/
def unitAutHom (L : LineBundle X) : Γ(X, ⊤)ˣ →* Aut L where
  toFun := unitAut L
  map_one' := by
    apply Aut.ext
    apply ObjectProperty.hom_ext
    exact congrArg Iso.hom ((Langlands.Scheme.Modules.unitAutHom L.obj).map_one)
  map_mul' r s := by
    apply Aut.ext
    apply ObjectProperty.hom_ext
    exact congrArg Iso.hom ((Langlands.Scheme.Modules.unitAutHom L.obj).map_mul r s)

@[simp]
lemma forget_mapIso_unitAut (L : LineBundle X) (r : Γ(X, ⊤)ˣ) :
    (forget X).mapIso (unitAut L r) = Langlands.Scheme.Modules.unitAut L.obj r := by
  apply Iso.ext
  rfl

/-- Pullback compatibility in the full subcategory, without quotienting objects. -/
lemma pullback_mapIso_unitAut (f : X ⟶ Y) (L : LineBundle Y) (r : Γ(Y, ⊤)ˣ) :
    (pullback f).mapIso (unitAut L r) =
      unitAut ((pullback f).obj L) (Units.map f.appTop.hom.toMonoidHom r) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (Langlands.Scheme.Modules.pullback_mapIso_unitAut f L.obj r)

end Langlands.AlgebraicGeometry.Picard.LineBundle

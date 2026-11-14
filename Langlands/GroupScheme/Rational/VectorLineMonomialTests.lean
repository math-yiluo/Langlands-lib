import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.RootActionWeights

/-! # Monomial coordinate identities on arbitrary scheme tests -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V W : GroupScheme (Spec (CommRingCat.of k))}
    (e : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (d : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ W.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (f : V ⟶ W)
    (he : IsNaturalVectorCoordinates e) (hd : IsNaturalVectorCoordinates d)

/-- The actual morphism of naturally coordinated lines defined by a scalar
monomial at the universal source point. -/
def monomialMap (c : k) (n : ℕ) : V.X ⟶ W.X :=
  (d V.X).symm (Multiplicative.ofAdd (fun _ =>
    V.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) *
      (e V.X (𝟙 V.X)).toAdd 0 ^ n))

include he hd

/-- The monomial morphism has its prescribed coordinate on every scheme test. -/
@[simp]
theorem coordinate_monomialMap (c : k) (n : ℕ)
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ V.X) :
    (d U (x ≫ monomialMap e d c n)).toAdd 0 =
      U.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) *
        (e U x).toAdd 0 ^ n := by
  have hl := congrFun (hd V.X U x (monomialMap e d c n)) 0
  rw [monomialMap, MulEquiv.apply_symm_apply] at hl
  change (d U (x ≫ monomialMap e d c n)).toAdd 0 =
    x.left.appTop (V.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) *
      (e V.X (𝟙 V.X)).toAdd 0 ^ n) at hl
  rw [map_mul, map_pow] at hl
  have hc : x.left.appTop
      (V.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      U.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
    change (x.left ≫ V.X.hom).appTop _ = _
    rw [Over.w x]
  have hr := congrFun (he V.X U x (𝟙 V.X)) 0
  rw [Category.comp_id] at hr
  rw [← hr, hc] at hl
  exact hl

/-- An affine monomial formula for a map of naturally coordinated lines is
the same formula on every scheme, with the field scalar pulled back from the base. -/
theorem coordinate_monomial_of_affine (c : k) (n : ℕ)
    (h : ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (x : Lie.AffinePoints V A),
      (vectorAffineCoordinates d A (x ≫ f.hom.hom)).toAdd 0 =
        algebraMap k A c * (vectorAffineCoordinates e A x).toAdd 0 ^ n)
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ V.X) :
    (d U (x ≫ f.hom.hom)).toAdd 0 =
      U.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) *
        (e U x).toAdd 0 ^ n := by
  have ha (A : CommAlgCat.{u} (CommRingCat.of k)) (xA : Lie.AffinePoints V A) :
      (d ((algSpec (CommRingCat.of k)).obj (op A)) (xA ≫ f.hom.hom)).toAdd 0 =
        ((algSpec (CommRingCat.of k)).obj (op A)).hom.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) *
            (e ((algSpec (CommRingCat.of k)).obj (op A)) xA).toAdd 0 ^ n := by
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom _ =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom _
    rw [map_mul, map_pow]
    have hc :
        ((algSpec (CommRingCat.of k)).obj (op A)).hom.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) =
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) :=
      (ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A))) c).symm
    rw [hc, Iso.inv_hom_id_apply]
    exact h A xA
  let : IsAffineHom V.X.hom := IsVectorGroupOfDimension.isAffineHom ⟨e, he⟩
  let : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  have hV : (algSpec (CommRingCat.of k)).essImage V.X := essImage_algSpec.mpr this
  let A := hV.witness.unop
  let φ : (algSpec (CommRingCat.of k)).obj (op A) ≅ V.X := hV.getIso
  have hu := ha A φ.hom
  have hleft := congrFun (hd V.X _ φ.hom f.hom.hom) 0
  have hright := congrFun (he V.X _ φ.hom (𝟙 V.X)) 0
  rw [Category.comp_id] at hright
  rw [hleft, hright] at hu
  have hcφ : φ.hom.left.appTop
      (V.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      ((algSpec (CommRingCat.of k)).obj (op A)).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
    change (φ.hom.left ≫ V.X.hom).appTop _ = _
    rw [Over.w φ.hom]
  have hUniversal :
      (d V.X f.hom.hom).toAdd 0 =
        V.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) *
          (e V.X (𝟙 V.X)).toAdd 0 ^ n := by
    apply (ConcreteCategory.bijective_of_isIso φ.hom.left.appTop).1
    rw [map_mul, map_pow, hcφ]
    exact hu
  have hpull := congrArg (fun z => x.left.appTop z) hUniversal
  rw [map_mul, map_pow] at hpull
  have hc : x.left.appTop
      (V.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      U.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
    change (x.left ≫ V.X.hom).appTop _ = _
    rw [Over.w x]
  have hl := congrFun (hd V.X U x f.hom.hom) 0
  have hr := congrFun (he V.X U x (𝟙 V.X)) 0
  rw [Category.comp_id] at hr
  rw [← hr, hc] at hpull
  exact hl.trans hpull

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.GroupScheme.VectorGroup

variable {k : Type u} [Field k]

local notation "R" => CommRingCat.of k
local notation "V" => groupScheme R 1
local notation "coords" => coordinates R 1

/-- An affine monomial formula for an actual additive-group map computes its
value at every global-function point of every scheme test. -/
theorem scalarPoint_comp_of_affine_monomial (f : V ⟶ V) (c : k) (n : ℕ)
    (h : ∀ (A : CommAlgCat.{u} R) (x : Lie.AffinePoints V A),
      (RelativeRoot.vectorAffineCoordinates coords A (x ≫ f.hom.hom)).toAdd 0 =
        algebraMap k A c *
          (RelativeRoot.vectorAffineCoordinates coords A x).toAdd 0 ^ n)
    (U : Over (Spec R)) (a : Γ(U.left, ⊤)) :
    scalarPoint R U a ≫ f.hom.hom =
      scalarPoint R U
        (U.hom.appTop ((Scheme.ΓSpecIso R).inv c) * a ^ n) := by
  have hm := RelativeRoot.coordinate_monomial_of_affine coords coords f
    isNaturalVectorCoordinates isNaturalVectorCoordinates c n h U (scalarPoint R U a)
  rw [coordinates_scalarPoint] at hm
  apply points_ext
  intro j
  rw [coordinates_scalarPoint, Subsingleton.elim j 0]
  exact hm

end Langlands.GroupScheme.VectorGroup

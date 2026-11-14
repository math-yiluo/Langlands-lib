import Langlands.GroupScheme.Absolute.CocharacterDescentGroup
import Mathlib.FieldTheory.Galois.Infinite

/-! # Descent of invariant cocharacters along a possibly infinite Galois extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.InfiniteGaloisCocharacterDescent

open Langlands.GroupScheme.GaloisCocharacterDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- A Laurent polynomial over a (possibly infinite) Galois extension comes from the
base field exactly when it is fixed by every automorphism. -/
theorem mem_range_extend_iff (p : LaurentPolynomial K) :
    p ∈ Set.range (LaurentGaloisDescent.extend k K) ↔
      ∀ σ : K ≃ₐ[k] K, LaurentGaloisDescent.conjugate k K σ p = p := by
  constructor
  · rintro ⟨q, rfl⟩ σ
    exact LaurentGaloisDescent.conjugate_extend k K σ q
  · intro h
    change p ∈ Set.range (AddMonoidAlgebra.map (algebraMap k K).toAddMonoidHom)
    rw [AddMonoidAlgebra.range_map]
    intro m
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (p.coeff m)).mpr
    intro σ
    exact congrArg (fun q : LaurentPolynomial K => q.coeff m) (h σ)

section RingHom

variable {A : Type v} [CommRing A] (f : A →+* LaurentPolynomial K)
  (hf : ∀ (σ : K ≃ₐ[k] K) (x : A), LaurentGaloisDescent.conjugate k K σ (f x) = f x)

/-- The unique polynomial over `k` extending to a specified invariant coordinate. -/
def descendValue (x : A) : LaurentPolynomial k :=
  ((mem_range_extend_iff k K (f x)).mpr (fun σ => hf σ x)).choose

@[simp] theorem extend_descendValue (x : A) :
    LaurentGaloisDescent.extend k K (descendValue k K f hf x) = f x :=
  ((mem_range_extend_iff k K (f x)).mpr (fun σ => hf σ x)).choose_spec

/-- An invariant Laurent-valued ring map descends to the base field. -/
def descendRingHom : A →+* LaurentPolynomial k where
  toFun := descendValue k K f hf
  map_one' := (LaurentGaloisDescent.extend_injective k K) (by simp)
  map_mul' x y := (LaurentGaloisDescent.extend_injective k K) (by simp)
  map_zero' := (LaurentGaloisDescent.extend_injective k K) (by simp)
  map_add' x y := (LaurentGaloisDescent.extend_injective k K) (by simp)

@[simp] theorem extend_descendRingHom (x : A) :
    LaurentGaloisDescent.extend k K (descendRingHom k K f hf x) = f x :=
  extend_descendValue k K f hf x

end RingHom

section AlgHom

variable {A : Type v} [CommRing A] [Algebra k A] (f : A →ₐ[k] LaurentPolynomial K)
  (hf : ∀ (σ : K ≃ₐ[k] K) (x : A), LaurentGaloisDescent.conjugate k K σ (f x) = f x)

/-- The descended map retains the algebra structure over the original field. -/
def descendAlgHom : A →ₐ[k] LaurentPolynomial k where
  __ := descendRingHom k K f.toRingHom hf
  commutes' r := by
    apply LaurentGaloisDescent.extend_injective k K
    change LaurentGaloisDescent.extend k K
        (descendRingHom k K f.toRingHom hf (algebraMap k A r)) =
      LaurentGaloisDescent.extend k K (algebraMap k (LaurentPolynomial k) r)
    rw [extend_descendRingHom]
    change f (algebraMap k A r) =
      LaurentGaloisDescent.extend k K (algebraMap k (LaurentPolynomial k) r)
    rw [f.commutes]
    change AddMonoidAlgebra.single 0 (algebraMap k K r) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap k K) (AddMonoidAlgebra.single 0 r)
    exact (AddMonoidAlgebra.mapRingHom_single (algebraMap k K) 0 r).symm

@[simp] theorem extend_descendAlgHom (x : A) :
    LaurentGaloisDescent.extend k K (descendAlgHom k K f hf x) = f x :=
  extend_descendRingHom k K f.toRingHom hf x

end AlgHom

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
    (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
  (hν : IsInvariant k K G ν)

/-- The Laurent coordinate map descended coefficient by coefficient. -/
def descendedCoordinates : Lie.coordinateAlgebra G →ₐ[k] LaurentPolynomial k :=
  descendAlgHom k K (coordinates k K G ν) (coordinates_fixed k K G ν hν)

theorem extend_comp_descendedCoordinates :
    (extendAlg k K).comp (descendedCoordinates k K G ν hν) = coordinates k K G ν := by
  apply AlgHom.ext
  intro c
  exact extend_descendAlgHom k K (coordinates k K G ν) (coordinates_fixed k K G ν hν) c

/-- The descended coordinates as an actual affine Laurent point of the original group. -/
def descendedPoint : Lie.AffinePoints G (LaurentPolynomial k) :=
  (Lie.pointCoordinates G).symm (descendedCoordinates k K G ν hν)

theorem pointCoordinates_descendedPoint :
    Lie.pointCoordinates G (descendedPoint k K G ν hν) =
      descendedCoordinates k K G ν hν :=
  (Lie.pointCoordinates G).apply_symm_apply _

/-- Extending the descended point recovers the given cocharacter on the universal unit. -/
theorem extend_descendedPoint :
    Lie.affineMap G (extendAlg k K) (descendedPoint k K G ν hν) =
      universalValue k K G ν := by
  apply (Lie.pointCoordinates G).injective
  rw [Lie.pointCoordinates_naturality, pointCoordinates_descendedPoint,
    extend_comp_descendedCoordinates]
  rfl

/-- The scheme morphism obtained from the descended Laurent point. -/
def descendedMorphism : (Gm (Spec (CommRingCat.of k))).X ⟶ G.X :=
  (Gm.relativeLaurentIso (CommRingCat.of k)).hom ≫
    (laurentAffineIso k).inv ≫ descendedPoint k K G ν hν

theorem laurentPoint_descendedMorphism :
    Gm.laurentPoint k ≫ descendedMorphism k K G ν hν =
      (laurentAffineIso k).inv ≫ descendedPoint k K G ν hν := by
  simp only [descendedMorphism, Gm.laurentPoint, Iso.inv_hom_id_assoc]

/-- The base change of the descended scheme morphism is the original cocharacter. -/
theorem baseChangedMorphism_descendedMorphism :
    baseChangedMorphism k K G (descendedMorphism k K G ν hν) = ν.hom.hom := by
  apply (cancel_epi (Gm.relativeLaurentIso (CommRingCat.of K)).inv).mp
  apply (baseChangePointsEquiv (algebraBaseMap k K) G
    (Gm.relativeLaurent (CommRingCat.of K))).injective
  apply (cancel_epi (laurentBaseIso k K).hom).mp
  change (laurentBaseIso k K).hom ≫
      baseChangePointsEquiv (algebraBaseMap k K) G _
        (Gm.laurentPoint K ≫ baseChangedMorphism k K G (descendedMorphism k K G ν hν)) =
    universalValue k K G ν
  rw [baseChangedMorphism_universal, laurentPoint_descendedMorphism]
  simp only [Iso.hom_inv_id_assoc]
  exact extend_descendedPoint k K G ν hν

/-- Recovery expressed on the ordinary pullback before the Gm comparison. -/
theorem pullback_descendedMorphism :
    (Over.pullback (algebraBaseMap k K)).map (descendedMorphism k K G ν hν) =
      (Gm.baseChangeIso (algebraBaseMap k K)).hom.hom.hom ≫ ν.hom.hom := by
  apply (cancel_epi (Gm.baseChangeIso (algebraBaseMap k K)).inv.hom.hom).mp
  change baseChangedMorphism k K G (descendedMorphism k K G ν hν) = _
  rw [baseChangedMorphism_descendedMorphism]
  change ν.hom.hom =
    ((Gm.baseChangeIso (algebraBaseMap k K)).inv ≫
      (Gm.baseChangeIso (algebraBaseMap k K)).hom ≫ ν).hom.hom
  rw [Iso.inv_hom_id_assoc]

/-- The descended scheme morphism preserves the group laws. -/
theorem descendedMorphism_isMonHom :
    IsMonHom (descendedMorphism k K G ν hν) := by
  let := faithful_algebraPullback k K
  have : IsMonHom
      ((Over.pullback (algebraBaseMap k K)).map (descendedMorphism k K G ν hν)) := by
    rw [pullback_descendedMorphism]
    infer_instance
  exact isMonHom_of_faithfulMap (Over.pullback (algebraBaseMap k K)) _

/-- The actual group-scheme cocharacter descended to the original field. -/
def descend :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
  letI := descendedMorphism_isMonHom k K G ν hν
  Grp.homMk (descendedMorphism k K G ν hν)

/-- Base change of the descended cocharacter recovers the original one. -/
theorem baseChange_descend :
    (Gm.baseChangeIso (algebraBaseMap k K)).inv ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map (descend k K G ν hν) = ν := by
  apply Grp.hom_ext
  exact baseChangedMorphism_descendedMorphism k K G ν hν

end Langlands.GroupScheme.InfiniteGaloisCocharacterDescent

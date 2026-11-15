import Langlands.AlgebraicGeometry.Picard.PicardZeroArtinianLiftingReduction
import Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingStatement
import Langlands.AbelianScheme.BaseChangeCoherence

/-! # Artinian lifting of Picard-zero families from lifting of primitive line bundles -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.PicardZeroArtinianLiftingReduction

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

section Primitive

variable {T : Scheme.{u}}

/-- A line bundle `L` on an abelian scheme `X` is primitive if `m^*L ≅ p₁^*L ⊗ p₂^*L` on
`X ×_T X`, where `m` is the group law and `p₁`, `p₂` are the projections. -/
def IsPrimitiveLineBundle (X : AbelianScheme T) (L : LineBundle X.X.left) : Prop :=
  let P : Over T := X.X ⨯ X.X
  let p1 : P ⟶ X.X := Limits.prod.fst
  let p2 : P ⟶ X.X := Limits.prod.snd
  let m : P ⟶ X.X := p1 * p2
  Nonempty ((Scheme.Modules.pullback m.left).obj L.obj ≅
    tensorObj ((Scheme.Modules.pullback p1.left).obj L.obj)
      ((Scheme.Modules.pullback p2.left).obj L.obj))

/-- Pull back an isomorphism `m^*M ≅ p^*M ⊗ q^*M` along a map `F` intertwining `m`, `p`, `q`
with `m'`, `p'`, `q'` through `g`. -/
lemma nonempty_tensor_iso_of_comp_eq {P Q Y Z : Scheme.{u}} (F : P ⟶ Q) (g : Y ⟶ Z)
    (m p q : Q ⟶ Z) (m' p' q' : P ⟶ Y) (hm : m' ≫ g = F ≫ m) (hp : p' ≫ g = F ≫ p)
    (hq : q' ≫ g = F ≫ q) (M : Z.Modules)
    (e : (Scheme.Modules.pullback m).obj M ≅
      tensorObj ((Scheme.Modules.pullback p).obj M) ((Scheme.Modules.pullback q).obj M)) :
    Nonempty ((Scheme.Modules.pullback m').obj ((Scheme.Modules.pullback g).obj M) ≅
      tensorObj ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj M))
        ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback g).obj M))) := by
  have : IsIso (pullbackTensorComparison F) := pullbackTensorComparisonIsIso F
  let c : ∀ (r : Q ⟶ Z) (r' : P ⟶ Y), r' ≫ g = F ≫ r →
      ((Scheme.Modules.pullback F).obj ((Scheme.Modules.pullback r).obj M) ≅
        (Scheme.Modules.pullback r').obj ((Scheme.Modules.pullback g).obj M)) :=
    fun r r' h ↦ (Scheme.Modules.pullbackComp F r).app M ≪≫
      (Scheme.Modules.pullbackCongr h.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp r' g).app M).symm
  refine ⟨(c m m' hm).symm ≪≫ (Scheme.Modules.pullback F).mapIso e ≪≫
    asIso ((pullbackTensorComparison F).app
      ((Scheme.Modules.pullback p).obj M, (Scheme.Modules.pullback q).obj M)) ≪≫ ?_⟩
  exact
    { hom := tensorMap (c p p' hp).hom (c q q' hq).hom
      inv := tensorMap (c p p' hp).inv (c q q' hq).inv
      hom_inv_id := by
        rw [tensorMap_comp, Iso.hom_inv_id, Iso.hom_inv_id]
        exact (tensorFunctor P).map_id _
      inv_hom_id := by
        rw [tensorMap_comp, Iso.inv_hom_id, Iso.inv_hom_id]
        exact (tensorFunctor P).map_id _ }

/-- Primitivity pulls back along homomorphisms of abelian schemes. -/
lemma isPrimitiveLineBundle_pullback {X Y : AbelianScheme T} (f : X ⟶ Y)
    (L : LineBundle Y.X.left) (hL : IsPrimitiveLineBundle Y L) :
    IsPrimitiveLineBundle X ((LineBundle.pullback (hom f)).obj L) := by
  obtain ⟨e⟩ := hL
  let g : X.X ⟶ Y.X := (groupHom f).hom.hom
  let F : X.X ⨯ X.X ⟶ Y.X ⨯ Y.X := Limits.prod.map g g
  have hp : (Limits.prod.fst : X.X ⨯ X.X ⟶ X.X) ≫ g = F ≫ Limits.prod.fst := by
    simp [F]
  have hq : (Limits.prod.snd : X.X ⨯ X.X ⟶ X.X) ≫ g = F ≫ Limits.prod.snd := by
    simp [F]
  have hm : ((Limits.prod.fst : X.X ⨯ X.X ⟶ X.X) * Limits.prod.snd) ≫ g =
      F ≫ ((Limits.prod.fst : Y.X ⨯ Y.X ⟶ Y.X) * Limits.prod.snd) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, hp, hq]
  exact nonempty_tensor_iso_of_comp_eq F.left g.left _ _ _ _ _ _
    (congrArg CommaMorphism.left hm) (congrArg CommaMorphism.left hp)
    (congrArg CommaMorphism.left hq) L.obj e

end Primitive

section Transport

variable {S : Scheme.{u}} (A : AbelianScheme S) {B' B : Type u} [CommRing B'] [CommRing B]

/-- `totalSpaceMap` is the composition comparison of base changes followed by the first
projection `(A ×_S Spec B') ×_{Spec B'} Spec B ⟶ A ×_S Spec B'`. -/
lemma totalSpaceMap_eq (φ : B' →+* B) (β : Spec (CommRingCat.of B') ⟶ S) :
    (hom (baseChangeCompIso β (Spec.map (CommRingCat.ofHom φ)) A).hom :
        Limits.pullback A.X.hom (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶
          Limits.pullback (Limits.pullback.snd A.X.hom β) (Spec.map (CommRingCat.ofHom φ))) ≫
      Limits.pullback.fst (Limits.pullback.snd A.X.hom β) (Spec.map (CommRingCat.ofHom φ)) =
      totalSpaceMap A φ β := by
  let j := Spec.map (CommRingCat.ofHom φ)
  let u : Limits.pullback A.X.hom (j ≫ β) ⟶ Limits.pullback (Limits.pullback.snd A.X.hom β) j :=
    hom (baseChangeCompIso β j A).hom
  let v : Limits.pullback (Limits.pullback.snd A.X.hom β) j ⟶ Limits.pullback A.X.hom (j ≫ β) :=
    hom (baseChangeCompIso β j A).inv
  have huv : u ≫ v = 𝟙 _ := by
    change hom ((baseChangeCompIso β j A).hom ≫ (baseChangeCompIso β j A).inv) = _
    rw [Iso.hom_inv_id]
    rfl
  have hfst : v ≫ Limits.pullback.fst A.X.hom (j ≫ β) =
      Limits.pullback.fst (Limits.pullback.snd A.X.hom β) j ≫ Limits.pullback.fst A.X.hom β :=
    GroupScheme.baseChangeCompIso_inv_fst β j A.toGrp
  have hsnd : u ≫ Limits.pullback.snd (Limits.pullback.snd A.X.hom β) j =
      Limits.pullback.snd A.X.hom (j ≫ β) :=
    Over.w (GroupScheme.baseChangeCompIso β j A.toGrp).hom.hom.hom
  change u ≫ Limits.pullback.fst (Limits.pullback.snd A.X.hom β) j = totalSpaceMap A φ β
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, ← hfst, ← Category.assoc, huv, Category.id_comp]
    exact ((Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm
  · rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd]
    exact (Limits.pullback.lift_snd _ _ _).symm

end Transport

/-- If primitive line bundles lift along elementary Artinian thickenings and every
geometrically Picard-zero line bundle over a local Artinian base is primitive, then the
underlying line bundle of every Picard-zero family over `Spec B` lifts along
`totalSpaceMap`. -/
theorem familyLineBundle_lift_of_primitive
    (hP : ArtinianPrimitiveLineBundleLiftingStatement.{u})
    (hQ : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
      (X : AbelianScheme (Spec (CommRingCat.of B))) (L : LineBundle X.X.left),
        IsGeometricallyPicardZero X L → IsPrimitiveLineBundle X L)
    (S : Scheme.{u}) (A : AbelianScheme S) (B' B : Type u) [CommRing B']
    [CommRing B] [IsLocalRing B'] [IsLocalRing B] [IsArtinianRing B'] [IsArtinianRing B]
    (φ : B' →+* B) (hφ : Function.Surjective φ) (hker : maximalIdeal B' * RingHom.ker φ = ⊥)
    (β : Spec (CommRingCat.of B') ⟶ S)
    (M : RigidifiedFamily A (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β)))
    (hM : IsPicardZeroFamily A M) :
    ∃ L' : LineBundle ((baseChange β).obj A).X.left,
      Nonempty ((LineBundle.pullback (totalSpaceMap A φ β)).obj L' ≅
        familyLineBundle (T := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β)) A M) := by
  let j := Spec.map (CommRingCat.ofHom φ)
  let L := familyLineBundle (T := Over.mk (j ≫ β)) A M
  let e := baseChangeCompIso β j A
  have hL : IsPrimitiveLineBundle ((baseChange (j ≫ β)).obj A) L := hQ B _ L hM
  have hL₀ := isPrimitiveLineBundle_pullback e.inv L hL
  obtain ⟨L', ⟨e'⟩⟩ := hP B' B φ hφ hker ((baseChange β).obj A) _ hL₀
  refine ⟨L', ⟨?_⟩⟩
  exact (LineBundle.pullbackCompEqIso _ _ (totalSpaceMap_eq A φ β) L').symm ≪≫
    (LineBundle.pullback (hom e.hom)).mapIso e' ≪≫
    LineBundle.pullbackCompEqIso (hom e.hom) (hom e.inv)
      (by rw [← hom_comp, Iso.hom_inv_id, hom_id]; rfl) L ≪≫
    (LineBundle.pullbackId _).app L

/-- The target statement follows from the lifting of primitive line bundles and the
primitivity of geometrically Picard-zero line bundles over local Artinian bases. -/
theorem picardZeroArtinianLifting_of_primitive
    (hP : ArtinianPrimitiveLineBundleLiftingStatement.{u})
    (hQ : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
      (X : AbelianScheme (Spec (CommRingCat.of B))) (L : LineBundle X.X.left),
        IsGeometricallyPicardZero X L → IsPrimitiveLineBundle X L) :
    PicardZeroArtinianLiftingStatement.{u} :=
  picardZeroArtinianLifting_of_familyLineBundle_lift (familyLineBundle_lift_of_primitive hP hQ)

end Langlands.AbelianScheme.PicardZeroArtinianLiftingReduction

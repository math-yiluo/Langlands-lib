import Langlands.GroupScheme.Rational.VectorHomogeneousCoordinates
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # All-test homogeneous coordinates for actual linear torus actions -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V} {d : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))}

/-- The affine diagonal formula extends to every test scheme. -/
theorem IsLinearVectorCoordinates.homogeneous_action
    (hb : IsLinearVectorCoordinates b e)
    [IsAffineHom S.X.hom] (q : HomogeneousLieBasis b (𝟙 S.toGrp))
    (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ V.X)
    (i : Fin q.dimension) :
    (vectorCoordinatesInBasis e hb.1 q.basis T (b.act s x)).toAdd i =
      (Gm.pointsEquiv _ T (s ≫ (CommGroupScheme.groupHom (q.weight i)).hom.hom) :
        Γ(T.left, ⊤)) *
      (vectorCoordinatesInBasis e hb.1 q.basis T x).toAdd i := by
  let c := vectorCoordinatesInBasis e hb.1 q.basis
  have hc : IsNaturalVectorCoordinates c := vectorCoordinatesInBasis_natural e hb.1 q.basis
  let χ := (CommGroupScheme.groupHom (q.weight i)).hom.hom
  have ha (A : CommAlgCat.{u} (CommRingCat.of k))
      (sA : Lie.AffinePoints S.toGrp A) (xA : Lie.AffinePoints V A) :
      (c _ (b.act sA xA)).toAdd i =
        (Gm.pointsEquiv _ _ (sA ≫ χ) : Γ(_, ⊤)) * (c _ xA).toAdd i := by
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    rw [map_mul]
    exact hb.homogeneous_affine_action q A sA xA i
  let P := S.X ⊗ V.X
  let : IsAffine S.X.left := isAffine_of_isAffineHom S.X.hom
  let : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  have : IsAffine P.left := by
    change IsAffine (CategoryTheory.Limits.pullback S.X.hom V.X.hom)
    infer_instance
  have hP : (algSpec (CommRingCat.of k)).essImage P := essImage_algSpec.mpr this
  let A := hP.witness.unop
  let φ : (algSpec (CommRingCat.of k)).obj (op A) ≅ P := hP.getIso
  have hu := ha A (φ.hom ≫ fst S.X V.X) (φ.hom ≫ snd S.X V.X)
  rw [← b.naturality, hc, hc] at hu
  simp only [Category.assoc, Gm.pointsEquiv_naturality, Units.coe_map] at hu
  have hUniversal :
      (c P (b.act (fst S.X V.X) (snd S.X V.X))).toAdd i =
        (Gm.pointsEquiv _ P (fst S.X V.X ≫ χ) : Γ(P.left, ⊤)) *
          (c P (snd S.X V.X)).toAdd i := by
    apply (ConcreteCategory.bijective_of_isIso φ.hom.left.appTop).1
    rw [map_mul]
    exact hu
  have h := congrArg (fun z => (lift s x).left.appTop z) hUniversal
  rw [map_mul] at h
  have hχ := congrArg Units.val (Gm.pointsEquiv_naturality _ (lift s x) (fst S.X V.X ≫ χ))
  simp only [← Category.assoc, lift_fst, Units.coe_map] at hχ
  change (Gm.pointsEquiv _ T (s ≫ χ) : Γ(T.left, ⊤)) =
    (lift s x).left.appTop
      (Gm.pointsEquiv _ P (fst S.X V.X ≫ χ) : Γ(P.left, ⊤)) at hχ
  rw [← hχ] at h
  have hl := congrFun (hc P T (lift s x) (b.act (fst S.X V.X) (snd S.X V.X))) i
  have hr := congrFun (hc P T (lift s x) (snd S.X V.X)) i
  rw [b.naturality, lift_fst, lift_snd] at hl
  rw [lift_snd] at hr
  rw [← hr] at h
  exact hl.trans h

/-- Natural finite coordinates in which the original action is diagonal by
actual characters on every test scheme. -/
structure HomogeneousVectorCoordinates (b : AutomorphicAction S.toGrp V) where
  dimension : ℕ
  coordinates : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ V.X) ≃* Multiplicative (Fin dimension → Γ(T.left, ⊤))
  weight : Fin dimension → characterLattice S
  naturality : IsNaturalVectorCoordinates coordinates
  action : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ V.X)
    (i : Fin dimension),
    (coordinates T (b.act s x)).toAdd i =
      (Gm.pointsEquiv _ T (s ≫ (CommGroupScheme.groupHom (weight i)).hom.hom) :
        Γ(T.left, ⊤)) * (coordinates T x).toAdd i

/-- Every actual linear split-torus action admits all-test homogeneous vector
coordinates, with no restriction on characteristic or dimension. -/
def IsLinearVectorCoordinates.homogeneousCoordinates
    (hb : IsLinearVectorCoordinates b e) (hS : IsSplitTorus S.toGrp) :
    HomogeneousVectorCoordinates b := by
  letI : IsAffineHom S.X.hom := hS.isAffineHom
  let q := (finiteLieCoordinatesOfVector e hb.1).homogeneousBasis hS b (𝟙 S.toGrp)
  exact {
    dimension := q.dimension
    coordinates := vectorCoordinatesInBasis e hb.1 q.basis
    weight := q.weight
    naturality := vectorCoordinatesInBasis_natural e hb.1 q.basis
    action := hb.homogeneous_action q }

end Langlands.GroupScheme.RelativeRoot

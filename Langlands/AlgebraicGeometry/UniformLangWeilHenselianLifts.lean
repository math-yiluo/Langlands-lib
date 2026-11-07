import Langlands.AlgebraicGeometry.UniformLangWeilFiniteFields
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothPointLifting

/-! # Uniform integral lifts over Henselian local rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- One constant controls lifts over all Henselian local rings with a finite
residue-field quotient larger than its square. -/
def uniformLangWeilLargeHenselianPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (B Y : Scheme.{u}) (f : Y ⟶ B) (d : ℕ)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B))
    (hBqc : CompactSpace B) (hsmooth : Smooth f)
    (hsep : _root_.AlgebraicGeometry.IsSeparated f) (hsurj : Surjective f)
    (hft : LocallyOfFiniteType f) (hqc : QuasiCompact f)
    (hconn : GeometricallyConnected f)
    (hdim : ∀ b : B, SchemeFiberGeometry.HasPureDimension (f.fiber b) d) :
    Σ C : {C : ℝ // 0 < C},
      (R : Type u) → [CommRing R] → [HenselianLocalRing R] →
        (K : Type u) → [Field K] → [Finite K] → [Algebra R K] →
        Function.Surjective (algebraMap R K) → C.1 ^ 2 < (Nat.card K : ℝ) →
        (p : Spec (CommRingCat.of R) ⟶ B) →
        {a : Spec (CommRingCat.of R) ⟶ Y // a ≫ f = p} := by
  classical
  let := hsmooth
  let lifts := uniformLangWeilLargeFiniteFieldPointLifts hLW B Y f d hBft hBqc
    hsmooth hsep hsurj hft hqc hconn hdim
  refine ⟨lifts.1, fun R _ _ K _ _ _ hK hlarge p => ?_⟩
  let q := lifts.2 K (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ p) hlarge
  let h := PointTopology.exists_smooth_lift_of_residue_point hK f p q.1 q.2
  exact ⟨h.choose, h.choose_spec.1⟩

namespace PointTopology

/-- The uniform integral lifts retain an arbitrary original coefficient base
and use the actual relative scheme-point type. -/
def uniformLangWeilLargeHenselianRingPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (C : Type u) [CommRing C] (B Y : Over (Spec (CommRingCat.of C)))
    (f : Y ⟶ B) (d : ℕ)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left))
    (hBqc : CompactSpace B.left) (hsmooth : Smooth f.left)
    (hsep : _root_.AlgebraicGeometry.IsSeparated f.left) (hsurj : Surjective f.left)
    (hft : LocallyOfFiniteType f.left) (hqc : QuasiCompact f.left)
    (hconn : GeometricallyConnected f.left)
    (hdim : ∀ b : B.left, SchemeFiberGeometry.HasPureDimension (f.left.fiber b) d) :
    Σ c : {c : ℝ // 0 < c},
      (R : Type u) → [CommRing R] → [HenselianLocalRing R] → [Algebra C R] →
        (K : Type u) → [Field K] → [Finite K] → [Algebra C K] →
        (φ : R →ₐ[C] K) → Function.Surjective φ → c.1 ^ 2 < (Nat.card K : ℝ) →
        (p : RingPoint C B R) → {a : RingPoint C Y R // a ≫ f = p} := by
  classical
  let lifts := uniformLangWeilLargeHenselianPointLifts hLW B.left Y.left f.left d
    hBft hBqc hsmooth hsep hsurj hft hqc hconn hdim
  refine ⟨lifts.1, fun R _ _ _ K _ _ _ φ hφ hlarge p => ?_⟩
  let : Algebra R K := φ.toRingHom.toAlgebra
  let a := lifts.2 R K hφ hlarge p.left
  let aR : RingPoint C Y R := Over.homMk a.1 (by
    change a.1 ≫ Y.hom = Spec.algebraMap C R
    rw [← Over.w f, ← Category.assoc, a.2]
    exact Over.w p)
  exact ⟨aR, RingPoint.ext C a.2⟩

end PointTopology
end Langlands.AlgebraicGeometry

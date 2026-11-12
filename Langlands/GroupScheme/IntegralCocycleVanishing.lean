import Langlands.GroupScheme.CocycleTorsor
import Langlands.GroupScheme.IntegralTorsorPoint

/-! # Vanishing of cocycles of smooth groups with connected special fibre over complete rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The base equation of a point of a scheme over `Spec C` with values in `C` itself says that it
is a section of the structure map. -/
theorem ringPoint_self_left_comp {C : Type u} [CommRing C] {X : Over (Spec (CommRingCat.of C))}
    (p : Langlands.AlgebraicGeometry.PointTopology.RingPoint C X C) :
    p.left ≫ X.hom = 𝟙 _ := by
  rw [Over.w p]
  change Spec.map (CommRingCat.ofHom (algebraMap C C)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- **Integral cocycle vanishing.** Let `R` be complete for a maximal ideal `I` with finite
residue ring `R ⧸ I`, and let `H` be a smooth affine group scheme over `Spec R` with connected
special fibre. Then every actual natural cocycle of `H` on an affine flat surjective cover of
`Spec R` is a coboundary. -/
def IntegralCocycleVanishingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) [I.IsMaximal] [Finite (R ⧸ I)] [IsAdicComplete I R]
    (H : GroupScheme (Spec (CommRingCat.of R))) [Smooth H.X.hom] [IsAffineHom H.X.hom],
    ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H).X.left →
    ∀ (U : Over (Spec (CommRingCat.of R))) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
      (ξ : Cocycle H U), ξ.IsTrivial

theorem integralCocycleVanishing : IntegralCocycleVanishingStatement.{u} := by
  intro R _ I _ _ _ H _ _ hconn U _ _ _ ξ
  let := CocycleTorsor.modObj ξ
  have hiso := CocycleTorsor.isIso_leftSMul ξ
  have : Smooth (CocycleTorsor.torsor ξ).hom := CocycleTorsor.smooth_hom ξ
  let p := IntegralTorsorPoint.integralTorsorPoint R I H (CocycleTorsor.torsor ξ) hconn
    inferInstance (CocycleTorsor.surjective_hom ξ) inferInstance hiso
  exact Cocycle.isTrivial_of_torsor_section hiso ξ (CocycleTorsor.point ξ)
    (fun a b => CocycleTorsor.toFun_smul_point ξ a b) p.left (ringPoint_self_left_comp p)

/-- **Lang's theorem for cocycles.** Every actual natural cocycle of a smooth connected affine
group scheme over a finite field, on an affine flat surjective cover, is a coboundary. -/
def FiniteFieldCocycleVanishingStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [Smooth H.X.hom] [IsAffineHom H.X.hom],
    ConnectedSpace H.X.left →
    ∀ (U : Over (Spec (CommRingCat.of k))) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
      (ξ : Cocycle H U), ξ.IsTrivial

theorem finiteFieldCocycleVanishing : FiniteFieldCocycleVanishingStatement.{u} := by
  intro k _ _ H _ _ hconn U _ _ _ ξ
  let := CocycleTorsor.modObj ξ
  have hiso := CocycleTorsor.isIso_leftSMul ξ
  have : Smooth (CocycleTorsor.torsor ξ).hom := CocycleTorsor.smooth_hom ξ
  obtain ⟨p⟩ := finiteFieldTorsorPointStatement k H hconn (CocycleTorsor.torsor ξ)
    inferInstance (CocycleTorsor.surjective_hom ξ) inferInstance hiso
  exact Cocycle.isTrivial_of_torsor_section hiso ξ (CocycleTorsor.point ξ)
    (fun a b => CocycleTorsor.toFun_smul_point ξ a b) p.left (ringPoint_self_left_comp p)

end Langlands.GroupScheme

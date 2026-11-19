import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldSchemePoints
import Langlands.GroupScheme.CentralIsogeny.GaloisCocycleLifting
import Langlands.GroupScheme.GaloisCocycleRefinement
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction

/-! # Simultaneous coefficient lifting through a central isogeny -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.IsCentralIsogeny

open Langlands.AlgebraicGeometry.AlgebraicSpace.FieldSchemePoints

set_option backward.isDefEq.respectTransparency false

variable {k L : Type u} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))} {f : G ⟶ H} (hf : IsCentralIsogeny f)

/-- The actual scheme fibre of a homomorphism over a target coefficient point. -/
def coefficientLiftFiber (f : G ⟶ H) (a : H.affinePoints (CommAlgCat.of k L)) : Scheme.{u} :=
  pullback a.left f.hom.hom.left

include hf in
/-- A finite family of points lifts through a central isogeny after a single finite Galois
extension of the base in characteristic zero. -/
theorem exists_finiteGalois_coefficient_lifts [CharZero k] {I : Type v} [Finite I]
    (a : I → H.affinePoints (CommAlgCat.of k L)) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : FiniteDimensional k E) (_ : IsGalois k E)
      (_ : Algebra L E) (_ : IsScalarTower k L E),
      ∀ i, ∃ b : G.affinePoints (CommAlgCat.of k E),
        G.affinePointsTarget f (CommAlgCat.of k E) b =
          GaloisPoint.relativeExtend k L E H (a i) := by
  classical
  let X (i : I) := coefficientLiftFiber f (a i)
  let π (i : I) : X i ⟶ Spec (CommRingCat.of L) := pullback.fst (a i).left f.hom.hom.left
  let : IsFinite f.hom.hom.left := hf.isFinite
  let : Surjective f.hom.hom.left := hf.surjective
  let hft (i : I) : LocallyOfFiniteType (π i) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst (a i).left f.hom.hom.left))
  have hpoint (i : I) : ∃ x : X i, IsClosed ({x} : Set (X i)) := by
    let : Surjective (π i) :=
      inferInstanceAs (Surjective (pullback.fst (a i).left f.hom.hom.left))
    obtain ⟨x, _⟩ := (π i).surjective (IsLocalRing.closedPoint L)
    obtain ⟨z, hz, _⟩ := exists_closed_specialization (π i) x
    exact ⟨z, hz⟩
  choose x hx using hpoint
  let R (i : I) := (X i).residueField (x i)
  let hR (i : I) : Algebra L (R i) := residueFieldAlgebra (π i) (x i)
  let hdim (i : I) : FiniteDimensional L (R i) :=
    residueField_finiteDimensional (π i) (x i) (hx i)
  let ψ (i : I) : R i →ₐ[L] AlgebraicClosure L := IsAlgClosed.lift
  let M : IntermediateField L (AlgebraicClosure L) := ⨆ i, (ψ i).fieldRange
  let hdimRange (i : I) : FiniteDimensional L (ψ i).fieldRange :=
    (ψ i).toLinearMap.finiteDimensional_range
  let : FiniteDimensional L M :=
    IntermediateField.finiteDimensional_iSup_of_finite (t := fun i => (ψ i).fieldRange)
  let : FiniteDimensional k M := FiniteDimensional.trans k L M
  obtain ⟨E, hEfin, hEgal, ⟨φ⟩⟩ := exists_finite_galois_algHom k M
  let j := φ.comp (IsScalarTower.toAlgHom k L M)
  let : Algebra L E := j.toRingHom.toAlgebra
  let : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq fun t => (j.commutes t).symm
  refine ⟨E, inferInstance, inferInstance, hEfin, hEgal, inferInstance, inferInstance, fun i => ?_⟩
  let ρ : R i →ₐ[L] M := (ψ i).codRestrict M.toSubalgebra
    (fun t => (le_iSup (fun i => (ψ i).fieldRange) i) ⟨t, rfl⟩)
  let θ : R i →+* E := φ.toRingHom.comp ρ.toRingHom
  have hθ : θ.comp (algebraMap L (R i)) = j.toRingHom := by
    apply RingHom.ext
    intro t
    change φ (ρ (algebraMap L (R i) t)) = φ (algebraMap L M t)
    rw [ρ.commutes]
  let r := (X i).fromSpecResidueField (x i)
  have hr : r ≫ π i = Spec.map (CommRingCat.ofHom (algebraMap L (R i))) := by
    change r ≫ π i = Spec.map (Spec.preimage (r ≫ π i))
    exact (Spec.map_preimage _).symm
  let y := Spec.map (CommRingCat.ofHom θ) ≫ r ≫ pullback.snd (a i).left f.hom.hom.left
  have hy : y ≫ f.hom.hom.left = Spec.map (CommRingCat.ofHom j.toRingHom) ≫ (a i).left := by
    simp only [y, Category.assoc]
    rw [← pullback.condition, ← Category.assoc r, hr, ← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun g : L →+* E => Spec.map (CommRingCat.ofHom g) ≫ (a i).left) hθ
  let b : G.affinePoints (CommAlgCat.of k E) := Over.homMk y (by
    change y ≫ G.X.hom = Spec.map (CommRingCat.ofHom (algebraMap k E))
    rw [← Over.w f.hom.hom, ← Category.assoc, hy, Category.assoc, Over.w (a i)]
    change Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) = _
    rw [← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom (RingHom.ext fun t => j.commutes t))
  exact ⟨b, Over.OverMorphism.ext hy⟩

/-- A finite Galois refinement of any natural cocycle has central lift data. -/
theorem exists_finiteGalois_refine_galoisLift [CharZero k] [IsGalois k L]
    (ξ : Cocycle H (GaloisCocycle.cover k L)) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : FiniteDimensional k E) (_ : IsGalois k E)
      (_ : Algebra L E) (_ : IsScalarTower k L E),
      Nonempty (hf.GaloisLift (ξ.refine (GaloisCocycle.coverMap k L E))) := by
  obtain ⟨E, _, _, _, _, _, _, hlift⟩ :=
    hf.exists_finiteGalois_coefficient_lifts (GaloisCocycle.value ξ)
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hf.nonempty_galoisLift _ fun σ => ?_⟩
  rw [GaloisCocycle.value_refine]
  exact hlift (σ.restrictNormal L)

end Langlands.GroupScheme.IsCentralIsogeny

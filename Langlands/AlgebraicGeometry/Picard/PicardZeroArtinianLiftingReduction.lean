import Langlands.AlgebraicGeometry.Picard.PicardZeroArtinianLiftingStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricDetectionProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Mathlib.RingTheory.KrullDimension.Zero

/-! # Artinian lifting of Picard-zero families from lifting of line bundles -/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

namespace Langlands.AbelianScheme.PicardZeroArtinianLiftingReduction

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

section Rings

variable {B' B : Type u} [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]

/-- Every element of the kernel of `φ` has square zero when the maximal ideal kills the
kernel. -/
lemma mul_self_eq_zero_of_mem_ker (φ : B' →+* B)
    (hker : maximalIdeal B' * RingHom.ker φ = ⊥) {x : B'} (hx : x ∈ RingHom.ker φ) :
    x * x = 0 := by
  have hm : x ∈ maximalIdeal B' := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hφx : IsUnit (φ x) := hu.map φ
    rw [RingHom.mem_ker.mp hx] at hφx
    exact not_isUnit_zero hφx
  have hmem : x * x ∈ maximalIdeal B' * RingHom.ker φ := Ideal.mul_mem_mul hm hx
  rw [hker] at hmem
  exact Ideal.mem_bot.mp hmem

/-- Every point of `Spec B'` with values in a field factors through `Spec B`. -/
lemma exists_comp_spec_eq (φ : B' →+* B) (hφ : Function.Surjective φ)
    (hker : maximalIdeal B' * RingHom.ker φ = ⊥) (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B')) :
    ∃ s₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B),
      s₀ ≫ Spec.map (CommRingCat.ofHom φ) = s := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective s
  have hψ : RingHom.ker φ ≤ RingHom.ker ψ.hom := by
    intro x hx
    rw [RingHom.mem_ker]
    have h2 : ψ.hom x * ψ.hom x = 0 := by
      rw [← map_mul, mul_self_eq_zero_of_mem_ker φ hker hx, map_zero]
    exact mul_self_eq_zero.mp h2
  refine ⟨Spec.map (CommRingCat.ofHom ((RingHom.liftOfSurjective φ hφ) ⟨ψ.hom, hψ⟩)), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact RingHom.liftOfSurjective_comp_apply φ hφ ⟨ψ.hom, hψ⟩ x

end Rings

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The Picard-zero condition on a twice-pulled-back family agrees with the condition on the
pullback along the composite. -/
lemma isPicardZeroFamily_relativePullback_comp {P T V : Over S} (L : RigidifiedFamily A P)
    (h : T ⟶ P) (g : V ⟶ T) :
    IsPicardZeroFamily A
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) g).obj
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) h).obj L)) ↔
      IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) (g ≫ h)).obj L) := by
  have hc := RigidifiedLineBundle.classifyingMap_comp A.X.hom (unitSection A)
    (unitSection_comp A) RigidifiedModule.pullbackCoherence L g h
  exact (congrArg (IsPicardZeroClass A) hc).symm.to_iff

/-- A pullback along `Over.homMk s hs` depends on the chosen structure map only through
the equation `hs`. -/
lemma isPicardZeroFamily_overHomMk_iff {P : Over S} (L : RigidifiedFamily A P)
    {X : Scheme.{u}} (p : X ⟶ S) (s : X ⟶ P.left) (hs : s ≫ P.hom = p) :
    IsPicardZeroFamily A
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) (Over.homMk s hs : Over.mk p ⟶ P)).obj L) ↔
      IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A)
          (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L) := by
  subst p
  rfl

section TotalSpace

variable {B' B : Type u} [CommRing B'] [CommRing B]

/-- The canonical map `A ×_S Spec B ⟶ A ×_S Spec B'` between the total spaces of the base
changes of `A` along `Spec φ ≫ β` and along `β`. -/
abbrev totalSpaceMap (φ : B' →+* B) (β : Spec (CommRingCat.of B') ⟶ S) :
    Limits.pullback A.X.hom (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶
      Limits.pullback A.X.hom β :=
  Limits.pullback.map A.X.hom (Spec.map (CommRingCat.ofHom φ) ≫ β) A.X.hom β (𝟙 _)
    (Spec.map (CommRingCat.ofHom φ)) (𝟙 S) (by simp) (by simp)

/-- The relative total-space map agrees with `totalSpaceMap` under the symmetry
isomorphisms. -/
lemma relativeSpaceSymmetry_inv_comp_map (φ : B' →+* B) (β : Spec (CommRingCat.of B') ⟶ S) :
    (relativeSpaceSymmetry A.X.hom (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β))).inv ≫
      (relativeSpace A.X.hom).map
        (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ Over.mk β) =
    totalSpaceMap A φ β ≫ (relativeSpaceSymmetry A.X.hom (Over.mk β)).inv := by
  apply Limits.pullback.hom_ext
  · simp [relativeSpaceSymmetry, relativeSpace, Over.pullback, totalSpaceMap,
      Limits.pullback.map]
  · simp [relativeSpaceSymmetry, relativeSpace, Over.pullback, totalSpaceMap,
      Limits.pullback.map]

/-- A lift of `familyLineBundle A M` along `totalSpaceMap` gives a lift of the underlying
line bundle of `M` along the relative total-space map. -/
lemma nonempty_lineBundle_lift_of_familyLineBundle_lift (φ : B' →+* B)
    (β : Spec (CommRingCat.of B') ⟶ S)
    (M : RigidifiedFamily A (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β)))
    (L' : LineBundle ((baseChange β).obj A).X.left)
    (e : (LineBundle.pullback (totalSpaceMap A φ β)).obj L' ≅
      familyLineBundle (T := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β)) A M) :
    Nonempty ((LineBundle.pullback ((relativeSpace A.X.hom).map
      (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ Over.mk β))).obj
        ((LineBundle.pullback (relativeSpaceSymmetry A.X.hom (Over.mk β)).hom).obj L') ≅
      (RigidifiedLineBundle.forget _).obj M) := by
  let σ := relativeSpaceSymmetry A.X.hom (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β))
  let τ := relativeSpaceSymmetry A.X.hom (Over.mk β)
  refine ⟨LineBundle.isoOfPullbackIso σ.inv ?_⟩
  exact LineBundle.pullbackCompEqIso σ.inv _ rfl _ ≪≫
    LineBundle.pullbackEqIso (relativeSpaceSymmetry_inv_comp_map A φ β) _ ≪≫
    (LineBundle.pullbackCompEqIso (totalSpaceMap A φ β) τ.inv rfl _).symm ≪≫
    (LineBundle.pullback (totalSpaceMap A φ β)).mapIso
      (LineBundle.pullbackCompEqIso τ.inv τ.hom τ.inv_hom_id L' ≪≫
        (LineBundle.pullbackId _).app L') ≪≫ e

end TotalSpace

variable {B' B : Type u} [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
  [IsArtinianRing B']

/-- Over the base `Spec B'` of a local Artinian ring, a line bundle on the total space whose
pullback along `Spec φ` is the underlying line bundle of a Picard-zero rigidified family `M`
can be rigidified to a Picard-zero rigidified family whose pullback is isomorphic to `M`. -/
theorem exists_picardZero_lift_of_lineBundle_lift
    (φ : B' →+* B) (hφ : Function.Surjective φ)
    (hker : maximalIdeal B' * RingHom.ker φ = ⊥)
    (β : Spec (CommRingCat.of B') ⟶ S)
    (M : RigidifiedFamily A (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β)))
    (hM : IsPicardZeroFamily A M)
    (N : LineBundle ((relativeSpace A.X.hom).obj (Over.mk β)))
    (e : (LineBundle.pullback ((relativeSpace A.X.hom).map
      (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ Over.mk β))).obj N ≅
      (RigidifiedLineBundle.forget _).obj M) :
    ∃ M' : RigidifiedFamily A (Over.mk β), IsPicardZeroFamily A M' ∧
      Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ Over.mk β)).obj M' ≅ M) := by
  let ε' := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app (Over.mk β)
  let _ : Unique ((Over.forget S).obj (Over.mk β)) :=
    inferInstanceAs (Unique (PrimeSpectrum B'))
  obtain ⟨t⟩ := LineBundle.nonempty_iso_trivial_of_unique ((LineBundle.pullback ε').obj N)
  let M' : RigidifiedFamily A (Over.mk β) :=
    RigidifiedLineBundle.ofLineBundle N ((LineBundle.forget _).mapIso t).symm
  obtain ⟨E⟩ : Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A)
      (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ Over.mk β)).obj M' ≅ M) :=
    RigidifiedLineBundle.nonempty_iso_of_forget_iso pullbackTensorComparisonIsIso
      ((relativeProjection A.X.hom).app _)
      (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) _) e
  refine ⟨M', ?_, ⟨E⟩⟩
  rw [picardZeroGeometricDetection S A (Over.mk β) M']
  intro K _ _ s
  obtain ⟨s₀, rfl⟩ := exists_comp_spec_eq φ hφ hker K s
  have h₀ := (picardZeroGeometricDetection S A _ M).mp hM K s₀
  rw [← isPicardZeroFamily_iff_of_iso A
    ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      _).mapIso E), isPicardZeroFamily_relativePullback_comp] at h₀
  have hcomp : (Over.homMk s₀ rfl :
        Over.mk (s₀ ≫ (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β)).hom) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β)) ≫
        (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ Over.mk β) =
      Over.homMk (s₀ ≫ Spec.map (CommRingCat.ofHom φ)) (by simp) := by
    ext
    rfl
  rw [hcomp, isPicardZeroFamily_overHomMk_iff] at h₀
  exact h₀

/-- The target statement follows once every underlying line bundle of a Picard-zero
rigidified family over `Spec B` lifts to the total space over `Spec B'`. -/
theorem picardZeroArtinianLifting_of_lineBundle_lift
    (hlift : ∀ (S : Scheme.{u}) (A : AbelianScheme S) (B' B : Type u) [CommRing B']
      [CommRing B] [IsLocalRing B'] [IsLocalRing B] [IsArtinianRing B'] [IsArtinianRing B]
      (φ : B' →+* B), Function.Surjective φ → maximalIdeal B' * RingHom.ker φ = ⊥ →
        ∀ (β : Spec (CommRingCat.of B') ⟶ S)
          (M : RigidifiedFamily A (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β))),
          IsPicardZeroFamily A M →
            ∃ N : LineBundle ((relativeSpace A.X.hom).obj (Over.mk β)),
              Nonempty ((LineBundle.pullback ((relativeSpace A.X.hom).map
                (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
                  Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ Over.mk β))).obj N ≅
                (RigidifiedLineBundle.forget _).obj M)) :
    PicardZeroArtinianLiftingStatement.{u} := by
  intro S A B' B _ _ _ _ _ _ φ hφ hker β M hM
  obtain ⟨N, ⟨e⟩⟩ := hlift S A B' B φ hφ hker β M hM
  exact exists_picardZero_lift_of_lineBundle_lift A φ hφ hker β M hM N e

/-- The target statement follows once, for every Picard-zero rigidified family `M` over
`Spec B`, the line bundle `familyLineBundle A M` on `A ×_S Spec B` is the pullback along
`totalSpaceMap` of a line bundle on `A ×_S Spec B'`. -/
theorem picardZeroArtinianLifting_of_familyLineBundle_lift
    (hlift : ∀ (S : Scheme.{u}) (A : AbelianScheme S) (B' B : Type u) [CommRing B']
      [CommRing B] [IsLocalRing B'] [IsLocalRing B] [IsArtinianRing B'] [IsArtinianRing B]
      (φ : B' →+* B), Function.Surjective φ → maximalIdeal B' * RingHom.ker φ = ⊥ →
        ∀ (β : Spec (CommRingCat.of B') ⟶ S)
          (M : RigidifiedFamily A (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β))),
          IsPicardZeroFamily A M →
            ∃ L' : LineBundle ((baseChange β).obj A).X.left,
              Nonempty ((LineBundle.pullback (totalSpaceMap A φ β)).obj L' ≅
                familyLineBundle (T := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β)) A M)) :
    PicardZeroArtinianLiftingStatement.{u} := by
  intro S A B' B _ _ _ _ _ _ φ hφ hker β M hM
  obtain ⟨L', ⟨e⟩⟩ := hlift S A B' B φ hφ hker β M hM
  obtain ⟨e'⟩ := nonempty_lineBundle_lift_of_familyLineBundle_lift A φ β M L' e
  exact exists_picardZero_lift_of_lineBundle_lift A φ hφ hker β M hM _ e'

end Langlands.AbelianScheme.PicardZeroArtinianLiftingReduction

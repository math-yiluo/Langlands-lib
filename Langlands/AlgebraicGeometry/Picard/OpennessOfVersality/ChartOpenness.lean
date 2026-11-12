import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.BaseLifting
import Langlands.Cohomology.ModuleComplex.ObstructionConeOpenProof

/-! # Openness of versality on an affine chart with framed Čech data -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections Langlands.Cohomology.ModuleComplex.ObstructionCone PicardGroupoid
open Langlands.AlgebraicGeometry.Deformation Langlands.Algebra

section Base

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- `affineBaseMap` is injective (`Spec` is faithful on rings). -/
lemma affineBaseMap_injective {a b : A →ₐ[R] B} (h : affineBaseMap a = affineBaseMap b) :
    a = b := by
  have h1 : Spec.map (CommRingCat.ofHom a.toRingHom) = Spec.map (CommRingCat.ofHom b.toRingHom) :=
    congrArg (fun φ : affineBase R B ⟶ affineBase R A => φ.left) h
  have h2 := Spec.map_injective h1
  ext x
  exact congrArg (fun φ : CommRingCat.of A ⟶ CommRingCat.of B => φ.hom x) h2

/-- The residue point of a chart map from an Artinian test is the composite with the
augmentation. -/
lemma reduction_comp_affineBaseMap {K' : Type u} [Field K'] [Algebra R K']
    (T : ArtinianTest R K') (χ : A →ₐ[R] T.algebra) :
    ArtinianTest.reduction T ≫ affineBaseMap χ = affineBaseMap (T.augmentation.comp χ) := by
  rw [affineBaseMap_comp]
  rfl

/-- A chart map from an Artinian test sends an element to a unit as soon as the residue point
does not vanish on it. -/
lemma isUnit_of_reduction {K' : Type u} [Field K'] [Algebra R K'] (T : ArtinianTest R K')
    (χ : A →ₐ[R] T.algebra) (χ' : A →ₐ[R] K')
    (h : ArtinianTest.reduction T ≫ affineBaseMap χ = affineBaseMap χ') (a : A)
    (ha : χ' a ≠ 0) : IsUnit (χ a) := by
  rw [reduction_comp_affineBaseMap] at h
  have hχ := affineBaseMap_injective h
  by_contra hu
  have hm : χ a ∈ IsLocalRing.maximalIdeal T.algebra := (IsLocalRing.mem_maximalIdeal _).mpr hu
  rw [← ArtinianTest.ker_augmentation] at hm
  apply ha
  rw [← hχ]
  exact hm

end Base

section Chart

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  [IsProper f] [Flat f]
  {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]
  [IsNoetherianRing A₀]
  (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
  {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]
  [Module.Finite A₀ Q]
  {F : Type u} [AddCommGroup F] [Module A₀ F] [Module P F] [IsScalarTower P A₀ F] [Module R F]
  [Module.Finite A₀ F] [Module.Projective A₀ F]

/-- **Openness of versality on an affine chart.** For framed Čech chart data of a line bundle
`L₀` on the relative space of `A₀`, if the obstruction cone has vanishing first cohomology
with coefficients in a field `k` over `A₀`, then some `g₀ ∈ A₀` not vanishing in `k` has the
property: the family `L₀` is formally versal at every field point of `Spec A₀` where `g₀` does
not vanish. -/
theorem exists_versal_basicOpen (hπ : Function.Surjective (algebraMap P A₀))
    (jQ : Q →ₗ[P] P) (hjQinj : Function.Injective jQ)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (hjQsq : ∀ x y, jQ x * jQ y = 0)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom)
    (D : Derivation R P F)
    {L₀ : LineBundle (relSpace f A₀)} (e : ∀ i, Γ(L₀.obj, (testCover f K A₀).U i))
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover f K A₀).U i))
    (hge : CocycleGluing.IsTransition e
      (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
        (fun _ _ => le_rfl) g))
    (hPlift : ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (q : A →ₐ[R] B), Function.Surjective q →
        (∀ a ∈ RingHom.ker q.toRingHom, ∀ b ∈ RingHom.ker q.toRingHom, a * b = 0) →
          ∀ χ : A₀ →ₐ[R] B, ∃ ρ : P →ₐ[R] A,
            q.comp ρ = χ.comp (IsScalarTower.toAlgHom R P A₀))
    {k : Type u} [Field k] [Algebra A₀ k]
    (hk : HOneVanishes (cplx f K A₀) (dif f K A₀) (deltaMap hπ jQ (hjQ0_of jQ hjQ) D)
      (thetaObs (A₀ := A₀) f K D g) (zObs f K jQ hjQ g hg) k) :
    ∃ g₀ : A₀, algebraMap A₀ k g₀ ≠ 0 ∧
      ∀ (K' : Type u) [Field K'] [Algebra R K'] (χ' : A₀ →ₐ[R] K'), χ' g₀ ≠ 0 →
        ArtinianChartVersality.IsFormallyVersalAt f L₀
          (affineBaseMap χ' : ArtinianTest.residueBase R K' ⟶ affineBase R A₀) := by
  obtain ⟨g₀, hg₀, hopen⟩ := openStatement A₀ (cplx f K A₀) (dif f K A₀)
    (fun i => dif_comp_dif f K A₀ i) (Fintype.card K.ι)
    (fun _ hi => subsingleton_cplx f K A₀ hi) (finiteCohomology_dif f K A₀).1
    (finiteCohomology_dif f K A₀).2 F Q (deltaMap hπ jQ (hjQ0_of jQ hjQ) D)
    (thetaObs (A₀ := A₀) f K D g) (zObs f K jQ hjQ g hg)
    (dif_thetaObs f K hπ jQ hjQ D g hg) (dif_zObs f K jQ hjQinj hjQ hjQsq g hg) k hk
  refine ⟨g₀, hg₀, fun K' _ _ χ' hχ' => ?_⟩
  rw [ArtinianChartVersality.isFormallyVersalAt_iff_elementary]
  intro A B q hq
  rw [ArtinianChartTestReduction.hasLiftingForAt_iff_base]
  have hsq : ∀ a ∈ RingHom.ker (ArtinianTest.toAlgHom q).toRingHom,
      ∀ b ∈ RingHom.ker (ArtinianTest.toAlgHom q).toRingHom, a * b = 0 := by
    intro a ha b hb
    have hab : a * b ∈ RingHom.ker (ArtinianTest.toAlgHom q).toRingHom ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ha hb
    rw [hq.ker_sq] at hab
    exact (Ideal.mem_bot.mp hab)
  refine hasBaseLiftingForAt_of_HOneVanishes f K g hπ jQ hjQ hg D e he hge _ q hq.1 hsq
    (fun χ => hPlift (ArtinianTest.toAlgHom q) hq.1 hsq χ) ?_
  intro χ hχ M _ _ _ hM
  letI : Algebra A₀ B.algebra := χ.toRingHom.toAlgebra
  haveI : IsScalarTower A₀ B.algebra M := ⟨fun a b m => by
    rw [Algebra.smul_def, mul_smul, hM]
    rfl⟩
  exact hopen B.algebra (isUnit_of_reduction B χ χ' hχ g₀ hχ') M

end Chart

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

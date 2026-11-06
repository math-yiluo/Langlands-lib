import Langlands.GroupScheme.Rational.RelativeWeylChamberGeneration

/-! # Assembling actual root systems from rational reflection functionals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

open RelativeRootSystem

/-- Rational coroot functionals and actual quotient reflections, with integral
root pairings. No integral lift of the functionals to torus cocharacters is
required. This structure records data, rather than asserting its existence. -/
structure RelativeRootRationalReflectionData where
  coroot : relativeRoots i → Module.Dual ℚ (relativeRootSpan i)
  representative : relativeRoots i → relativeWeylGroup i
  pair_self : ∀ α, coroot α (rootVector i α) = 2
  integral : ∀ α β, ∃ z : ℤ, (z : ℚ) = coroot β (rootVector i α)
  action : ∀ α (x : relativeRootSpan i),
    relativeWeylAction i (representative α) x =
      x - coroot α x • rootVector i α

namespace RelativeRootRationalReflectionData

variable {i} (D : RelativeRootRationalReflectionData i)

theorem mapsTo_preReflection (α : relativeRoots i) :
    Set.MapsTo (Module.preReflection (rootVector i α) (D.coroot α))
      (Set.range (rootVector i)) (Set.range (rootVector i)) := by
  rintro _ ⟨β, rfl⟩
  refine ⟨relativeWeylRootPermutation i (D.representative α) β, ?_⟩
  rw [← relativeWeylAction_rootVector, D.action]
  rfl

/-- Finiteness and reflection stability make the rational functionals injective. -/
theorem coroot_injective (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) : Function.Injective D.coroot := by
  let := hfinite.fintype
  have : IsAddTorsionFree (relativeRootSpan i) := .of_isTorsionFree ℚ _
  intro α β h
  apply (rootEmbedding i hT).injective
  change rootVector i α = rootVector i β
  exact Module.eq_of_mapsTo_reflection_of_mem (Set.finite_range (rootVector i))
    (D.pair_self α) (D.pair_self β)
    (by rw [← h]; exact D.pair_self α) (by rw [h]; exact D.pair_self β)
    (D.mapsTo_preReflection α) (D.mapsTo_preReflection β) (Set.mem_range_self β)

/-- The evaluation pairing on the existing actual root span. -/
def rootPairing (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite) :
    RootPairing (relativeRoots i) ℚ (relativeRootSpan i)
      (Module.Dual ℚ (relativeRootSpan i)) :=
  letI := hfinite.fintype
  have : FiniteDimensional ℚ (relativeRootSpan i) :=
    FiniteDimensional.span_of_finite ℚ (hfinite.image toRat)
  RootPairing.mk'' (Module.Dual.eval ℚ (relativeRootSpan i)) (rootEmbedding i hT)
    ⟨D.coroot, D.coroot_injective hT hfinite⟩ D.pair_self
    D.mapsTo_preReflection (span_range_rootVector i)

theorem rootPairing_isRootSystem (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hT hfinite).IsRootSystem := by
  let := hfinite.fintype
  have : FiniteDimensional ℚ (relativeRootSpan i) :=
    FiniteDimensional.span_of_finite ℚ (hfinite.image toRat)
  unfold rootPairing
  exact RootPairing.isRootSystem_mk''
    (p := Module.Dual.eval ℚ (relativeRootSpan i))
    (root := rootEmbedding i hT)
    (coroot := ⟨D.coroot, D.coroot_injective hT hfinite⟩)
    (hsp := span_range_rootVector i) D.integral

theorem rootPairing_isCrystallographic (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hT hfinite).IsCrystallographic :=
  ⟨D.integral⟩

theorem rootPairing_root_image (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    Subtype.val '' Set.range (D.rootPairing hT hfinite).root =
      toRat '' relativeRoots i := by
  change Subtype.val '' Set.range (rootVector i) = _
  ext x
  constructor
  · rintro ⟨_, ⟨α, rfl⟩, rfl⟩
    exact ⟨α.val, α.property, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨rootVector i ⟨α, hα⟩, Set.mem_range_self _, rfl⟩

theorem reflection_eq_relativeWeylAction (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) (α : relativeRoots i) :
    (D.rootPairing hT hfinite).reflection α =
      relativeWeylAction i (D.representative α) := by
  apply LinearEquiv.ext
  intro x
  exact (D.action α x).symm

theorem weylGroup_image (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hT hfinite).weylGroup.map
        (RootPairing.Equiv.weightHom (D.rootPairing hT hfinite)) =
      Subgroup.closure (Set.range fun α =>
        relativeWeylAction i (D.representative α)) := by
  rw [← MonoidHom.domRestrict_range, RootPairing.range_weylGroup_weightHom]
  congr 2
  funext α
  exact D.reflection_eq_relativeWeylAction hT hfinite α

/-- Chamber transitivity and the actual positive-root stabilizer identify the
whole actual quotient, including possible central directions. -/
theorem closure_representatives_eq_top_of_positive_stabilizer
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hstab : HasTrivialPositiveRootStabilizer i ν) :
    Subgroup.closure (Set.range D.representative) = ⊤ := by
  let := hfinite.fintype
  let P := D.rootPairing hT hfinite
  have : P.IsRootSystem := D.rootPairing_isRootSystem hT hfinite
  let f := corootFunctional i ν
  have hf : Langlands.LinearAlgebra.RootPairingChambers.Regular P f := by
    intro α
    change corootFunctional i ν (rootVector i α) ≠ 0
    rw [corootFunctional_rootVector]
    exact_mod_cast hν α.val α.property
  let H := Subgroup.closure (Set.range D.representative)
  have hmap : P.weylGroup.map (RootPairing.Equiv.weightHom P) =
      H.map (relativeWeylAction i) := by
    rw [D.weylGroup_image]
    rw [MonoidHom.map_closure]
    congr 1
    exact Set.range_comp _ _
  apply top_unique
  intro q _
  let g : Module.Dual ℚ (relativeRootSpan i) :=
    f.comp (relativeWeylAction i q).toLinearMap
  have hg : Langlands.LinearAlgebra.RootPairingChambers.Regular P g := by
    intro α
    change corootFunctional i ν (relativeWeylAction i q (rootVector i α)) ≠ 0
    rw [corootFunctional_relativeWeylAction_rootVector]
    exact_mod_cast hν _ (relativeWeylRootPermutation i q α).property
  obtain ⟨w, hw⟩ :=
    Langlands.LinearAlgebra.RootPairingChambers.exists_weylGroup_sameChamber P hf hg
  have hwmap : RootPairing.Equiv.weightHom P w.val ∈ H.map (relativeWeylAction i) := by
    rw [← hmap]
    exact ⟨w.val, w.property, rfl⟩
  obtain ⟨r, hr, hwr⟩ := hwmap
  have hqr : q * r = 1 := by
    apply hstab (q * r)
    intro α hα
    have he := w.val.toLinearMap_weightEquiv (P.root ⟨α, hα⟩) g
    have hs := hw ⟨α, hα⟩
    change 0 < f (rootVector i ⟨α, hα⟩) ↔
      0 < w.val.coweightEquiv g (rootVector i ⟨α, hα⟩) at hs
    change g (w.val.weightEquiv (rootVector i ⟨α, hα⟩)) =
      w.val.coweightEquiv g (rootVector i ⟨α, hα⟩) at he
    rw [← he] at hs
    change 0 < f (rootVector i ⟨α, hα⟩) ↔
      0 < f (relativeWeylAction i q
        (RootPairing.Equiv.weightHom P w.val (rootVector i ⟨α, hα⟩))) at hs
    rw [← hwr, ← LinearEquiv.mul_apply, ← map_mul] at hs
    rw [corootFunctional_relativeWeylAction_rootVector,
      corootFunctional_rootVector] at hs
    exact_mod_cast hs.symm
  have hq : q = r⁻¹ := (eq_inv_iff_mul_eq_one).mpr hqr
  exact hq ▸ H.inv_mem hr

include D in
/-- Rational reflection functionals, integral root evaluations and the actual
positive-root stabilizer imply the full published root-system predicate. -/
theorem hasRelativeRootSystem_of_positive_stabilizer
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hstab : HasTrivialPositiveRootStabilizer i ν) : HasRelativeRootSystem i := by
  let := hfinite.fintype
  refine ⟨relativeRoots i, inferInstance, D.rootPairing hT hfinite,
    D.rootPairing_isRootSystem hT hfinite,
    D.rootPairing_isCrystallographic hT hfinite, rfl,
    D.rootPairing_root_image hT hfinite, ?_, hstab.relativeWeylAction_injective⟩
  rw [D.weylGroup_image]
  have h := congrArg (Subgroup.map (relativeWeylAction i))
    (D.closure_representatives_eq_top_of_positive_stabilizer hT hfinite hν hstab)
  rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top] at h
  exact h

end RelativeRootRationalReflectionData

end Langlands.GroupScheme

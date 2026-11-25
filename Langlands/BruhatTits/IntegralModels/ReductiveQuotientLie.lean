import Langlands.BruhatTits.IntegralModels.ReductiveQuotientRoots
import Langlands.GroupScheme.IntegralModel.LieLatticeReduction

/-! # The Lie algebra of the reductive quotient of a special fibre

For supplied special-fibre quotient data `Q` of the neutral model `𝒢°` of
`D : RelativeComponentModelData R K G`, with radical `R_u ⟶ H = 𝒢°_𝔣` and reductive
quotient `H ⟶ Gred`, this file proves the following (Kaletha–Prasad, §2.4(a) and §13.3.2):

* `Lie(H) ⧸ Lie(R_u) ≃ Lie(Gred)` over the residue field;
* with `g_0 = D.neutral.lieLattice` and `g_0+` the elements of `g_0` whose reduction lies in
  `Lie(R_u)`, one has `𝔪 • g_0 ≤ g_0+ ≤ g_0` and `g_0 ⧸ g_0+ ≃ Lie(Gred)` over `R`;
* if a smooth model `𝒩` maps to `𝒢°` over the identity of `G`, its special-fibre map factors
  through a smooth map to `R_u`, and `𝔪 • g_0 ≤ Lie(𝒩)`, then `g_0+ = Lie(𝒩)`, so
  `Lie(Gred) ≃ g_0 ⧸ Lie(𝒩)`. -/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

section SpecialFibre

variable (hQ : Q.IsReductiveQuotient)

include hQ

/-- The supplied radical of a reductive quotient is affine over the residue field: it is a
closed subgroup of the affine special fibre. -/
theorem radical_isAffineHom : IsAffineHom Q.radical.X.hom := by
  have : IsClosedImmersion Q.radicalInclusion.hom.hom.left := hQ.1.isClosedSubgroup
  rw [← Over.w Q.radicalInclusion.hom.hom]
  infer_instance

/-- The tangent submodule of the radical's image is the image of the radical's Lie
algebra. -/
theorem radical_lie_eq_range :
    haveI := Q.radical_isAffineHom hQ
    (SubgroupFunctor.range Q.radicalInclusion).lie (IsLocalRing.ResidueField R) =
      LinearMap.range (Lie.targetMapLinear Q.radicalInclusion (IsLocalRing.ResidueField R)) := by
  have := Q.radical_isAffineHom hQ
  have : IsClosedImmersion Q.radicalInclusion.hom.hom.left := hQ.1.isClosedSubgroup
  have : Mono Q.radicalInclusion.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.lie_eq_range _ _ Q.radicalInclusion ⟨inferInstance, rfl⟩

/-- KP §2.4(a) for the supplied reductive quotient: the differential of the projection
identifies `Lie(H) ⧸ Lie(R_u)` with `Lie(Gred)`. -/
def specialFibreLieQuotientEquiv :
    (Additive (lieKernel D.neutral.specialFibre (IsLocalRing.ResidueField R)) ⧸
        (SubgroupFunctor.range Q.radicalInclusion).lie (IsLocalRing.ResidueField R)) ≃ₗ[
          IsLocalRing.ResidueField R]
      Additive (lieKernel Q.quotient (IsLocalRing.ResidueField R)) :=
  (Submodule.quotEquivOfEq _ _ (Q.ker_projection_eq_radical_lie hQ).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      (Lie.targetMapLinear_surjective_of_smooth Q.projection _ (Q.projection_smooth hQ)))

theorem specialFibreLieQuotientEquiv_mk
    (X : Additive (lieKernel D.neutral.specialFibre (IsLocalRing.ResidueField R))) :
    Q.specialFibreLieQuotientEquiv hQ (Submodule.Quotient.mk X) =
      Lie.targetMapLinear Q.projection (IsLocalRing.ResidueField R) X := rfl

end SpecialFibre

variable [IsAffineHom G.X.hom]

/-- The Lie algebra of the radical, as an `R`-submodule of the special-fibre Lie algebra
`GenericLie R H`. -/
def radicalLie : Submodule R (GenericLie R D.neutral.specialFibre) :=
  (((SubgroupFunctor.range Q.radicalInclusion).lie (IsLocalRing.ResidueField R)).comap
    (GenericLie.equiv R D.neutral.specialFibre).toLinearMap).restrictScalars R

omit [IsAffineHom G.X.hom] in
theorem mem_radicalLie (X : GenericLie R D.neutral.specialFibre) :
    X ∈ Q.radicalLie ↔ GenericLie.equiv R D.neutral.specialFibre X ∈
      (SubgroupFunctor.range Q.radicalInclusion).lie (IsLocalRing.ResidueField R) :=
  Iff.rfl

/-- The positive Lie lattice `g_0+ ⊆ Lie(G)`: the image of those `X ∈ Lie(𝒢°)` whose
reduction lies in the Lie algebra of the radical. -/
def positiveLieLattice : Submodule R (GenericLie R G) :=
  (Q.radicalLie.comap D.neutral.lieReduction).map D.neutral.lieMap

theorem positiveLieLattice_le : Q.positiveLieLattice ≤ D.neutral.lieLattice :=
  LinearMap.map_le_range

/-- `𝔪 • g_0 ≤ g_0+`. -/
theorem smul_lieLattice_le_positiveLieLattice :
    IsLocalRing.maximalIdeal R • D.neutral.lieLattice ≤ Q.positiveLieLattice := by
  rw [IntegralModel.lieLattice, LinearMap.range_eq_map, ← Submodule.map_smul'']
  apply Submodule.map_mono
  intro X hX
  have h := D.neutral.smul_top_le_ker_lieReduction hX
  rw [LinearMap.mem_ker] at h
  change D.neutral.lieReduction X ∈ Q.radicalLie
  rw [h]
  exact Q.radicalLie.zero_mem

/-- Reduction followed by the differential of the projection to the reductive quotient. -/
def reductiveLieMap : D.neutral.LieModule →ₗ[R] GenericLie R Q.quotient :=
  (GenericLie.map R Q.projection).comp D.neutral.lieReduction

/-- The `R`-linear map `g_0 → Lie(Gred)`. -/
def latticeReductiveLieMap : D.neutral.lieLattice →ₗ[R] GenericLie R Q.quotient :=
  Q.reductiveLieMap.comp D.neutral.lieLatticeEquiv.symm.toLinearMap

variable (hQ : Q.IsReductiveQuotient)

include hQ

omit [IsAffineHom G.X.hom] in
/-- `radicalLie` is the image of the differential of the radical's inclusion. -/
theorem mem_radicalLie_iff (X : GenericLie R D.neutral.specialFibre) :
    haveI := Q.radical_isAffineHom hQ
    X ∈ Q.radicalLie ↔ ∃ Z : GenericLie R Q.radical, GenericLie.map R Q.radicalInclusion Z = X := by
  have := Q.radical_isAffineHom hQ
  rw [mem_radicalLie, Q.radical_lie_eq_range hQ]
  constructor
  · rintro ⟨Z, hZ⟩
    refine ⟨(GenericLie.equiv R Q.radical).symm Z, ?_⟩
    rw [GenericLie.map_apply, LinearEquiv.apply_symm_apply, hZ]
    simp only [LinearEquiv.symm_apply_apply]
  · rintro ⟨Z, rfl⟩
    exact ⟨GenericLie.equiv R Q.radical Z, rfl⟩

omit [IsAffineHom G.X.hom] in
/-- The differential of the projection kills exactly the Lie algebra of the radical. -/
theorem map_projection_eq_zero_iff (X : GenericLie R D.neutral.specialFibre) :
    GenericLie.map R Q.projection X = 0 ↔ X ∈ Q.radicalLie := by
  have h : GenericLie.map R Q.projection X = (GenericLie.equiv R Q.quotient).symm
      (Lie.targetMapLinear Q.projection (IsLocalRing.ResidueField R)
        (GenericLie.equiv R D.neutral.specialFibre X)) := GenericLie.map_apply _ _ _
  rw [h, LinearEquiv.map_eq_zero_iff, mem_radicalLie, ← Q.ker_projection_eq_radical_lie hQ]
  exact LinearMap.mem_ker.symm

omit [IsAffineHom G.X.hom] in
theorem ker_reductiveLieMap :
    LinearMap.ker Q.reductiveLieMap = Q.radicalLie.comap D.neutral.lieReduction := by
  ext X
  exact Q.map_projection_eq_zero_iff hQ (D.neutral.lieReduction X)

theorem reductiveLieMap_surjective : Function.Surjective Q.reductiveLieMap :=
  (GenericLie.map_surjective R (Lie.targetMapLinear_surjective_of_smooth Q.projection
    (IsLocalRing.ResidueField R) (Q.projection_smooth hQ))).comp
    (IntegralModel.lieReduction_surjective D.neutral_smooth)

theorem ker_latticeReductiveLieMap :
    LinearMap.ker Q.latticeReductiveLieMap =
      Q.positiveLieLattice.comap D.neutral.lieLattice.subtype := by
  apply Submodule.ext
  intro Y
  obtain ⟨Y, X, rfl⟩ := Y
  have hX : (⟨D.neutral.lieMap X, X, rfl⟩ : D.neutral.lieLattice) =
      D.neutral.lieLatticeEquiv X := rfl
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, hX,
    latticeReductiveLieMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, ← LinearMap.mem_ker, Q.ker_reductiveLieMap hQ]
  constructor
  · intro h
    exact ⟨X, h, rfl⟩
  · rintro ⟨X', hX', h⟩
    rwa [← D.neutral.lieMap_injective h]

theorem latticeReductiveLieMap_surjective : Function.Surjective Q.latticeReductiveLieMap :=
  (Q.reductiveLieMap_surjective hQ).comp D.neutral.lieLatticeEquiv.symm.surjective

/-- KP §13.3.2 for the supplied data: `g_0 ⧸ g_0+ ≃ Lie(Gred)` as `R`-modules. -/
def reductiveQuotientLieEquiv :
    (D.neutral.lieLattice ⧸ Q.positiveLieLattice.comap D.neutral.lieLattice.subtype) ≃ₗ[R]
      GenericLie R Q.quotient :=
  (Submodule.quotEquivOfEq _ _ (Q.ker_latticeReductiveLieMap hQ).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (Q.latticeReductiveLieMap_surjective hQ))

section Positive

variable {N : IntegralModel R K G} (φ : N.Hom D.neutral (𝟙 G))
  (s : N.specialFibre ⟶ Q.radical)
  (hs : φ.specialFibreMap = s ≫ Q.radicalInclusion)

include hs

/-- If the special-fibre map of `φ : 𝒩 → 𝒢°` factors through the radical, then
`Lie(𝒩) ≤ g_0+`. -/
theorem lieLattice_le_positiveLieLattice : N.lieLattice ≤ Q.positiveLieLattice := by
  have := Q.radical_isAffineHom hQ
  rintro _ ⟨Y, rfl⟩
  refine ⟨Lie.targetMapLinear φ.hom (CommRingCat.of R) Y, ?_, ?_⟩
  · change D.neutral.lieReduction (Lie.targetMapLinear φ.hom (CommRingCat.of R) Y) ∈
      Q.radicalLie
    rw [φ.lieReduction_naturality, hs, mem_radicalLie, GenericLie.map_apply,
      LinearEquiv.apply_symm_apply, Q.radical_lie_eq_range hQ]
    refine ⟨Lie.targetMapLinear s (IsLocalRing.ResidueField R)
      (GenericLie.equiv R N.specialFibre (N.lieReduction Y)), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact Category.assoc _ _ _
  · rw [φ.lieMap_naturality, GenericLie.map_id]

/-- The lifting step of KP §13.3.2: if `𝒩` and `s` are smooth, every element of `Lie(𝒢°)`
whose reduction lies in the Lie algebra of the radical has the same reduction as the
differential of an element of `Lie(𝒩)`. -/
theorem exists_lieReduction_eq (hN : N.IsSmooth) (hsm : Smooth s.hom.hom.left)
    (X : D.neutral.LieModule) (hX : D.neutral.lieReduction X ∈ Q.radicalLie) :
    ∃ Y : N.LieModule, D.neutral.lieReduction (Lie.targetMapLinear φ.hom (CommRingCat.of R) Y) =
      D.neutral.lieReduction X := by
  have := Q.radical_isAffineHom hQ
  obtain ⟨Z, hZ⟩ := (Q.mem_radicalLie_iff hQ _).mp hX
  obtain ⟨W, rfl⟩ := GenericLie.map_surjective R
    (Lie.targetMapLinear_surjective_of_smooth s (IsLocalRing.ResidueField R) hsm) Z
  obtain ⟨Y, rfl⟩ := IntegralModel.lieReduction_surjective hN W
  refine ⟨Y, (φ.lieReduction_naturality Y).trans ?_⟩
  rw [hs]
  exact (GenericLie.map_comp R s Q.radicalInclusion _).trans hZ

omit [IsLocalRing R] hQ hs in
/-- Splitting `X ∈ Lie(𝒢°)` along the differential of `φ : 𝒩 → 𝒢°`. -/
theorem lieMap_eq_add (X : D.neutral.LieModule) (Y : N.LieModule) :
    D.neutral.lieMap X =
      N.lieMap Y + D.neutral.lieMap (X - Lie.targetMapLinear φ.hom (CommRingCat.of R) Y) := by
  rw [map_sub, φ.lieMap_naturality, GenericLie.map_id]
  abel

/-- KP §13.3.2, conditional form: if `𝒩` is smooth and the factorization `s` of its
special-fibre map through the radical is smooth, then `g_0+ = Lie(𝒩) + 𝔪 • g_0`. -/
theorem positiveLieLattice_eq_sup (hN : N.IsSmooth) (hsm : Smooth s.hom.hom.left) :
    Q.positiveLieLattice =
      N.lieLattice ⊔ IsLocalRing.maximalIdeal R • D.neutral.lieLattice := by
  refine le_antisymm ?_ (sup_le (Q.lieLattice_le_positiveLieLattice hQ φ s hs)
    Q.smul_lieLattice_le_positiveLieLattice)
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨Y, hY⟩ := Q.exists_lieReduction_eq hQ φ s hs hN hsm X hX
  have hker : X - Lie.targetMapLinear φ.hom (CommRingCat.of R) Y ∈
      LinearMap.ker D.neutral.lieReduction := by
    rw [LinearMap.mem_ker, LinearMap.map_sub, hY, sub_self]
  rw [IntegralModel.ker_lieReduction D.neutral_smooth] at hker
  rw [lieMap_eq_add φ X Y]
  refine Submodule.add_mem_sup ⟨Y, rfl⟩ ?_
  rw [IntegralModel.lieLattice, LinearMap.range_eq_map, ← Submodule.map_smul'']
  exact Submodule.mem_map_of_mem hker

/-- If moreover `𝔪 • g_0 ≤ Lie(𝒩)`, then `g_0+ = Lie(𝒩)`. -/
theorem positiveLieLattice_eq (hN : N.IsSmooth) (hsm : Smooth s.hom.hom.left)
    (hm : IsLocalRing.maximalIdeal R • D.neutral.lieLattice ≤ N.lieLattice) :
    Q.positiveLieLattice = N.lieLattice := by
  rw [Q.positiveLieLattice_eq_sup hQ φ s hs hN hsm, sup_eq_left.mpr hm]

/-- KP §13.3.2, `Lie(Gred) = g_0 ⧸ g_0+`, with `g_0+` the Lie lattice of the supplied
smooth model `𝒩`. -/
def lieLatticeQuotientEquiv (hN : N.IsSmooth) (hsm : Smooth s.hom.hom.left)
    (hm : IsLocalRing.maximalIdeal R • D.neutral.lieLattice ≤ N.lieLattice) :
    (D.neutral.lieLattice ⧸ N.lieLattice.comap D.neutral.lieLattice.subtype) ≃ₗ[R]
      GenericLie R Q.quotient :=
  (Submodule.quotEquivOfEq _ _ (by rw [Q.positiveLieLattice_eq hQ φ s hs hN hsm hm])).trans
    (Q.reductiveQuotientLieEquiv hQ)

end Positive

end SpecialFibreQuotientData

end Langlands.BruhatTits.IntegralModels

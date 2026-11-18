import Langlands.GroupScheme.Reductive.HighestWeightSubquotientRepresentation
import Langlands.GroupScheme.Reductive.GaloisTwistWeights
import Langlands.Algebra.GaloisTwistedFlags
import Langlands.GroupScheme.Reductive.InnerStarWeights

/-! # Galois-twisted stability of the highest-weight flag -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The `σ`-preimage of a subspace stable under the Galois twist by `σ` is stable. -/
theorem IsStableSubspace.galoisComap_of_galoisTwist (σ : K ≃ₐ[k] K)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {V : Submodule K (n → K)} (hV : (galoisTwist σ ρ).IsStableSubspace V) :
    ρ.IsStableSubspace (galoisComap σ V) := by
  rw [isStableSubspace_iff_universalMatrix] at hV ⊢
  intro L w hw
  rw [mem_galoisComap]
  have h := hV (untwistFunctional (CharacterUnits.Coord G) σ L) _ hw
  rw [universalMatrix_galoisTwist_map_untwist] at h
  convert h using 1
  funext i
  exact RingHom.map_mulVec σ.toRingHom _ _ i

/-- Stability only depends on the universal matrix. -/
theorem IsStableSubspace.of_universalMatrix_eq
    {ρ₁ ρ₂ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    (h : universalMatrix ρ₁ = universalMatrix ρ₂) {V : Submodule K (n → K)}
    (hV : ρ₁.IsStableSubspace V) : ρ₂.IsStableSubspace V := by
  rw [isStableSubspace_iff_universalMatrix] at hV ⊢
  rw [← h]
  exact hV

/-- The `σ`-image `galoisComap σ⁻¹ V` of a stable subspace is stable for the Galois twist by
`σ`. -/
theorem IsStableSubspace.galoisComap_galoisTwist (σ : K ≃ₐ[k] K)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {V : Submodule K (n → K)} (hV : ρ.IsStableSubspace V) :
    (galoisTwist σ ρ).IsStableSubspace (galoisComap σ⁻¹ V) :=
  IsStableSubspace.galoisComap_of_galoisTwist σ⁻¹
    (IsStableSubspace.of_universalMatrix_eq (universalMatrix_galoisTwist_inv σ ρ).symm hV)

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  (p : SplitPinning H) {n : Type} [Fintype n] [DecidableEq n]

/-- The weight multiplicities of a stable subspace are those of a representation. -/
theorem exists_finrank_inf_representationWeightSpace {ρ : MatrixRepresentation H n}
    {V : Submodule F (n → F)} (hV : ρ.IsStableSubspace V) :
    ∃ (d : ℕ) (τ : MatrixRepresentation H (Fin d)), ∀ mu : characterLattice p.torus,
      Module.finrank F (V ⊓ p.representationWeightSpace ρ mu : Submodule F (n → F)) =
        Module.finrank F (p.representationWeightSpace τ mu) := by
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hstable := hV.isStableCoordinates B C hcols hproj
  have hB : Intertwines (restrictCoordinates ρ B C hCB hstable) ρ B :=
    intertwines_restrictCoordinates ρ B C hCB hstable
  have hrange := range_coordinateInclusion_eq _ B C hcols hproj
  refine ⟨d, restrictCoordinates ρ B C hCB hstable, fun mu => ?_⟩
  have h := Intertwines.map_weightSpace_eq_inf_range p hB hCB mu
  rw [hrange, inf_comm] at h
  have hinj : Function.Injective B.mulVecLin := by
    intro a b hab
    have := congrArg (fun v => C *ᵥ v) hab
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] using this
  rw [← h]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

end Langlands.GroupScheme.SplitPinning

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (d : GaloisPinningData k K G) {n : Type} [Fintype n] [DecidableEq n]

local instance highestTwistedAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- Weight multiplicities of a stable subspace are invariant under the Weyl group. -/
theorem finrank_inf_representationWeightSpace_weyl
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    {V : Submodule K (n → K)} (hV : ρ.IsStableSubspace V)
    (w : d.toSplitPinning.rootDatum.Aut) (hw : w ∈ d.toSplitPinning.rootDatum.weylGroup)
    (mu : characterLattice d.toSplitPinning.torus) :
    Module.finrank K
        (V ⊓ d.toSplitPinning.representationWeightSpace ρ (w • mu) : Submodule K (n → K)) =
      Module.finrank K
        (V ⊓ d.toSplitPinning.representationWeightSpace ρ mu : Submodule K (n → K)) := by
  obtain ⟨m, τ, hτ⟩ := d.toSplitPinning.exists_finrank_inf_representationWeightSpace hV
  rw [hτ, hτ, d.finrank_representationWeightSpace_weyl τ w hw]

/-- The subspace generated by the `nu` weight space contains every Weyl-conjugate weight
space. -/
theorem representationWeightSpace_weyl_le_highestGenerated
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (nu : characterLattice d.toSplitPinning.torus)
    (w : d.toSplitPinning.rootDatum.Aut) (hw : w ∈ d.toSplitPinning.rootDatum.weylGroup) :
    d.toSplitPinning.representationWeightSpace ρ (w • nu) ≤
      d.toSplitPinning.highestGenerated ρ nu := by
  have h1 := d.finrank_inf_representationWeightSpace_weyl ρ
    (d.toSplitPinning.isStableSubspace_highestGenerated ρ nu) w hw nu
  rw [inf_eq_right.mpr (d.toSplitPinning.weightSpace_le_highestGenerated ρ nu),
    ← d.finrank_representationWeightSpace_weyl ρ w hw nu] at h1
  have h2 := Submodule.eq_of_le_of_finrank_eq inf_le_right h1
  rw [← h2]
  exact inf_le_left

/-- The radical meets every Weyl conjugate of the `nu` weight space trivially. -/
theorem highestRadical_inf_representationWeightSpace_weyl
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (nu : characterLattice d.toSplitPinning.torus)
    (w : d.toSplitPinning.rootDatum.Aut) (hw : w ∈ d.toSplitPinning.rootDatum.weylGroup) :
    d.toSplitPinning.highestRadical ρ nu ⊓
      d.toSplitPinning.representationWeightSpace ρ (w • nu) = ⊥ := by
  have h1 := d.finrank_inf_representationWeightSpace_weyl ρ
    (d.toSplitPinning.isStableSubspace_highestRadical ρ nu) w hw nu
  rw [d.toSplitPinning.highestRadical_inf_weightSpace ρ nu, finrank_bot] at h1
  exact Submodule.finrank_eq_zero.mp h1

variable [LocallyOfFiniteType G.X.hom]

/-- A weight fixed by the star action of `σ` is moved by the ordinary Galois action of `σ`
to a Weyl conjugate. -/
theorem exists_weyl_smul_eq_galoisAction_smul (σ : K ≃ₐ[k] K)
    {nu : characterLattice d.toSplitPinning.torus} (hfix : (d.starAction σ).val • nu = nu) :
    ∃ w ∈ d.toSplitPinning.rootDatum.weylGroup, d.galoisAction σ • nu = w • nu := by
  obtain ⟨w, hw⟩ := d.exists_weyl_mul_galoisAction_eq_starAction σ
  refine ⟨w.val⁻¹, inv_mem w.2, ?_⟩
  conv_rhs => rw [← hfix, ← hw, mul_smul, inv_smul_smul]

/-- For a star-fixed weight `nu` and intertwiners `P σ : ρ → ρ^σ`, the subspace generated by
the `nu` weight space is twisted-stable. -/
theorem isTwistedStable_highestGenerated [IsGalois k K]
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {nu : characterLattice d.toSplitPinning.torus} (hfix : d.IsStarFixedWeight nu)
    (P : (K ≃ₐ[k] K) → Matrix n n K) (hP : ∀ σ, Intertwines ρ (galoisTwist σ ρ) (P σ)) :
    IsTwistedStable P (d.toSplitPinning.highestGenerated ρ nu) := by
  intro σ u hu
  set X := d.toSplitPinning.highestGenerated ρ nu with hX
  have hVst : ρ.IsStableSubspace ((galoisComap σ⁻¹ X).comap (P σ).mulVecLin) :=
    ((d.toSplitPinning.isStableSubspace_highestGenerated ρ nu).galoisComap_galoisTwist
      σ).comap (hP σ)
  have hXV : X ≤ (galoisComap σ⁻¹ X).comap (P σ).mulVecLin := by
    refine d.toSplitPinning.highestGenerated_le ρ nu hVst fun v hv => ?_
    have h1 := SplitPinning.Intertwines.mulVec_mem_weightSpace d.toSplitPinning (hP σ) hv
    obtain ⟨w, hw, hwnu⟩ := d.exists_weyl_smul_eq_galoisAction_smul σ⁻¹ (hfix σ⁻¹)
    have h1' : P σ *ᵥ v ∈ d.toSplitPinning.representationWeightSpace (galoisTwist σ ρ)
        (d.galoisAction σ • (d.galoisAction σ⁻¹ • nu)) := by
      rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
      exact h1
    rw [representationWeightSpace_galoisTwist_smul, mem_galoisComap, hwnu] at h1'
    change (fun i => σ⁻¹ ((P σ *ᵥ v) i)) ∈ X
    exact d.representationWeightSpace_weyl_le_highestGenerated ρ nu w hw h1'
  have h := hXV hu
  change (fun i => σ⁻¹ ((P σ *ᵥ u) i)) ∈ X at h
  exact h

/-- For a star-fixed weight `nu` and invertible intertwiners `P σ : ρ → ρ^σ`, the radical of
the `nu` weight space is twisted-stable. -/
theorem isTwistedStable_highestRadical [IsGalois k K]
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {nu : characterLattice d.toSplitPinning.torus} (hfix : d.IsStarFixedWeight nu)
    (P : (K ≃ₐ[k] K) → Matrix n n K) (hP : ∀ σ, Intertwines ρ (galoisTwist σ ρ) (P σ))
    (hPu : ∀ σ, IsUnit (P σ)) :
    IsTwistedStable P (d.toSplitPinning.highestRadical ρ nu) := by
  intro σ u hu
  set Y := d.toSplitPinning.highestRadical ρ nu with hY
  set Z := galoisComap σ (Y.map (P σ).mulVecLin) with hZ
  have hZst : ρ.IsStableSubspace Z :=
    ((d.toSplitPinning.isStableSubspace_highestRadical ρ nu).map (hP σ)).galoisComap_of_galoisTwist
      σ
  have hXst := d.isTwistedStable_highestGenerated hfix P hP
  have hmem : ∀ z ∈ Z, ∃ y ∈ Y, z = fun i => σ.symm ((P σ *ᵥ y) i) := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := (mem_galoisComap σ _ z).mp hz
    refine ⟨y, hy, ?_⟩
    funext i
    change P σ *ᵥ y = _ at hyz
    rw [hyz]
    simp
  have hZX : Z ≤ d.toSplitPinning.highestGenerated ρ nu := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hmem z hz
    exact hXst σ y (d.toSplitPinning.highestRadical_le ρ nu hy)
  have hZnu : Z ⊓ d.toSplitPinning.representationWeightSpace ρ nu = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzZ, hzw⟩ := Submodule.mem_inf.mp hz
    obtain ⟨y, hy, rfl⟩ := hmem z hzZ
    have h1 := d.conjugate_mem_representationWeightSpace σ ρ nu hzw
    simp only [AlgEquiv.apply_symm_apply] at h1
    rw [← galoisAction_smul] at h1
    have hPinv : (P σ)⁻¹ * P σ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (hPu σ))
    have hy' := SplitPinning.Intertwines.mem_weightSpace_of_leftInverse d.toSplitPinning (hP σ) hPinv h1
    obtain ⟨w, hw, hwnu⟩ := d.exists_weyl_smul_eq_galoisAction_smul σ (hfix σ)
    rw [hwnu] at hy'
    have h0 : y ∈ Y ⊓ d.toSplitPinning.representationWeightSpace ρ (w • nu) :=
      Submodule.mem_inf.mpr ⟨hy, hy'⟩
    rw [d.highestRadical_inf_representationWeightSpace_weyl ρ nu w hw, Submodule.mem_bot] at h0
    rw [h0, Submodule.mem_bot]
    funext i
    simp
  have hZY := d.toSplitPinning.le_highestRadical ρ nu hZst hZX hZnu
  apply hZY
  rw [hZ, mem_galoisComap]
  refine ⟨u, hu, ?_⟩
  funext i
  simp

end Langlands.GroupScheme.GaloisPinningData

namespace Langlands.GroupScheme

open MatrixRepresentation Langlands.Algebra.GaloisTwistedMatrix

/-- Galois-twisted stability of the flag `highestRadical ρ ν ≤ highestGenerated ρ ν` of a
star-fixed weight `ν`, for invertible intertwiners `P σ : ρ → ρ^σ` (the Galois-stability input of
Tits's Proposition 3.4). -/
def HighestWeightTwistedStabilityStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : GaloisPinningData k K G) (n : Type) [Fintype n]
    [DecidableEq n] (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (nu : characterLattice d.toSplitPinning.torus), d.IsStarFixedWeight nu →
    ∀ P : (K ≃ₐ[k] K) → Matrix n n K, (∀ σ, Intertwines ρ (galoisTwist σ ρ) (P σ)) →
      (∀ σ, IsUnit (P σ)) →
        IsTwistedStable P (d.toSplitPinning.highestGenerated ρ nu) ∧
          IsTwistedStable P (d.toSplitPinning.highestRadical ρ nu)

theorem highestWeightTwistedStability : HighestWeightTwistedStabilityStatement.{u} := by
  intro k K _ _ _ _ G _ _ d n _ _ ρ nu hfix P hP hPu
  exact ⟨d.isTwistedStable_highestGenerated hfix P hP,
    d.isTwistedStable_highestRadical hfix P hP hPu⟩

end Langlands.GroupScheme

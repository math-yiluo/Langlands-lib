import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicEisensteinWeightCharacters
import Langlands.Global.AdelicParabolicProjectiveHeight
import Langlands.GroupScheme.Dynamic.ParabolicCharacters
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Mathlib.RingTheory.Flat.Domain

/-! # Regular parameter decay for rational parabolic cosets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct NumberField
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Plancherel RealTorusSpace RepresentationGrowth

variable {F : Type u} [Field F] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)

include r in
/-- The Levi limit retraction and detection by the Levi split component make
character restriction from the inducing parabolic injective. -/
theorem characterRestrict_splitComponent_injective :
    Function.Injective (characterRestrict (a ≫ l)) := by
  let ζ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  let := r.isCompatible.levi.isClosedSubgroup.mono
  have hP : (Dynamic.parabolic ζ).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, r.parabolic_eq_splitComponentCocharacter⟩
  have hZ : (Dynamic.centralizer ζ).IsRepresentedBy (l ≫ p) := by
    have : Mono (l ≫ p).hom.hom.left := by
      change Mono (l.hom.hom.left ≫ p.hom.hom.left)
      infer_instance
    exact ⟨Over.mono_of_mono_left _, r.levi_eq_splitComponentCocharacter⟩
  have hl : Dynamic.centralizerToParabolic hP hZ = l :=
    hP.hom_ext (Dynamic.centralizerToParabolic_comp hP hZ)
  have hL : Function.Injective (characterRestrict l) := by
    rw [← hl]
    exact (Dynamic.parabolicCharacterEquiv hP r.isCompatible.parabolic.isClosedSubgroup hZ).injective
  have hA := characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter
    r.isCompatible.levi.isConnectedReductive r.isCompatible.splitComponent
  rw [characterRestrict_comp]
  exact hA.comp hL

include r in
/-- Real character restriction is injective by flatness over the integers. -/
theorem realParameterRestriction_splitComponent_injective :
    Function.Injective (realParameterRestriction (F := F) (a ≫ l)) := by
  let f := ((rationalCharacters.equivCharacterLattice A).toAddMonoidHom.comp
    (characterRestrict (a ≫ l))).toIntLinearMap
  have hf : Function.Injective f :=
    (rationalCharacters.equivCharacterLattice A).injective.comp (characterRestrict_splitComponent_injective r)
  change Function.Injective (f.lTensor ℝ)
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

variable [NumberField F] {K : Subgroup (AdelicGroupPoints F G)}

/-- View the Iwasawa functional on parabolic characters as a linear functional
on the real split-component character space, using a linear retraction of
restriction. -/
def IsIwasawaCompact.splitComponentLinearHeight (hK : IsIwasawaCompact p K)
    (x : AdelicGroupPoints F G) : Vstar A →ₗ[ℝ] ℝ :=
  ((realParameterPairing F P).flip (hK.height x)).comp
    (realParameterRestriction (a ≫ l)).leftInverse

include r in
/-- On restricted parabolic parameters this is the original height pairing. -/
theorem IsIwasawaCompact.splitComponentLinearHeight_restrict (hK : IsIwasawaCompact p K)
    (x : AdelicGroupPoints F G) (ν : RealCharacterParameter F P) :
    hK.splitComponentLinearHeight (a := a) (l := l) x (realParameterRestriction (a ≫ l) ν) =
      realParameterPairing F P ν (hK.height x) := by
  rw [IsIwasawaCompact.splitComponentLinearHeight, LinearMap.comp_apply,
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr
      (realParameterRestriction_splitComponent_injective r))]
  rfl

include r in
/-- On each restricted integral character the linear functional is the original
Iwasawa character evaluation. -/
theorem IsIwasawaCompact.splitComponentLinearHeight_character (hK : IsIwasawaCompact p K)
    (x : AdelicGroupPoints F G) (χ : rationalCharacters P) :
    hK.splitComponentLinearHeight (a := a) (l := l) x
        ((1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
          (characterRestrict (a ≫ l) χ)) = hK.height x χ := by
  change hK.splitComponentLinearHeight (a := a) (l := l) x
    (realParameterRestriction (a ≫ l) ((1 : ℝ) ⊗ₜ[ℤ] χ)) = _
  rw [hK.splitComponentLinearHeight_restrict r, realParameterPairing_tmul, one_mul]

variable [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]

omit [IsAffineHom G.X.hom] in
/-- Restricted ambient characters have zero Iwasawa evaluation at principal points. -/
theorem IsIwasawaCompact.height_rational_characterRestrict (hK : IsIwasawaCompact p K)
    (x : RationalGroupPoints F G) (χ : rationalCharacters G) :
    hK.height (rational F G x) (characterRestrict p χ) = 0 := by
  obtain ⟨q, k, hk, hq⟩ := hK.exists_eq (rational F G x)
  have h0 := characterLog_rational F G x
  rw [← hq, characterLog_mul, characterLog_eq_zero_on_compactSubgroup F G K hK.isCompact hk,
    add_zero, characterLog_map] at h0
  rw [hK.height_eq hk hq]
  exact congrArg (fun H : RealCharacterDual F G => H χ) h0

variable [LocallyOfFiniteType G.X.hom]
  [Mono r.data.i.hom.hom.left] [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  [Fintype (relativeWeylGroup r.data.i)]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

include hA hT in
set_option maxHeartbeats 900000 in
/-- Sufficiently regular parameters give an arbitrary inverse power of the
projective height of the rational parabolic coset, uniformly on compact
parameter sets in the specified coordinates. -/
theorem IsIwasawaCompact.exists_norm_heightPower_rational_le_projectiveHeight
    (hK : IsIwasawaCompact p K) (hG : IsConnectedReductive G)
    {n : ℕ} (σ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hstab : σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j)
    (d : ℝ) (hd : 0 ≤ d) :
    ∃ R : ℝ, ∀ (m : ℕ) (e : (Fin m → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P)
      (Λ : Set (Fin m → ℂ)), IsCompact Λ →
      (∀ s ∈ Λ, r.IsRegularParameter hA hT R (e s)) →
      ∃ B : ℝ, 0 < B ∧ ∀ x : RationalGroupPoints F G, ∀ s ∈ Λ,
        ‖hK.heightPower (e s) (rational F G x)‖ ≤ B *
          (parabolicRationalProjectiveEmbedding σ j hstab
            (Quotient.mk _ ⟨rational F G x, ⟨x, rfl⟩⟩)).mulHeight ^ (-d) := by
  classical
  let αP := r.splitComponentCocharacter
  let iA := a ≫ l ≫ p
  let H := fun x : RationalGroupPoints F G =>
    hK.splitComponentLinearHeight (a := a) (l := l) (rational F G x)
  let adm := IsOppositeIntersectionAdmissible iA αP (-αP)
  choose D hD using fun (mu : cocharacterLattice A) (hmu : adm mu) =>
    exists_le_height_oppositeAdmissibleWeightCharacter r hK hG mu hmu
  let c : cocharacterLattice A → ℝ := fun mu => if hmu : adm mu then D mu hmu else 0
  have hlow (x : RationalGroupPoints F G) (mu : cocharacterLattice A) (hmu : adm mu) :
      -c mu ≤ H x ((1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
        (positiveWeightCharacter iA mu)) := by
    rw [show c mu = D mu hmu by simp only [c, dite_eq_left hmu]]
    rw [show positiveWeightCharacter iA mu = characterRestrict (a ≫ l)
      (r.oppositeAdmissibleWeightCharacter hG mu hmu) from
        (r.characterRestrict_oppositeAdmissibleWeightCharacter hG mu hmu).symm]
    change -D mu hmu ≤ hK.splitComponentLinearHeight (a := a) (l := l) (rational F G x) _
    rw [hK.splitComponentLinearHeight_character r]
    exact hD mu hmu x
  have hGzero (x : RationalGroupPoints F G) (χ : rationalCharacters G) :
      H x ((1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
        (characterRestrict (a ≫ l ≫ p) χ)) = 0 := by
    rw [← Category.assoc, characterRestrict_comp, AddMonoidHom.comp_apply]
    change hK.splitComponentLinearHeight (a := a) (l := l) (rational F G x) _ = 0
    rw [hK.splitComponentLinearHeight_character r, hK.height_rational_characterRestrict]
  obtain ⟨χ, Dχ, hχ⟩ := exists_height_le_sub_log_parabolicProjectiveEmbedding σ j hK hstab
  let ψ : Vstar A := realParameterRestriction (a ≫ l) ((1 : ℝ) ⊗ₜ[ℤ] χ)
  let B := weylInducedCharacterForm hA hT r.data.f r.data.i
  obtain ⟨R, L, hcone⟩ := exists_parabolicRootCone_decay r hA hT relativeRootSystem hG
    αP (-αP) c ψ d
  refine ⟨R, fun m e Λ hΛ hreg => ?_⟩
  let ν := fun s : Fin m → ℂ => realParameterRestriction (a ≫ l) (parameterRealPart F P (e s))
  let S := (hA.finite_relativeRoots iA).toFinset
  have hS (α : characterLattice A) : α ∈ S ↔ α ∈ relativeRoots iA := Set.Finite.mem_toFinset _
  have hcont (α : characterLattice A) : Continuous fun s => B (ν s) ((1 : ℝ) ⊗ₜ[ℤ] α) := by
    let f := (B.flip ((1 : ℝ) ⊗ₜ[ℤ] α)).comp
      ((realParameterRestriction (a ≫ l)).comp
        ((parameterRealPart F P).comp (e.restrictScalars ℝ)))
    exact f.continuous_of_finiteDimensional
  have hcontAbs : Continuous fun s => relativeRootAbsSum iA B (ν s) := by
    simp_rw [relativeRootAbsSum_eq_sum iA B S hS]
    exact continuous_finsetSum _ fun α _ => (hcont α).abs
  let g : (Fin m → ℂ) → ℝ := fun s => L * (1 + relativeRootAbsSum iA B (ν s))
  have hg : Continuous g := continuous_const.mul (continuous_const.add hcontAbs)
  obtain ⟨M, hM⟩ := (hΛ.image hg).bddAbove
  refine ⟨Real.exp (d * Dχ + M), Real.exp_pos _, fun x s hs => ?_⟩
  let q := parabolicRationalProjectiveEmbedding σ j hstab
    (Quotient.mk _ ⟨rational F G x, ⟨x, rfl⟩⟩)
  have hψ : H x ψ ≤ Dχ - q.logHeight := by
    change hK.splitComponentLinearHeight (a := a) (l := l) (rational F G x)
      (realParameterRestriction (a ≫ l) ((1 : ℝ) ⊗ₜ[ℤ] χ)) ≤ _
    rw [hK.splitComponentLinearHeight_restrict r, realParameterPairing_tmul, one_mul]
    exact hχ x
  have hreg' : ∀ α ∈ relativeRoots iA, 0 < latticePairing A α αP →
      latticePairing A α (-αP) < 0 → R < B (ν s) ((1 : ℝ) ⊗ₜ[ℤ] α) := by
    intro α hα hp _
    have hm : α ∈ r.unipotentRoots := by
      rw [r.unipotentRoots_eq_intrinsicPositiveRoots hG]
      exact ⟨hα, hp⟩
    exact hreg s hs α hm
  have hdecay := hcone (H x) (hlow x) (hGzero x) (ν s) hreg'
  have hM' : g s ≤ M := hM ⟨s, hs, rfl⟩
  have habs : -d * |H x ψ| ≤ d * Dχ - d * q.logHeight := by
    have h := mul_le_mul_of_nonneg_left hψ hd
    have h' := mul_le_mul_of_nonneg_left (neg_le_abs (H x ψ)) hd
    linarith
  have hineq : H x (ν s) ≤ d * Dχ + M + Real.log q.mulHeight * (-d) := by
    rw [← Projectivization.logHeight_eq_log_mulHeight]
    change H x (ν s) ≤ -d * |H x ψ| + g s at hdecay
    linarith
  rw [hK.norm_heightPower, ← hK.splitComponentLinearHeight_restrict r]
  change Real.exp (H x (ν s)) ≤ Real.exp (d * Dχ + M) * q.mulHeight ^ (-d)
  rw [Real.rpow_def_of_pos q.mulHeight_pos, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hineq

end Langlands.Global.AdelicGroupPoints

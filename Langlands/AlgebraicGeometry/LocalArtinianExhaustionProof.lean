import Langlands.AlgebraicGeometry.LocalArtinianExhaustionKernels

/-! # The local geometric Artinian exhaustion theorem -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.UnramifiedFunctor
open Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.LocalArtinianExhaustion

variable {X Y : Scheme.{u}}

/-- An isomorphism on a canonical thickening forces the defining ideal inside
the corresponding extended maximal-ideal power. -/
theorem ker_ideal_le_pow_of_thickening_isIso {R : CommRingCat.{u}} [IsLocalRing R]
    (f : X ⟶ Spec R) (j : Y ⟶ X) (n : ℕ)
    [IsIso (pullback.snd j (pullback.fst f (maximalIdealPowQuotientMap R n)))]
    (U : X.affineOpens) :
    j.ker.ideal U ≤ ((maximalIdeal R).map (baseSectionHom f U)) ^ (n + 1) := by
  let p := pullback.fst f (maximalIdealPowQuotientMap R n)
  have hker : j.ker ≤ p.ker := by
    simpa only [liftOfPullbackIso_fac] using (liftOfPullbackIso j p).le_ker_comp j
  have : IsClosedImmersion (maximalIdealPowQuotientMap R n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  calc
    j.ker.ideal U ≤ p.ker.ideal U := hker U
    _ = RingHom.ker (p.app U).hom := p.ker_apply U
    _ = ((maximalIdeal R) ^ (n + 1)).map (baseSectionHom f U) := by
      simpa only [p, maximalIdealPowQuotientMap, Picard.AffineBaseChangeKernel.sectionHom,
        Ideal.mk_ker] using
        Picard.AffineBaseChangeKernel.affine_ker
          (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1))) f
          Ideal.Quotient.mk_surjective U.1 U.2
    _ = _ := Ideal.map_pow _ _ _

/-- A chosen affine separating stage for a morphism already full on the
punctured base. -/
def affineSeparationIndex {R : CommRingCat.{u}} [IsLocalRing R]
    [IsLocallyNoetherian X] (f : X ⟶ Spec R) (j : Y ⟶ X)
    [IsIso (pullback.snd j (pullback.fst f (puncturedSpectrum R).ι))]
    (U : X.affineOpens) : ℕ :=
  (exists_affine_ker_inf_pow_eq_bot f j U).choose

theorem affineSeparationIndex_spec {R : CommRingCat.{u}} [IsLocalRing R]
    [IsLocallyNoetherian X] (f : X ⟶ Spec R) (j : Y ⟶ X)
    [IsIso (pullback.snd j (pullback.fst f (puncturedSpectrum R).ι))]
    (U : X.affineOpens) :
    0 < affineSeparationIndex f j U ∧ j.ker.ideal U ⊓
      ((maximalIdeal R).map (baseSectionHom f U)) ^ (affineSeparationIndex f j U + 1) = ⊥ :=
  (exists_affine_ker_inf_pow_eq_bot f j U).choose_spec

/-- A separating affine stage also separates every deeper power. -/
theorem affine_ker_inf_pow_eq_bot_of_ge {R : CommRingCat.{u}} [IsLocalRing R]
    [IsLocallyNoetherian X] (f : X ⟶ Spec R) (j : Y ⟶ X)
    [IsIso (pullback.snd j (pullback.fst f (puncturedSpectrum R).ι))]
    (U : X.affineOpens) (n : ℕ) (hn : affineSeparationIndex f j U ≤ n) :
    j.ker.ideal U ⊓ ((maximalIdeal R).map (baseSectionHom f U)) ^ (n + 1) = ⊥ := by
  apply le_antisymm ?_ bot_le
  exact (inf_le_inf_left _ (Ideal.pow_le_pow_right (Nat.add_le_add_right hn 1))).trans_eq
    (affineSeparationIndex_spec f j U).2

/-- The local geometric exhaustion step, retaining all scheme structure. -/
theorem localArtinianExhaustion : Statement.{u, v} := by
  intro R _ _ X f hft hqf hqc I _ _ _ Y j hj hmono hU hn
  let := hft
  let := hqf
  let := hqc
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨k, hsk, hck, hUk⟩ := exists_closed_surjective_stage R f Y j hj hmono hU (hn 0)
  let := hsk
  let := hck
  let := hUk
  let 𝒰 := X.affineCover.finiteSubcover
  let V (a : 𝒰.I₀) : X.affineOpens := ⟨(𝒰.f a).opensRange, isAffineOpen_opensRange _⟩
  let n := Finset.univ.sup (fun a : 𝒰.I₀ => affineSeparationIndex f (j k) (V a))
  have hsep (a : 𝒰.I₀) : (j k).ker.ideal (V a) ⊓
      ((maximalIdeal R).map (baseSectionHom f (V a))) ^ (n + 1) = ⊥ :=
    affine_ker_inf_pow_eq_bot_of_ge f (j k) (V a) n (Finset.le_sup (f := fun a : 𝒰.I₀ => affineSeparationIndex f (j k) (V a))
      (Finset.mem_univ a))
  obtain ⟨i, hi⟩ := hn n
  obtain ⟨l, hkl, hil⟩ := exists_ge_ge k i
  obtain ⟨a, ha⟩ := hmono k l hkl
  obtain ⟨b, hb⟩ := hmono i l hil
  let := hj l
  let := hi
  have hnl := pullback_isIso_of_factor (j i) (j l)
    (pullback.fst f (maximalIdealPowQuotientMap R n)) b hb
  have hsl : Surjective (j l) := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := (j k).surjective x
    refine ⟨a y, ?_⟩
    change (a ≫ j l) y = x
    rw [ha]
    exact hy
  have : IsClosedImmersion (j l) := closedImmersion_of_surjective (j l)
  refine ⟨l, IsClosedImmersion.isIso_iff_ker_eq_bot.mpr ?_⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V 𝒰.iSup_opensRange
  intro c
  change (j l).ker.ideal (V c) = ⊥
  have hker : (j l).ker ≤ (j k).ker := by
    simpa only [ha] using a.le_ker_comp (j l)
  exact le_antisymm ((le_inf (hker (V c))
    (ker_ideal_le_pow_of_thickening_isIso f (j l) n (V c))).trans_eq (hsep c)) bot_le

end Langlands.AlgebraicGeometry.LocalArtinianExhaustion

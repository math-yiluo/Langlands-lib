import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.ReflectionStandardCocharacter
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.StandardParabolicClassificationStatement
import Langlands.GroupScheme.Rational.StandardParabolicClassificationReduction
import Langlands.GroupScheme.Rational.PositiveRootStabilizerAveraging
import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof

/-! # Proof of the rational classification of standard parabolics -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-! ### Chamber combinatorics inside the stabilizer of a cocharacter -/

section Chamber

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

omit [IsAffineHom G.X.hom] in
/-- The identity normalizing point acts trivially on cocharacters. -/
theorem cocharacterAut_normalizingAut_one (ξ : cocharacterLattice T) :
    cocharacterAut (normalizingAut i 1) ξ = ξ := by
  change normalizerCocharacterAction i 1 ξ = ξ
  rw [map_one]
  rfl

/-- **Chamber move in the stabilizer of `ξ`.** Among the normalizing points fixing the
pairings of `ξ` with all relative roots, one moves `eta` so that it pairs nonnegatively with
every positive relative root of `ν` orthogonal to `ξ`. The point maximizes the pairing with
the sum of the positive roots; a reflection in a positive root orthogonal to `ξ` keeps the
pairings of `ξ` and would increase it. -/
theorem HasRelativeRootSystem.exists_normalizerPoint_fixing_nonneg
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (ν ξ eta : cocharacterLattice T) :
    ∃ u : normalizerPoints i,
      (∀ β ∈ relativeRoots i,
        latticePairing T β (cocharacterAut (normalizingAut i u) ξ) = latticePairing T β ξ) ∧
      ∀ α ∈ positiveRelativeRoots i ν, latticePairing T α ξ = 0 →
        0 ≤ latticePairing T α (cocharacterAut (normalizingAut i u) eta) := by
  classical
  have hΦ := hroot.finite_relativeRoots i hT
  have hfin := hroot.finite_positiveRelativeRoots i hT ν
  have := hΦ.to_subtype
  set A := hfin.toFinset with hA
  have hmemA : ∀ {β : characterLattice T}, β ∈ A ↔ β ∈ positiveRelativeRoots i ν :=
    fun {_} => hfin.mem_toFinset
  set ρ : characterLattice T := positiveRootSum i ν with hρdef
  have hρ : ρ = ∑ β ∈ A, β := positiveRootSum_eq_sum i hfin
  have hpair_sum : ∀ (f : characterLattice T ≃ₗ[ℤ] characterLattice T)
      (ζ : cocharacterLattice T),
      latticePairing T (f ρ) ζ = ∑ β ∈ A, latticePairing T (f β) ζ := by
    intro f ζ
    rw [hρ, map_sum, map_sum, LinearMap.sum_apply]
  set N : Set (normalizerPoints i) := {u | ∀ β ∈ relativeRoots i,
    latticePairing T β (cocharacterAut (normalizingAut i u) ξ) = latticePairing T β ξ}
    with hNdef
  set F : normalizerPoints i → ℤ :=
    fun n => latticePairing T ρ (cocharacterAut (normalizingAut i n) eta) with hFdef
  -- the values of `F` are sums of pairings of `eta` with actual relative roots
  have hrange : (Set.range F).Finite := by
    let H : (A → relativeRoots i) → ℤ :=
      fun g => ∑ β ∈ A.attach, latticePairing T (g β : characterLattice T) eta
    refine (Set.finite_range H).subset ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨fun β => ⟨weylAction i n⁻¹ β,
      weylAction_mapsTo_relativeRoots i n⁻¹ (hmemA.mp β.2).1⟩, ?_⟩
    simp only [H, hFdef, latticePairing_cocharacterAut_normalizingAut]
    rw [Finset.sum_attach A (fun β => latticePairing T (weylAction i n⁻¹ β) eta)]
    have := hpair_sum (weylAction i n⁻¹) eta
    exact this.symm
  have h1 : (1 : normalizerPoints i) ∈ N := by
    intro β _
    rw [cocharacterAut_normalizingAut_one]
  obtain ⟨_, ⟨u₀, hu₀, rfl⟩, hmax⟩ := Set.exists_max_image (F '' N) id
    (hrange.subset (Set.image_subset_range F N)) ⟨F 1, 1, h1, rfl⟩
  refine ⟨u₀, hu₀, fun α hα hαξ => ?_⟩
  set eta' := cocharacterAut (normalizingAut i u₀) eta with heta'
  by_contra hneg
  replace hneg := lt_of_not_ge hneg
  obtain ⟨w, hαr, c, hc, hw⟩ := hroot.exists_isRelativeReflection hα.1
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
  have hρmem : toRat ρ ∈ relativeRootSpan i := by
    rw [hρ, map_sum]
    exact Submodule.sum_mem _ fun β hβ => toRat_mem_ratSpan (hmemA.mp hβ).1
  have hαν : 0 < latticePairing T α ν := hα.2
  -- the reflection negates `α`
  have hmα : latticePairing T (weylAction i m α) ν = -latticePairing T α ν := by
    have h := latticePairing_weylAction_of_reflection i hαr hc hw (toRat_mem_ratSpan hαr) ν
    rw [hc] at h
    exact_mod_cast (by linarith : (latticePairing T (weylAction i m α) ν : ℚ) =
      -(latticePairing T α ν : ℚ))
  -- comparison of the sums over the positive roots and over their images
  have hlt : ∑ β ∈ A, latticePairing T (weylAction i m β) ν <
      ∑ β ∈ A, latticePairing T β ν := by
    have himage : ∑ β ∈ A, latticePairing T (weylAction i m β) ν =
        ∑ y ∈ A.image (weylAction i m), latticePairing T y ν :=
      (Finset.sum_image (f := fun y => latticePairing T y ν)
        fun x _ y _ h => (weylAction i m).injective h).symm
    rw [himage, ← Finset.sum_filter_add_sum_filter_not (A.image (weylAction i m)) (· ∈ A)]
    have hle : ∑ y ∈ (A.image (weylAction i m)).filter (· ∈ A), latticePairing T y ν ≤
        ∑ β ∈ A, latticePairing T β ν :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => (Finset.mem_filter.mp hy).2)
        fun y hy _ => (hmemA.mp hy).2.le
    have hneg' : ∑ y ∈ (A.image (weylAction i m)).filter (· ∉ A), latticePairing T y ν < 0 := by
      have h0 : ∑ y ∈ (A.image (weylAction i m)).filter (· ∉ A), latticePairing T y ν <
          ∑ y ∈ (A.image (weylAction i m)).filter (· ∉ A), (0 : ℤ) := by
        apply Finset.sum_lt_sum
        · intro y hy
          obtain ⟨hyB, hyA⟩ := Finset.mem_filter.mp hy
          obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hyB
          have hroot' : weylAction i m β ∈ relativeRoots i :=
            weylAction_mapsTo_relativeRoots i m (hmemA.mp hβ).1
          by_contra hpos
          exact hyA (hmemA.mpr ⟨hroot', lt_of_not_ge hpos⟩)
        · refine ⟨weylAction i m α, Finset.mem_filter.mpr
            ⟨Finset.mem_image_of_mem _ (hmemA.mpr hα), ?_⟩, ?_⟩
          · intro hgα
            have := (hmemA.mp hgα).2
            rw [hmα] at this
            linarith
          · rw [hmα]
            linarith
      simpa using h0
    linarith
  -- hence the reflection coefficient of `ρ` is positive
  have hcpos : 0 < c ⟨toRat ρ, hρmem⟩ := by
    have h := latticePairing_weylAction_of_reflection i hαr hc hw hρmem ν
    have hsum := hpair_sum (weylAction i m) ν
    have hsum1 := hpair_sum (LinearEquiv.refl ℤ _) ν
    simp only [LinearEquiv.refl_apply] at hsum1
    have hlt' : (latticePairing T (weylAction i m ρ) ν : ℚ) < latticePairing T ρ ν := by
      rw [hsum, hsum1]
      exact_mod_cast hlt
    have hανq : (0 : ℚ) < latticePairing T α ν := by exact_mod_cast hαν
    have hprod : 0 < c ⟨toRat ρ, hρmem⟩ * latticePairing T α ν := by linarith
    exact pos_of_mul_pos_left hprod hανq.le
  -- the reflected point still fixes the pairings of `ξ`
  have hmem : m⁻¹ * u₀ ∈ N := by
    intro β hβ
    rw [cocharacterAut_normalizingAut_mul, latticePairing_cocharacterAut_normalizingAut, inv_inv]
    have h := latticePairing_weylAction_of_reflection i hαr hc hw (toRat_mem_ratSpan hβ)
      (cocharacterAut (normalizingAut i u₀) ξ)
    rw [hu₀ β hβ, hu₀ α hαr, hαξ] at h
    have h' : (latticePairing T (weylAction i m β) (cocharacterAut (normalizingAut i u₀) ξ) : ℚ) =
        latticePairing T β ξ := by
      rw [h]
      push_cast
      ring
    exact_mod_cast h'
  -- and has a strictly larger value of `F`
  have hbig : F u₀ < F (m⁻¹ * u₀) := by
    have hval : F (m⁻¹ * u₀) = latticePairing T (weylAction i m ρ) eta' := by
      simp only [hFdef]
      rw [cocharacterAut_normalizingAut_mul, latticePairing_cocharacterAut_normalizingAut,
        inv_inv]
    have hFu : F u₀ = latticePairing T ρ eta' := rfl
    have h := latticePairing_weylAction_of_reflection i hαr hc hw hρmem eta'
    have hetaq : (latticePairing T α eta' : ℚ) < 0 := by exact_mod_cast hneg
    have hmul : 0 < c ⟨toRat ρ, hρmem⟩ * -(latticePairing T α eta' : ℚ) :=
      mul_pos hcpos (neg_pos.mpr hetaq)
    have : (F u₀ : ℚ) < F (m⁻¹ * u₀) := by
      rw [hval, h, hFu]
      linarith
    exact_mod_cast this
  exact absurd (hmax _ ⟨m⁻¹ * u₀, hmem, rfl⟩) (not_le.mpr hbig)

/-- **Dominant cocharacters in one Weyl orbit have the same root pairings.** If `λ` and its
image under a normalizing point `n` both pair nonnegatively with the positive relative roots
of a generic `ν`, then they have the same pairing with every relative root. The proof moves
`n⁻¹ ν` into the chamber of `ν` by a point fixing the pairings of `λ` and applies the trivial
positive-root stabilizer. -/
theorem HasRelativeRootSystem.latticePairing_eq_of_dominant
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hstab : HasTrivialPositiveRootStabilizer i ν)
    (lam : cocharacterLattice T) (n : normalizerPoints i)
    (hlam : ∀ α ∈ positiveRelativeRoots i ν, 0 ≤ latticePairing T α lam)
    (hnlam : ∀ α ∈ positiveRelativeRoots i ν,
      0 ≤ latticePairing T α (cocharacterAut (normalizingAut i n) lam)) :
    ∀ β ∈ relativeRoots i,
      latticePairing T β (cocharacterAut (normalizingAut i n) lam) = latticePairing T β lam := by
  set eta := cocharacterAut (normalizingAut i n⁻¹) ν with hetadef
  have heta : ∀ β, latticePairing T β eta = latticePairing T (weylAction i n β) ν := by
    intro β
    rw [hetadef, latticePairing_cocharacterAut_normalizingAut, inv_inv]
  have hinv : ∀ (m : normalizerPoints i) (β : characterLattice T),
      weylAction i m⁻¹ (weylAction i m β) = β := by
    intro m β
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  -- the roots positive on `eta` are nonnegative on `λ`
  have hetalam : ∀ β ∈ relativeRoots i, 0 < latticePairing T β eta →
      0 ≤ latticePairing T β lam := by
    intro β hβ hpos
    have hmem : weylAction i n β ∈ positiveRelativeRoots i ν :=
      ⟨weylAction_mapsTo_relativeRoots i n hβ, by rwa [← heta β]⟩
    have h := hnlam _ hmem
    rwa [latticePairing_cocharacterAut_normalizingAut, hinv] at h
  obtain ⟨u, hu, hu0⟩ := hroot.exists_normalizerPoint_fixing_nonneg i hT ν lam eta
  set eta' := cocharacterAut (normalizingAut i u) eta with heta'def
  have heta' : ∀ α, latticePairing T α eta' = latticePairing T (weylAction i u⁻¹ α) eta := by
    intro α
    rw [heta'def, latticePairing_cocharacterAut_normalizingAut]
  have hgen : ∀ α ∈ relativeRoots i, latticePairing T α eta' ≠ 0 := by
    intro α hα
    rw [heta', heta]
    exact hν _ (weylAction_mapsTo_relativeRoots i n (weylAction_mapsTo_relativeRoots i u⁻¹ hα))
  -- roots positive on `λ` are positive on `eta'`
  have hposlam : ∀ α ∈ relativeRoots i, 0 < latticePairing T α lam →
      0 < latticePairing T α eta' := by
    intro α hα hαlam
    have hβ : weylAction i u⁻¹ α ∈ relativeRoots i := weylAction_mapsTo_relativeRoots i u⁻¹ hα
    have hβlam : latticePairing T (weylAction i u⁻¹ α) lam = latticePairing T α lam := by
      rw [← hu α hα, latticePairing_cocharacterAut_normalizingAut]
    rcases lt_or_gt_of_ne (hgen α hα) with hlt | hgt
    · exfalso
      rw [heta'] at hlt
      have hnegpos : 0 < latticePairing T (-weylAction i u⁻¹ α) eta := by
        rw [map_neg, LinearMap.neg_apply]
        omega
      have h := hetalam _ (hneg _ hβ) hnegpos
      rw [map_neg, LinearMap.neg_apply, hβlam] at h
      omega
    · exact hgt
  -- `eta'` lies in the chamber of `ν`
  have hchamber : ∀ α ∈ positiveRelativeRoots i ν, 0 < latticePairing T α eta' := by
    intro α hα
    rcases (hlam α hα).lt_or_eq with hpos | hzero
    · exact hposlam α hα.1 hpos
    · exact lt_of_le_of_ne (hu0 α hα hzero.symm) (Ne.symm (hgen α hα.1))
  -- the class of `n u⁻¹` preserves the positive roots of `ν`
  have hw : (QuotientGroup.mk (n * u⁻¹) : relativeWeylGroup i) = 1 := by
    apply hstab
    intro α hα
    rw [relativeWeylCharacterAction_mk]
    have he : latticePairing T (weylAction i (n * u⁻¹) α) ν = latticePairing T α eta' := by
      rw [map_mul, LinearEquiv.mul_apply, ← heta, ← heta']
    rw [he]
    constructor
    · intro hpos
      by_contra hnot
      have hneg' : latticePairing T α ν < 0 := lt_of_le_of_ne (not_lt.mp hnot) (hν α hα)
      have hmem : -α ∈ positiveRelativeRoots i ν :=
        ⟨hneg α hα, by rw [map_neg, LinearMap.neg_apply]; omega⟩
      have h := hchamber _ hmem
      rw [map_neg, LinearMap.neg_apply] at h
      omega
    · intro hpos
      exact hchamber α ⟨hα, hpos⟩
  -- hence `n` and `u` act in the same way on cocharacters
  have hnu : cocharacterAut (normalizingAut i n) lam =
      cocharacterAut (normalizingAut i u) lam := by
    have h1 := congrArg (fun w => relativeWeylCocharacterAction i w
      (cocharacterAut (normalizingAut i u) lam)) hw
    simp only [relativeWeylCocharacterAction_mk, map_one, LinearEquiv.coe_one, id_eq] at h1
    rwa [← cocharacterAut_normalizingAut_mul, inv_mul_cancel_right] at h1
  intro β hβ
  rw [hnu, hu β hβ]

end Chamber

/-! ### Rational conjugacy -/

section Conjugacy

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- With the rational Bruhat decomposition for `P = P(ν)`, a rational conjugacy between two
subgroup functors containing `P` is realized by a normalizing point. -/
theorem exists_normalizerPoint_comap_of_bruhat {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
    (hBr : HasRationalBruhatDecomposition i ν) {Q R : SubgroupFunctor G}
    (hQ : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Q)
    (hR : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ R)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (h : Q = R.comap (G.innerIso g).hom) :
    ∃ n : normalizerPoints i,
      Q = R.comap (G.innerIso (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)).hom := by
  obtain ⟨n, hn, p, hp, q, hq, rfl⟩ := hBr.1 g
  refine ⟨⟨n, hn⟩, ?_⟩
  have hpR : R.comap (G.innerIso p).hom = R :=
    R.comap_innerIso_hom_eq_of_mem (hR _ hp)
  have hqQ : Q.comap (G.innerIso q⁻¹).hom = Q :=
    Q.comap_innerIso_hom_eq_of_mem ((Q.carrier _).inv_mem (hQ _ hq))
  calc Q = Q.comap (G.innerIso q⁻¹).hom := hqQ.symm
    _ = (R.comap (G.innerIso (p * n * q)).hom).comap (G.innerIso q⁻¹).hom := by rw [← h]
    _ = R.comap (G.innerIso n).hom := by
        rw [← SubgroupFunctor.comap_comp, ← innerIso_mul_hom, mul_inv_cancel_right,
          innerIso_mul_hom, SubgroupFunctor.comap_comp, hpR]

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

omit [IsAffineHom G.X.hom] in
/-- Conjugating the dynamic parabolic of a cocharacter of the torus by a normalizing point
gives the dynamic parabolic of the transformed cocharacter. -/
theorem dynamicParabolic_comap_normalizerPoint (n : normalizerPoints i)
    (ξ : cocharacterLattice T) :
    (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).comap
        (G.innerIso (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)).hom =
      Dynamic.parabolic
        (CommGroupScheme.groupHom (cocharacterAut (normalizingAut i n⁻¹) ξ) ≫ i) := by
  rw [Dynamic.parabolic_eq_comap_of_iso
    (CommGroupScheme.groupHom (cocharacterAut (normalizingAut i n⁻¹) ξ) ≫ i)
    (G.innerIso (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)),
    ← groupHom_cocharacterAut_comp, ← cocharacterAut_normalizingAut_mul, mul_inv_cancel,
    cocharacterAut_normalizingAut_one]

end Conjugacy

/-! ### Cocharacters conjugated into the torus -/

section Cocharacters

/-- Every cocharacter of a connected reductive group is conjugated by a rational point to a
cocharacter of a maximal split torus `i`, given closed representatives of `P_G(ν ≫ i)` and of
the opposite contracting subgroup for a cocharacter `ν` whose dynamic centralizer is the
centralizer of the torus. The orbit of the base coset of `G / P` under the cocharacter has a
fixed limit point; its rational lift conjugates the cocharacter into `P`, and inside `P` it is
conjugated into the torus. -/
theorem exists_innerIso_comp_eq_torus_of_represented
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hZχ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    {P U : GroupScheme (Spec (CommRingCat.of k))} {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iP)
    (hPc : IsClosedSubgroup iP)
    (hU : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ (CommGroupScheme.groupHom ν ≫ i))).IsRepresentedBy
        iU)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (ξ : cocharacterLattice T),
      zeta ≫ (G.innerIso g).hom = CommGroupScheme.groupHom ξ ≫ i := by
  let := hG.isAffineHom
  let := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Mono iP.hom.hom := hP.1
  have hPpar : IsParabolicSubgroup iP :=
    isParabolicSubgroup_of_range_eq_dynamicParabolic hG iP hPc _ hP.2
  -- the proper homogeneous quotient `G / P`
  obtain ⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqcc, hf⟩ :=
    smoothSubgroupQuotientExistence k G P iP hPc hPpar.smooth
  have hQproper : IsProper Q.hom :=
    parabolicSubgroupQuotientProper k G hG.connectedSpace P iP hPpar Q q
      hsep hft hqc hsm hsurj hqcc hf
  let : IsSeparated Q.hom := hsep
  let : IsProper Q.hom := hQproper
  let : Smooth q.left := hsm
  let : Surjective q.left := hsurj
  let : QuasiCompact q.left := hqcc
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range iP) q hf
  have hact : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q :=
    fun _ g h => Dynamic.flagQuotientSchemeAction_act_lift G _ q hf g h
  -- the orbit of the base coset under `zeta` extends over the affine line
  obtain ⟨e, he⟩ := AffineLine.exists_extension_of_isProper Q
    ((a.restrict zeta).gmOrbit ((1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ≫ q))
  have hfix := SchemeAction.IsGmOrbitExtension.isFixed_evalZero _ he
  -- a rational lift `h₀` of its limit; the cocharacter fixes its coset
  obtain ⟨h₀, hh₀⟩ :=
    exists_rational_lift_of_dynamicParabolic hG _ hP hPc hU q hf (Dynamic.evalZero e)
  have hfixed : ∀ (V : Over (Spec (CommRingCat.of k)))
      (t : V ⟶ (Gm (Spec (CommRingCat.of k))).toGrp.X),
      ((t ≫ zeta.hom.hom) * G.constantPoint h₀ V) ≫ q = G.constantPoint h₀ V ≫ q := by
    intro V t
    have e' := hfix V (Over.homMk V.hom (by simp)) t
    rw [SchemeAction.restrict_act, ← hh₀, ← Category.assoc] at e'
    change a.act (t ≫ zeta.hom.hom) (G.constantPoint h₀ V ≫ q) =
      G.constantPoint h₀ V ≫ q at e'
    rwa [hact] at e'
  have hle : SubgroupFunctor.range (zeta ≫ (G.innerIso h₀⁻¹).hom) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
    rw [← hP.2]
    exact range_conjugate_le_of_fixed_coset _ iP q hf h₀ hfixed
  -- conjugate `h₀⁻¹ zeta h₀` into the torus inside `P(k)`
  obtain ⟨p, -, ρ, hρ⟩ := exists_parabolic_conj_into_torus hG hi ν hZχ _ hle
  refine ⟨p * h₀⁻¹, Additive.ofMul ρ, ?_⟩
  rw [innerIso_mul_hom, ← Category.assoc, hρ]
  rfl

/-- Every cocharacter of a connected reductive group is conjugated by a rational point to a
cocharacter of a given maximal split torus admitting a generic cocharacter. -/
theorem exists_innerIso_comp_eq_torus_cocharacter
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (ξ : cocharacterLattice T),
      zeta ≫ (G.innerIso g).hom = CommGroupScheme.groupHom ξ ≫ i := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact exists_innerIso_comp_eq_torus_of_represented hG hi ν
    (genericCentralizer k G hG T i hi ν hν)
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _) zeta

end Cocharacters

/-! ### The three local inputs of the classification -/

section Inputs

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (hG : IsConnectedReductive G)
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
  (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice T}

include hG hi

/-- Every cocharacter is conjugated by a rational point to a cocharacter of the torus whose
dynamic parabolic contains `P(ν)`. -/
theorem exists_innerIso_comp_eq_dominant_cocharacter (hν : IsGenericCocharacter i ν)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (ξ : cocharacterLattice T),
      zeta ≫ (G.innerIso g).hom = CommGroupScheme.groupHom ξ ≫ i ∧
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i) := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨g, ξ, hg⟩ := exists_innerIso_comp_eq_torus_cocharacter hG hi hν zeta
  obtain ⟨n, hn⟩ := exists_normalizerPoint_parabolic_le_of_statements
    (relativeRootSystemStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization)
    relativeRootSignInclusions hG hi hν ξ
  refine ⟨(n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * g,
    cocharacterAut (normalizingAut i n) ξ, ?_, ?_⟩
  · rw [innerIso_mul_hom, ← Category.assoc, hg, groupHom_cocharacterAut_comp]
  · rw [groupHom_cocharacterAut_comp]
    exact hn

/-- **Standardness by containment.** A dynamic parabolic containing `P(ν)` is a standard
parabolic. -/
theorem exists_standardParabolic_eq_of_parabolic_le_of_bruhat (hν : IsGenericCocharacter i ν)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic zeta) :
    ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν ∧
      Dynamic.parabolic zeta = standardParabolic i ν J := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨g, ξ, hg, hξ⟩ := exists_innerIso_comp_eq_dominant_cocharacter hG hi hν zeta
  have hcomap : Dynamic.parabolic zeta =
      (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).comap (G.innerIso g).hom := by
    rw [← hg]
    exact Dynamic.parabolic_eq_comap_of_iso zeta (G.innerIso g)
  obtain ⟨n, hQ⟩ := exists_normalizerPoint_comap_of_bruhat
    (rationalBruhat k G hG T i hi ν hν) hle hξ g hcomap
  rw [dynamicParabolic_comap_normalizerPoint i n ξ] at hQ
  rw [hQ] at hle ⊢
  exact exists_standardParabolic_eq_of_parabolic_le_of_statements relativeRootSignInclusions
    relativeRootNegation hG T i hi ν hν _ hle

/-- **Conjugacy rigidity.** Two rationally conjugate standard parabolics are equal. -/
theorem standardParabolic_eq_of_isRationallyConjugate_of_bruhat (hν : IsGenericCocharacter i ν) :
    ∀ J K : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
      (standardParabolic i ν J.1).IsRationallyConjugate (standardParabolic i ν K.1) →
        standardParabolic i ν J.1 = standardParabolic i ν K.1 := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  intro J K hJK
  have hstd : StandardCocharacterStatement.{u} :=
    standardCocharacterStatement_of_reflections_of_signs
      (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)
      relativeRootSignsDetermineDynamic
  obtain ⟨ξJ, hξJ⟩ := (hstd k G hG T i hi ν hν J.1 J.2).1
  obtain ⟨ξK, hξK⟩ := (hstd k G hG T i hi ν hν K.1 K.2).1
  have hPJ := ((hstd k G hG T i hi ν hν J.1 J.2).2 ξJ hξJ).1
  have hPK := ((hstd k G hG T i hi ν hν K.1 K.2).2 ξK hξK).1
  have hE := (standardParabolicEndpoints k G hG T i hi ν hν).1
  have hO := (standardParabolic_order_of_root_comparison i ν hν
    (relativeRootNegation k G hG T i hi) (fun J hJ => (hstd k G hG T i hi ν hν J hJ).1)
    (fun a b => (relativeRootSignInclusions k G hG T i hi a b).1)
    (fun a b => (relativeRootSignInclusions k G hG T i hi a b).2)).1
  have hBJ : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ standardParabolic i ν J.1 := by
    rw [← hE]
    exact (hO ∅ J.1 (Set.empty_subset _) J.2).1.mp (Set.empty_subset _)
  have hBK : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ standardParabolic i ν K.1 := by
    rw [← hE]
    exact (hO ∅ K.1 (Set.empty_subset _) K.2).1.mp (Set.empty_subset _)
  obtain ⟨g, hg⟩ := hJK
  obtain ⟨n, hQ⟩ := exists_normalizerPoint_comap_of_bruhat
    (rationalBruhat k G hG T i hi ν hν) hBJ hBK g hg
  rw [hPJ, hPK] at hQ ⊢
  rw [hPJ] at hBJ
  rw [hPK] at hBK
  rw [dynamicParabolic_comap_normalizerPoint i n ξK] at hQ
  rw [hQ] at hBJ ⊢
  -- both cocharacters are dominant
  have hsign := relativeRootSignInclusions k G hG T i hi
  have hdom : ∀ x : cocharacterLattice T,
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom x ≫ i) →
      ∀ α ∈ positiveRelativeRoots i ν, 0 ≤ latticePairing T α x := by
    intro x hx α hα
    exact (hsign ν x).1.mp hx α hα.1 hα.2.le
  have heq := (relativeRootSystemStatement_of_rootRankOneFactorizationStatement
    rootRankOneFactorization k G hG T i hi).latticePairing_eq_of_dominant i
    hi.isSplitSubtorus.1 (relativeRootNegation k G hG T i hi) hν
    (hasTrivialPositiveRootStabilizer i hG hi hν) ξK n⁻¹
    (hdom ξK hBK) (hdom _ hBJ)
  apply le_antisymm
  · exact (hsign _ ξK).1.mpr fun α hα h0 => by rwa [← heq α hα]
  · exact (hsign ξK _).1.mpr fun α hα h0 => by rwa [heq α hα]

end Inputs

/-- **The rational classification of standard parabolics** (Borel–Tits 5.12–5.14): for a
maximal split torus of a connected reductive group over any field and a generic cocharacter,
every dynamic parabolic containing `P(ν)` is standard, and every dynamic parabolic is
rationally conjugate to the standard parabolic of exactly one set of simple relative roots. -/
theorem standardParabolicClassification : StandardParabolicClassificationStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  have hstd : StandardCocharacterStatement.{u} :=
    standardCocharacterStatement_of_reflections_of_signs
      (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)
      relativeRootSignsDetermineDynamic
  refine standardParabolicClassification_of_local_inputs i ν
    (exists_standardParabolic_eq_of_parabolic_le_of_bruhat hG hi hν)
    (fun zeta => ?_)
    (standardParabolic_order_of_root_comparison i ν hν
      (relativeRootNegation k G hG T i hi) (fun J hJ => (hstd k G hG T i hi ν hν J hJ).1)
      (fun a b => (relativeRootSignInclusions k G hG T i hi a b).1)
      (fun a b => (relativeRootSignInclusions k G hG T i hi a b).2)).2
    (standardParabolic_eq_of_isRationallyConjugate_of_bruhat hG hi hν)
  obtain ⟨g, ξ, hg, hξ⟩ := exists_innerIso_comp_eq_dominant_cocharacter hG hi hν zeta
  refine ⟨g, ?_⟩
  rw [hg]
  exact hξ

end Langlands.GroupScheme

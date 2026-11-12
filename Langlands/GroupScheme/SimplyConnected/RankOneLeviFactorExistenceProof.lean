import Langlands.GroupScheme.SimplyConnected.RankOneLeviFactors
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProduct
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedProof
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Reductive.NormalRootContainment
import Langlands.GroupScheme.Derived.NormalityTransfer
import Langlands.GroupScheme.Derived.SemisimpleReflectionReduction
import Langlands.GroupScheme.Derived.CentralSplitTorusProductProof
import Langlands.GroupScheme.Derived.MaximalSplitTorusProof
import Langlands.GroupScheme.Rational.DerivedRelativeRoots
import Langlands.GroupScheme.Rational.DerivedRootTransport
import Langlands.GroupScheme.Rational.TorusCentralizerImage
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof
import Langlands.GroupScheme.Rational.RelativeRankIdentityProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.RootOrthogonalCentralizer
import Langlands.GroupScheme.ProductFactorInclusion

/-!
# Existence of rank-one Levi factors

This module proves `Langlands.GroupScheme.RankOneLeviFactorExistenceStatement`.
For a simple relative root `α`, the factor is the almost-simple factor of the
derived subgroup of the centralizer of a cocharacter orthogonal to `α` that
contains the maximal split torus of that derived subgroup.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

section Helpers

variable {S : Scheme.{u}}

/-- A homomorphism maps commuting points to commuting points. -/
theorem Commute.comp_hom {H G : GroupScheme S} (f : H ⟶ G) {T : Over S} {x y : T ⟶ H.X}
    (h : Commute x y) : Commute (x ≫ f.hom.hom) (y ≫ f.hom.hom) := by
  change (x ≫ f.hom.hom) * (y ≫ f.hom.hom) = (y ≫ f.hom.hom) * (x ≫ f.hom.hom)
  rw [← MonObj.mul_comp, ← MonObj.mul_comp, h.eq]

/-- A monomorphic homomorphism reflects commuting points. -/
theorem Commute.of_comp_hom {H G : GroupScheme S} (f : H ⟶ G) [Mono f.hom.hom] {T : Over S}
    {x y : T ⟶ H.X} (h : Commute (x ≫ f.hom.hom) (y ≫ f.hom.hom)) : Commute x y := by
  change x * y = y * x
  apply (cancel_mono f.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact h.eq

/-- Normality of a range is preserved by an isomorphism of the ambient group. -/
theorem SubgroupFunctor.IsNormal.range_comp_iso {H G G' : GroupScheme S} (f : H ⟶ G)
    (e : G ≅ G') (hf : (SubgroupFunctor.range f).IsNormal) :
    (SubgroupFunctor.range (f ≫ e.hom)).IsNormal := by
  intro T g x _ hx
  obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  obtain ⟨w', hw'⟩ := SubgroupFunctor.mem_range.mp
    (hf T (g ≫ e.inv.hom.hom) (w ≫ f.hom.hom) (Subgroup.mem_top _)
      (SubgroupFunctor.mem_range.mpr ⟨w, rfl⟩))
  refine SubgroupFunctor.mem_range.mpr ⟨w', ?_⟩
  have hg : (g ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = g := by
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
    exact Category.comp_id g
  rw [Grp.comp_hom_hom, ← Category.assoc, hw', MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, hg, Category.assoc, ← Grp.comp_hom_hom]

/-- If every point of a commutative group scheme is trivial, every character vanishes. -/
theorem character_eq_zero_of_points_eq_one {T : CommGroupScheme S}
    (h : ∀ (U : Over S) (x : U ⟶ T.X), x = 1) (χ : characterLattice T) : χ = 0 := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  rw [h U x, MonObj.one_comp, comp_groupHom_zero]

end Helpers

section Field

variable {k : Type u} [Field k]

/-- A group scheme isomorphic to an affine one is affine over the base. -/
theorem isAffineHom_of_iso {G H : GroupScheme (Spec (CommRingCat.of k))} (e : G ≅ H)
    [IsAffineHom G.X.hom] : IsAffineHom H.X.hom := by
  have : IsIso e.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e.symm)).hom)
  rw [← Over.w e.inv.hom.hom]
  infer_instance

/-- In a semisimple group, a closed split torus all of whose roots have a fixed
nonzero multiple in `ℤ • α'` has split-torus rank at most one. -/
theorem IsSemisimple.splitTorusRank_le_one_of_smul_roots
    {D : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom D.X.hom] (hD : IsSemisimple D)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ D}
    (hT : IsSplitTorus T.toGrp) (hj : IsClosedSubgroup j) (α' : characterLattice T)
    {n : ℤ} (hn : n ≠ 0) (hroots : ∀ gam ∈ relativeRoots j, ∃ m : ℤ, n • gam = m • α') :
    splitTorusRank T ≤ 1 := by
  have : Module.Finite ℚ (ℚ ⊗[ℤ] characterLattice T) := hT.finite_characterLatticeRat
  by_contra hlt
  push Not at hlt
  let p : Submodule ℚ (ℚ ⊗[ℤ] characterLattice T) := Submodule.span ℚ {toRat α'}
  have hp : p < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have h1 : Module.finrank ℚ p ≤ 1 :=
      (finrank_span_le_card ({toRat α'} : Set (ℚ ⊗[ℤ] characterLattice T))).trans
        (by rw [Set.toFinset_singleton, Finset.card_singleton])
    rw [htop, finrank_top] at h1
    exact absurd hlt (not_lt.mpr h1)
  obtain ⟨f, hf0, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hp inferInstance
  have hfα : f (toRat α') = 0 := by
    have hmem : f (toRat α') ∈ p.map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
    rw [hfp] at hmem
    exact (Submodule.mem_bot ℚ).mp hmem
  obtain ⟨d, hd, ζ, hζ⟩ := hT.exists_positive_multiple_pairing f
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hα0 : latticePairing T α' ζ = 0 := by
    have h := hζ α'
    rw [hfα, mul_zero] at h
    exact_mod_cast h
  have hann : ∀ gam ∈ relativeRoots j, latticePairing T gam ζ = 0 := by
    intro gam hgam
    obtain ⟨m, hm⟩ := hroots gam hgam
    have h1 := congrArg (fun χ => latticePairing T χ ζ) hm
    simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, hα0, mul_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hn
  have hζ0 := hD.cocharacter_eq_zero_of_annihilates_relativeRoots hT hj ζ hann
  have hfχ : ∀ χ : characterLattice T, f (toRat χ) = 0 := by
    intro χ
    have h := hζ χ
    rw [hζ0, map_zero, Int.cast_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hdq
  apply hf0
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul q χ =>
    have hq : q ⊗ₜ[ℤ] χ = q • toRat χ := by
      rw [toRat_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hq, map_smul, hfχ χ, smul_zero]
    rfl
  | add x y hx hy =>
    rw [map_add, hx, hy]
    simp

/-- A nontrivial homomorphism from a split torus into an affine group scheme has a
closed split-torus image of positive rank. -/
theorem IsSplitTorus.exists_closed_splitTorus_of_ne_zero
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] (σ : T.toGrp ⟶ H)
    (hσ : σ ≠ 0) :
    ∃ (J : Type u) (_ : Finite J) (t : splitTorus (Spec (CommRingCat.of k)) J ⟶ H),
      IsClosedSubgroup t ∧ 1 ≤ Nat.card J := by
  obtain ⟨D', π, t', ht', hπ, -⟩ := hT.exists_factor_isSplitSubtorus σ
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := ht'.1
  refine ⟨J, hJ, eJ.inv ≫ t', ht'.2.iso_comp eJ.symm, ?_⟩
  rw [Nat.one_le_iff_ne_zero, Nat.card_ne_zero]
  refine ⟨?_, hJ⟩
  by_contra hne
  rw [not_nonempty_iff] at hne
  have : Subsingleton (splitTorus (Spec (CommRingCat.of k)) J ⟶ H) :=
    splitTorus.subsingleton_hom_of_isEmpty J H
  have h0 : eJ.inv ≫ t' = 0 := Subsingleton.elim _ _
  apply hσ
  rw [← hπ, ← Iso.hom_inv_id_assoc eJ t', h0, comp_zero, comp_zero]

/-- A closed split torus of a group with split rank at most one, carrying a nonzero
character, factors through a single factor of a finite product decomposition. -/
theorem exists_piSingle_factorization {D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] {I : Type u} [Finite I] [DecidableEq I]
    (F : I → GroupScheme (Spec (CommRingCat.of k))) [∀ x, IsAffineHom (F x).X.hom]
    (φ : D ≅ pi F) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ D) (hj : IsClosedSubgroup j)
    (hrank : splitRank D ≤ 1) {χ : characterLattice T} (hχ : χ ≠ 0) :
    ∃ (x : I) (s : T.toGrp ⟶ F x), j ≫ φ.hom = s ≫ piSingle F x := by
  have : IsAffineHom (pi F).X.hom := isAffineHom_of_iso φ
  let σ : ∀ y, T.toGrp ⟶ F y := fun y => j ≫ φ.hom ≫ Pi.π F y
  have hex : ∃ x, σ x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : j ≫ φ.hom = 0 := by
      apply Pi.hom_ext
      intro y
      rw [Category.assoc, zero_comp]
      exact h y
    have hj0 : j = 0 := by
      rw [← Category.comp_id j, ← φ.hom_inv_id, ← Category.assoc, hz, zero_comp]
    have : Mono j.hom.hom := hj.mono_hom
    apply hχ
    apply character_eq_zero_of_points_eq_one
    intro U x
    apply (cancel_mono j.hom.hom).mp
    rw [hj0]
    change x ≫ (1 : T.X ⟶ D.X) = (1 : U ⟶ T.X) ≫ (1 : T.X ⟶ D.X)
    rw [MonObj.comp_one, MonObj.comp_one]
  obtain ⟨x, hx⟩ := hex
  have hother : ∀ y, y ≠ x → σ y = 0 := by
    intro y hy
    by_contra hy0
    obtain ⟨J₁, _, t₁, ht₁, hJ₁⟩ := hT.exists_closed_splitTorus_of_ne_zero (σ x) hx
    obtain ⟨J₂, _, t₂, ht₂, hJ₂⟩ := hT.exists_closed_splitTorus_of_ne_zero (σ y) hy0
    have h := card_add_card_le_splitRank_pi F (Ne.symm hy) t₁ t₂ ht₁ ht₂
    rw [← splitRank_eq_of_iso φ] at h
    have h2 : ((2 : ℕ) : ℕ∞) ≤ ((Nat.card J₁ + Nat.card J₂ : ℕ) : ℕ∞) := by
      exact_mod_cast (by omega)
    have h3 := (h2.trans h).trans hrank
    norm_num at h3
  refine ⟨x, σ x, ?_⟩
  refine (eq_comp_piSingle F (j ≫ φ.hom) x fun y hy => ?_).trans ?_
  · rw [Category.assoc]
    exact hother y hy
  · simp only [σ, Category.assoc]

end Field

/-- Rank-one Levi factors exist for every simple relative root of a simply connected
group over a field. -/
theorem rankOneLeviFactorExistence : RankOneLeviFactorExistenceStatement.{u} := by
  classical
  intro k _ G _ hsc S i hi ν hν M j hj α hα
  -- The ambient group and the simple root.
  have hGred : IsConnectedReductive G := hsc.isSemisimple.isConnectedReductive
  have : Smooth G.X.hom := hGred.smooth
  have : ConnectedSpace G.X.left := hGred.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hαroot : α ∈ relativeRoots i :=
    positiveRelativeRoots_subset_relativeRoots i ν (simpleRelativeRoots_subset_positive i ν hα)
  have hαν : latticePairing S α ν ≠ 0 := hν α hαroot
  obtain ⟨ζ₀, hαζ₀, hζ₀⟩ := hS.exists_rootOrthogonalCocharacter i α ν
  -- The Levi subgroup `L`, the centralizer of `ζ₀`.
  let χ₀ := CommGroupScheme.groupHom ζ₀ ≫ i
  let L := Dynamic.Affine.centralizerScheme χ₀
  let l : L ⟶ G := Dynamic.Affine.centralizerHom χ₀
  have hl : (Dynamic.centralizer χ₀).IsRepresentedBy l :=
    Dynamic.Affine.isRepresentedBy_centralizerHom χ₀
  have hlc : IsClosedSubgroup l := Dynamic.Affine.isClosedSubgroup_centralizerHom χ₀
  have hLred : IsConnectedReductive L := dynamicCentralizerReductive k G hGred χ₀ L l hlc hl
  have : IsAffineHom L.X.hom := hLred.isAffineHom
  have : Smooth L.X.hom := hLred.smooth
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have hiχ : SubgroupFunctor.range i ≤ Dynamic.centralizer χ₀ :=
    (range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i _)
  obtain ⟨iL, hiLmax, hiL⟩ := hi.lift hl hlc hiχ
  -- A central torus and the derived subgroup `D` of `L`.
  obtain ⟨Z, D, z, d, -, -, -, -, hz, hd, hepi⟩ := reductiveCentralDerivedProduct k L hLred
  have hDss : IsSemisimple D := derivedSubgroupSemisimple k L D d hLred hd
  have hDred := hDss.isConnectedReductive
  have : IsAffineHom D.X.hom := hDred.isAffineHom
  have : Smooth D.X.hom := hDred.smooth
  have hDsc : IsSimplyConnected D := by
    let d₀ := isSplitTorus_gm.dominantFactorization χ₀
    have hrep : (torusCentralizer d₀.inclusion).IsRepresentedBy l := by
      rw [← dynamicCentralizer_eq_torusCentralizer_image χ₀ d₀]
      exact hl
    exact splitTorusCentralizerDerivedSimplyConnected k G hsc _ d₀.inclusion
      d₀.isSplitSubtorus L l hrep D d hd
  -- A maximal split torus of `D` and the split component of `L`.
  obtain ⟨SD, jD, e, hjD, he, hjDe⟩ := derivedMaximalSplitTorus k L D d hLred hd S iL hiLmax
  have hSD : IsSplitTorus SD.toGrp := hjD.isSplitSubtorus.1
  obtain ⟨C, aC, haC⟩ := (splitComponentStatement k L hLred).1
  have hiLl : IsMaximalSplitTorus (iL ≫ l) := by
    rw [hiL]
    exact hi
  obtain ⟨g, hg⟩ := IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus hlc hiLl haC.1
  let c : C ⟶ S := Additive.ofMul g
  have hc : CommGroupScheme.groupHom c ≫ iL = aC := hg
  have hC : IsSplitTorus C.toGrp := haC.1.1.1
  have hcentral : IsCentral (CommGroupScheme.groupHom c ≫ iL) := by
    rw [hc]
    exact haC.1.2
  have hiso := derivedCentralSplitTorusProduct k L D d hLred hd S SD C iL jD e aC c hiLmax hjD
    he hjDe haC hc
  have : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left := hiso.flat
  have : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left := hiso.surjective
  -- The root `α` restricts to a root of `SD`.
  have hαL : α ∈ relativeRoots iL :=
    mem_relativeRoots_of_pairing_eq_zero i ζ₀ hl iL hiL hαroot hαζ₀
  have hα' : e ≫ α ∈ relativeRoots jD :=
    RelativeRoot.mem_relativeRoots_precomp_derived e c jD iL d hd hjDe hSD hS hC hcentral hαL
  -- The split rank of `D` is at most one.
  have hroots : ∀ gam ∈ relativeRoots jD, ∃ m : ℤ, latticePairing S α ν • gam = m • (e ≫ α) := by
    intro gam hgam
    obtain ⟨β, hβL, rfl⟩ :=
      RelativeRoot.exists_relativeRoot_precomp_eq_derived e jD iL d hd hjDe hSD hS hgam
    have hβ : β ∈ relativeRoots i := relativeRoots_subset_of_factor hl iL hiL hβL
    have hβ0 : latticePairing S β ζ₀ = 0 :=
      relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer hl iL hiL ζ₀ le_rfl hβL
    refine ⟨latticePairing S β ν, ?_⟩
    rw [← Preadditive.comp_zsmul, ← Preadditive.comp_zsmul, hζ₀ β hβ hβ0]
  have hrankSD : splitTorusRank SD ≤ 1 :=
    hDss.splitTorusRank_le_one_of_smul_roots hSD hjD.isSplitSubtorus.2 (e ≫ α) hαν hroots
  have hrankD : splitRank D ≤ 1 := by
    rw [(relativeRankIdentity k D hDred SD jD hjD).2.2.2.1]
    exact_mod_cast hrankSD
  -- The almost-simple factor containing `SD`.
  let P := hDsc.almostSimpleProduct
  have : ∀ x, IsAffineHom (P.factor x).X.hom := fun x =>
    (P.isSimplyConnected x).isSemisimple.isConnectedReductive.isAffineHom
  have : IsAffineHom (pi P.factor).X.hom := isAffineHom_of_iso P.iso
  obtain ⟨x₀, s, hs⟩ := exists_piSingle_factorization P.factor P.iso hSD jD
    hjD.isSplitSubtorus.2 hrankD hα'.1
  let A := P.factor x₀
  let incl : A ⟶ pi P.factor := piSingle P.factor x₀
  let h : A ⟶ L := (incl ≫ P.iso.inv) ≫ d
  let a : A ⟶ G := h ≫ l
  have hAsc : IsSimplyConnected A := P.isSimplyConnected x₀
  have hAred : IsConnectedReductive A := hAsc.isSemisimple.isConnectedReductive
  have hincl : IsClosedSubgroup incl := isClosedSubgroup_piSingle P.factor x₀
  have hinv : IsClosedSubgroup P.iso.inv := IsClosedSubgroup.of_iso P.iso.symm
  have hinclD : IsClosedSubgroup (incl ≫ P.iso.inv) := hincl.comp hinv
  have hh : IsClosedSubgroup h := hinclD.comp hd.1
  have ha : IsClosedSubgroup a := hh.comp hlc
  have : Mono a.hom.hom := ha.mono_hom
  have : Epi (subgroupProductMap z d) := hepi
  have hhnormal : (SubgroupFunctor.range h).IsNormal :=
    SubgroupFunctor.IsNormal.range_comp_of_isCentral_of_epi_subgroupProductMap z d hz hd.1 hinclD
      (SubgroupFunctor.IsNormal.range_comp_iso incl P.iso.symm (isNormal_range_piSingle P.factor x₀))
  have hjDs : jD = s ≫ incl ≫ P.iso.inv := by
    rw [← Category.assoc, ← hs, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcomp : CommGroupScheme.groupHom e ≫ iL = s ≫ h := by
    rw [← hjDe, hjDs]
    simp only [h, Category.assoc]
  -- The closed split torus `s` of `A`.
  have hsClosed : IsClosedSubgroup s := by
    apply IsClosedSubgroup.of_comp hincl
    rw [← hs]
    exact hjD.isSplitSubtorus.2.comp (IsClosedSubgroup.of_iso P.iso)
  -- The split rank of `A`.
  have hrankA : splitRank A = 1 := by
    apply le_antisymm
    · exact (splitRank_le_of_isClosedSubgroup _ hinclD).trans hrankD
    · obtain ⟨I, hI, ⟨eI⟩⟩ := hSD
      have hI1 : 1 ≤ Nat.card I := by
        rw [Nat.one_le_iff_ne_zero, Nat.card_ne_zero]
        refine ⟨?_, hI⟩
        by_contra hne
        rw [not_nonempty_iff] at hne
        have : Subsingleton (splitTorus (Spec (CommRingCat.of k)) I ⟶ SD.toGrp) :=
          splitTorus.subsingleton_hom_of_isEmpty I SD.toGrp
        have h0 : eI.inv = 0 := Subsingleton.elim _ _
        apply hα'.1
        apply character_eq_zero_of_points_eq_one
        intro U y
        calc y = y ≫ (eI.hom ≫ eI.inv).hom.hom := by
              rw [Iso.hom_inv_id]
              exact (Category.comp_id y).symm
          _ = 1 := by
              rw [h0, comp_zero]
              exact MonObj.comp_one y
      have hcard := card_le_splitRank I (eI.inv ≫ s) (hsClosed.iso_comp eI.symm)
      exact le_trans (by exact_mod_cast hI1) hcard
  -- The root subgroup of `α` lies in the factor.
  obtain ⟨hqc, hfl, hsu⟩ := RelativeRoot.characterFpqc k S hS α hαroot.1
  have hUL : RelativeRoot.subgroup iL α ≤ SubgroupFunctor.range h :=
    RelativeRoot.subgroup_le_range_of_restriction_ne_zero e iL s h hSD hh hhnormal hcomp α hα'.1
  have hUl : RelativeRoot.subgroup i α ≤ SubgroupFunctor.range l := by
    have hz0 : ζ₀ ≫ α = 0 := by
      apply (gmEndEquiv k).injective
      rw [map_zero]
      exact hαζ₀
    have h1 := RelativeRoot.subgroup_le_fixedSubgroup_of_restriction_eq_zero ζ₀ i α hz0
    rwa [AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer,
      torusCentralizer_gm_eq_dynamicCentralizer, ← hl.2] at h1
  have hcomap : SubgroupFunctor.comap l (RelativeRoot.subgroup i α) = RelativeRoot.subgroup iL α := by
    have := RelativeRoot.subgroup_comap_closedEmbedding iL α l hlc
    rwa [hiL] at this
  have hU : RelativeRoot.subgroup i α ≤ SubgroupFunctor.range a := by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp (hUl T hx)
    have hy : y ∈ (RelativeRoot.subgroup iL α).carrier T := by
      rw [← hcomap, SubgroupFunctor.mem_comap]
      exact hx
    obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp (hUL T hy)
    exact SubgroupFunctor.mem_range.mpr ⟨w, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  -- The factor centralizes every cocharacter orthogonal to `α`.
  have hrange_a : SubgroupFunctor.range a ≤ Dynamic.centralizer χ₀ := by
    intro T x hx
    obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [← hl.2]
    exact SubgroupFunctor.mem_range.mpr ⟨w ≫ h.hom.hom, by
      simp only [a, h, Grp.comp_hom_hom, Category.assoc]⟩
  have h6 : ∀ ζ : cocharacterLattice S, latticePairing S α ζ = 0 →
      SubgroupFunctor.range a ≤ Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) :=
    fun ζ hζ => hrange_a.trans (dynamicCentralizer_le_of_rootOrthogonal hS i hαν hζ₀ hζ)
  -- The factor is normalized by the common centralizer.
  have h7 : ∀ (T : Over (Spec (CommRingCat.of k))) (g x : T ⟶ G.X),
      (∀ ζ : cocharacterLattice S, latticePairing S α ζ = 0 →
        g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier T) →
      x ∈ (SubgroupFunctor.range a).carrier T →
        g * x * g⁻¹ ∈ (SubgroupFunctor.range a).carrier T := by
    intro T g x hg hx
    have hgl : g ∈ (SubgroupFunctor.range l).carrier T := by
      rw [hl.2]
      exact hg ζ₀ hαζ₀
    obtain ⟨g', rfl⟩ := SubgroupFunctor.mem_range.mp hgl
    obtain ⟨w, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    obtain ⟨w', hw'⟩ := SubgroupFunctor.mem_range.mp
      (hhnormal T g' (w ≫ h.hom.hom) (Subgroup.mem_top _)
        (SubgroupFunctor.mem_range.mpr ⟨w, rfl⟩))
    refine SubgroupFunctor.mem_range.mpr ⟨w', ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hw', MonObj.mul_comp, MonObj.mul_comp,
      GrpObj.inv_comp, Category.assoc, ← Grp.comp_hom_hom]
  -- The intersection with `M` is the centralizer of `s` in `A`.
  have hMS : SubgroupFunctor.range j = torusCentralizer i := by
    rw [hj.2]
    exact hS.dynamicCentralizer_eq_torusCentralizer i ν hν
  have hts : ∀ {V : Over (Spec (CommRingCat.of k))} (t : V ⟶ SD.X),
      (t ≫ (CommGroupScheme.groupHom e).hom.hom) ≫ i.hom.hom =
        (t ≫ s.hom.hom) ≫ a.hom.hom := by
    intro V t
    rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← hiL, ← Category.assoc,
      hcomp]
    simp only [a, Grp.comp_hom_hom, Category.assoc]
  let N := subgroupIntersection j a
  let sn : N ⟶ A := subgroupIntersectionSnd j a
  have hpb := subgroupIntersection_isPullback j a
  have : Mono j.hom.hom := hj.1
  have hsnmono : Mono sn.hom.hom := hpb.mono_snd_of_mono
  have hrange : SubgroupFunctor.range sn = torusCentralizer s := by
    apply SubgroupFunctor.ext
    intro U
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      have hy : (y ≫ sn.hom.hom) ≫ a.hom.hom ∈ (torusCentralizer i).carrier U := by
        rw [← hMS]
        refine SubgroupFunctor.mem_range.mpr ⟨y ≫ (subgroupIntersectionFst j a).hom.hom, ?_⟩
        rw [Category.assoc, Category.assoc, hpb.w]
      intro V b t
      have hc := hy V b (t ≫ (CommGroupScheme.groupHom e).hom.hom)
      rw [hts, ← Category.assoc b] at hc
      exact Commute.of_comp_hom a hc
    · intro hx
      let PC : CommGroupScheme (Spec (CommRingCat.of k)) :=
        { toGrp := SD.toGrp ⊗ C.toGrp
          comm := by exact (inferInstance : IsCommMonObj (SD.X ⊗ C.X)) }
      let p : PC.toGrp ⟶ S.toGrp := RelativeRoot.centralComplementProduct e c
      have : IsFinite p.hom.hom.left := hiso.isFinite
      have : Smooth S.X.hom := hS.smooth
      have : IsReduced S.X.left :=
        Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
          S.X.left S.X.hom
      have : Surjective p.hom.hom.left := hiso.surjective
      have : IsSchemeTheoreticallyDominant p.hom.hom.left :=
        IsSchemeTheoreticallyDominant.of_isDominant _
      have hax : x ≫ a.hom.hom ∈ (SubgroupFunctor.range j).carrier U := by
        rw [hMS, ← torusCentralizer_comp_eq_of_isSchemeTheoreticallyDominant p i]
        intro V b t
        have hpt : t ≫ (p ≫ i).hom.hom =
            ((productPointsEquiv SD.toGrp C.toGrp V t).1 ≫
                (CommGroupScheme.groupHom e).hom.hom) ≫ i.hom.hom *
              ((productPointsEquiv SD.toGrp C.toGrp V t).2 ≫
                (CommGroupScheme.groupHom c).hom.hom) ≫ i.hom.hom := by
          rw [Grp.comp_hom_hom, ← Category.assoc, comp_prodHom, MonObj.mul_comp]
        rw [hpt]
        apply Commute.mul_right
        · rw [hts, ← Category.assoc b]
          exact Commute.comp_hom a (hx V b _)
        · have hcen := hcentral V (productPointsEquiv SD.toGrp C.toGrp V t).2
          have hcomm := (commute_of_mem_center hcen ((b ≫ x) ≫ h.hom.hom)).symm
          have hcomm' := Commute.comp_hom l hcomm
          rw [← hiL]
          simpa only [a, Grp.comp_hom_hom, Category.assoc] using hcomm'
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hax
      exact SubgroupFunctor.mem_range.mpr ⟨hpb.lift y x hy, hpb.lift_snd _ _ _⟩
  have hrepN : (torusCentralizer s).IsRepresentedBy sn := ⟨hsnmono, hrange⟩
  refine ⟨A, a, ⟨ha, hAsc, P.isAlmostSimple x₀, hrankA, hU, h6, h7⟩,
    splitTorusCentralizerReductive k A hAred SD s hSD N sn hrepN, ?_⟩
  intro D' d' hd'
  exact splitTorusCentralizerDerivedSimplyConnected k A hAsc SD s ⟨hSD, hsClosed⟩ N sn hrepN
    D' d' hd'

end Langlands.GroupScheme

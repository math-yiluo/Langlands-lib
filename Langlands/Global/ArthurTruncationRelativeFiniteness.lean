import Langlands.Global.ArthurTruncationFinitenessProof
import Langlands.Global.ArthurTruncationChambers
import Langlands.Global.ArthurTruncationCosets
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof
import Langlands.Representation.Exponents.MaximalLeviExponentTransport

/-! # Relative finiteness and rational height invariance for Arthur truncation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Finset TensorProduct
open scoped CategoryTheory.MonObj Classical TensorProduct

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra.StandardLevi
open AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "Roots" => characterLattice T
local notation "Δ" => simpleRelativeRoots i ν
local notation "Points" => AdelicGroupPoints F G
local notation "p[" J "]" => Standard.parabolicHom i ν J
local notation "Pᵣ[" J "]" => parabolicRationalSubgroup F (p[J])
local notation "H₀" => height hi hK hρ
local notation "CorootSpan[" J "]" => ArthurRelative.corootSubspace D J
local notation "Weight[" J "]" => ArthurRelative.weight hG hi ν D J
local notation "Proj[" J "]" => ArthurRelative.levelProjection hG hi ν D J

omit [NumberField F] [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
private def parabolicInclusion {J L : Set Roots} (h : standardParabolic i ν J ≤ standardParabolic i ν L) :
    Standard.parabolicScheme i ν J ⟶ Standard.parabolicScheme i ν L :=
  (Standard.isRepresentedBy_parabolicHom i ν L).factorHom (p[J]) (by
    rw [(Standard.isRepresentedBy_parabolicHom i ν J).2]
    exact h)

omit [NumberField F] [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
private theorem parabolicInclusion_comp {J L : Set Roots}
    (h : standardParabolic i ν J ≤ standardParabolic i ν L) :
    parabolicInclusion h ≫ p[L] = p[J] :=
  (Standard.isRepresentedBy_parabolicHom i ν L).factorHom_comp _ _

omit [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
/-- Membership of a rational point in the standard parabolic is membership in its adelic image. -/
theorem mem_parabolicRationalSubgroup_iff {J : Set Roots} (a : rationalSubgroup F G) :
    a ∈ Pᵣ[J] ↔ (a : Points) ∈ rationalImage F (p[J]) := by
  rw [rationalImage_eq_map]
  rfl

omit [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
include hG hi hν in
/-- Standard parabolic inclusions induce inclusions of their principal rational points. -/
theorem parabolicRationalSubgroup_mono {J L : Set Roots} (hJL : J ⊆ L) (hL : L ⊆ Δ) :
    Pᵣ[J] ≤ Pᵣ[L] := by
  let a := parabolicInclusion
    (((standardParabolicOrder F G hG T i hi ν hν).1 J L (hJL.trans hL) hL).1.mp hJL)
  have ha : a ≫ p[L] = p[J] := parabolicInclusion_comp _
  intro z hz
  rw [mem_parabolicRationalSubgroup_iff] at hz ⊢
  rw [← ha] at hz
  exact rationalImage_comp_le a (p[L]) hz

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
include hG hi hν in
private theorem corootAnnihilator_le_range_parabolic {J : Set Roots} (hJ : J ⊆ Δ) :
    corootAnnihilator i D J ≤ (restrictToTorus F i ν J).range := by
  let L := Standard.leviHom i ν J
  let hL := Standard.isRepresentedBy_leviHom i ν J
  let t := standardLeviTorusFactor i ν J hL
  have ht : t ≫ L = i := standardLeviTorusFactor_comp i ν J hL
  have hrange := standardLeviCharacterAnnihilator F G hG T i hi ν hν J hJ _ L
    (Standard.isClosedSubgroup_leviHom i ν J) hL t ht D
  rw [← hrange]
  rintro _ ⟨χ, rfl⟩
  obtain ⟨⟨ζ, hζ⟩, hstandard⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  have heq := hstandard ζ hζ
  have hp := Standard.isRepresentedBy_parabolicHom i ν J
  have hp' := heq.1 ▸ hp
  have hL' := heq.2.1 ▸ hL
  let π := Dynamic.limitGroupHom hp' hL'
  let j := Dynamic.centralizerToParabolic hp' hL'
  have hj : j ≫ p[J] = L := Dynamic.centralizerToParabolic_comp hp' hL'
  have hjt : t ≫ j = torusToParabolic F i ν J := by
    apply hp.hom_ext
    rw [Category.assoc, hj, ht, torusToParabolic_comp]
  have hπ : torusToParabolic F i ν J ≫ π = t := by
    rw [← hjt, Category.assoc, Dynamic.centralizerToParabolic_comp_limitGroupHom,
      Category.comp_id]
  refine ⟨rationalCharacterRestrictReal π χ, ?_⟩
  change rationalCharacterRestrictReal (torusToParabolic F i ν J)
      (rationalCharacterRestrictReal π χ) = _
  rw [rationalCharacterRestrictReal_comp_apply, hπ]

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
private theorem height_eq_of_comp {P₀ P : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [IsAffine P₀.X.left] [IsAffine P.X.left]
    {p₀ : P₀ ⟶ G} {p : P ⟶ G}
    [IsClosedImmersion p₀.hom.hom.left] [IsClosedImmersion p.hom.hom.left]
    (inc : P₀ ⟶ P) (hinc : inc ≫ p = p₀)
    (hmin : IsIwasawaCompact p₀ K) (hpar : IsIwasawaCompact p K) (g : Points) :
    hpar.height g = realCharacterDualMap F P₀ P inc (hmin.height g) := by
  subst p₀
  exact hpar.height_eq_realCharacterDualMap inc hmin g

omit [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
private theorem toCharacterDual_height_eq {J : Set Roots}
    (inc : Standard.parabolicScheme i ν ∅ ⟶ Standard.parabolicScheme i ν J)
    (hinc : inc ≫ p[J] = p[∅]) (hKP : IsIwasawaCompact (p[J]) K) (g : Points) :
    toCharacterDual F i ν J (H₀ g) = hKP.height g := by
  have hti : torusToParabolic F i ν ∅ ≫ inc = torusToParabolic F i ν J := by
    apply (Standard.isRepresentedBy_parabolicHom i ν J).hom_ext
    rw [Category.assoc, hinc, torusToParabolic_comp, torusToParabolic_comp]
  have hcomp := height_eq_of_comp inc hinc hK hKP g
  refine Eq.trans ?_ hcomp.symm
  apply AddMonoidHom.ext
  intro χ
  let ψ := characterRestrict inc χ
  let m : RealCharacterParameter F (Standard.parabolicScheme i ν ∅) := (1 : ℝ) ⊗ₜ[ℤ] ψ
  have hχ : restrictToTorus F i ν J ((1 : ℝ) ⊗ₜ[ℤ] χ) = restrictToTorus F i ν ∅ m := by
    unfold restrictToTorus
    rw [← hti]
    exact (rationalCharacterRestrictReal_comp_apply (torusToParabolic F i ν ∅) inc
      ((1 : ℝ) ⊗ₜ[ℤ] χ)).symm
  change pair T (restrictToTorus F i ν J ((1 : ℝ) ⊗ₜ[ℤ] χ)) (H₀ g) = hK.height g ψ
  calc
    _ = pair T (restrictToTorus F i ν ∅ m) (H₀ g) := congrArg (fun s => pair T s (H₀ g)) hχ
    _ = realParameterPairing F (Standard.parabolicScheme i ν ∅) m (hK.height g) :=
      pair_toA0 hi.isSplitSubtorus.1 hρ (hK.height g) m
    _ = hK.height g ψ := by
      rw [show m = (1 : ℝ) ⊗ₜ[ℤ] ψ from rfl, realParameterPairing_tmul, one_mul]

omit [LocallyOfFiniteType G.X.hom] in
include hG hi hν in
/-- Rational translation by `P(F)` changes the minimal height by a vector in `𝔞₀ᴾ`. -/
theorem height_sub_mem_parabolicCorootSpan {J : Set Roots} (hJ : J ⊆ Δ)
    (a : rationalSubgroup F G) (ha : a ∈ Pᵣ[J]) (x : Points) :
    H₀ ((a : Points) * x) - H₀ x ∈ CorootSpan[J] := by
  let inc := parabolicInclusion
    (((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J (Set.empty_subset _) hJ).1.mp
      (Set.empty_subset _))
  have hinc : inc ≫ p[J] = p[∅] := parabolicInclusion_comp _
  let hKP : IsIwasawaCompact (p[J]) K := IsIwasawaCompact.of_comp inc (hinc.symm ▸ hK)
  let v := H₀ ((a : Points) * x) - H₀ x
  have hv : toCharacterDual F i ν J v = 0 := by
    obtain ⟨q, hq⟩ := (mem_rationalImage_iff (p[J]) (a : Points)).mp
      ((mem_parabolicRationalSubgroup_iff a).mp ha)
    simp only [v, ← hq, map_sub, toCharacterDual_height_eq hi hK hρ inc hinc hKP,
      hKP.height_rational_mul, sub_self]
  have := isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1
  have hann : v ∈ rightAnn (pair T) (corootAnnihilator i D J) := by
    rw [mem_rightAnn]
    intro m hm
    obtain ⟨χ, rfl⟩ := corootAnnihilator_le_range_parabolic hG hi hν D hJ hm
    rw [← realParameterPairing_toCharacterDual, hv, map_zero]
  rw [StandardLevi.corootAnnihilator_eq_leftAnn, rightAnn_leftAnn] at hann
  exact hann

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
include hν in
private theorem weight_eq_zero_of_notMem {J L : Set Roots} (hJL : J ⊆ L) (hL : L ⊆ Δ)
    {β : Roots} (hβ : β ∈ L) (hb : β ∉ J) {v : V T} (hv : v ∈ CorootSpan[J]) :
    Weight[L] β v = 0 := by
  induction hv using Submodule.span_induction with
  | mem _ ha =>
    obtain ⟨α, hα, rfl⟩ := ha
    have hne : β ≠ α.1 := fun he => hb (he.symm ▸ hα)
    rw [ArthurRelative.weight_coroot hG hi D hν hL hβ α (hJL hα), ite_eq_right hne]
  | zero => simp
  | add v w _ _ hv hw => rw [map_add, hv, hw, add_zero]
  | smul c v _ hv => rw [map_smul, hv, smul_zero]

omit [NumberField F] in
include hν in
private theorem exists_weight_one : ∃ v : V T, ∀ β ∈ Δ, Weight[Δ] β v = 1 := by
  let _ := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  refine ⟨∑ a : Δ, D.realCoroot (simpleToRelativeRoot i ν a), fun β hβ => ?_⟩
  rw [map_sum, Finset.sum_eq_single (⟨β, hβ⟩ : Δ)]
  · rw [ArthurRelative.weight_coroot hG hi D hν subset_rfl hβ _ hβ]
    simp
  · intro a _ ha
    rw [ArthurRelative.weight_coroot hG hi D hν subset_rfl hβ _ a.2]
    exact ite_eq_right (fun h => ha (Subtype.ext h.symm))
  · simp

omit [LocallyOfFiniteType G.X.hom] in
include hν in
/-- The hatted cutoff on the interval `J ⊆ L` is left invariant under `P_J(F)`. -/
theorem tauHat_rationalParabolic_mul {J L : Set Roots} (hJL : J ⊆ L) (hL : L ⊆ Δ) (Tp : V T)
    (a : rationalSubgroup F G) (ha : a ∈ Pᵣ[J]) (x : Points) :
    ArthurRelative.tauHat hG hi ν D J L (H₀ ((a : Points) * x) - Tp) =
      ArthurRelative.tauHat hG hi ν D J L (H₀ x - Tp) := by
  have hv := height_sub_mem_parabolicCorootSpan hG hi hν D hK hρ (hJL.trans hL) a ha x
  simp only [ArthurRelative.tauHat_eq hG hi D J (J₂ := L) hL]
  congr 1
  apply propext (forall_congr' fun β => forall_congr' fun hβ => ?_)
  have he := weight_eq_zero_of_notMem hG hi hν D hJL hL hβ.1 hβ.2 hv
  simp only [map_sub, sub_eq_zero] at he
  rw [map_sub, he, ← map_sub]

omit [LocallyOfFiniteType G.X.hom] in
include hν in
/-- The simple-root cutoff on the interval `J ⊆ L` is left invariant under `P_J(F)`. -/
theorem tau_rationalParabolic_mul {J L : Set Roots} (hJ : J ⊆ Δ) (hL : L ⊆ Δ) (Tp : V T)
    (a : rationalSubgroup F G) (ha : a ∈ Pᵣ[J]) (x : Points) :
    ArthurRelative.tau hG hi ν D J L (H₀ ((a : Points) * x) - Tp) =
      ArthurRelative.tau hG hi ν D J L (H₀ x - Tp) := by
  have hv := height_sub_mem_parabolicCorootSpan hG hi hν D hK hρ hJ a ha x
  have hp : Proj[J] (H₀ ((a : Points) * x) - H₀ x) = 0 := by
    rw [← ArthurRelative.levelProjection_eq_projectionOnto hG hi hν D hJ,
      Submodule.projectionOnto_apply_of_mem_right _ hv]
    rfl
  rw [map_sub, sub_eq_zero] at hp
  have he : Proj[J] (H₀ ((a : Points) * x) - Tp) = Proj[J] (H₀ x - Tp) := by
    simp only [map_sub, hp]
  simp only [ArthurRelative.tau_eq hG hi D J (J₂ := L) hL, he]

include hν in
/-- The relative hatted chamber has finite support on `Q(F) \ P(F)` at every parameter. -/
theorem relative_tauHat_finite {SQ SP : Finset Roots} (hQP : SQ ⊆ SP)
    (hSP : SP ⊆ simpleFinset ν hG hi) (Tp : V T) (x : Points) :
    (Function.support fun c : RelativeCosets (F := F) (i := i) (ν := ν) (SQ : Set Roots) SP =>
      ArthurRelative.tauHat hG hi ν D (SQ : Set Roots) SP
        (H₀ ((((c.out : Pᵣ[(SP : Set Roots)]) : rationalSubgroup F G) : Points) * x) - Tp)).Finite := by
  let J : Set Roots := SP
  have hJ : J ⊆ Δ := fun _ h => (mem_simpleFinset hG hi).mp (hSP h)
  obtain ⟨w, hw⟩ := exists_weight_one hG hi hν D
  let z := Proj[J] (H₀ x - Tp)
  have hz : z ∈ rootAnnihilator T J :=
    ArthurRelative.levelProjection_mem_rootAnnihilator hG hi D hν hJ _
  let X := Tp + z - w
  let E := nestedCosetsEmbedding (Pᵣ[(SQ : Set Roots)]) (Pᵣ[J])
  have hinvariant (a : rationalSubgroup F G) (ha : a ∈ Pᵣ[(SQ : Set Roots)]) (b : rationalSubgroup F G) :
      ArthurRelative.tauHat hG hi ν D (SQ : Set Roots) Δ (H₀ (((a * b : rationalSubgroup F G) : Points) * x) - X) =
      ArthurRelative.tauHat hG hi ν D (SQ : Set Roots) Δ (H₀ ((b : Points) * x) - X) := by
    simp only [Subgroup.coe_mul, mul_assoc]
    exact tauHat_rationalParabolic_mul hG hi hν D hK hρ
      (fun _ h => hJ (hQP h)) subset_rfl X a ha ((b : Points) * x)
  have hfull := truncationFiniteness F G T i ν hG hi hν D K hK hρ SQ
    (mem_powerset.mpr (hQP.trans hSP)) X x
  apply (hfull.preimage E.injective.injOn).subset
  intro c hc
  let g : Pᵣ[J] := c.out
  let y := H₀ ((g : Points) * x)
  let v := y - Tp - z
  have hv : v ∈ CorootSpan[J] := by
    have h := height_sub_mem_parabolicCorootSpan hG hi hν D hK hρ hJ g g.2 x
    have hz' := ArthurRelative.sub_levelProjection_mem_span hG hi (ν := ν) D J (H₀ x - Tp)
    have hv' : v = (y - H₀ x) + (H₀ x - Tp - z) := by dsimp only [v]; abel
    rw [hv']
    exact Submodule.add_mem _ h hz'
  change ArthurRelative.tauHat hG hi ν D (SQ : Set Roots) J (y - Tp) ≠ 0 at hc
  rw [ArthurRelative.tauHat_eq hG hi D (SQ : Set Roots) hJ] at hc
  have hpos : ∀ β ∈ J \ (SQ : Set Roots), 0 < Weight[J] β (y - Tp) := by
    by_contra hn
    exact hc (ite_eq_right hn)
  change ArthurRelative.tauHat hG hi ν D (SQ : Set Roots) Δ (H₀ (((E c).out : Points) * x) - X) ≠ 0
  let f (a : rationalSubgroup F G) :=
    ArthurRelative.tauHat hG hi ν D (SQ : Set Roots) Δ (H₀ ((a : Points) * x) - X)
  have hrep := nestedCosetsEmbedding_out (Pᵣ[(SQ : Set Roots)]) (Pᵣ[J]) (f := f) hinvariant c
  change f ((E c).out) ≠ 0
  rw [hrep]
  change ArthurRelative.tauHat hG hi ν D (SQ : Set Roots) Δ (y - X) ≠ 0
  rw [ArthurRelative.tauHat_eq hG hi D (SQ : Set Roots) subset_rfl, ite_eq_left]
  · exact one_ne_zero
  · intro β hb
    have hX : y - X = v + w := by dsimp only [X, v]; abel
    rw [hX, map_add, hw β hb.1]
    by_cases hj : β ∈ J
    · rw [← ArthurRelative.weight_eq_of_mem_corootSubspace hG hi D hν hJ subset_rfl hj hv]
      change 0 < Weight[J] β (y - Tp - z) + 1
      rw [map_sub, ArthurRelative.weight_eq_zero_of_mem_rootAnnihilator hG hi ν D J β hz, sub_zero]
      exact add_pos (hpos β ⟨hj, hb.2⟩) zero_lt_one
    · rw [weight_eq_zero_of_notMem hG hi hν D hJ subset_rfl hb.1 hj hv, zero_add]
      exact zero_lt_one

include hν in
/-- The relative simple-root chamber also has finite support on `Q(F) \ P(F)`. -/
theorem relative_tau_finite {SQ SP : Finset Roots} (hQP : SQ ⊆ SP)
    (hSP : SP ⊆ simpleFinset ν hG hi) (Tp : V T) (x : Points) :
    (Function.support fun c : RelativeCosets (F := F) (i := i) (ν := ν) (SQ : Set Roots) SP =>
      ArthurRelative.tau hG hi ν D (SQ : Set Roots) SP
        (H₀ ((((c.out : Pᵣ[(SP : Set Roots)]) : rationalSubgroup F G) : Points) * x) - Tp)).Finite :=
  (relative_tauHat_finite hG hi hν D hK hρ hQP hSP Tp x).subset fun _ hc =>
    ArthurRelative.tauHat_ne_zero_of_tau_ne_zero hG hi hν D (fun _ h => hQP h) hc

end Langlands.Global.ArthurTruncation

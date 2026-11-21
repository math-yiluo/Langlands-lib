import Langlands.Global.ArthurTruncationL2Statement
import Langlands.Global.ArthurTruncationRay
import Langlands.Global.LapidTruncationLimits

/-! # Applying the truncation pairing limit on the full rational quotient

The measure-theoretic reduction of Lapid 2011, Lemma 9 and §8 for the actual full-adelic
truncation along a regular ray. Cutoff finiteness and the orthogonal projection extension for
sufficiently regular parameters are hypotheses, in the forms of the Library statements
`TruncationFinitenessStatement` and `IsOrthogonalL2Extension`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter MeasureTheory
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

section Assembly

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

/-- Evaluate the full-adelic truncation of a quotient function at the chosen representatives. -/
def fullQuotientTruncation (Tp : V T) (f : RationalQuotient F G → ℂ) (q : RationalQuotient F G) : ℂ :=
  truncation hG hi D hK hρ Tp (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out

/-- Finiteness gives eventual equality of the evaluated quotient functions, pointwise in `q`. -/
theorem fullQuotientTruncationRay (hfin : TruncationFinitenessStatement.{u})
    (hν : IsGenericCocharacter i ν) (v : V T)
    (hv : ∀ β ∈ simpleRelativeRoots i ν, 0 < eval T β v)
    (f : RationalQuotient F G → ℂ) (q : RationalQuotient F G) :
    ∀ᶠ n : ℕ in atTop, fullQuotientTruncation hG hi D hK hρ ((n : ℝ) • v) f q = f q := by
  let Φ (x : AdelicGroupPoints F G) := f (LeftCosetSpace.mk (rationalSubgroup F G) x)
  have hΦ (g : AdelicGroupPoints F G) (hg : g ∈ rationalSubgroup F G) (x : AdelicGroupPoints F G) :
      Φ (g * x) = Φ x := congrArg f (LeftCosetSpace.mk_subgroup_mul _ ⟨g, hg⟩ x)
  have hq : Φ q.out = f q := congrArg f (Quotient.out_eq q)
  exact (truncationRay hfin F G T i ν hG hi hν D K hK hρ v hv Φ hΦ q.out).mono fun n hn => hn.trans hq

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
include hG hi in
/-- A simple-positive ray eventually satisfies any common lower bound on the simple roots. -/
theorem eventually_regular_ray (v : V T)
    (hv : ∀ β ∈ simpleRelativeRoots i ν, 0 < eval T β v) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ β ∈ simpleRelativeRoots i ν, C < eval T β ((n : ℝ) • v) := by
  have hfin := (ArthurRelative.finite_relativeRoots hG hi).subset
    (simpleRelativeRoots_subset_relativeRoots i ν)
  refine (eventually_all_finite hfin).mpr fun β hβ => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (C / eval T β v)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [map_smul, smul_eq_mul]
  exact (div_lt_iff₀ (hv β hβ)).mp (hN.trans_le (Nat.cast_le.mpr hn))

/-- Adelically applying the Fatou and projection argument of Lapid Lemma 9 and §8. The estimates
are only required in the regular tail of the ray and no test against an untruncated function
is needed before its square integrability is known. -/
theorem pairing_eq_of_fullQuotientTruncationRay
    (hfin : TruncationFinitenessStatement.{u}) (hν : IsGenericCocharacter i ν) (v : V T)
    (hv : ∀ β ∈ simpleRelativeRoots i ν, 0 < eval T β v)
    (hProj : ∃ C : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, C < eval T β Tp) →
      IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
        (fullQuotientTruncation hG hi D hK hρ Tp))
    {f f' : RationalQuotient F G → ℂ} (hf : Measurable f) (hf' : Measurable f')
    (hfb : ∀ C : Set (RationalQuotient F G), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖f x‖ ≤ M)
    (hfb' : ∀ C : Set (RationalQuotient F G), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖f' x‖ ≤ M)
    (z : ℂ) :
    let m := rationalQuotientHaarMeasure F G
    let trunc n := fullQuotientTruncation hG hi D hK hρ ((n : ℝ) • v)
    (∀ᶠ n : ℕ in atTop, MemLp (trunc n f) 2 m) →
    (∀ᶠ n : ℕ in atTop, MemLp (trunc n f') 2 m) →
    (∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (∫ q, trunc n f q * (starRingEnd ℂ) (trunc n f q) ∂m).re ≤ C) →
    (∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (∫ q, trunc n f' q * (starRingEnd ℂ) (trunc n f' q) ∂m).re ≤ C) →
    Tendsto (fun n : ℕ => ∫ q, trunc n f q * (starRingEnd ℂ) (trunc n f' q) ∂m) atTop (𝓝 z) →
    MemLp f 2 m ∧ MemLp f' 2 m ∧ ∫ q, f q * (starRingEnd ℂ) (f' q) ∂m = z := by
  dsimp only
  intro hL hL' hb hb' hz
  let m := rationalQuotientHaarMeasure F G
  let trunc (n : ℕ) := fullQuotientTruncation hG hi D hK hρ ((n : ℝ) • v)
  obtain ⟨C, hC⟩ := hProj
  have hProj' : ∀ᶠ n : ℕ in atTop, IsOrthogonalL2Extension m (trunc n) :=
    (eventually_regular_ray hG hi v hv C).mono fun n hn => hC _ hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hL.and hL').and hProj')
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  let g (n : ℕ) := trunc (n + N) f
  let g' (n : ℕ) := trunc (n + N) f'
  have htail (n : ℕ) := hN (n + N) (Nat.le_add_left N n)
  have hg (n : ℕ) : MemLp (g n) 2 m := (htail n).1.1
  have hg' (n : ℕ) : MemLp (g' n) 2 m := (htail n).1.2
  choose Q hQ hQeq using fun n => (htail n).2
  have hlim (b : RationalQuotient F G → ℂ) :
      ∀ᵐ q ∂m, Tendsto (fun n => trunc (n + N) b q) atTop (𝓝 (b q)) := by
    refine Filter.Eventually.of_forall fun q => ?_
    have he : (fun n : ℕ => trunc (n + N) b q) =ᶠ[atTop] fun _ => b q :=
      hshift.eventually (fullQuotientTruncationRay hG hi D hK hρ hfin hν v hv b q)
    exact (tendsto_const_nhds (x := b q) (f := atTop)).congr' he.symm
  apply pairing_eq_of_truncation_limits hf.aestronglyMeasurable hf'.aestronglyMeasurable
    hg hg' (hlim f) (hlim f') _ _ Q (Filter.Eventually.of_forall hQ) _ _ (hz.comp hshift)
  · obtain ⟨B, hB⟩ := hb
    exact ⟨B, hshift.eventually hB⟩
  · obtain ⟨B, hB⟩ := hb'
    exact ⟨B, hshift.eventually hB⟩
  · intro h
    refine Filter.Eventually.of_forall fun n => Lp.ext ?_
    exact (hg n).coeFn_toLp.trans (hQeq n f h hf hfb).symm
  · intro h
    refine Filter.Eventually.of_forall fun n => Lp.ext ?_
    exact (hg' n).coeFn_toLp.trans (hQeq n f' h hf' hfb').symm

end Assembly

/-- **Lapid 2011, Lemma 9 and §8, full-quotient reduction.** Assume cutoff finiteness. Fix the
truncation data and a direction `v` strictly positive on the simple roots, and suppose the
full-quotient truncation extends to an orthogonal projection on `L²` for all parameters beyond
some common simple-root threshold. Let `f` and `f'` be measurable functions on the full rational
quotient, bounded on compact sets. Suppose their truncations at `n • v` are eventually square
integrable, with eventually bounded squared norms, and that the mixed truncated pairing tends to
`z`. Then `f` and `f'` are square integrable and their pairing equals `z`. -/
def FullQuotientTruncationPairingStatement : Prop :=
  TruncationFinitenessStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ (D : RelativeRootReflectionData i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    (v : V T), (∀ β ∈ simpleRelativeRoots i ν, 0 < eval T β v) →
    (∃ C : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, C < eval T β Tp) →
      IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
        (fun f q => truncation hG hi D hK hρ Tp
          (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out)) →
    ∀ (f f' : RationalQuotient F G → ℂ), Measurable f → Measurable f' →
    (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖f x‖ ≤ M) →
    (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖f' x‖ ≤ M) →
    ∀ z : ℂ,
    let m := rationalQuotientHaarMeasure F G
    let trunc (n : ℕ) (b : RationalQuotient F G → ℂ) (q : RationalQuotient F G) : ℂ :=
      truncation hG hi D hK hρ ((n : ℝ) • v)
        (fun x => b (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out
    (∀ᶠ n : ℕ in atTop, MemLp (trunc n f) 2 m) →
    (∀ᶠ n : ℕ in atTop, MemLp (trunc n f') 2 m) →
    (∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (∫ q, trunc n f q * (starRingEnd ℂ) (trunc n f q) ∂m).re ≤ C) →
    (∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (∫ q, trunc n f' q * (starRingEnd ℂ) (trunc n f' q) ∂m).re ≤ C) →
    Tendsto (fun n : ℕ => ∫ q, trunc n f q * (starRingEnd ℂ) (trunc n f' q) ∂m) atTop (𝓝 z) →
    MemLp f 2 m ∧ MemLp f' 2 m ∧ ∫ q, f q * (starRingEnd ℂ) (f' q) ∂m = z

theorem fullQuotientTruncationPairing : FullQuotientTruncationPairingStatement.{u} :=
  fun hfin _F _ _ _G _ _ _T _i _ _ν hG hi hν D _K hK hρ v hv hProj _f _f' hf hf' hfb hfb' z =>
    pairing_eq_of_fullQuotientTruncationRay hG hi D hK hρ hfin hν v hv hProj hf hf' hfb hfb' z

end Langlands.Global.ArthurTruncation

import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.IdeleDecomposition
import Langlands.ClassFieldTheory.Local.ClassFormationTateIsomorphismsProof
import Langlands.ClassFieldTheory.Local.ClassFormationInflationLawsProof
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Cohomology.Profinite.Comparison.FiniteQuotients

/-!
# Local cohomology in degrees `≥ 3` at a finite level, and `H³` of the idèles

*Finite places.* For a finite Galois extension `L` of a `p`-adic field `F` and the Library's local
invariant family `I` (a relative class formation), every class of `Hⁿ⁺²(Gal(L/F), Lˣ)`, `n ≥ 1`,
is the cup product `u ∪ x` of the fundamental class `u` with a class `x ∈ Hⁿ(Gal(L/F), ℤ)`
(Tate's theorem, through the Library's `classFormationTateIsomorphisms`;
`exists_relativeOrdinaryCup_eq`). Hence `H³(Gal(L/F), Lˣ) = 0`, since `H¹(Gal(L/F), ℤ) = 0`
(`subsingleton_relativeCohomology_three`), and a class of degree `≥ 3` dies under inflation to a
Galois extension `M ⊇ L` of `F` with `[L : F] ∣ [M : L]`, because inflation sends `u` to
`[M : L]` times the fundamental class of `M` (`relativeInflationLinear_eq_zero_of_dvd`).

*Infinite places.* The stabilizer `D_w` of an infinite place `w` of a Galois extension `E / F` has
order at most two and acts on `E_wˣ` through complex conjugation; `H¹(D_w, E_wˣ) = 0` (Hilbert 90
for `ℂ / ℝ`, by an explicit primitive), hence the cohomology of `E_wˣ` vanishes in odd degrees.

*Idèles.* With the local triviality of idèle cohomology this gives `H³(Gal(E/F), J_E) = 0`
(`subsingleton_relativeIdeleCohomology_three`; Neukirch–Schmidt–Wingberg (8.1.7), Tate in
Cassels–Fröhlich VII §7 and §11.4).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local Reciprocity
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic FundamentalClass
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

section Local

variable {p : ℕ} [Fact p.Prime] (I : InvariantFamily.{u, u} p) (hI : I.RelativeClassFormation)
  (F : PadicField.{u} p) (L : Type u) [Field L] [Algebra F.Carrier L]
  [FiniteDimensional F.Carrier L] [IsGalois F.Carrier L]

include hI in
/-- **Local Tate–Nakayama.** Every class of `Hⁿ⁺²(Gal(L/F), Lˣ)`, `n ≥ 1`, is the cup product of a
fundamental class with a class of `Hⁿ(Gal(L/F), ℤ)`. -/
theorem exists_relativeOrdinaryCup_eq (c : relativeCohomology F.Carrier L 2)
    (hc : IsFundamentalClass F.Carrier L (I.relative F L) c) (n : ℕ) [NeZero n]
    (y : relativeCohomology F.Carrier L (n + 2)) :
    ∃ x : integralCohomology F.Carrier L n, y = relativeOrdinaryCup F.Carrier L n c x := by
  have hT := classFormationTateIsomorphisms Langlands.Tate.tateCupIsomorphism p I hI F L c hc
    (n : ℤ)
  obtain ⟨t, ht⟩ := hT.2 ((relativeTateToOrdinary F.Carrier L (n + 2)).symm y)
  refine ⟨integralTateToOrdinary F.Carrier L n t, ?_⟩
  rw [← relativeTateToOrdinary_relativeTateCup]
  erw [ht]
  exact ((relativeTateToOrdinary F.Carrier L (n + 2)).apply_symm_apply y).symm

/-- A fundamental class exists. -/
theorem exists_isFundamentalClass (hF : I.FundamentalClasses) :
    ∃ c, IsFundamentalClass F.Carrier L (I.relative F L) c :=
  (hF F L).1.exists

include hI in
/-- **`H³` of a local Galois extension vanishes.** -/
theorem subsingleton_relativeCohomology_three (hF : I.FundamentalClasses) :
    Subsingleton (relativeCohomology F.Carrier L 3) := by
  obtain ⟨c, hc⟩ := exists_isFundamentalClass I F L hF
  have key : ∀ y : relativeCohomology F.Carrier L (1 + 2), y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := exists_relativeOrdinaryCup_eq I hI F L c hc 1 y
    have hx : x = 0 := (ModuleCat.isZero_iff_subsingleton.1
      (isZero_H1_trivial_integers (G := Gal(L/F.Carrier)))).elim _ _
    rw [hx, map_zero]
  exact ⟨fun a b => (key a).trans (key b).symm⟩

include hI in
/-- **Inflation kills local classes of degree `≥ 3`.** For a Galois extension `M ⊇ L` of `F` with
`[L : F] ∣ [M : L]`, inflation `Hⁿ⁺²(Gal(L/F), Lˣ) → Hⁿ⁺²(Gal(M/F), Mˣ)` (`n ≥ 1`) is zero. -/
theorem relativeInflationLinear_eq_zero_of_dvd (hF : I.FundamentalClasses) (M : Type u) [Field M]
    [Algebra F.Carrier M] [Algebra L M] [IsScalarTower F.Carrier L M]
    [FiniteDimensional F.Carrier M] [IsGalois F.Carrier M]
    (hdvd : Module.finrank F.Carrier L ∣ Module.finrank L M) (n : ℕ) [NeZero n]
    (y : relativeCohomology F.Carrier L (n + 2)) :
    relativeInflationLinear F.Carrier L M (n + 2) y = 0 := by
  obtain ⟨c, hc⟩ := exists_isFundamentalClass I F L hF
  obtain ⟨d, hd⟩ := exists_isFundamentalClass I F M hF
  obtain ⟨x, rfl⟩ := exists_relativeOrdinaryCup_eq I hI F L c hc n y
  rw [I.ordinaryInflation_of_relativeClassFormation hI F L M c d hc hd n x, ← map_nsmul,
    ← map_nsmul]
  have hx : Module.finrank L M • x = 0 := by
    let := Fintype.ofFinite Gal(L/F.Carrier)
    have h0 := ProfiniteCohomology.card_smul_groupCohomology _ (NeZero.ne n) x
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank] at h0
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, mul_comm, mul_smul, h0, smul_zero]
  rw [hx, map_zero, map_zero]

end Local

section Infinite

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E] (w : InfinitePlace E)

/-- The action of a complex conjugation of `w` on `E_wˣ` is complex conjugation. -/
theorem extensionEmbedding_infiniteLocalRepresentation_of_isConj
    (c : MulAction.stabilizer (E ≃ₐ[F] E) w)
    (hc : ComplexEmbedding.IsConj w.embedding (c : E ≃ₐ[F] E))
    (a : (infiniteLocalRepresentation F w).V) :
    InfinitePlace.Completion.extensionEmbedding w
        ((Additive.toMul (α := (w.Completion)ˣ) ((infiniteLocalRepresentation F w).ρ c a) :
          (w.Completion)ˣ) : w.Completion) =
      star (InfinitePlace.Completion.extensionEmbedding w
        ((Additive.toMul (α := (w.Completion)ˣ) a : (w.Completion)ˣ) : w.Completion)) := by
  change InfinitePlace.Completion.extensionEmbedding w (ideleInfiniteCoordinate w
    (relativeIdeleAut F E c (IdeleGroup.ofCompletion (𝓞 E) E w
      (Additive.toMul (α := (w.Completion)ˣ) a))) : w.Completion) = _
  rw [extensionEmbedding_ideleInfiniteCoordinate_of_isConj hc,
    ideleInfiniteCoordinate_ofCompletion_self]

/-- A unit complex number `ζ` with `ζ · ζ̄ = 1` is `η̄ / η` for some nonzero `η`. -/
theorem exists_star_eq_mul_of_mul_star_eq_one (ζ : ℂ) (h : star ζ * ζ = 1) :
    ∃ η : ℂ, η ≠ 0 ∧ star η = ζ * η := by
  by_cases hζ : ζ = -1
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    rw [hζ]
    simp [Complex.conj_I]
  · refine ⟨1 + star ζ, fun h0 => hζ ?_, ?_⟩
    · have : star ζ = -1 := by linear_combination h0
      have h2 := congrArg star this
      simpa using h2
    · rw [star_add, star_one, star_star, mul_add, mul_one, mul_comm ζ (star ζ), h, add_comm]

/-- **Hilbert 90 at an infinite place**: `H¹(D_w, E_wˣ) = 0`. -/
theorem isZero_H1_infiniteLocalRepresentation :
    IsZero (groupCohomology (infiniteLocalRepresentation F w) 1) := by
  classical
  by_cases htriv : ∀ d : MulAction.stabilizer (E ≃ₐ[F] E) w, d = 1
  · have : Subsingleton (MulAction.stabilizer (E ≃ₐ[F] E) w) :=
      ⟨fun a b => (htriv a).trans (htriv b).symm⟩
    exact isZero_groupCohomology_succ_of_subsingleton _ 0
  push Not at htriv
  obtain ⟨c, hc1⟩ := htriv
  have hconj : ComplexEmbedding.IsConj w.embedding (c : E ≃ₐ[F] E) :=
    isConj_of_mem_stabilizer w c.2 fun h => hc1 (Subtype.ext h)
  have hcx : w.IsComplex := InfinitePlace.isComplex_iff.2
    ((ComplexEmbedding.isConj_ne_one_iff hconj).1 fun h => hc1 (Subtype.ext h))
  have hD : ∀ d : MulAction.stabilizer (E ≃ₐ[F] E) w, d = 1 ∨ d = c := by
    intro d
    by_cases hd : d = 1
    · exact Or.inl hd
    · right
      have hdc := isConj_of_mem_stabilizer w d.2 fun h => hd (Subtype.ext h)
      apply Subtype.ext
      exact ComplexEmbedding.IsConj.ext hdc hconj
  have hcc : c * c = 1 := Subtype.ext (conjugation_mul_self w hconj)
  rw [ModuleCat.isZero_iff_subsingleton]
  suffices h : ∀ z : groupCohomology (infiniteLocalRepresentation F w) 1, z = 0 from
    ⟨fun a b => (h a).trans (h b).symm⟩
  intro z
  induction z using groupCohomology.H1_induction_on with | h f => ?_
  rw [groupCohomology.H1π_eq_zero_iff]
  -- the value at the conjugation
  set ζ : ℂ := InfinitePlace.Completion.extensionEmbedding w
    ((Additive.toMul (f c) : (w.Completion)ˣ) : w.Completion) with hζ
  have hcoc : (infiniteLocalRepresentation F w).ρ c (f c) + f c = 0 := by
    have h := (groupCohomology.mem_cocycles₁_iff (f : _ → _)).1 f.2 c c
    rw [hcc, groupCohomology.cocycles₁_map_one] at h
    exact h.symm
  have hζ1 : star ζ * ζ = 1 := by
    have h1 : Additive.toMul (α := (w.Completion)ˣ) ((infiniteLocalRepresentation F w).ρ c (f c)) *
        Additive.toMul (α := (w.Completion)ˣ) (f c) = 1 :=
      congrArg (Additive.toMul (α := (w.Completion)ˣ)) hcoc
    have h2 := congrArg (fun u : (w.Completion)ˣ =>
      InfinitePlace.Completion.extensionEmbedding w (u : w.Completion)) h1
    simp only [Units.val_mul, map_mul, Units.val_one, map_one] at h2
    rwa [extensionEmbedding_infiniteLocalRepresentation_of_isConj w c hconj] at h2
  obtain ⟨η, hη0, hη⟩ := exists_star_eq_mul_of_mul_star_eq_one ζ hζ1
  obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hcx η
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hη0 (by rw [← hy, map_zero])
  let Y : (infiniteLocalRepresentation F w).V := Additive.ofMul (Units.mk0 y hy0)
  refine ⟨Y, ?_⟩
  funext d
  rcases hD d with hd | hd <;> rw [hd]
  · rw [groupCohomology.d₀₁_hom_apply, map_one, Module.End.one_apply, sub_self,
      groupCohomology.cocycles₁_map_one]
  · rw [groupCohomology.d₀₁_hom_apply]
    apply Additive.toMul.injective
    apply Units.ext
    apply (InfinitePlace.Completion.extensionEmbedding w).injective
    change InfinitePlace.Completion.extensionEmbedding w
        (((Additive.toMul (α := (w.Completion)ˣ) ((infiniteLocalRepresentation F w).ρ c Y)) /
          Units.mk0 y hy0 : (w.Completion)ˣ) : w.Completion) = ζ
    rw [Units.val_div_eq_div_val, map_div₀,
      extensionEmbedding_infiniteLocalRepresentation_of_isConj w c hconj]
    change star (InfinitePlace.Completion.extensionEmbedding w y) /
      InfinitePlace.Completion.extensionEmbedding w y = ζ
    rw [hy, hη, mul_div_assoc, div_self hη0, mul_one]

omit [NumberField E] in
/-- The stabilizer of an infinite place in a finite Galois group is cyclic (of order at most
two). -/
theorem isCyclic_stabilizer_infinitePlace :
    IsCyclic (MulAction.stabilizer (E ≃ₐ[F] E) w) := by
  classical
  by_cases htriv : ∀ d : MulAction.stabilizer (E ≃ₐ[F] E) w, d = 1
  · have : Subsingleton (MulAction.stabilizer (E ≃ₐ[F] E) w) :=
      ⟨fun a b => (htriv a).trans (htriv b).symm⟩
    exact isCyclic_of_subsingleton
  push Not at htriv
  obtain ⟨c, hc1⟩ := htriv
  have hconj : ComplexEmbedding.IsConj w.embedding (c : E ≃ₐ[F] E) :=
    isConj_of_mem_stabilizer w c.2 fun h => hc1 (Subtype.ext h)
  refine ⟨c, fun d => ?_⟩
  by_cases hd : d = 1
  · exact ⟨0, show c ^ (0 : ℤ) = d by rw [zpow_zero, hd]⟩
  · have hdc := isConj_of_mem_stabilizer w d.2 fun h => hd (Subtype.ext h)
    exact ⟨1, show c ^ (1 : ℤ) = d by
      rw [zpow_one]; exact Subtype.ext (ComplexEmbedding.IsConj.ext hconj hdc)⟩

/-- The cohomology of `E_wˣ` vanishes in odd degrees at an infinite place. -/
theorem isZero_groupCohomology_infiniteLocalRepresentation_odd [Finite (E ≃ₐ[F] E)] (n : ℕ)
    (hn : Odd n) : IsZero (groupCohomology (infiniteLocalRepresentation F w) n) := by
  have := isCyclic_stabilizer_infinitePlace (F := F) w
  exact isZero_groupCohomology_odd _ (isZero_H1_infiniteLocalRepresentation w) n hn

end Infinite

section Ideles

variable (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

/-- `H³(Gal(E_w/F_v), E_wˣ) = 0` at a finite place. -/
theorem subsingleton_relativeCohomology_three_adicCompletion (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    Subsingleton (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 3) := by
  have := isGalois_adicCompletion v w
  have := FiniteExtension.local_finite v w
  obtain ⟨I, -, hRCF, -, -, hF, -⟩ := localRelativeClassFormation.{u} (residuePrime v)
  exact subsingleton_relativeCohomology_three I hRCF (padicField v) (w.adicCompletion E) hF

/-- **`H³` of the idèles vanishes**: `H³(Gal(E/F), J_E) = 0`. -/
theorem subsingleton_relativeIdeleCohomology_three :
    Subsingleton (relativeIdeleCohomology F E 3) := by
  classical
  let wf : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E) := fun v => (placeAbove E v).1
  have hwf : ∀ v, (wf v).asIdeal.LiesOver v.asIdeal := fun v => (placeAbove E v).2
  have hex : ∀ v : InfinitePlace F, ∃ u : InfinitePlace E, u.comap (algebraMap F E) = v :=
    fun v => InfinitePlace.comap_surjective v
  choose wi hwi using hex
  suffices h : ∀ x : relativeIdeleCohomology F E (2 + 1), x = 0 from
    ⟨fun a b => (h a).trans (h b).symm⟩
  intro x
  refine eq_zero_of_ideleLocalMap_eq_zero wf wi hwi 2 x (fun v => ?_) (fun v => ?_)
  · exact (subsingleton_relativeCohomology_three_adicCompletion F E v (wf v)).elim _ _
  · exact (ModuleCat.isZero_iff_subsingleton.1
      (isZero_groupCohomology_infiniteLocalRepresentation_odd (F := F) (wi v) 3
        ⟨1, rfl⟩)).elim _ _

end Ideles

end

end Langlands.GaloisCohomology

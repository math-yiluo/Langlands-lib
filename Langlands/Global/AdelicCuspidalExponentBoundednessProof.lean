import Langlands.Global.AdelicCuspidalExponentFibreBound
import Langlands.Global.AdelicCuspidalExponentNonexistenceReduction
import Langlands.Global.AdelicParabolicCuspidalVanishingProof

/-! # Boundedness of forms with only negative maximal cuspidal exponents

Proof of `CuspidalExponentBoundednessStatement` (the boundedness that Bernstein–Lapid take from
Mœglin–Waldspurger I.4.1 in §6.4). The vanishing criterion (`parabolicCuspidalVanishing`) shows
that the constant terms of `f` along the maximal parabolics `R \ {α}` of `M_R` are their cuspidal
projections. `cuspidalExponentFibreBound` then bounds `f` on the fibres of the Iwasawa height
`H_{P_R}`. These fibres contain `U_Q(𝔸) M_R(𝔸)^1 g`, and the constant term is an average over a
compact quotient of `U_Q(𝔸)`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  RealTorusSpace PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

section RankZero

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem bijective_algebraMap_coordinateRing_fin_zero' :
    Function.Bijective (algebraMap (CommRingCat.of F)
      (GeneralLinear.CoordinateRing (Fin 0) (CommRingCat.of F))) := by
  have : IsEmpty (GeneralLinear.Coordinate (Fin 0)) :=
    ⟨fun x => by cases x <;> exact Fin.elim0 ‹_›⟩
  have : Nontrivial (GeneralLinear.CoordinateRing (Fin 0) (CommRingCat.of F)) :=
    (GeneralLinear.classify (R := CommRingCat.of F) (S := F)
      (1 : GL (Fin 0) F)).toRingHom.domain_nontrivial
  refine ⟨RingHom.injective _, fun a => ?_⟩
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨MvPolynomial.isEmptyAlgEquiv (CommRingCat.of F) (GeneralLinear.Coordinate (Fin 0)) q, ?_⟩
  conv_rhs => rw [← (MvPolynomial.isEmptyAlgEquiv (CommRingCat.of F)
    (GeneralLinear.Coordinate (Fin 0))).symm_apply_apply q]
  rw [MvPolynomial.isEmptyAlgEquiv_symm_apply]
  rfl

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem subsingleton_hom_groupScheme_fin_zero' (X : Over (Spec (CommRingCat.of F))) :
    Subsingleton (X ⟶ (GeneralLinear.groupScheme (Fin 0) (CommRingCat.of F)).X) := by
  have hiso : IsIso (GeneralLinear.groupScheme (Fin 0) (CommRingCat.of F)).X.hom := by
    rw [GeneralLinear.groupScheme_hom]
    exact isIso_SpecMap_iff.mpr bijective_algebraMap_coordinateRing_fin_zero'
  constructor
  intro x y
  apply Over.OverMorphism.ext
  rw [← cancel_mono (GeneralLinear.groupScheme (Fin 0) (CommRingCat.of F)).X.hom, Over.w x,
    Over.w y]

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- A closed subgroup of the general linear group of rank zero has at most one point over
every base. -/
private theorem subsingleton_hom_of_fin_zero' {H : GroupScheme (Spec (CommRingCat.of F))}
    (j : MatrixRepresentation H (Fin 0)) (hj : IsClosedSubgroup j)
    (X : Over (Spec (CommRingCat.of F))) : Subsingleton (X ⟶ H.X) := by
  have := subsingleton_hom_groupScheme_fin_zero' (F := F) X
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact ⟨fun x y => (cancel_mono j.hom.hom).mp (Subsingleton.elim _ _)⟩


end RankZero

section Helpers

private theorem isIwasawaCompact_of_minimal'' {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K) (Q : Idx) :
    IsIwasawaCompact (𝓕.p Q) K := by
  refine ⟨hK.isCompact, Set.eq_univ_of_univ_subset ?_⟩
  rw [← hK.range_mul]
  apply Set.mul_subset_mul_right
  rintro _ ⟨x, rfl⟩
  have hx : x ≫ (𝓕.p ⟨∅, Set.empty_subset _⟩).hom.hom ∈
      (SubgroupFunctor.range (𝓕.p ⟨∅, Set.empty_subset _⟩)).carrier _ :=
    SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp
    ((𝓕.le_iff_range_le ⟨∅, Set.empty_subset _⟩ Q).mp (Set.empty_subset _) _ hx)
  exact ⟨y, by simpa [AdelicGroupPoints.map_apply] using hy⟩



private theorem not_maximal_of_lt' {Q'' Q' Q R : Idx} (h1 : Q'' ≤ Q') (h2 : Q' < Q)
    {β : relativeRoots 𝓕.i} (hβ : β.1 ∉ Q.1) (hins : insert β.1 Q.1 = R.1) :
    ¬ ∃ b : relativeRoots 𝓕.i, b.1 ∉ Q''.1 ∧ insert b.1 Q''.1 = R.1 := by
  rintro ⟨b, hb, hins'⟩
  have hQfin : Q.1.Finite := 𝓕.finite_simpleRoots.subset Q.2
  have hQ''fin : Q''.1.Finite := 𝓕.finite_simpleRoots.subset Q''.2
  have e1 := Set.ncard_insert_of_notMem hβ hQfin
  have e2 := Set.ncard_insert_of_notMem hb hQ''fin
  rw [hins] at e1
  rw [hins'] at e2
  have hne : Q'' ≠ Q := ne_of_lt (lt_of_le_of_lt h1 h2)
  have hsub : Q''.1 ⊆ Q.1 := h1.trans h2.le
  have hss : Q''.1 ⊂ Q.1 := Set.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne (Subtype.ext h)⟩
  have hlt := Set.ncard_lt_ncard hss hQfin
  omega

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

private theorem leviPairingIntegrand_sub'' (P : Idx) (f h : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F (𝓕.M P) → ℂ) :
    𝓕.leviPairingIntegrand P (f - h) g ψ =
      𝓕.leviPairingIntegrand P f g ψ - 𝓕.leviPairingIntegrand P h g ψ := by
  funext x
  simp only [leviPairingIntegrand, Pi.sub_apply, sub_mul]

/-- Cuspidal projections of two inputs give a cuspidal projection of their difference. -/
private theorem isCuspidalProjection_sub'' {P : Idx} {f f' fc fc' : AdelicGroupPoints F G → ℂ}
    (h₁ : 𝓕.IsCuspidalProjection hsmooth Kinf rho P f fc)
    (h₂ : 𝓕.IsCuspidalProjection hsmooth Kinf rho P f' fc') :
    𝓕.IsCuspidalProjection hsmooth Kinf rho P (f - f') (fc - fc') := by
  refine ⟨(𝓕.automorphicSubmodule hsmooth Kinf rho P).sub_mem h₁.1 h₂.1,
    𝓕.isCuspidalAlong_sub hsmooth Kinf rho P h₁.1 h₂.1 h₁.2.1 h₂.2.1, ?_⟩
  intro ψ hψ g
  obtain ⟨i₁, j₁, e₁⟩ := h₁.2.2 ψ hψ g
  obtain ⟨i₂, j₂, e₂⟩ := h₂.2.2 ψ hψ g
  refine ⟨?_, ?_, ?_⟩
  · rw [leviPairingIntegrand_sub'']
    exact i₁.sub i₂
  · rw [leviPairingIntegrand_sub'']
    exact j₁.sub j₂
  · unfold leviPairing at e₁ e₂ ⊢
    rw [leviPairingIntegrand_sub'', leviPairingIntegrand_sub'']
    simp only [Pi.sub_apply]
    rw [integral_sub i₁ i₂, integral_sub j₁ j₂, e₁, e₂]



end Helpers

section Heights

/-- Left translation by the adelic points of the unipotent radical `U_Q` of a standard
`Q ⊆ R` does not change the Iwasawa height `H_{P_R}`. -/
theorem height_radical_mul {Q R : Idx} (hQR : Q ≤ R) {K : Subgroup A}
    (hKR : IsIwasawaCompact (𝓕.p R) K) {u : A}
    (hu : u ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q)))
    (z : A) : hKR.height (u * z) = hKR.height z := by
  let := (𝓕.isCompatible R).parabolic.isClosedSubgroup.mono
  let : IsClosedImmersion (𝓕.p R).hom.hom.left := (𝓕.isCompatible R).parabolic.isClosedSubgroup
  have hle : SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q) ≤ SubgroupFunctor.range (𝓕.p R) :=
    (SubgroupFunctor.range_comp_le _ _).trans ((𝓕.le_iff_range_le Q R).mp hQR)
  let j := SubgroupFunctor.rangeFactor (𝓕.iU Q ≫ 𝓕.p Q) (𝓕.p R) hle
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hu
  have hu' : map F (𝓕.P R) G (𝓕.p R) (map F (𝓕.U Q) (𝓕.P R) j w) = u := by
    rw [← map_comp_apply_of_hom, SubgroupFunctor.rangeFactor_comp]
    simpa [AdelicGroupPoints.map_apply] using hw
  rw [← hu', hKR.height_map_mul, characterLog_map,
    characterLog_eq_zero_of_isUnipotent (𝓕.isUnipotentRadical Q).1.isUnipotent, map_zero,
    zero_add]

/-- Left translation by `M_R(𝔸)^1` does not change the Iwasawa height `H_{P_R}`. -/
theorem height_leviNormOne_mul (R : Idx) {K : Subgroup A} (hKR : IsIwasawaCompact (𝓕.p R) K)
    {m : AdelicGroupPoints F (𝓕.M R)} (hm : m ∈ normOneSubgroup F (𝓕.M R)) (z : A) :
    hKR.height (map F (𝓕.M R) G (𝓕.l R ≫ 𝓕.p R) m * z) = hKR.height z := by
  let : IsClosedImmersion (𝓕.p R).hom.hom.left := (𝓕.isCompatible R).parabolic.isClosedSubgroup
  rw [map_comp_apply_of_hom, hKR.height_map_mul, characterLog_map,
    (characterLog_eq_zero_iff F _ _).mpr hm, map_zero, zero_add]

/-- A constant term is bounded by a bound of the function on the `U_Q(𝔸)`-orbit of the point, the
measure on `U_Q(F) \ U_Q(𝔸)` being a probability measure. -/
theorem norm_constantTerm_le (Q : Idx) {φ : A → ℂ} {C : ℝ} {x : A}
    (h : ∀ u ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q)),
      ‖φ (u * x)‖ ≤ C) :
    ‖𝓕.constantTerm Q φ x‖ ≤ C := by
  let : IsClosedImmersion (𝓕.p Q).hom.hom.left := (𝓕.isCompatible Q).parabolic.isClosedSubgroup
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q)) :
      Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
      (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F
      (𝓕.iU Q ≫ 𝓕.p Q) (𝓕.isUnipotentRadical Q).1.smooth
        (𝓕.isUnipotentRadical Q).1.connectedSpace (𝓕.isUnipotentRadical Q).1.isUnipotent
  let := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G
    (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q))
  unfold constantTerm subgroupConstantTerm
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun q =>
    h _ (Quotient.out q).2)).trans_eq ?_
  simp

end Heights

section Main

omit [NumberField F] in
/-- The simple root `α ∈ R` together with `R \ {α}` gives back `R`. -/
theorem insert_removeSimpleRoot {R : Idx} {α : characterLattice 𝓕.T} (hα : α ∈ R.1) :
    insert α (𝓕.removeSimpleRoot R α).1 = R.1 := by
  ext x
  constructor
  · rintro (rfl | ⟨hx, -⟩)
    · exact hα
    · exact hx
  · intro hx
    by_cases hxα : x = α
    · exact Or.inl hxα
    · exact Or.inr ⟨hx, R.2 hx, hxα⟩

end Main

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- `CuspidalExponentBoundednessStatement` follows from the vanishing criterion (8.1) of
Bernstein–Lapid (`ParabolicCuspidalVanishingStatement`). -/
theorem cuspidalExponentBoundedness_of_parabolicCuspidalVanishing
    (hvan : ParabolicCuspidalVanishingStatement.{u}) :
    CuspidalExponentBoundednessStatement.{u} := by
  intro F _ _ G _ _ _ fam K hK hKmin hKlevi N d rho hsmooth hrho Kinf R f hf φc s c hfam
    hexp Q hQR g
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have : Subsingleton (AdelicGroupPoints F G) :=
      StandardParabolicFamily.subsingleton_hom_of_fin_zero' rho hrho _
    refine ⟨‖fam.constantTerm Q f g‖, fun m _ => ?_⟩
    rw [Subsingleton.elim (map F (fam.M R) G (fam.l R ≫ fam.p R) m * g) g]
  -- components along non-maximal parabolics vanish
  have hnm : ∀ Q : StandardIndex F G fam.i fam.ν, Q ≤ R →
      (¬ ∃ b : relativeRoots fam.i, b.1 ∉ Q.1 ∧ insert b.1 Q.1 = R.1) → φc Q = 0 := by
    intro Q hQ hnot
    rw [(hfam Q hQ).2.sum_eq]
    refine Finset.sum_eq_zero fun mu hmu => ?_
    by_contra hc
    obtain ⟨b, hb, hins, -⟩ := hexp Q hQ mu hmu hc
    exact hnot ⟨b, hb, hins⟩
  -- a vanishing projection puts the constant term in the cuspidal annihilator
  have hann : ∀ Q : StandardIndex F G fam.i fam.ν, Q ≤ R → φc Q = 0 →
      fam.InCuspidalAnnihilator Kinf rho Q (fam.constantTerm Q f) := by
    intro Q hQ h0 ψ hψ g
    obtain ⟨hi, -, he⟩ := (hfam Q hQ).1.2.2 ψ hψ g
    refine ⟨hi, he.trans ?_⟩
    rw [h0]
    have hz : fam.leviPairingIntegrand Q 0 g ψ = 0 := by
      funext x
      simp [StandardParabolicFamily.leviPairingIntegrand]
    simp [StandardParabolicFamily.leviPairing, hz]
  -- along the maximal parabolics `R \ {α}` the constant term is its cuspidal projection
  have hCφ : ∀ α ∈ R.1, fam.constantTerm (fam.removeSimpleRoot R α) f =
      φc (fam.removeSimpleRoot R α) := by
    intro α hα
    set Q₀ := fam.removeSimpleRoot R α with hQ₀
    have hQ₀R : Q₀ ≤ R := (fam.removeSimpleRoot_lt R hα).le
    let β : relativeRoots fam.i := ⟨α, (R.2 hα).1.1⟩
    have hβQ : β.1 ∉ Q₀.1 := fun h => h.2.2 rfl
    have hins : insert β.1 Q₀.1 = R.1 := fam.insert_removeSimpleRoot hα
    have hlow : ∀ Q' : StandardIndex F G fam.i fam.ν, Q' < Q₀ → fam.constantTerm Q' f = 0 := by
      intro Q' hQ'
      have hQ'R : Q' ≤ R := hQ'.le.trans hQ₀R
      have hCQ' := constantTermAutomorphy F G fam Kinf rho hsmooth hrho R Q' hQ'R f hf
      apply hvan F G fam K hK (fam.isIwasawaCompact_of_minimal'' hKmin) rho hN hrho Q'
        (fam.constantTerm Q' f) ⟨hCQ'.1, hCQ'.2.1.1, hCQ'.2.2.2.2⟩
      intro Q'' hQ''
      rw [fam.constantTerm_constantTerm_of_parabolicQuotient hQ'' hQ'R hf.2.1.1 hf.1]
      exact hann Q'' (hQ''.trans hQ'R)
        (hnm Q'' (hQ''.trans hQ'R) (fam.not_maximal_of_lt' hQ'' hQ' hβQ hins))
    have hCQ := constantTermAutomorphy F G fam Kinf rho hsmooth hrho R Q₀ hQ₀R f hf
    have hcusp : fam.IsCuspidalAlong Q₀ (fam.constantTerm Q₀ f) := by
      intro Q' hQ'
      rw [fam.constantTerm_constantTerm_of_parabolicQuotient hQ'.le hQ₀R hf.2.1.1 hf.1]
      exact hlow Q' hQ'
    have hself : fam.IsCuspidalProjection hsmooth Kinf rho Q₀ (fam.constantTerm Q₀ f)
        (fam.constantTerm Q₀ f) :=
      ⟨hCQ, hcusp, fun ψ hψ g =>
        ⟨((hfam Q₀ hQ₀R).1.2.2 ψ hψ g).1, ((hfam Q₀ hQ₀R).1.2.2 ψ hψ g).1, rfl⟩⟩
    have hdiff := fam.isCuspidalProjection_sub'' hsmooth Kinf rho hself (hfam Q₀ hQ₀R).1
    rw [sub_self] at hdiff
    have heq := fam.eq_zero_of_isCuspidalProjection_zero hsmooth rho hvan K hK hKmin hrho hdiff
    exact sub_eq_zero.mp heq
  have hdec : ∀ α ∈ R.1, fam.IsExponentDecomposition hsmooth Kinf rho (fam.removeSimpleRoot R α)
      (fam.constantTerm (fam.removeSimpleRoot R α) f) (s (fam.removeSimpleRoot R α))
      (c (fam.removeSimpleRoot R α)) := by
    intro α hα
    rw [hCφ α hα]
    exact (hfam _ (fam.removeSimpleRoot_lt R hα).le).2
  have hexp' := fun α (hα : α ∈ R.1) mu hmu hc =>
    hexp (fam.removeSimpleRoot R α) (fam.removeSimpleRoot_lt R hα).le mu hmu hc
  -- the bound on the fibre of `H_{P_R}` through `g`
  have hKinf : Langlands.CompactIwasawa.IsMaximalCompact Kinf :=
    hK.isMaximalCompact_comap_ofInfinite
  have hKR := fam.isIwasawaCompact_of_minimal'' hKmin R
  obtain ⟨C, hC⟩ := fam.cuspidalExponentFibreBound hsmooth rho hN hrho K hKmin Kinf hKinf R hKR f
    hf s c hdec hexp' g
  refine ⟨C, fun m hm => fam.norm_constantTerm_le Q fun u hu => hC _ ?_⟩
  rw [fam.height_radical_mul hQR hKR hu, fam.height_leviNormOne_mul R hKR hm]

/-- **Boundedness of forms with only negative maximal cuspidal exponents** (Bernstein–Lapid,
first step of the proof of the lemma of §6.4, from Mœglin–Waldspurger I.4.1). -/
theorem cuspidalExponentBoundedness : CuspidalExponentBoundednessStatement.{u} :=
  cuspidalExponentBoundedness_of_parabolicCuspidalVanishing parabolicCuspidalVanishing

end Langlands.Global

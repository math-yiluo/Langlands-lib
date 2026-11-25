import Langlands.AlgebraicGeometry.FibrewiseClopenAffineOpen
import Langlands.AlgebraicGeometry.ClosedSubschemeFiberIncidence
import Langlands.GroupScheme.GenericSubgroupClosureFactorization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # Affine fibrewise closed opens in integral Dedekind models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- An affine flat model of an integral generic group has integral total space. -/
theorem isIntegral_of_generic (M : IntegralModel R K G) [IsIntegral G.X.left] :
    IsIntegral M.group.X.left := by
  let t := M.genericToModel
  have : QuasiCompact t := by
    dsimp [t, genericToModel]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in infer_instance
  have : IsSchemeTheoreticallyDominant t := by
    dsimp [t, genericToModel]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in infer_instance
  have : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  have : IsDomain Γ(M.group.X.left, ⊤) :=
    Function.Injective.isDomain (α := Γ(G.X.left, ⊤))
      t.appTop.hom (t.app_injective ⊤)
  have : Nonempty M.group.X.left := Nonempty.map t inferInstance
  exact isIntegral_of_isAffine_of_isDomain _

end Langlands.GroupScheme.IntegralModel

namespace Langlands.AlgebraicGeometry.AffineFiberwiseOpen

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- A nonzero coefficient in a Dedekind domain vanishes at finitely many primes. -/
theorem finite_zeroLocus {r : R} (hr : r ≠ 0) :
    (PrimeSpectrum.zeroLocus ({r} : Set R)).Finite := by
  let I : Ideal R := Ideal.span {r}
  apply Set.Finite.of_finite_image
    (f := fun p : PrimeSpectrum R => p.asIdeal) ?_
    (fun _ _ _ _ h => PrimeSpectrum.ext h)
  apply ((Ideal.finite_minimalPrimes_of_isNoetherianRing R I).subset ?_)
  rintro p ⟨q, hq, rfl⟩
  have hIq : I ≤ q.asIdeal := Ideal.span_le.mpr hq
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hIq
  have hpne : p ≠ ⊥ := by
    intro heq
    apply hr
    have hrp : r ∈ p := hp.1.2 (Ideal.subset_span (Set.mem_singleton r))
    simpa [heq] using hrp
  have hpm : p.IsMaximal := hp.1.1.isMaximal_of_ne_bot hpne
  have hpq' : p = q.asIdeal := hpm.eq_of_le q.isPrime.ne_top hpq
  simpa only [hpq'] using hp

/-- An open containing the generic fibre contains all fibres above some
nonzero principal open of the base. -/
theorem exists_principal_preimage_subset
    (X : Scheme.{u}) [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (U : X.Opens)
    (hη : f ⁻¹' {⟨⊥, inferInstance⟩} ⊆ (U : Set X)) :
    ∃ r : R, r ≠ 0 ∧
      f ⁻¹' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆ (U : Set X) := by
  let η : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  have hgen : IsGenericPoint η (Set.univ : Set (PrimeSpectrum R)) := by
    change closure ({η} : Set (PrimeSpectrum R)) = _
    rw [PrimeSpectrum.closure_singleton]
    simp [η]
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := inferInstance }
  have hc : IsConstructible (f '' (U : Set X)ᶜ) :=
    f.isConstructible_image
      ((NoetherianSpace.isCompact (U : Set X)).isConstructible U.isOpen).compl
  obtain ⟨V, hV, hηV, hconst⟩ :=
    GenericImagePattern.exists_open_constructible_membership hgen hc
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hηr, hrV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hηV hV
  have hr : r ≠ 0 := by
    simpa [η, PrimeSpectrum.mem_basicOpen] using hηr
  refine ⟨r, hr, ?_⟩
  intro x hx
  by_contra hxU
  have hηbad : η ∈ f '' (U : Set X)ᶜ :=
    (hconst (f x) (hrV hx)).mp ⟨x, hxU, rfl⟩
  obtain ⟨y, hy, hfy⟩ := hηbad
  exact hy (hη hfy)

/-- A fibrewise closed open containing the generic fibre of an integral
smooth affine Dedekind scheme is affine. -/
theorem isAffineOpen_of_contains_generic_fiber
    (X : Scheme.{u}) [IsAffine X] [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (U : X.Opens)
    (hη : f ⁻¹' {⟨⊥, inferInstance⟩} ⊆ (U : Set X))
    (hclosed : ∀ s : Spec (CommRingCat.of R),
      IsClosed ((Subtype.val : (f ⁻¹' {s}) → X) ⁻¹' (U : Set X))) :
    IsAffineOpen U := by
  classical
  obtain ⟨r, hr, hrU⟩ := exists_principal_preimage_subset R X f U hη
  let a : Γ(X, ⊤) := f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  have hD : (X.basicOpen a : Set X) =
      f ⁻¹' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    change (X.basicOpen (f.appTop _) : Set X) = _
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    rfl
  have hbase : Dense (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    apply (PrimeSpectrum.basicOpen r).isOpen.dense
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    simpa [PrimeSpectrum.mem_basicOpen] using hr
  have hdense : Dense (X.basicOpen a : Set X) := by
    rw [hD]
    exact hbase.preimage f.isOpenMap
  have hlocal (x : X) : ∃ N : X.Opens, x ∈ N ∧ IsIrreducible (N : Set X) :=
    ⟨⊤, trivial, by simpa using (IrreducibleSpace.isIrreducible_univ (X := X))⟩
  have hgeneric : IsClosed
      ((Subtype.val : X.basicOpen a → X) ⁻¹' (U : Set X)) := by
    have heq : ((Subtype.val : X.basicOpen a → X) ⁻¹' (U : Set X)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact hrU (hD ▸ x.property)
    rw [heq]
    exact isClosed_univ
  let E : Set (PrimeSpectrum R) := PrimeSpectrum.zeroLocus ({r} : Set R)
  have hE : E.Finite := finite_zeroLocus R hr
  have hs (s : E) : IsClosed ((U : Set X) ∩ (f ⁻¹' {s.val})) := by
    have hsne : s.val.asIdeal ≠ ⊥ := by
      intro heq
      apply hr
      have hrs : r ∈ s.val.asIdeal := s.property (Set.mem_singleton r)
      simpa [heq] using hrs
    have hsclosed : IsClosed ({s.val} : Set (PrimeSpectrum R)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal s.val).mpr
        (s.val.isPrime.isMaximal_of_ne_bot hsne)
    have hfclosed : IsClosed (f ⁻¹' {s.val}) := hsclosed.preimage f.continuous
    have himage := hfclosed.isClosedEmbedding_subtypeVal.isClosedMap _ (hclosed s.val)
    convert himage using 1
    ext x
    simp [Set.image_preimage_eq_inter_range]
  have hspecial : IsClosed ((U : Set X) \ (X.basicOpen a : Set X)) := by
    let : Finite E := hE.to_subtype
    have heq : (U : Set X) \ (X.basicOpen a : Set X) =
        ⋃ s : E, ((U : Set X) ∩ (f ⁻¹' {s.val})) := by
      rw [hD]
      ext x
      simp only [Set.mem_sdiff, Set.mem_preimage, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxU, hxr⟩
        have hxE : f x ∈ E := by
          change ¬r ∉ (f x).asIdeal at hxr
          exact Set.singleton_subset_iff.mpr (not_not.mp hxr)
        exact ⟨⟨f x, hxE⟩, hxU, rfl⟩
      · rintro ⟨s, hxU, hxs⟩
        refine ⟨hxU, ?_⟩
        rw [hxs]
        exact fun h => h (s.property (Set.mem_singleton r))
    rw [heq]
    exact isClosed_iUnion_of_finite hs
  exact FibrewiseClopenAffineOpen.isAffineOpen_of_closed_on_principal_and_complement
    X a U hlocal hdense hgeneric hspecial

end Langlands.AlgebraicGeometry.AffineFiberwiseOpen

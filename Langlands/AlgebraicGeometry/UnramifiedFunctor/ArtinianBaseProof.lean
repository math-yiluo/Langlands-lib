import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseSpec

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section RingChart

/-- The ring-level chart conditions on `ξ ∈ F(Spec B)`: unique infinitesimal lifting along
nilpotent thickenings of local artinian rings, and separation of maps to fields. -/
def RingChart {B : Type u} [CommRing B] [Algebra R B] (ξ : F.obj (op (ovR R B))) : Prop :=
  (∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A] [IsArtinianRing A]
    (I : Ideal A), IsNilpotent I → ∀ (u₀ : B →ₐ[R] A ⧸ I) (v : F.obj (op (ovR R A))),
      res u₀ ξ = res (Ideal.Quotient.mkₐ R I) v →
        ∃! u : B →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp u = u₀ ∧ res u ξ = v) ∧
  (∀ (K : Type u) [Field K] [Algebra R K] (φ₁ φ₂ : B →ₐ[R] K),
    res φ₁ ξ = res φ₂ ξ → φ₁ = φ₂)

lemma RingChart.transport {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B']
    [Algebra R B'] {ξ : F.obj (op (ovR R B))} (h : RingChart ξ) (e : B ≃ₐ[R] B') :
    RingChart (res e.toAlgHom ξ) := by
  refine ⟨fun A _ _ _ _ I hI u₀ v hv ↦ ?_, fun K _ _ φ₁ φ₂ hφ ↦ ?_⟩
  · rw [res_res] at hv
    obtain ⟨u, ⟨hu1, hu2⟩, huniq⟩ := h.1 A I hI (u₀.comp e.toAlgHom) v hv
    refine ⟨u.comp e.symm.toAlgHom, ⟨?_, ?_⟩, fun u' ⟨hu'1, hu'2⟩ ↦ ?_⟩
    · rw [← AlgHom.comp_assoc, hu1, AlgHom.comp_assoc]
      ext x
      simp
    · rw [res_res, AlgHom.comp_assoc]
      convert hu2 using 2
      ext x
      simp
    · have := huniq (u'.comp e.toAlgHom) ⟨by rw [← AlgHom.comp_assoc, hu'1], by
        rw [← res_res, hu'2]⟩
      rw [← this]
      ext x
      simp
  · rw [res_res, res_res] at hφ
    have := h.2 K _ _ hφ
    ext x
    have h' := congrArg (fun f ↦ f (e.symm x)) this
    simpa using h'

/-- The `Over`-level chart conditions from the ring-level ones. -/
lemma RingChart.good {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Algebra.FormallyUnramified R B] {ξ : F.obj (op (ovR R B))} (h : RingChart ξ) :
    IsMonoElement F ξ ∧ ∀ y, InfinitesimallyEtaleAt F ξ y :=
  ⟨isMonoElement_of_field ξ h.2, infinitesimallyEtaleAt_of_ring ξ h.1⟩

end RingChart


section Finite

variable [IsLocalRing R] [IsArtinianRing R]

lemma residue_nil (r : R) (h : algebraMap R (ResidueField R) r = 0) : IsNilpotent r := by
  have hr : r ∈ maximalIdeal R := (residue_eq_zero_iff r).mp h
  exact isNilpotent_of_mem_maximalIdeal hr

/-- A ring-level chart through every point of `F` with values in a finite extension `κ` of the
residue field `k` of `R`: the minimal field of definition `E ⊆ κ` (`exists_minimal`), its étale
lift `E_L` (`exists_etale_lift`) and the minimal lift `ξ ∈ F(Spec (E_L/J))`
(`exists_chart_ring`). -/
theorem exists_ringChart_finite (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F)
    (hF : FaithfullyFlatSheaf F) (h2 : FilteredColimits F) (h5 : NilpotentInjective F)
    {κ : Type u} [Field κ] [Algebra (ResidueField R) κ] [Algebra R κ]
    [IsScalarTower R (ResidueField R) κ] [FiniteDimensional (ResidueField R) κ]
    (η : F.obj (op (ovR R κ))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (ξ : F.obj (op (ovR R B))),
      Algebra.FiniteType R B ∧ Algebra.FormallyUnramified R B ∧ IsArtinianRing B ∧
        RingChart ξ ∧ ∃ ρ : B →ₐ[R] κ, res ρ ξ = η := by
  obtain ⟨E, θ, hθ, hmin, hsep⟩ :=
    exists_minimal hZ hF h5 (k := ResidueField R) IsLocalRing.residue_surjective η
  have : FiniteDimensional (ResidueField R) E := inferInstance
  obtain ⟨Et, _, _, hEl, hEa, hEe, hEf, πE, hπE⟩ :=
    exists_etale_lift (R := R) (k := ResidueField R) (L := E) IsLocalRing.residue_surjective
  obtain ⟨J, ξ, hJ, hξ, hInf, hMono⟩ := exists_chart_ring h4 hZ hF h2 h5 (k := ResidueField R)
    (L := E) (E := Et) IsLocalRing.residue_surjective residue_nil πE hπE θ hmin
  obtain ⟨πJ, hπJ⟩ := exists_factor (Ideal.Quotient.mkₐ R J) Ideal.Quotient.mk_surjective πE
    (fun a ha ↦ by
      rw [← RingHom.mem_ker]
      exact hJ ((Ideal.Quotient.eq_zero_iff_mem).mp ha))
  have hres : res πJ ξ = θ := by
    have := hξ E πJ (AlgHom.id R E) (by rw [AlgHom.id_comp, hπJ])
    rwa [res_id] at this
  have : Algebra.FiniteType R (Et ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R J) Ideal.Quotient.mk_surjective
  refine ⟨Et ⧸ J, inferInstance, inferInstance, ξ, inferInstance, inferInstance, inferInstance,
    ⟨hInf, hMono⟩, (E.val.restrictScalars R).comp πJ, ?_⟩
  rw [← res_res, hres, hθ]

end Finite

section Index

variable (F) [hSm : ∀ T : Over (Spec R), Small.{u} (F.obj (op T))]

/-- The presented `R`-algebras `R[X₁, …, Xₙ]/I`. -/
abbrev PRing (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) : Type u := MvPolynomial (Fin n) R ⧸ I

/-- Raw chart data: a presented `R`-algebra and a (shrunk) element of `F` over it. -/
abbrev ChartData : Type u :=
  Σ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)), Shrink.{u} (F.obj (op (ovR R (PRing n I))))

variable {F} in
/-- The element of `F` carried by chart data. -/
def ChartData.elem (x : ChartData F) : F.obj (op (ovR R (PRing x.1 x.2.1))) :=
  (equivShrink _).symm x.2.2

variable {F} in
/-- Chart data whose ring is formally unramified and artinian and whose element is a
monomorphism, infinitesimally étale at every point. -/
def ChartData.Good (x : ChartData F) : Prop :=
  Algebra.FormallyUnramified R (PRing x.1 x.2.1) ∧ IsArtinianRing (PRing x.1 x.2.1) ∧
    IsMonoElement F x.elem ∧ ∀ y, InfinitesimallyEtaleAt F x.elem y

/-- The index type of the charts. -/
def ChartIdx : Type u := {x : ChartData F // x.Good}

variable {F}

/-- Every ring-level chart is isomorphic to one of the indexed charts. -/
lemma exists_index {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Algebra.FormallyUnramified R B] [IsArtinianRing B] {ξ : F.obj (op (ovR R B))}
    (hξ : RingChart ξ) :
    ∃ (i : ChartIdx F) (e : B ≃ₐ[R] PRing i.1.1 i.1.2.1), i.1.elem = res e.toAlgHom ξ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance :
    Algebra.FiniteType R B)
  let e : B ≃ₐ[R] PRing n (RingHom.ker f) := (Ideal.quotientKerAlgEquivOfSurjective hf).symm
  let x : ChartData F := ⟨n, RingHom.ker f, equivShrink _ (res e.toAlgHom ξ)⟩
  have hx : x.elem = res e.toAlgHom ξ := (equivShrink _).symm_apply_apply _
  have : Algebra.FiniteType R (PRing n (RingHom.ker f)) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R _) Ideal.Quotient.mk_surjective
  have : Algebra.FormallyUnramified R (PRing n (RingHom.ker f)) :=
    Algebra.FormallyUnramified.of_equiv e
  have hgood : x.Good := by
    refine ⟨inferInstance, e.toRingEquiv.isArtinianRing, ?_⟩
    rw [hx]
    exact (hξ.transport e).good
  exact ⟨⟨x, hgood⟩, e, hx⟩

/-- Every point of `F` with values in a field `K` factors through an indexed chart. By (F2) it
comes from a finitely generated subalgebra `D ⊆ K`; at a closed point of `Spec D` the residue
field is finite over `k`, so the restriction factors through a chart; the factorization locus
`W` is open (`ChartGluing.isOpen_W'`) and so contains the generic point of `Spec D`. -/
theorem exists_fac_field [IsLocalRing R] [IsArtinianRing R] (hZ : ZariskiSheaf F)
    (hF : FaithfullyFlatSheaf F) (h2 : FilteredColimits F) (h3 : AdicLimits F)
    (h4 : ArtinianLifting F) (h5 : NilpotentInjective F) {K : Type u} [Field K] [Algebra R K]
    (η : F.obj (op (ovR R K))) :
    ∃ (i : ChartIdx F) (ρ : PRing i.1.1 i.1.2.1 →ₐ[R] K), res ρ i.1.elem = η := by
  obtain ⟨s, x, hx⟩ := exists_fg hZ h2 (C := R) (A := K) η
  let D := Algebra.adjoin (R : Type u) (s : Set K)
  have : Algebra.FiniteType R D :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
  obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal D
  have := h𝔫
  let κ := D ⧸ 𝔫
  let : Field κ := Ideal.Quotient.field 𝔫
  obtain ⟨kκ, hkκ⟩ := exists_factor (Algebra.ofId R (ResidueField R))
    IsLocalRing.residue_surjective (Algebra.ofId R κ)
    (fun r hr ↦ ((residue_nil r hr).map (algebraMap R κ)).eq_zero)
  let : Algebra (ResidueField R) κ := kκ.toRingHom.toAlgebra
  have : IsScalarTower R (ResidueField R) κ := IsScalarTower.of_algebraMap_eq fun r ↦
    (congrArg (fun f ↦ f r) hkκ).symm
  have : Algebra.FiniteType R κ :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R 𝔫) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (ResidueField R) κ :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (ResidueField R) κ
  have : FiniteDimensional (ResidueField R) κ :=
    finite_of_finite_type_of_isJacobsonRing (ResidueField R) κ
  obtain ⟨B, _, _, ξB, hBf, hBu, hBa, hBc, ρ, hρ⟩ := exists_ringChart_finite h4 hZ hF h2 h5 (κ := κ)
    (res (Ideal.Quotient.mkₐ R 𝔫) x)
  obtain ⟨i, e, hie⟩ := exists_index hBc
  obtain ⟨-, -, hmono, hét⟩ := i.2
  have : LocallyOfFiniteType (ovR R (PRing i.1.1 i.1.2.1)).hom := Charts.locallyOfFiniteType_ovR _
  -- the closed point lies in the factorization locus
  let g₁ : ovR R κ ⟶ ovR R D := homR (Ideal.Quotient.mkₐ R 𝔫)
  have hfac₁ : ChartGluing.Fac i.1.elem x g₁ := by
    refine ⟨homR (ρ.comp e.symm.toAlgHom), ?_⟩
    change res (ρ.comp e.symm.toAlgHom) i.1.elem = res (Ideal.Quotient.mkₐ R 𝔫) x
    rw [hie, res_res, AlgHom.comp_assoc]
    convert hρ using 2
    ext b
    simp
  have hmem₁ := (ChartGluing.fac_fieldPt_iff hmono hF g₁).mp hfac₁
  have hopen := ChartGluing.isOpen_W' hmono hZ hF h2 h3 hét x
  -- hence so does the generic point
  let g₀ : ovR R K ⟶ ovR R D := homR (D.val.restrictScalars R)
  have hmem₀ : g₀.left (IsLocalRing.closedPoint K) ∈ ChartGluing.W i.1.elem x := by
    obtain ⟨_, ⟨a, rfl⟩, ha, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      hmem₁ hopen
    apply hsub
    change a ∉ (PrimeSpectrum.comap (D.val.restrictScalars R).toRingHom
      (IsLocalRing.closedPoint K)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal]
    change a ∉ Ideal.comap (D.val.restrictScalars R).toRingHom (maximalIdeal K)
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_comap, Ideal.mem_bot]
    intro h0
    apply ha
    have : a = 0 := Subtype.ext h0
    rw [this]
    exact Ideal.zero_mem _
  obtain ⟨h, hh⟩ := (ChartGluing.fac_fieldPt_iff hmono hF g₀).mpr hmem₀
  obtain ⟨ρ', rfl⟩ := exists_homR h
  exact ⟨i, ρ', hh.trans hx⟩

end Index

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

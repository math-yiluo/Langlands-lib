import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalRankZeroOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFixedCoefficientFiniteness
import Langlands.Representation.Plancherel.FiniteSmoothCompactEvaluation
import Langlands.BruhatTits.RationalPoints.CentralSplitQuotientCompactness
import Langlands.GroupScheme.Nilpotent.EmptyRoots
import Langlands.GroupScheme.Rational.AnisotropicCompactnessProof
import Langlands.GroupScheme.Rational.CenterQuotientModel
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.SplitTorusRationalRank
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveProof
import Langlands.GroupScheme.Torus.OpenSections
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit

/-! # Proof of discrete-series orbit finiteness in relative semisimple rank zero -/

noncomputable section

universe u uG uV

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.HarishChandraSchwartz

section FiniteEvaluation

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- A subspace of left character-equivariant, right `H`-invariant functions is
finite dimensional if the quotient by the character subgroup is compact. -/
private theorem finiteDimensional_of_compact_quotient
    (A : Subgroup Γ) [A.Normal] [CompactSpace (Γ ⧸ A)] (χ : A →* ℂˣ)
    (H : OpenSubgroup Γ) (E : Submodule ℂ (Γ → ℂ))
    (hχ : ∀ (f : E) (a : A) x, f.val ((a : Γ) * x) = (χ a : ℂ) * f.val x)
    (hH : ∀ (f : E) x (h : H), f.val (x * (h : Γ)) = f.val x) :
    FiniteDimensional ℂ E := by
  classical
  let p := QuotientGroup.mk' A
  let L := H.toSubgroup.map p
  let C := (Γ ⧸ A) ⧸ L
  have hLo : IsOpen (L : Set (Γ ⧸ A)) :=
    (QuotientGroup.isOpenMap_coe (N := A)) _ H.isOpen
  let : Finite C := Subgroup.quotient_finite_of_isOpen L hLo
  let : Fintype C := Fintype.ofFinite C
  let r (q : C) : Γ := q.out.out
  let ev : E →ₗ[ℂ] (C → ℂ) :=
    { toFun := fun f q => f.val (r q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective ev
  intro f g hfg
  apply Subtype.ext
  funext x
  let q : C := QuotientGroup.mk (p x)
  have hr : p (r q) = q.out := Quotient.out_eq _
  have hq : (QuotientGroup.mk (p (r q)) : C) = QuotientGroup.mk (p x) :=
    (congrArg (fun y => (QuotientGroup.mk y : C)) hr).trans (Quotient.out_eq q)
  have hmem : (p (r q))⁻¹ * p x ∈ L := QuotientGroup.eq.mp hq
  obtain ⟨h, hh, heq⟩ := Subgroup.mem_map.mp hmem
  have hxq : p x = p (r q * h) := by
    rw [map_mul, heq, mul_inv_cancel_left]
  let a : A := ⟨x * (r q * h)⁻¹,
    by simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hxq⟩
  have hx : (a : Γ) * (r q * h) = x := inv_mul_cancel_right _ _
  have hval (w : E) : w.val x = (χ a : ℂ) * w.val (r q) := by
    rw [← hx, hχ w a, hH w (r q) ⟨h, hh⟩]
  change f.val x = g.val x
  rw [hval f, hval g]
  exact congrArg ((χ a : ℂ) * ·) (congrFun hfg q)

omit [IsTopologicalGroup Γ] in
/-- Coefficients of a representation with the specified character lie in
the corresponding algebraic equivariant function space. -/
private theorem coefficientFunctionSpace_le_equivariantFunctions
    (A : Subgroup Γ) (χ : A →* ℂˣ) (π : SmoothRep.{0, uG, uV} ℂ Γ)
    (hχ : ∀ (a : A) v, π.representation (a : Γ) v = (χ a : ℂ) • v) :
    coefficientFunctionSpace π ≤ (Whittaker.equivariantFunctions A χ).toSubmodule := by
  apply iSup_le
  intro ℓ
  rintro _ ⟨v, rfl⟩
  intro a x
  change ℓ.val (π.representation ((a : Γ) * x) v) =
    (χ a : ℂ) * ℓ.val (π.representation x v)
  rw [map_mul, Module.End.mul_apply, hχ, map_smul, smul_eq_mul]

/-- Compactness of the split-central quotient provides the finite-dimensional
coefficient space required in the proof of VIII.1.2. -/
theorem finiteDimensional_discreteSeriesCentralFixedCoefficientSpace_of_compact_quotient
    (A : Subgroup Γ) [A.Normal] (hA : A ≤ Subgroup.center Γ) [CompactSpace (Γ ⧸ A)]
    [MeasurableSpace (Γ ⧸ A)] (mu : Measure (Γ ⧸ A)) [mu.IsHaarMeasure]
    (χ : A →* ℂˣ) (H : OpenSubgroup Γ) :
    FiniteDimensional ℂ
      (discreteSeriesCentralFixedCoefficientSpace.{uG, uV} A hA mu χ H.toSubgroup) := by
  let E := discreteSeriesCentralFixedCoefficientSpace.{uG, uV} A hA mu χ H.toSubgroup
  let I := LinearMap.id (R := ℂ) (M := Γ → ℂ)
  have hle : E ≤ (Whittaker.equivariantFunctions A χ).toSubmodule ⊓
      rightInvariantEvaluationSubmodule I H.toSubgroup := by
    apply (discreteSeriesCentralFixedCoefficientSpace_le_iff A hA mu χ H.toSubgroup _).mpr
    intro ω hω f hf hfH
    have hωχ : classActsByCharacter A χ (Quotient.mk _ ω.val.out) :=
      (Quotient.out_eq ω.val).symm ▸ hω.1
    refine ⟨coefficientFunctionSpace_le_equivariantFunctions A χ ω.val.out.obj
      ((classActsByCharacter_mk A χ ω.val.out).mp hωχ) hf, ?_⟩
    change ∀ x (h : H), f (x * (h : Γ)) = f x
    intro x h
    simpa only [one_mul] using hfH 1 H.one_mem h h.property x
  exact finiteDimensional_of_compact_quotient A χ H E
    (fun f => (hle f.property).1) (fun f => (hle f.property).2)

end FiniteEvaluation

section RationalQuotient

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {s : T.toGrp ⟶ G}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem isCentral_of_relativeRootRank_eq_zero (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i)
    (hzero : haveI := hG.isAffineHom; relativeRootRank i = 0) : IsCentral i := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hG.connectedSpace
  let := hi.1.1.finite_relativeRootSpan i
  have hspan : relativeRootSpan i = ⊥ := Submodule.finrank_eq_zero.mp hzero
  apply isCentral_of_roots_eq_empty hi.1.1 i
  rw [← relativeRoots_eq_roots]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro α hα
  have hαrat : toRat α ∈ relativeRootSpan i := toRat_mem_ratSpan hα
  rw [hspan, Submodule.mem_bot] at hαrat
  exact (mem_relativeRoots.mp hα).1
    (hi.1.1.character_toRat_injective (by simpa [toRat] using hαrat))

/-- In relative semisimple rank zero the quotient of the actual rational
point group by any split component is compact in the quotient topology. -/
theorem compactSpace_rationalPoints_quotient_of_relativeRootRank_eq_zero
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hzero : haveI := hG.isAffineHom; relativeRootRank i = 0) (hs : IsSplitComponent s) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    CompactSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := hG.isAffineHom
  let := hG.smooth
  have hc := isCentral_of_relativeRootRank_eq_zero hG hi hzero
  obtain ⟨f, hf⟩ := hs.exists_comp_eq (finiteType_coordinateAlgebra G) ⟨hi.1, hc⟩
  let := hi.2 T s hs.1.1 f hf
  have hsmax : IsMaximalSplitTorus s :=
    (IsMaximalSplitTorus.iso_comp_iff (asIso f) s).mp
      (show IsMaximalSplitTorus (f ≫ s) from hf ▸ hi)
  obtain ⟨Q, q, hQs, hQa, hani, _, hq⟩ :=
    BruhatTits.RationalPoints.exists_smooth_anisotropic_central_split_quotient
      G hsmax hs.1.2
  let := hQs
  let := hQa
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have hcentral : SubgroupFunctor.range s ≤ center G := by
    rintro U _ ⟨a, rfl⟩
    exact hs.1.2 U a
  have hQ := centralQuotientReductive F G Q q _ hG hQa
    (inferInstance : LocallyOfFiniteType Q.X.hom) hcentral hq
  let : IsClosedImmersion s.hom.hom.left := hs.1.1.2
  let : Mono s.hom.hom := Over.mono_of_mono_left _
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have hsections := SplitTorusQuotient.hasOpenSectionsAtPoints s q hq.2.2.2 hs.1.1.1
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints Q) := rationalPointTopology F Q.X
  let := (rationalPoints.map s).range.normal_of_le_center hs.1.2.range_le_center
  let : CompactSpace (rationalPoints Q) :=
    isCompact_univ_iff.mp ((anisotropicCompactness_proof F Q hQ).mpr hani)
  exact (pointQuotientHomeomorph (rationalPoints.map s).range (rationalPoints.map q)
    (rationalPoints_ker_eq_range_of_fppfQuotient s q hq)
    (isQuotientMap_rationalPointMap_of_open_sections F q.hom.hom hsections)).symm.toHomeomorph.compactSpace

end RationalQuotient

/-- The rank-zero specialization of Waldspurger VIII.1.2 for the actual
unitary unramified twist orbits at any compact open level. -/
theorem rationalRankZeroDiscreteSeriesOrbitFiniteness :
    RationalRankZeroDiscreteSeriesOrbitFinitenessStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi hzero T s hs
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
  let A := (rationalPoints.map s).range
  have hA : A ≤ Subgroup.center (rationalPoints G) := hs.1.2.range_le_center
  let : A.Normal := A.normal_of_le_center hA
  let : MeasurableSpace (rationalPoints G ⧸ A) := borel _
  let : CompactSpace (rationalPoints G ⧸ A) :=
    compactSpace_rationalPoints_quotient_of_relativeRootRank_eq_zero hG hi hzero hs
  intro mu _ H hHo hHc
  let Hopen : OpenSubgroup (rationalPoints G) := ⟨H, hHo⟩
  apply finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional G s mu hG hs Hopen hHc
  intro χ _ _ _
  exact ⟨discreteSeriesCentralFixedCoefficientSpace.{u, uV} A hA mu χ H,
    finiteDimensional_discreteSeriesCentralFixedCoefficientSpace_of_compact_quotient
      A hA mu χ Hopen,
    fun _ hω _ hf hfH => mem_discreteSeriesCentralFixedCoefficientSpace A hA mu χ H hω hf hfH⟩

end Langlands.HarishChandraSchwartz

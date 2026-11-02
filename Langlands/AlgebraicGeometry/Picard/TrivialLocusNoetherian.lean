import Langlands.AlgebraicGeometry.Picard.TrivialLocusOpen
import Langlands.AlgebraicGeometry.Picard.ClassEqualizerReduction

/-! # The triviality locus over a Noetherian base is cut out by an immersion

Over a Noetherian `k`-algebra `B`, the fppf triviality locus of a line bundle on `Spec B ×_k X`
lies in the union of the basic opens of the scalars of column splits with `a` remaining columns.
On each of them it lies in the stratum of the split, where it is cut out by an open immersion.
Together with `ClassEqualizerReduction` this proves `FieldPicardClassEqualizerImmersionStatement`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open Scheme.TwoAffineOpenCover (moduleSectionsOfHom specMap)
open Langlands.AlgebraicGeometry.AlgebraicSpace (specOver)

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativePicard

open Langlands.LinearAlgebra.KernelColumnSplit SectionsComparison

namespace HasImmersionLocus

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- Transport along a factorization of the comparison morphism. -/
lemma of_eq_comp {T V V' : Over S} {φ : V ⟶ T} {φ' : V' ⟶ T} (ψ : V ⟶ V')
    (h : ψ ≫ φ' = φ) {N : LineBundle ((relativeSpace f).obj T)}
    (hN : HasImmersionLocus f V' ((LineBundle.pullback ((relativeSpace f).map φ')).obj N)) :
    HasImmersionLocus f V ((LineBundle.pullback ((relativeSpace f).map φ)).obj N) :=
  of_pullback f ψ (LineBundle.pullbackCompEqIso _ _ (by rw [← Functor.map_comp, h]) N) hN

/-- If every member of the triviality locus factors through the immersion `φ.left`, the
property can be checked after pulling back along `φ`. -/
lemma of_factor {T V : Over S} (φ : V ⟶ T) [IsImmersion φ.left]
    {N : LineBundle ((relativeSpace f).obj T)}
    (hj : ∀ ⦃T' : Scheme.{u}⦄ (g : T' ⟶ T.left), trivialLocus f T N g →
      ∃ g' : T' ⟶ V.left, g' ≫ φ.left = g)
    (h : HasImmersionLocus f V ((LineBundle.pullback ((relativeSpace f).map φ)).obj N)) :
    HasImmersionLocus f T N := by
  obtain ⟨Z, ι, hι, hcut⟩ := h
  have := hι
  refine ⟨Z, ι ≫ φ.left, inferInstance, CutsOut.comp φ.left hj ?_⟩
  rw [trivialLocus_pullback]
  exact hcut

end HasImmersionLocus

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

/-- The morphism from the stratum of a column split to the base, over `Spec k`. -/
def stratumHom {B : Type u} [CommRing B] [Algebra k B] {M₀ M₁ : Type*} [AddCommGroup M₀]
    [Module B M₀] [AddCommGroup M₁] [Module B M₁] {d : M₀ →ₗ[B] M₁} (S : ColumnSplit d) :
    specOver k (Stratum S) ⟶ specOver k B :=
  Over.homMk (specMap B (Stratum S)) (FrameCombination.specMap_comp k B (Stratum S))

/-- On the stratum of a column split, the sections of all base changes of `N` are free, with one
generator for each remaining column. -/
theorem sectionsFree_stratum {B : Type u} [CommRing B] [Algebra k B]
    {N : LineBundle ((relativeSpace X.hom).obj (specOver k B))}
    (G : CoherentBaseChange.TwoTermComplex.{u, u} B) (ε : SectionsEquivs X N G)
    (S : ColumnSplit G.d) :
    SectionsFree X ((LineBundle.pullback ((relativeSpace X.hom).map (stratumHom S))).obj N)
      (Fintype.card S.α) := by
  intro A _ _
  let : Algebra B A := ((algebraMap (Stratum S) A).comp (algebraMap B (Stratum S))).toAlgebra
  have : @IsScalarTower B (Stratum S) A Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have ht : IsUnit (algebraMap B A S.t) := by
    show IsUnit (algebraMap (Stratum S) A (algebraMap B (Stratum S) S.t))
    rw [IsScalarTower.algebraMap_apply B (Localization.Away S.t) (Stratum S)]
    exact ((IsLocalization.Away.algebraMap_isUnit S.t).map _).map _
  have h0 : S.schurMatrix.map (algebraMap B A) = 0 := by
    ext i j
    rw [Matrix.map_apply, Matrix.zero_apply]
    show algebraMap (Stratum S) A (algebraMap B (Stratum S) (S.schurMatrix i j)) = 0
    rw [IsScalarTower.algebraMap_apply B (Localization.Away S.t) (Stratum S)]
    have : algebraMap (Localization.Away S.t) (Stratum S)
        (algebraMap B (Localization.Away S.t) (S.schurMatrix i j)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, j), rfl⟩)
    rw [this, map_zero]
  have hpb : IsPullback (pullback.fst (baseMap X (Stratum S)) (specMap (Stratum S) A) ≫
      (relativeSpace X.hom).map (stratumHom S))
      (pullback.snd (baseMap X (Stratum S)) (specMap (Stratum S) A))
      (baseMap X B) (specMap B A) := by
    rw [← FrameCombination.specMap_comp B (Stratum S) A]
    exact (IsPullback.of_hasPullback _ _).paste_horiz
      (relativeSpace_isPullback X.hom (stratumHom S))
  exact ⟨((sectionsEquivOfIso _ ((Scheme.Modules.pullbackComp _ _).app N.obj)).trans
    ((sectionsEquivOfIsPullback hpb (IsPullback.of_hasPullback (baseMap X B) (specMap B A))
      N.obj).trans ((ε A).trans (S.kerBaseChangeEquivFun ht h0)))).trans
    (LinearEquiv.funCongrLeft A A (Fintype.equivFin S.α).symm)⟩

namespace HasImmersionLocus

/-- The property only depends on the isomorphism class of the bundle. -/
lemma of_iso {S X : Scheme.{u}} {f : X ⟶ S} {T : Over S}
    {N N' : LineBundle ((relativeSpace f).obj T)} (e : N ≅ N') (h : HasImmersionLocus f T N) :
    HasImmersionLocus f T N' := by
  obtain ⟨Z, ι, hι, hcut⟩ := h
  exact ⟨Z, ι, hι, trivialLocus_congr f e ▸ hcut⟩

end HasImmersionLocus

/-- The morphism from the spectrum of a localization to the base, over `Spec k`. -/
def awayHom {B : Type u} [CommRing B] [Algebra k B] (t : B) :
    specOver k (Localization.Away t) ⟶ specOver k B :=
  Over.homMk (specMap B (Localization.Away t)) (FrameCombination.specMap_comp k B _)

set_option backward.isDefEq.respectTransparency.types false in
/-- Over a Noetherian `k`-algebra `B`, the triviality locus of a line bundle on `Spec B ×_k X`
is cut out by an immersion. -/
theorem hasImmersionLocus_of_isNoetherianRing [IsProper X.hom] (B : Type u) [CommRing B]
    [IsNoetherianRing B] [Algebra k B] (N : LineBundle ((relativeSpace X.hom).obj (specOver k B))) :
    HasImmersionLocus X.hom (specOver k B) N := by
  obtain ⟨a, ha⟩ := exists_sectionsRank X
  have hN := isInvertible_of_isLocallyFreeRankOne N.property
  obtain ⟨G, -, ε, -⟩ :=
    Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange (baseMap X B) N.obj
      hN.exists_trivialization
  have hopen (r : B) : IsOpenImmersion (specMap B (Localization.Away r)) :=
    IsOpenImmersion.of_isLocalization r
  -- The property over the localization at the scalar of a column split with `a` columns.
  have hloc (S : ColumnSplit G.d) (hS : Fintype.card S.α = a) :
      HasImmersionLocus X.hom (specOver k (Localization.Away S.t))
        ((LineBundle.pullback ((relativeSpace X.hom).map (awayHom S.t))).obj N) := by
    let ψ : specOver k (Stratum S) ⟶ specOver k (Localization.Away S.t) :=
      Over.homMk (specMap (Localization.Away S.t) (Stratum S))
        (FrameCombination.specMap_comp k (Localization.Away S.t) (Stratum S))
    have : IsClosedImmersion ψ.left :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hψ : ψ ≫ awayHom S.t = stratumHom S := by
      ext
      exact FrameCombination.specMap_comp B (Localization.Away S.t) (Stratum S)
    refine HasImmersionLocus.of_factor X.hom ψ (fun T' g hg => ?_) ?_
    · rw [← trivialLocus_pullback] at hg
      obtain ⟨h, hh⟩ := factorSieve_stratum_of_mem_trivialLocus X ha G ε S hS hg ⟨g, rfl⟩
      refine ⟨h, ?_⟩
      rw [← cancel_mono (specMap B (Localization.Away S.t)), Category.assoc]
      change h ≫ specMap (Localization.Away S.t) (Stratum S) ≫ specMap B _ = _
      rw [FrameCombination.specMap_comp B (Localization.Away S.t) (Stratum S)]
      exact hh
    · refine HasImmersionLocus.of_iso (LineBundle.pullbackCompEqIso _ _
        (by rw [← Functor.map_comp, hψ]) N).symm ?_
      exact hasImmersionLocus_of_sectionsFree X ha (hS ▸ sectionsFree_stratum X G ε S)
  -- The union of the localizations at the scalars of column splits with `a` columns.
  let 𝒮 := {S : ColumnSplit G.d // Fintype.card S.α = a}
  let W : (Spec (.of B)).Opens := ⨆ S : 𝒮, (specMap B (Localization.Away S.1.t)).opensRange
  have hrange (S : 𝒮) : Set.range (specMap B (Localization.Away S.1.t)) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact le_iSup (fun S : 𝒮 => (specMap B (Localization.Away S.1.t)).opensRange) S
  have hW : ∀ ⦃T' : Scheme.{u}⦄ (g : T' ⟶ Spec (.of B)),
      trivialLocus X.hom (specOver k B) N g → ∃ g' : T' ⟶ W, g' ≫ W.ι = g := by
    intro T' g hg
    refine ⟨IsOpenImmersion.lift W.ι g ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨S, hS, htx⟩ := exists_columnSplit_of_mem_trivialLocus X ha G ε hg x
    apply hrange ⟨S, hS⟩
    change g x ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away S.t)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away S.t) S.t]
    exact htx
  let ℓ (S : 𝒮) : Spec (.of (Localization.Away S.1.t)) ⟶ W :=
    IsOpenImmersion.lift W.ι (specMap B _) (hrange S)
  have hℓ (S : 𝒮) : IsOpenImmersion (ℓ S) := by
    have : IsOpenImmersion (ℓ S ≫ W.ι) := by
      rw [IsOpenImmersion.lift_fac]
      exact hopen _
    exact IsOpenImmersion.of_comp _ W.ι
  have : IsImmersion
      (Over.homMk W.ι rfl : Over.mk (W.ι ≫ (specOver k B).hom) ⟶ specOver k B).left :=
    inferInstanceAs (IsImmersion W.ι)
  refine HasImmersionLocus.of_factor X.hom
    (Over.homMk W.ι rfl : Over.mk (W.ι ≫ (specOver k B).hom) ⟶ specOver k B) hW ?_
  refine HasImmersionLocus.of_cover X.hom _
    (Sieve.generate (Presieve.ofArrows (fun S : 𝒮 => Spec (.of (Localization.Away S.1.t))) ℓ))
    ?_ ?_
  · apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun w => ?_, fun S => ⟨inferInstance, inferInstance⟩⟩
    have hw : W.ι w ∈ W := by
      change W.ι w ∈ (W : Set (Spec (.of B)))
      rw [← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
    obtain ⟨S, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hw
    refine ⟨S, y, W.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]
    exact hy
  · rintro V _ ⟨Y', v, _, ⟨S⟩, rfl⟩
    let ψ : Over.mk ((v ≫ ℓ S) ≫ (Over.mk (W.ι ≫ (specOver k B).hom)).hom) ⟶
        specOver k (Localization.Away S.1.t) :=
      Over.homMk v (by
        simp only [Over.mk_hom, Category.assoc]
        rw [IsOpenImmersion.lift_fac_assoc, FrameCombination.specMap_comp k B])
    have hcomp : ψ ≫ awayHom S.1.t =
        (Over.homMk (v ≫ ℓ S) : Over.mk ((v ≫ ℓ S) ≫ (Over.mk (W.ι ≫ (specOver k B).hom)).hom) ⟶
          Over.mk (W.ι ≫ (specOver k B).hom)) ≫
          (Over.homMk W.ι rfl : Over.mk (W.ι ≫ (specOver k B).hom) ⟶ specOver k B) := by
      ext
      simp [ψ, awayHom, ℓ]
    refine HasImmersionLocus.of_pullback X.hom ψ
      (LineBundle.pullbackCompEqIso _ _ rfl N ≪≫
        eqToIso (by rw [← Functor.map_comp, ← Functor.map_comp, hcomp]) ≪≫
        (LineBundle.pullbackCompEqIso _ _ rfl N).symm) (hloc S.1 S.2)

/-- The Library statement `FieldPicardClassEqualizerImmersionStatement`: for a proper scheme
over a field, the locus where the fppf Picard classes of two line bundles agree is represented
by an immersion. -/
theorem fieldPicardClassEqualizerImmersion : FieldPicardClassEqualizerImmersionStatement.{u} :=
  fieldPicardClassEqualizerImmersion_of_noetherian fun _ _ X hX B _ _ _ N =>
    have := hX
    hasImmersionLocus_of_isNoetherianRing X B N

end Langlands.AlgebraicGeometry.Picard.RelativePicard

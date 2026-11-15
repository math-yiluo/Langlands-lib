import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsMono
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsFromEtaleLocus

/-! # Murre's charts over a noetherian affine base, from Lemma 2

This module proves `MurreNoetherianChartsStatement` assuming Murre's Lemma 2
(`MurreEtaleLocusOpenStatement`). For every point `s` of `Spec R` and every point of the
scheme representing `F` over `Spec 𝒪_{Spec R, s}`, an affine open `Spec B` around it is spread
out to `Spec A[1/b]` with `A` of finite type over `R`; the restriction of the corresponding
element is a formally unramified, infinitesimally étale monomorphism through which every
point over `s` that lands in `Spec B` factors. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

lemma locallyOfFiniteType_ovR (T : Type u) [CommRing T] [Algebra R T]
    [Algebra.FiniteType R T] : LocallyOfFiniteType (ovR R T).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R T)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.2 inferInstance

lemma formallyUnramified_ovR (T : Type u) [CommRing T] [Algebra R T]
    [Algebra.FormallyUnramified R T] : FormallyUnramified (ovR R T).hom := by
  change FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap R T)))
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  exact RingHom.formallyUnramified_algebraMap.2 inferInstance

section Datum

variable {s : Spec R} {Y : Over (Spec ((Spec R).presheaf.stalk s))}
  (e : (baseChange ((Spec R).fromSpecStalk s) F).RepresentableBy Y)
variable {B : Type u} [CommRing B] [Algebra R B]
  (t : Spec (CommRingCat.of B) ⟶ Spec ((Spec R).presheaf.stalk s))
  (ht : t ≫ (Spec R).fromSpecStalk s = (ovR R B).hom)
  (j : Over.mk t ⟶ Y) [IsOpenImmersion j.left]
variable {A : Type u} [CommRing A] [Algebra R A] [Algebra A B] [IsScalarTower R A B]
  (M : Submonoid A) [IsLocalization M B]
  (ξ : F.obj (op (ovR R A)))

/-- The three shrinkings combined. -/
theorem exists_good_away (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (hF : FaithfullyFlatSheaf F)
    (hrep : ∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F))
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FormallyUnramified R B]
    (hξ : F.map (homR (IsScalarTower.toAlgHom R A B)).op ξ =
      elemEquiv ((Spec R).fromSpecStalk s) e (ovR R B) t ht j)
    (hopen : ∀ a : A, Algebra.FormallyUnramified R (Localization.Away a) →
      IsOpen {y : PrimeSpectrum (Localization.Away a) |
        InfinitesimallyEtaleAt F (resA ξ a) y}) :
    ∃ b ∈ M, Algebra.FormallyUnramified R (Localization.Away b) ∧
      IsMonoElement F (resA ξ b) ∧ ∀ y, InfinitesimallyEtaleAt F (resA ξ b) y := by
  obtain ⟨m₁, hm₁, hFU⟩ := exists_unramified (R := R) (B := B) M
  have := hFU m₁ (dvd_refl _)
  obtain ⟨nE, hnE, het⟩ := exists_etale e t ht j M ξ hξ m₁ hm₁ (hopen m₁ this)
  obtain ⟨nM, hnM, hmono⟩ := exists_mono e t ht j M ξ hZ h2 hF hrep hξ m₁ hm₁
  refine ⟨m₁ * nE * nM, M.mul_mem (M.mul_mem hm₁ hnE) hnM,
    hFU _ ⟨nE * nM, by ring⟩, hmono _ ⟨nE, by ring⟩, het _ ⟨nM, rfl⟩⟩

end Datum

set_option maxHeartbeats 1000000 in
/-- The chart attached to an open immersion `j : Spec B ⟶ Y` into the scheme representing
`F` over `Spec 𝒪_{Spec R, s}`. -/
theorem exists_chart [IsNoetherianRing R] (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (hF : FaithfullyFlatSheaf F)
    (hrep : ∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F))
    (hL2 : ∀ (T : Type u) [CommRing T] [Algebra R T] (ξ : F.obj (op (ovR R T))),
      Algebra.FiniteType R T → Algebra.FormallyUnramified R T →
        IsOpen {y : PrimeSpectrum T | InfinitesimallyEtaleAt F ξ y})
    (s : Spec R) (Y : Scheme.{u}) (q : Y ⟶ Spec ((Spec R).presheaf.stalk s))
    (e : (baseChange ((Spec R).fromSpecStalk s) F).RepresentableBy (Over.mk q))
    [LocallyOfFiniteType q] [FormallyUnramified q]
    (B' : CommRingCat.{u}) (j : Spec B' ⟶ Y) [IsOpenImmersion j] :
    ∃ (U : Over (Spec R)) (ξU : F.obj (op U)),
      (LocallyOfFiniteType U.hom ∧ FormallyUnramified U.hom ∧ IsMonoElement F ξU ∧
        ∀ y, InfinitesimallyEtaleAt F ξU y) ∧
      ∀ (T : Over (Spec R)) (tT : T.left ⟶ Spec ((Spec R).presheaf.stalk s))
        (htT : tT ≫ (Spec R).fromSpecStalk s = T.hom) (x' : Over.mk tT ⟶ Over.mk q),
        Set.range x'.left ⊆ Set.range j →
          ∃ h : T ⟶ U, F.map h.op ξU = elemEquiv ((Spec R).fromSpecStalk s) e T tT htT x' := by
  let O := (Spec R).presheaf.stalk s
  let g := (Spec R).fromSpecStalk s
  let B : Type u := B'
  let φ : O ⟶ B' := Spec.preimage (j ≫ q)
  have hφ : Spec.map φ = j ≫ q := Spec.map_preimage _
  let _ : Algebra O B := φ.hom.toAlgebra
  let _ : Algebra R O := StructureSheaf.stalkAlgebra R s
  have := s.isPrime
  have : IsLocalization.AtPrime O s.asIdeal := StructureSheaf.IsLocalization.to_stalk R s
  let _ : Algebra R B := (φ.hom.comp (algebraMap R O)).toAlgebra
  have : IsScalarTower R O B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hLFTφ : LocallyOfFiniteType (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : IsIso (pullback.diagonal j) := (pullback.isIso_diagonal_iff j).2 inferInstance
  have : FormallyUnramified j := inferInstance
  have hFUφ : FormallyUnramified (Spec.map φ) := by
    rw [hφ]
    exact MorphismProperty.comp_mem @FormallyUnramified j q inferInstance inferInstance
  have : Algebra.FiniteType O B :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hLFTφ
  have : Algebra.FormallyUnramified O B :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).1 hFUφ
  have : Algebra.FormallyUnramified R O :=
    Algebra.FormallyUnramified.of_isLocalization s.asIdeal.primeCompl
  have : Algebra.FormallyUnramified R B := Algebra.FormallyUnramified.comp R O B
  let t : Spec (CommRingCat.of B) ⟶ Spec O := Spec.map φ
  have ht : t ≫ g = (ovR R B).hom := by
    change Spec.map φ ≫ (Spec R).fromSpecStalk s = Spec.map (CommRingCat.ofHom (algebraMap R B))
    rw [Spec.fromSpecStalk_eq']
    exact (Spec.map_comp (StructureSheaf.toStalk R s) φ).symm
  let jO : Over.mk t ⟶ Over.mk q := Over.homMk j hφ.symm
  have : IsOpenImmersion jO.left := inferInstanceAs (IsOpenImmersion j)
  let ξB := elemEquiv g e (ovR R B) t ht jO
  -- spreading out
  obtain ⟨A₀, hA₀ft, hA₀loc⟩ := exists_subalgebra_isLocalization s.asIdeal O B
  let M₀ : Submonoid A₀ := s.asIdeal.primeCompl.map (algebraMap R A₀)
  -- (F2)
  obtain ⟨a₀, ζ, hζ⟩ := exists_away_of_isLocalization M₀ B hZ h2 ξB
  -- rebase to `A = A₀[1/a₀]`
  let A := Localization.Away a₀.val
  let _ : Algebra A B := (toLoc M₀ B a₀).toAlgebra
  have : IsScalarTower A₀ A B :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext (toLoc_algebraMap M₀ B a₀)).symm
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R B r = toLoc M₀ B a₀ (algebraMap R A r)
    rw [IsScalarTower.algebraMap_apply R A₀ A, toLoc_algebraMap,
      ← IsScalarTower.algebraMap_apply]
  let M : Submonoid A := M₀.map (algebraMap A₀ A)
  have : IsLocalization M B :=
    IsLocalization.isLocalization_of_submonoid_le A B (Submonoid.powers a₀.val) M₀
      (Submonoid.powers_le.2 a₀.val_mem)
  have : Algebra.FiniteType R A := Algebra.FiniteType.trans hA₀ft
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a₀.val) A)
  have hξ : F.map (homR (IsScalarTower.toAlgHom R A B)).op ζ = ξB := by
    have : IsScalarTower.toAlgHom R A B = toLocₐ M₀ B a₀ := AlgHom.ext fun _ => rfl
    rw [this]
    exact hζ
  have hopen : ∀ a : A, Algebra.FormallyUnramified R (Localization.Away a) →
      IsOpen {y : PrimeSpectrum (Localization.Away a) |
        InfinitesimallyEtaleAt F (resA ζ a) y} := by
    intro a ha
    have hft : Algebra.FiniteType R (Localization.Away a) :=
      Algebra.FiniteType.trans (S := A) inferInstance
        (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) (Localization.Away a))
    exact hL2 (Localization.Away a) (resA ζ a) hft ha
  obtain ⟨b, hbM, hbFU, hbmono, hbet⟩ :=
    exists_good_away e t ht jO M ζ hZ h2 hF hrep hξ hopen
  have : Algebra.FiniteType R (Localization.Away b) :=
    Algebra.FiniteType.trans (S := A) inferInstance
      (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers b) (Localization.Away b))
  refine ⟨ovR R (Localization.Away b), resA ζ b,
    ⟨locallyOfFiniteType_ovR _, formallyUnramified_ovR _, hbmono, hbet⟩, ?_⟩
  intro T tT htT x' hrange
  let ρ : ovR R B ⟶ ovR R (Localization.Away b) := homR (toLocₐ M B (DivIndex.mk b hbM))
  have hrange' : Set.range x'.left ⊆ Set.range jO.left := hrange
  let l := IsOpenImmersion.lift jO.left x'.left hrange'
  have hl : l ≫ jO.left = x'.left := IsOpenImmersion.lift_fac _ _ _
  have hlt : l ≫ t = tT := by
    have h1 : jO.left ≫ q = t := Over.w jO
    have h2' : x'.left ≫ q = tT := Over.w x'
    rw [← h1, ← Category.assoc, hl, h2']
  let lO : T ⟶ ovR R B := Over.homMk l (by
    change l ≫ (ovR R B).hom = T.hom
    rw [← ht, ← Category.assoc, hlt, htT])
  refine ⟨lO ≫ ρ, ?_⟩
  have e1 : F.map (lO ≫ ρ).op (resA ζ b) = F.map lO.op (elemEquiv g e (ovR R B) t ht jO) := by
    rw [op_comp, Functor.map_comp_apply, map_toLocₐ_resA e t ht jO M ζ hξ b hbM]
  have e2 := elemEquiv_naturality g e lO tT t htT ht jO
  have e3 : (Over.homMk lO.left (lift_comp g lO tT t htT ht) : Over.mk tT ⟶ Over.mk t) ≫ jO =
      x' := by
    ext1
    exact hl
  rw [e3] at e2
  exact e1.trans e2

/-- **Murre's charts from Lemma 2.** Murre's Lemma 2 implies the construction of charts over a
noetherian affine base. -/
theorem noetherianCharts_of_etaleLocusOpen (hL2 : MurreEtaleLocusOpenStatement.{u, v}) :
    MurreNoetherianChartsStatement.{u, v} := by
  intro R _ F hcond hloc hclosed
  have hcond' := hcond
  obtain ⟨-, hZ, hF, h2, -⟩ := hcond'
  have hL2' : ∀ (T : Type u) [CommRing T] [Algebra R T] (ξ : F.obj (op (ovR R T))),
      Algebra.FiniteType R T → Algebra.FormallyUnramified R T →
        IsOpen {y : PrimeSpectrum T | InfinitesimallyEtaleAt F ξ y} := by
    intro T _ _ ξ hft hfu
    have hqc : QuasiCompact (ovR R T).hom :=
      inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    have hsep : IsSeparated (ovR R T).hom :=
      inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    exact hL2 R F hcond hloc hclosed (ovR R T) ξ (locallyOfFiniteType_ovR T) hqc hsep
      (formallyUnramified_ovR T)
  have hrep := hloc
  choose Y q hY using hloc
  have H : ∀ i : (Σ s : Spec R, Y s), ∃ (U : Over (Spec R)) (ξU : F.obj (op U)),
      (LocallyOfFiniteType U.hom ∧ FormallyUnramified U.hom ∧ IsMonoElement F ξU ∧
        ∀ y, InfinitesimallyEtaleAt F ξU y) ∧
      ∀ (T : Over (Spec R)) (tT : T.left ⟶ Spec ((Spec R).presheaf.stalk i.1))
        (htT : tT ≫ (Spec R).fromSpecStalk i.1 = T.hom) (x' : Over.mk tT ⟶ Over.mk (q i.1)),
        Set.range x'.left ⊆ Set.range ((Y i.1).affineOpenCover.f
          ((Y i.1).affineOpenCover.idx i.2)) →
          ∃ h : T ⟶ U, F.map h.op ξU =
            elemEquiv ((Spec R).fromSpecStalk i.1) (hY i.1).1.some T tT htT x' := by
    intro i
    have := (hY i.1).2.2.1
    have := (hY i.1).2.2.2
    exact exists_chart hZ h2 hF hrep hL2' i.1 (Y i.1) (q i.1) (hY i.1).1.some _
      ((Y i.1).affineOpenCover.f ((Y i.1).affineOpenCover.idx i.2))
  choose U ξU hprop hcov using H
  refine ⟨Σ s : Spec R, Y s, U, ξU, hprop, ?_⟩
  intro K _ f η
  let s := f (IsLocalRing.closedPoint (CommRingCat.of K))
  obtain ⟨f', hf'⟩ := exists_comp_fromSpecStalk s f (specializes_refl _)
  let E := elemEquiv ((Spec R).fromSpecStalk s) (hY s).1.some (Over.mk f) f' hf'
  let y := (E.symm η).left (IsLocalRing.closedPoint (CommRingCat.of K))
  obtain ⟨h, hh⟩ := hcov ⟨s, y⟩ (Over.mk f) f' hf' (E.symm η) (by
    rintro _ ⟨z, rfl⟩
    rw [eq_of_isArtinianRing z (IsLocalRing.closedPoint (CommRingCat.of K))]
    exact (Y s).affineOpenCover.covers y)
  exact ⟨⟨s, y⟩, h, hh.trans (E.apply_symm_apply η)⟩

/-- `MurreChartsFromEtaleLocusStatement` holds. -/
theorem murreChartsFromEtaleLocus : MurreChartsFromEtaleLocusStatement.{u, v} :=
  noetherianCharts_of_etaleLocusOpen

end Charts

end Langlands.AlgebraicGeometry.UnramifiedFunctor

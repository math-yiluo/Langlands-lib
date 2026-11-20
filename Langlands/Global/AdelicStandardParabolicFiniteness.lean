import Langlands.Global.AdelicSpectralDecompositionStatement
import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.GroupScheme.Rational.RationalLeviConjugacyProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicReduction
import Langlands.GroupScheme.Rational.LeviAmbientTransport
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyReduction
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Rational.RootSupportFiniteness

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Only finitely many dynamic parabolics contain a fixed minimal rational parabolic `P₀`.
Conjugating `P₀` to `P(ν)` for a maximal split torus with a generic cocharacter `ν`, every such
dynamic parabolic is the conjugate of a standard parabolic `P_J`, `J ⊆ Δ(ν)`. -/
theorem exists_finite_dynamicParabolics_of_minimal_le [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    {P₀ : GroupScheme (Spec (CommRingCat.of k))} {p₀ : P₀ ⟶ G}
    (hp₀ : IsMinimalParabolicSubgroup p₀) :
    ∃ R : Set (SubgroupFunctor G), R.Finite ∧
      ∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        SubgroupFunctor.range p₀ ≤ Dynamic.parabolic zeta → Dynamic.parabolic zeta ∈ R := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨P₁, p₁, hp₁, h₁⟩ :=
    isMinimalParabolicFunctor_iff_exists.mp (genericMinimalParabolic k G hG T i hi ν hν)
  obtain ⟨g, e, he⟩ := minimalParabolicConjugacy k G hG P₁ P₀ p₁ p₀ hp₁ hp₀
  have hcomap : SubgroupFunctor.range p₁ =
      (SubgroupFunctor.range p₀).comap (G.innerIso g).hom :=
    SubgroupFunctor.range_eq_comap_of_iso_square (G.innerIso g) e he
  refine ⟨(fun J => (standardParabolic i ν J).comap (G.innerIso g).inv) ''
      {J | J ⊆ simpleRelativeRoots i ν}, ?_, ?_⟩
  · exact ((hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).finite_subsets).image _
  · intro zeta hle
    have hz : Dynamic.parabolic zeta =
        (Dynamic.parabolic (zeta ≫ (G.innerIso g).inv)).comap (G.innerIso g).inv :=
      Dynamic.parabolic_eq_comap_of_iso zeta (G.innerIso g).symm
    have h2 : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        Dynamic.parabolic (zeta ≫ (G.innerIso g).inv) := by
      have h3 := SubgroupFunctor.comap_mono (f := (G.innerIso g).hom) hle
      rw [hz, SubgroupFunctor.comap_iso_inv_hom, ← hcomap, h₁] at h3
      exact h3
    obtain ⟨J, hJ, hJeq⟩ :=
      (standardParabolicClassification k G hG T i hi ν hν).1 _ h2
    exact ⟨J, hJ, by rw [hz, hJeq]⟩

/-- Two rational parabolics with the same all-test image carry rational Levis that are
conjugate by a rational point of `G`: for the identification `P' ≅ P` over `G`, the two
Levis of `P` are conjugate by a rational point of the unipotent radical of `P`. -/
theorem exists_innerIso_levi_conjugation_of_range_eq (hG : IsConnectedReductive G)
    {P P' M M' : GroupScheme (Spec (CommRingCat.of k))} {p : P ⟶ G} {p' : P' ⟶ G}
    [Mono p.hom.hom] [Mono p'.hom.hom] (hp : IsParabolicSubgroup p)
    {l : M ⟶ P} {l' : M' ⟶ P'} (hl : IsRationalLeviSubgroup l)
    (hl' : IsRationalLeviSubgroup l')
    (h : SubgroupFunctor.range p = SubgroupFunctor.range p') :
    ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (c : M' ≅ M),
      c.hom ≫ l ≫ p = l' ≫ p' ≫ (G.innerIso w).inv := by
  let e : P' ≅ P := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := SubgroupFunctor.range p) (i := p') ⟨inferInstance, h.symm⟩ ⟨inferInstance, rfl⟩
  have he : e.hom ≫ p = p' :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _
  obtain ⟨U, iU, hU, -⟩ := hl.exists_unipotentRadical
  obtain ⟨q, ⟨e', he'⟩, -⟩ :=
    rationalLeviConjugacy k G hG P p hp M M' l (l' ≫ e.hom) hl (hl'.comp_iso e) U iU hU
  refine ⟨(q ≫ iU.hom.hom) ≫ p.hom.hom, e'.symm, ?_⟩
  have key := innerIso_hom_comp_groupHom p (q ≫ iU.hom.hom)
  rw [← Category.assoc l' p', Iso.eq_comp_inv]
  calc (e'.symm.hom ≫ l ≫ p) ≫ (G.innerIso ((q ≫ iU.hom.hom) ≫ p.hom.hom)).hom
      = e'.inv ≫ (l ≫ (P.innerIso (q ≫ iU.hom.hom)).hom) ≫ p := by
        rw [Category.assoc l, key]
        simp only [Category.assoc, Iso.symm_hom]
    _ = l' ≫ p' := by
        rw [he', Category.assoc, Category.assoc, he, Iso.inv_hom_id_assoc]

end Langlands.GroupScheme

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- An elementary counting principle: if every element of `S` is related to some element of
a finite set `R`, and every `b : β` is related to at most one `a : α` (the premise `h₂` ranges
over all of `α` and `β`, not only over `S` and `R`), then `S` is finite. -/
theorem finite_of_forall_exists_rel {α β : Type*} {S : Set α} {R : Set β} (hR : R.Finite)
    (rel : α → β → Prop) (h₁ : ∀ a ∈ S, ∃ b ∈ R, rel a b)
    (h₂ : ∀ a a' b, rel a b → rel a' b → a = a') : S.Finite := by
  refine (hR.biUnion fun b _ => (show ({a | rel a b} : Set α).Subsingleton from
    fun a ha a' ha' => h₂ a a' b ha ha').finite).subset ?_
  intro a ha
  obtain ⟨b, hb, hab⟩ := h₁ a ha
  exact Set.mem_biUnion hb hab

/-- Two presented rational parabolics over a number field with the same all-test image are
Weyl conjugate in the sense of `IsWeylConjugation`. -/
theorem exists_isWeylConjugation_of_range_eq {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {P P' M M' : GroupScheme (Spec (CommRingCat.of F))}
    {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
    {p : P ⟶ G} {p' : P' ⟶ G} [IsClosedImmersion p.hom.hom.left]
    [IsClosedImmersion p'.hom.hom.left] {l : M ⟶ P} {l' : M' ⟶ P'}
    {a : A.toGrp ⟶ M} {a' : A'.toGrp ⟶ M'}
    (r : ParabolicRootPresentation p l a) (r' : ParabolicRootPresentation p' l' a')
    (h : SubgroupFunctor.range p = SubgroupFunctor.range p') :
    ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
      IsWeylConjugation p l p' l' w c := by
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  have : Mono p'.hom.hom := Over.mono_of_mono_left _
  obtain ⟨w, c, hc⟩ := exists_innerIso_levi_conjugation_of_range_eq hG
    r.isCompatible.parabolic r.isCompatible.levi r'.isCompatible.levi h
  exact ⟨w, c.hom, ⟨inferInstance, hc⟩⟩

/-- (e1) Over a number field, only finitely many all-test images `SubgroupFunctor.range p`
occur among the presented rational parabolics `p : P → G` (those admitting a
`ParabolicRootPresentation p l a` for some `l`, `a`) that contain a fixed minimal parabolic
`P₀`. Derived: Getz–Hahn §10.5 uses that there are finitely many standard parabolics. -/
def PresentedStandardParabolicRangeFiniteStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (p₀ : P₀ ⟶ G),
      IsMinimalParabolicSubgroup p₀ →
      {H : SubgroupFunctor G | ∃ (P M : GroupScheme (Spec (CommRingCat.of F)))
          (A : CommGroupScheme (Spec (CommRingCat.of F)))
          (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (_ : ParabolicRootPresentation p l a),
          SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p ∧
            SubgroupFunctor.range p = H}.Finite

/-- (e2) Two presented rational parabolics over a number field, embedded by closed
immersions, with the same all-test image `SubgroupFunctor.range` are Weyl conjugate in the
sense of `IsWeylConjugation`: their presented Levis are conjugate by a rational point of `G`. -/
def PresentedStandardParabolicWeylConjugacyStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom],
    IsConnectedReductive G →
    ∀ (P P' M M' : GroupScheme (Spec (CommRingCat.of F)))
      (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (l' : M' ⟶ P')
      (a' : A'.toGrp ⟶ M'),
      ParabolicRootPresentation p l a → ParabolicRootPresentation p' l' a' →
      SubgroupFunctor.range p = SubgroupFunctor.range p' →
      ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
        IsWeylConjugation p l p' l' w c

/-- (e3) The finiteness in item 1 of `SpectralDecompositionStatement`, given its item 3: with the
binders of `SpectralDecompositionStatement`, if `L²_P([G]) = L²_{P'}([G])` whenever the presented
standard data are Weyl conjugate, then only finitely many subspaces `L²_P([G])` occur. -/
def StandardParabolicSpectrumFinitenessStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P₀ : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P₀.X.left] (p₀ : P₀ ⟶ G)
      [IsClosedImmersion p₀.hom.hom.left],
      IsMinimalParabolicSubgroup p₀ → IsIwasawaCompact p₀ K →
    let S : Set (Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G))) :=
      {V | ∃ (P M U : GroupScheme (Spec (CommRingCat.of F)))
        (A : CommGroupScheme (Spec (CommRingCat.of F)))
        (_ : IsAffine P.X.left) (_ : IsAffine M.X.left) (_ : LocallyOfFiniteType M.X.hom)
        (_ : IsAffine U.X.left)
        (p : P ⟶ G) (_ : IsClosedImmersion p.hom.hom.left) (iU : U ⟶ P) (l : M ⟶ P)
        (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
        (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
        (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
        (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
        haveI : LocallyOfFiniteType P.X.hom :=
          IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
        SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p ∧
        LeviSubgroup.IsGeometricUnipotentRadical iU ∧ ∃ hK : IsIwasawaCompact p K,
          V = parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT}
    (∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
      (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
      (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
      [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
      [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
      (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
      haveI : LocallyOfFiniteType P.X.hom :=
        IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
      SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p →
      LeviSubgroup.IsGeometricUnipotentRadical iU →
      ∀ hK : IsIwasawaCompact p K,
        ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
          (A' : CommGroupScheme (Spec (CommRingCat.of F)))
          [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
          [IsAffine U'.X.left]
          (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
          (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
          [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
          [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
          (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp),
          haveI : LocallyOfFiniteType P'.X.hom :=
            IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
          SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p' →
          LeviSubgroup.IsGeometricUnipotentRadical iU' →
          ∀ hK' : IsIwasawaCompact p' K,
            (∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
                IsWeylConjugation p l p' l' w c) →
              parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT =
                parabolicSpectrum hK' rho hsmooth hcalc iU' l' r' hA' hT') →
    S.Finite

theorem presentedStandardParabolicRangeFinite :
    PresentedStandardParabolicRangeFiniteStatement := by
  intro F _ _ G _ _ hG P₀ p₀ hp₀
  set R := {H : SubgroupFunctor G | ∃ (P M : GroupScheme (Spec (CommRingCat.of F)))
          (A : CommGroupScheme (Spec (CommRingCat.of F)))
          (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (_ : ParabolicRootPresentation p l a),
          SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p ∧
            SubgroupFunctor.range p = H} with hRdef
  rcases R.eq_empty_or_nonempty with hR | ⟨H₀, P, M, A, p, l, a, r₀, -, -⟩
  · rw [hR]; exact Set.finite_empty
  obtain ⟨R', hR', hmem⟩ := exists_finite_dynamicParabolics_of_minimal_le hG
    r₀.isCompatible.maximalSplit r₀.isCompatible.generic hp₀
  refine hR'.subset ?_
  rintro H ⟨P, M, A, p, l, a, r, hle, rfl⟩
  obtain ⟨ζ, -, hζ, -⟩ := r.isCompatible.realization
  rw [hζ] at hle ⊢
  exact hmem _ hle

theorem presentedStandardParabolicWeylConjugacy :
    PresentedStandardParabolicWeylConjugacyStatement := by
  intro F _ _ G _ hG P P' M M' A A' p _ l a p' _ l' a' r r' h
  exact exists_isWeylConjugation_of_range_eq hG r r' h

theorem standardParabolicSpectrumFiniteness :
    StandardParabolicSpectrumFinitenessStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc _ _ P₀ _ p₀ _ hp₀ _ S hassoc
  refine finite_of_forall_exists_rel (presentedStandardParabolicRangeFinite F G hG P₀ p₀ hp₀)
    (fun V H => ∃ (P M U : GroupScheme (Spec (CommRingCat.of F)))
        (A : CommGroupScheme (Spec (CommRingCat.of F)))
        (_ : IsAffine P.X.left) (_ : IsAffine M.X.left) (_ : LocallyOfFiniteType M.X.hom)
        (_ : IsAffine U.X.left)
        (p : P ⟶ G) (_ : IsClosedImmersion p.hom.hom.left) (iU : U ⟶ P) (l : M ⟶ P)
        (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
        (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
        (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
        (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
        haveI : LocallyOfFiniteType P.X.hom :=
          IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
        SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p ∧
        LeviSubgroup.IsGeometricUnipotentRadical iU ∧ SubgroupFunctor.range p = H ∧
        ∃ hK : IsIwasawaCompact p K,
          V = parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT) ?_ ?_
  · rintro V ⟨P, M, U, A, i₁, i₂, i₃, i₄, p, i₅, iU, l, a, r, i₆, i₇, i₈, hA, hT, hle, hiU,
      hK, hV⟩
    exact ⟨_, ⟨P, M, A, p, l, a, r, hle, rfl⟩,
      P, M, U, A, i₁, i₂, i₃, i₄, p, i₅, iU, l, a, r, i₆, i₇, i₈, hA, hT, hle, hiU, rfl,
      hK, hV⟩
  · rintro V V' H ⟨P, M, U, A, _, _, _, _, p, _, iU, l, a, r, _, _, _, hA, hT, hle, hiU, rfl,
      hK, rfl⟩ ⟨P', M', U', A', _, _, _, _, p', _, iU', l', a', r', _, _, _, hA', hT', hle',
      hiU', hrange, hK', rfl⟩
    exact hassoc P M U A p iU l a r hA hT hle hiU hK P' M' U' A' p' iU' l' a' r' hA' hT' hle'
      hiU' hK' (exists_isWeylConjugation_of_range_eq hG r r' hrange.symm)

end Langlands.Global

import Langlands.Geometry.Analytic.SpaceChartTrivialOpen
import Langlands.Geometry.Analytic.EtaleMonoOpenImmersion
import Langlands.Geometry.Analytic.LocalizedOpenRelationGluing
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinePullback
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.LocalizedEtaleComposition

/-! # Gluing data from relation-trivial open subsets of elementary charts

For a family of étale affine charts of a separated algebraic space, each elementary at a
prime, and open subsets of their analytifications on which the analytified relation is
trivial, the open subsets and the open parts of the analytified chart intersections form
gluing data along open subspaces. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ChartQuotient

open SaturatedAtlasPresentation AffineAnalytification ExistenceReduction
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An étale affine chart of finite type of an algebraic space, elementary at a prime `q`: the
only prime of any model of its self-intersection over `q` along both projections is the
diagonal prime. -/
structure ElemChart (X : AlgebraicSpace (Spec (CommRingCat.of K))) where
  /-- The coordinate algebra. -/
  B : CommAlgCat.{u} K
  /-- A finite polynomial presentation. -/
  Q : FinitePolynomialPresentation K B
  /-- The point. -/
  y : RingPoints K X B
  etale : AlgebraicSpace.IsEtale (pointHom K y)
  /-- The prime at which the chart is elementary. -/
  q : PrimeSpectrum B
  elem : ∀ (C : Type u) [CommRing C] [Algebra K C] (f g : (B : Type u) →ₐ[K] C),
    IsPullback (ty f) (ty g) (pointHom K y) (pointHom K y) →
    ∀ μ : C →ₐ[K] B, μ.comp f = AlgHom.id K B → μ.comp g = AlgHom.id K B →
      ∀ P : PrimeSpectrum C, PrimeSpectrum.comap (f : B →+* C) P = q →
        PrimeSpectrum.comap (g : B →+* C) P = q → P = PrimeSpectrum.comap (μ : C →+* B) q

variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- Relation-trivial neighbourhoods for the chosen model of the self-intersection of an
elementary chart. -/
theorem ElemChart.exists_trivial_open (hX : IsSeparated X) (E : ElemChart X)
    (v : Space K E.Q) (hv : center K E.Q v = E.q) :
    ∃ O : Set (Space K E.Q), IsOpen O ∧ v ∈ O ∧
      ∀ (T : LocalizedCategory.{u, u, u} (K := K)) (α β : T ⟶ localized K E.Q),
        (∀ t, localizedSpaceFunctor.map α t ∈ O) → (∀ t, localizedSpaceFunctor.map β t ∈ O) →
        (pointModel hX E.Q E.Q E.y E.y).ARel E.Q E.Q α β → α = β := by
  obtain ⟨C, _, _, R, f, g, hsurj, hpb⟩ :=
    hasClosedAffinePointPullbacks_of_isSeparated hX E.B E.Q E.B E.Q E.y E.y
  let M : TestModel (pointHom K E.y) (pointHom K E.y) :=
    { C := CommAlgCat.of K C, R := R, f := f, g := g, isPullback := hpb }
  obtain ⟨O, hO, hvO, htriv⟩ :=
    Langlands.Analytic.SpaceAnalytification.ChartQuotient.exists_trivial_open E.Q E.etale M hsurj E.q
    (E.elem C f g hpb) v hv
  exact ⟨O, hO, hvO, fun T α β hα hβ h => htriv T α β hα hβ (h.of_model M)⟩

section Gluing

variable (hX : IsSeparated X) {J : Type u} (E : J → ElemChart X) {M : Type u} (c : M → J)
  (O : ∀ m, Set (Space K (E (c m)).Q)) (hO : ∀ m, IsOpen (O m))

/-- The analytified chart of a piece. -/
abbrev Vm (m : M) : LocalizedCategory.{u, u, u} (K := K) := localized K (E (c m)).Q

/-- The chosen model of the intersection of the charts of two pieces. -/
abbrev Wm (m n : M) := pointModel hX (E (c m)).Q (E (c n)).Q (E (c m)).y (E (c n)).y

/-- The first projection of an analytified chart intersection. -/
abbrev p₁ (m n : M) : localized K (Wm hX E c m n).R ⟶ Vm E c m :=
  localizedHom K (E (c m)).Q (Wm hX E c m n).R (Wm hX E c m n).f

/-- The second projection of an analytified chart intersection. -/
abbrev p₂ (m n : M) : localized K (Wm hX E c m n).R ⟶ Vm E c n :=
  localizedHom K (E (c n)).Q (Wm hX E c m n).R (Wm hX E c m n).g

/-- The open domain of a piece. -/
abbrev DZ (m : M) : (presentationOf (Vm E c m)).AnalyticDomain :=
  (presentationOf (Vm E c m)).openDomain (O m) (hO m)

/-- The open subset of a chart intersection lying over the open sets of both pieces. -/
def SSet (m n : M) : Set (Space K (Wm hX E c m n).R) :=
  localizedSpaceFunctor.map (p₁ hX E c m n) ⁻¹' O m ∩
    localizedSpaceFunctor.map (p₂ hX E c m n) ⁻¹' O n

include hO in
theorem isOpen_SSet (m n : M) : IsOpen (SSet hX E c O m n) :=
  ((hO m).preimage (localizedSpaceFunctor.map (p₁ hX E c m n)).hom.continuous).inter
    ((hO n).preimage (localizedSpaceFunctor.map (p₂ hX E c m n)).hom.continuous)

/-- The open domain of a chart intersection. -/
abbrev DS (m n : M) : (presentationOf (localized K (Wm hX E c m n).R)).AnalyticDomain :=
  (presentationOf (localized K (Wm hX E c m n).R)).openDomain (SSet hX E c O m n)
    (isOpen_SSet hX E c O hO m n)

/-- The first projection of the relation. -/
def aM (m n : M) : domainObj _ (DS hX E c O hO m n) ⟶ domainObj _ (DZ E c O hO m) :=
  domainRestrict (DS hX E c O hO m n) (DZ E c O hO m) (p₁ hX E c m n) fun _ hx => hx.1

/-- The second projection of the relation. -/
def bM (m n : M) : domainObj _ (DS hX E c O hO m n) ⟶ domainObj _ (DZ E c O hO n) :=
  domainRestrict (DS hX E c O hO m n) (DZ E c O hO n) (p₂ hX E c m n) fun _ hx => hx.2

theorem aM_ι (m n : M) : aM hX E c O hO m n ≫ domainι _ (DZ E c O hO m) =
    domainι _ (DS hX E c O hO m n) ≫ p₁ hX E c m n :=
  domainRestrict_comp _ _ _ _

theorem bM_ι (m n : M) : bM hX E c O hO m n ≫ domainι _ (DZ E c O hO n) =
    domainι _ (DS hX E c O hO m n) ≫ p₂ hX E c m n :=
  domainRestrict_comp _ _ _ _

theorem etale_aM (m n : M) : etale (aM hX E c O hO m n) := by
  apply etale_of_comp_domainι
  rw [aM_ι]
  exact etale_comp (etaleOpenDomainStatement _ _ _)
    (etale_localizedHom _ _ _ ((Wm hX E c m n).etale_f (E (c n)).etale))

theorem etale_bM (m n : M) : etale (bM hX E c O hO m n) := by
  apply etale_of_comp_domainι
  rw [bM_ι]
  exact etale_comp (etaleOpenDomainStatement _ _ _)
    (etale_localizedHom _ _ _ ((Wm hX E c m n).etale_g (E (c m)).etale))

variable (htriv : ∀ (m : M) (T : LocalizedCategory.{u, u, u} (K := K))
    (α β : T ⟶ localized K (E (c m)).Q),
    (∀ t, localizedSpaceFunctor.map α t ∈ O m) → (∀ t, localizedSpaceFunctor.map β t ∈ O m) →
    (Wm hX E c m m).ARel _ _ α β → α = β)

include htriv in
theorem mono_aM (m n : M) : Mono (aM hX E c O hO m n) := by
  constructor
  intro T s s' hss
  let t := s ≫ domainι _ (DS hX E c O hO m n)
  let t' := s' ≫ domainι _ (DS hX E c O hO m n)
  have h₁ : t ≫ p₁ hX E c m n = t' ≫ p₁ hX E c m n := by
    simp only [t, t', Category.assoc, ← aM_ι]
    rw [← Category.assoc, hss, Category.assoc]
  have hmem : ∀ (u : T ⟶ domainObj _ (DS hX E c O hO m n)) x,
      localizedSpaceFunctor.map (u ≫ domainι _ (DS hX E c O hO m n) ≫ p₂ hX E c m n) x ∈ O n := by
    intro u x
    rw [Functor.map_comp, Functor.map_comp, TopCat.comp_app, TopCat.comp_app, domainι_apply]
    exact (localizedSpaceFunctor.map u x).property.2
  have hA : (Wm hX E c n n).ARel _ _ (t ≫ p₂ hX E c m n) (t' ≫ p₂ hX E c m n) :=
    (TestModel.ARel.symm (⟨t, rfl, rfl⟩ : (Wm hX E c m n).ARel _ _ (t ≫ p₁ hX E c m n)
      (t ≫ p₂ hX E c m n))).trans _ (⟨t', h₁.symm, rfl⟩ : (Wm hX E c m n).ARel _ _
        (t ≫ p₁ hX E c m n) (t' ≫ p₂ hX E c m n))
  have h₂ : t ≫ p₂ hX E c m n = t' ≫ p₂ hX E c m n :=
    htriv n T _ _ (by simpa only [t, Category.assoc] using hmem s)
      (by simpa only [t', Category.assoc] using hmem s') hA
  have htt : t = t' := (Wm hX E c m n).jointly_mono t t' h₁ h₂
  exact (cancel_mono (domainι _ (DS hX E c O hO m n))).1 htt

include htriv in
theorem mono_bM (m n : M) : Mono (bM hX E c O hO m n) := by
  constructor
  intro T s s' hss
  let t := s ≫ domainι _ (DS hX E c O hO m n)
  let t' := s' ≫ domainι _ (DS hX E c O hO m n)
  have h₂ : t ≫ p₂ hX E c m n = t' ≫ p₂ hX E c m n := by
    simp only [t, t', Category.assoc, ← bM_ι]
    rw [← Category.assoc, hss, Category.assoc]
  have hmem : ∀ (u : T ⟶ domainObj _ (DS hX E c O hO m n)) x,
      localizedSpaceFunctor.map (u ≫ domainι _ (DS hX E c O hO m n) ≫ p₁ hX E c m n) x ∈ O m := by
    intro u x
    rw [Functor.map_comp, Functor.map_comp, TopCat.comp_app, TopCat.comp_app, domainι_apply]
    exact (localizedSpaceFunctor.map u x).property.1
  have hA : (Wm hX E c m m).ARel _ _ (t ≫ p₁ hX E c m n) (t' ≫ p₁ hX E c m n) :=
    TestModel.ARel.trans (Wm hX E c m m) (⟨t, rfl, rfl⟩ : (Wm hX E c m n).ARel _ _
      (t ≫ p₁ hX E c m n) (t ≫ p₂ hX E c m n)) (TestModel.ARel.symm (⟨t', rfl, h₂.symm⟩ :
        (Wm hX E c m n).ARel _ _ (t' ≫ p₁ hX E c m n) (t ≫ p₂ hX E c m n)))
  have h₁ : t ≫ p₁ hX E c m n = t' ≫ p₁ hX E c m n :=
    htriv m T _ _ (by simpa only [t, Category.assoc] using hmem s)
      (by simpa only [t', Category.assoc] using hmem s') hA
  have htt : t = t' := (Wm hX E c m n).jointly_mono t t' h₁ h₂
  exact (cancel_mono (domainι _ (DS hX E c O hO m n))).1 htt

/-- Maps into two pieces related through the chart intersection lift to the relation. -/
theorem exists_of_aRel {T : LocalizedCategory.{u, u, u} (K := K)} {m n : M}
    (α : T ⟶ domainObj _ (DZ E c O hO m)) (β : T ⟶ domainObj _ (DZ E c O hO n))
    (h : (Wm hX E c m n).ARel _ _ (α ≫ domainι _ (DZ E c O hO m))
      (β ≫ domainι _ (DZ E c O hO n))) :
    ∃ s : T ⟶ domainObj _ (DS hX E c O hO m n),
      s ≫ aM hX E c O hO m n = α ∧ s ≫ bM hX E c O hO m n = β := by
  obtain ⟨t, ht₁, ht₂⟩ := h
  have hmem : ∀ x, localizedSpaceFunctor.map t x ∈ (DS hX E c O hO m n).carrier := by
    intro x
    refine ⟨?_, ?_⟩
    · change localizedSpaceFunctor.map (p₁ hX E c m n) (localizedSpaceFunctor.map t x) ∈ O m
      rw [← TopCat.comp_app, ← Functor.map_comp, ht₁, Functor.map_comp, TopCat.comp_app,
        domainι_apply]
      exact Subtype.property _
    · change localizedSpaceFunctor.map (p₂ hX E c m n) (localizedSpaceFunctor.map t x) ∈ O n
      rw [← TopCat.comp_app, ← Functor.map_comp, ht₂, Functor.map_comp, TopCat.comp_app,
        domainι_apply]
      exact Subtype.property _
  refine ⟨domainLift _ t hmem, ?_, ?_⟩
  · apply (cancel_mono (domainι _ (DZ E c O hO m))).1
    rw [Category.assoc, aM_ι, domainLift_comp_assoc, ht₁]
  · apply (cancel_mono (domainι _ (DZ E c O hO n))).1
    rw [Category.assoc, bM_ι, domainLift_comp_assoc, ht₂]

/-- Maps into two pieces lifting to the relation are related through the chart
intersection. -/
theorem aRel_of_lift {T : LocalizedCategory.{u, u, u} (K := K)} {m n : M}
    {α : T ⟶ domainObj _ (DZ E c O hO m)} {β : T ⟶ domainObj _ (DZ E c O hO n)}
    (s : T ⟶ domainObj _ (DS hX E c O hO m n)) (hs₁ : s ≫ aM hX E c O hO m n = α)
    (hs₂ : s ≫ bM hX E c O hO m n = β) :
    (Wm hX E c m n).ARel _ _ (α ≫ domainι _ (DZ E c O hO m))
      (β ≫ domainι _ (DZ E c O hO n)) :=
  ⟨s ≫ domainι _ _, by rw [Category.assoc, ← aM_ι, ← Category.assoc, hs₁],
    by rw [Category.assoc, ← bM_ι, ← Category.assoc, hs₂]⟩

variable (hSheaf : EtaleHomSheafStatement.{u, u})

/-- The gluing data along open subspaces given by relation-trivial open subsets of elementary
charts and the open parts of the analytified chart intersections. -/
def chartRelation : LocalizedOpenRelation K where
  M := M
  Z m := domainObj (Vm E c m) (DZ E c O hO m)
  S m n := domainObj _ (DS hX E c O hO m n)
  a := aM hX E c O hO
  b := bM hX E c O hO
  a_open m n := by
    have := mono_aM hX E c O hO htriv m n
    exact openImmersion_of_etale_of_mono hSheaf _ (etale_aM hX E c O hO m n)
  b_open m n := by
    have := mono_bM hX E c O hO htriv m n
    exact openImmersion_of_etale_of_mono hSheaf _ (etale_bM hX E c O hO m n)
  refl m := exists_of_aRel hX E c O hO (𝟙 _) (𝟙 _) (by
    rw [Category.id_comp]
    exact TestModel.aRel_refl _ _)
  symm m n := exists_of_aRel hX E c O hO (bM hX E c O hO m n) (aM hX E c O hO m n)
    ((TestModel.ARel.symm (aRel_of_lift hX E c O hO (𝟙 _) (Category.id_comp _)
      (Category.id_comp _))).of_model _)
  trans {m n l T} s t hst := exists_of_aRel hX E c O hO _ _
    ((aRel_of_lift hX E c O hO s rfl hst).trans _ (aRel_of_lift hX E c O hO t rfl rfl))

end Gluing

end Langlands.Analytic.SpaceAnalytification.ChartQuotient

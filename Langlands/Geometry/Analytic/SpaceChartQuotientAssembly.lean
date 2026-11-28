import Langlands.Geometry.Analytic.SpaceChartQuotientGluing
import Langlands.Geometry.Analytic.AffineAnalytificationCenterLift
import Langlands.Geometry.Analytic.LocalizedEtaleSourceOpenLocality
import Langlands.Geometry.Analytic.SpaceChartRelationLocal
import Langlands.Geometry.Analytic.AffineAnalytificationOpenImmersionReflection

/-! # The chart maps into the glued analytic space

For a family of étale affine charts `xᵢ : Spec Aᵢ → X` of a separated algebraic space and a
family of elementary charts with relation-trivial open subsets, this module constructs the
maps `πᵢ : Spec(Aᵢ)ᵃⁿ → Y` into the glued space by étale descent along the open parts of the
analytified intersections with the elementary charts. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ChartQuotient

open SaturatedAtlasPresentation AffineAnalytification ExistenceReduction
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : IsSeparated X)
  (hSheaf : EtaleHomSheafStatement.{u, u})
  {ι : Type u} {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
  (P : ∀ i, FinitePolynomialPresentation K (A i)) (x : ∀ i, RingPoints K X (A i))
  (hx : ∀ i, AlgebraicSpace.IsEtale (pointHom K (x i)))

/-- The index type of the elementary charts: a chart `xᵢ` and a prime of its algebra. -/
abbrev CJ (A : ι → Type u) [∀ i, CommRing (A i)] : Type u := Σ i, PrimeSpectrum (A i)

variable (E : CJ A → ElemChart X)

/-- The pieces: an elementary chart and an analytic point over its elementary prime. -/
abbrev CM : Type u := Σ j : CJ A, {v : Space K (E j).Q // center K (E j).Q v = (E j).q}

/-- The chosen model of the intersection of a chart `xᵢ` with the elementary chart at `(i, p)`. -/
@[irreducible] def Nj (j : CJ A) : TestModel (pointHom K (x j.1)) (pointHom K (E j).y) :=
  pointModel hX (P j.1) (E j).Q (x j.1) (E j).y

variable (O : ∀ m : CM E, Set (Space K (E m.1).Q)) (hO : ∀ m, IsOpen (O m))
  (htriv : ∀ (m : CM E) (T : LocalizedCategory.{u, u, u} (K := K))
    (α β : T ⟶ localized K (E m.1).Q),
    (∀ t, localizedSpaceFunctor.map α t ∈ O m) → (∀ t, localizedSpaceFunctor.map β t ∈ O m) →
    (Wm hX E (fun m : CM E => m.1) m m).ARel _ _ α β → α = β)

/-- The cover indices of the chart `xᵢ`: a prime of `Aᵢ` and a point over the elementary prime
of its elementary chart. -/
abbrev CI (i : ι) : Type u :=
  Σ p : PrimeSpectrum (A i), {v : Space K (E ⟨i, p⟩).Q // center K _ v = (E ⟨i, p⟩).q}

/-- The piece of a cover index. -/
abbrev toM (i : ι) (k : CI E i) : CM E := ⟨⟨i, k.1⟩, k.2⟩

/-- The open subset of the analytified intersection lying over the open set of the piece. -/
def DkSet (i : ι) (k : CI E i) : Set (Space K (Nj hX P x E ⟨i, k.1⟩).R) :=
  localizedSpaceFunctor.map (localizedHom K (E ⟨i, k.1⟩).Q (Nj hX P x E ⟨i, k.1⟩).R
    (Nj hX P x E ⟨i, k.1⟩).g) ⁻¹' O (toM E i k)

include hO in
/-- The cover-domain subsets are open. -/
theorem isOpen_DkSet (i : ι) (k : CI E i) : IsOpen (DkSet hX P x E O i k) :=
  (hO _).preimage (localizedSpaceFunctor.map _).hom.continuous

/-- The open domain of the analytified intersection lying over the open set of the piece. -/
abbrev Dk (i : ι) (k : CI E i) :
    (presentationOf (localized K (Nj hX P x E ⟨i, k.1⟩).R)).AnalyticDomain :=
  (presentationOf _).openDomain (DkSet hX P x E O i k) (isOpen_DkSet hX P x E O hO i k)

/-- The cover map to the analytified chart `xᵢ`. -/
abbrev ek (i : ι) (k : CI E i) : domainObj _ (Dk hX P x E O hO i k) ⟶ localized K (P i) :=
  domainι _ _ ≫ localizedHom K (P i) (Nj hX P x E ⟨i, k.1⟩).R (Nj hX P x E ⟨i, k.1⟩).f

/-- The cover map to the piece. -/
def hk (i : ι) (k : CI E i) :
    domainObj _ (Dk hX P x E O hO i k) ⟶ domainObj _ (DZ E (fun m : CM E => m.1) O hO (toM E i k)) :=
  domainRestrict _ _ (localizedHom K (E ⟨i, k.1⟩).Q (Nj hX P x E ⟨i, k.1⟩).R
    (Nj hX P x E ⟨i, k.1⟩).g) fun _ hw => hw

/-- The cover map to the piece followed by the inclusion of the piece. -/
theorem hk_ι (i : ι) (k : CI E i) :
    hk hX P x E O hO i k ≫ domainι _ (DZ E (fun m : CM E => m.1) O hO (toM E i k)) =
      domainι _ _ ≫ localizedHom K (E ⟨i, k.1⟩).Q (Nj hX P x E ⟨i, k.1⟩).R
        (Nj hX P x E ⟨i, k.1⟩).g :=
  domainRestrict_comp _ _ _ _

/-- The cover maps to the analytified chart are étale. -/
theorem etale_ek (i : ι) (k : CI E i) : etale (ek hX P x E O hO i k) :=
  etale_comp (etaleOpenDomainStatement _ _ _)
    (etale_localizedHom _ _ _ ((Nj hX P x E ⟨i, k.1⟩).etale_f (E ⟨i, k.1⟩).etale))

/-- Maps into two cover domains whose composites to the analytified charts are related give
related maps into the pieces. -/
theorem rel_hk {T : LocalizedCategory.{u, u, u} (K := K)} {i i' : ι} {k : CI E i} {k' : CI E i'}
    (a : T ⟶ domainObj _ (Dk hX P x E O hO i k)) (b : T ⟶ domainObj _ (Dk hX P x E O hO i' k'))
    (M₀ : TestModel (pointHom K (x i)) (pointHom K (x i')))
    (h : M₀.ARel (P i) (P i') (a ≫ ek hX P x E O hO i k) (b ≫ ek hX P x E O hO i' k')) :
    (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).Rel
      (a ≫ hk hX P x E O hO i k) (b ≫ hk hX P x E O hO i' k') := by
  refine exists_of_aRel hX E (fun m : CM E => m.1) O hO _ _ ?_
  have A₁ : (Nj hX P x E ⟨i, k.1⟩).flip.ARel _ _
      (a ≫ domainι _ _ ≫ localizedHom K (E ⟨i, k.1⟩).Q (Nj hX P x E ⟨i, k.1⟩).R
        (Nj hX P x E ⟨i, k.1⟩).g)
      (a ≫ ek hX P x E O hO i k) :=
    TestModel.ARel.symm ⟨a ≫ domainι _ _, Category.assoc _ _ _, Category.assoc _ _ _⟩
  have A₃ : (Nj hX P x E ⟨i', k'.1⟩).ARel _ _ (b ≫ ek hX P x E O hO i' k')
      (b ≫ domainι _ _ ≫ localizedHom K (E ⟨i', k'.1⟩).Q (Nj hX P x E ⟨i', k'.1⟩).R
        (Nj hX P x E ⟨i', k'.1⟩).g) :=
    ⟨b ≫ domainι _ _, Category.assoc _ _ _, Category.assoc _ _ _⟩
  have A := TestModel.ARel.trans (Wm hX E (fun m : CM E => m.1) (toM E i k) (toM E i' k'))
    (TestModel.ARel.trans (pointModel hX (E ⟨i, k.1⟩).Q (P i') (E ⟨i, k.1⟩).y (x i')) A₁ h) A₃
  have e₁ : (a ≫ hk hX P x E O hO i k) ≫ domainι _ (DZ E (fun m : CM E => m.1) O hO (toM E i k)) =
      a ≫ domainι _ _ ≫ localizedHom K (E ⟨i, k.1⟩).Q (Nj hX P x E ⟨i, k.1⟩).R
        (Nj hX P x E ⟨i, k.1⟩).g := by
    rw [Category.assoc, hk_ι]
  have e₂ : (b ≫ hk hX P x E O hO i' k') ≫
      domainι _ (DZ E (fun m : CM E => m.1) O hO (toM E i' k')) =
      b ≫ domainι _ _ ≫ localizedHom K (E ⟨i', k'.1⟩).Q (Nj hX P x E ⟨i', k'.1⟩).R
        (Nj hX P x E ⟨i', k'.1⟩).g := by
    rw [Category.assoc, hk_ι]
  obtain ⟨t, ht₁, ht₂⟩ := A
  exact ⟨t, ht₁.trans e₁.symm, ht₂.trans e₂.symm⟩

variable (hvO : ∀ m : CM E, m.2.1 ∈ O m)
  (ha : ∀ j : CJ A, ∃ 𝔓 : PrimeSpectrum (Nj hX P x E j).C,
    PrimeSpectrum.comap ((Nj hX P x E j).f : A j.1 →+* (Nj hX P x E j).C) 𝔓 = j.2 ∧
      PrimeSpectrum.comap ((Nj hX P x E j).g : (E j).B →+* (Nj hX P x E j).C) 𝔓 = (E j).q)

include hvO in
/-- A point of an analytified intersection over the chosen point of a piece maps into the range
of the corresponding cover map. -/
theorem mem_range_ek (i : ι) (k : CI E i) (w : Space K (Nj hX P x E ⟨i, k.1⟩).R)
    (hw : baseMap K (E ⟨i, k.1⟩).Q (Nj hX P x E ⟨i, k.1⟩).R (Nj hX P x E ⟨i, k.1⟩).g w = k.2.1) :
    baseMap K (P i) (Nj hX P x E ⟨i, k.1⟩).R (Nj hX P x E ⟨i, k.1⟩).f w ∈
      Set.range (localizedSpaceFunctor.map (ek hX P x E O hO i k)) := by
  have hwD : w ∈ DkSet hX P x E O i k := by
    have h₁ : localizedSpaceFunctor.map (localizedHom K (E ⟨i, k.1⟩).Q (Nj hX P x E ⟨i, k.1⟩).R
        (Nj hX P x E ⟨i, k.1⟩).g) w ∈ O (toM E i k) := by
      rw [localizedSpaceFunctor_map_localizedHom]
      exact (congrArg (· ∈ O (toM E i k)) hw).mpr (hvO (toM E i k))
    exact h₁
  obtain ⟨z, hz⟩ : ∃ z : localizedSpaceFunctor.obj (domainObj _ (Dk hX P x E O hO i k)),
      Subtype.val (p := (· ∈ (Dk hX P x E O hO i k).carrier)) z = w :=
    ⟨Subtype.mk (p := (· ∈ (Dk hX P x E O hO i k).carrier)) w hwD, rfl⟩
  refine ⟨z, ?_⟩
  dsimp only [ek]
  rw [Functor.map_comp, TopCat.comp_app, domainι_apply, hz, localizedSpaceFunctor_map_localizedHom]
  rfl

include hvO ha in
/-- The cover domains of the chart `xᵢ` cover its analytification. -/
theorem ek_cover (i : ι) (u : localizedSpaceFunctor.obj (localized K (P i))) :
    ∃ k : CI E i, u ∈ Set.range (localizedSpaceFunctor.map (ek hX P x E O hO i k)) := by
  obtain ⟨p, hp⟩ : ∃ p, center K (P i) u = p := ⟨_, rfl⟩
  obtain ⟨𝔓, h𝔓f, h𝔓g⟩ := ha ⟨i, p⟩
  obtain ⟨w, hwu, hw𝔓⟩ := exists_baseMap_eq_center K (P i) (Nj hX P x E ⟨i, p⟩).R
    (Nj hX P x E ⟨i, p⟩).f ((Nj hX P x E ⟨i, p⟩).etale_f (E ⟨i, p⟩).etale) u 𝔓
    (h𝔓f.trans hp.symm)
  have hv : center K (E ⟨i, p⟩).Q (baseMap K (E ⟨i, p⟩).Q
      (Nj hX P x E ⟨i, p⟩).R (Nj hX P x E ⟨i, p⟩).g w) = (E ⟨i, p⟩).q := by
    rw [center_baseMap, hw𝔓, h𝔓g]
  refine ⟨⟨p, _, hv⟩, ?_⟩
  rw [← hwu]
  exact mem_range_ek hX P x E O hO hvO i ⟨p, _, hv⟩ w rfl

/-- A morphism is étale when its composites with a jointly surjective family of open
immersions are étale. -/
theorem etale_of_openImmersion_cover {X' Y' : LocalizedCategory.{u, u, u} (K := K)} (f : X' ⟶ Y')
    {I : Type u} (U : I → LocalizedCategory.{u, u, u} (K := K)) (e : ∀ l, U l ⟶ X')
    (he : ∀ l, openImmersion (e l))
    (hcov : ∀ t, ∃ l, t ∈ Set.range (localizedSpaceFunctor.map (e l)))
    (hf : ∀ l, etale (e l ≫ f)) : etale f := by
  choose V hV φ hφ using he
  refine etale_of_open_source_cover f V hV (fun t => ?_) (fun l => ?_)
  · obtain ⟨l, y, rfl⟩ := hcov t
    refine ⟨l, ?_⟩
    rw [← hφ l, Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact Subtype.property _
  · have e₁ : domainι X' ((presentationOf X').openDomain (V l) (hV l)) ≫ f =
        (φ l).inv ≫ e l ≫ f := by
      rw [← hφ l, Category.assoc, Iso.inv_hom_id_assoc]
    rw [e₁]
    exact etale_comp (etale_of_isIso _) (hf l)

include hx in
/-- The cover maps to the pieces are étale. -/
theorem etale_hk (i : ι) (k : CI E i) : etale (hk hX P x E O hO i k) := by
  apply etale_of_comp_domainι
  rw [hk_ι]
  exact etale_comp (etaleOpenDomainStatement _ _ _)
    (etale_localizedHom _ _ _ ((Nj hX P x E ⟨i, k.1⟩).etale_g (hx i)))

/-- The local maps of the cover domains of `xᵢ` into the glued space. -/
def φk (i : ι) (k : CI E i) :
    domainObj _ (Dk hX P x E O hO i k) ⟶
      (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).glued :=
  hk hX P x E O hO i k ≫
    (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).ιL (toM E i k)

include hx in
/-- The local maps into the glued space are étale. -/
theorem etale_φk (i : ι) (k : CI E i) : etale (φk hX hSheaf P x E O hO htriv i k) :=
  etale_comp (etale_hk hX P x hx E O hO i k)
    (openImmersion.etale (LocalizedOpenRelation.openImmersion_ιL
      (R := chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf) (toM E i k)))

/-- Cover maps with equal composites to the chart have equal local maps. -/
theorem φk_compat (i : ι) (V : LocalizedCategory.{u, u, u} (K := K)) (k k' : CI E i)
    (a : V ⟶ domainObj _ (Dk hX P x E O hO i k)) (b : V ⟶ domainObj _ (Dk hX P x E O hO i k'))
    (h : a ≫ ek hX P x E O hO i k = b ≫ ek hX P x E O hO i k') :
    a ≫ φk hX hSheaf P x E O hO htriv i k = b ≫ φk hX hSheaf P x E O hO htriv i k' := by
  have hr := rel_hk (hX := hX) (hSheaf := hSheaf) (P := P) (x := x) (E := E) (O := O) (hO := hO)
    (htriv := htriv) a b (pointModel hX (P i) (P i) (x i) (x i)) (by
      rw [h]
      exact TestModel.aRel_refl _ _)
  exact (Category.assoc _ _ _).symm.trans (hr.ιL_eq.trans (Category.assoc _ _ _))

include hSheaf htriv in
/-- The cover maps of the chart `xᵢ` are monomorphisms. -/
theorem mono_ek (i : ι) (k : CI E i) : Mono (ek hX P x E O hO i k) := by
  constructor
  intro T l m h
  have hr := rel_hk (hX := hX) (hSheaf := hSheaf) (P := P) (x := x) (E := E) (O := O) (hO := hO)
    (htriv := htriv) l m (pointModel hX (P i) (P i) (x i) (x i)) (by
      rw [h]
      exact TestModel.aRel_refl _ _)
  have e : l ≫ hk hX P x E O hO i k = m ≫ hk hX P x E O hO i k :=
    LocalizedOpenRelation.rel_self_iff.1 hr
  apply (cancel_mono (domainι _ (Dk hX P x E O hO i k))).1
  apply (Nj hX P x E ⟨i, k.1⟩).jointly_mono (P := P i) (Q := (E ⟨i, k.1⟩).Q)
  · simpa only [Category.assoc] using h
  · rw [Category.assoc, Category.assoc, ← hk_ι, ← Category.assoc, e, Category.assoc]

include hSheaf htriv in
/-- The cover maps of the chart `xᵢ` are open immersions. -/
theorem openImmersion_ek (i : ι) (k : CI E i) : openImmersion (ek hX P x E O hO i k) := by
  have := mono_ek hX hSheaf P x E O hO htriv i k
  exact openImmersion_of_etale_of_mono hSheaf _ (etale_ek hX P x E O hO i k)

include hvO ha in
/-- The local maps descend along the cover of the analytified chart `xᵢ`. -/
theorem exists_π (i : ι) :
    ∃ π : localized K (P i) ⟶ (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).glued,
      ∀ k, ek hX P x E O hO i k ≫ π = φk hX hSheaf P x E O hO htriv i k :=
  exists_glue_of_etale_cover (hSheaf K (localized K (P i)) _)
    (fun k => domainObj _ (Dk hX P x E O hO i k)) (ek hX P x E O hO i)
    (etale_ek hX P x E O hO i) (ek_cover hX P x E O hO hvO ha i)
    (φk hX hSheaf P x E O hO htriv i) (φk_compat hX hSheaf P x E O hO htriv i)

/-- The chart maps into the glued space. -/
def π (i : ι) :
    localized K (P i) ⟶ (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).glued :=
  Classical.choose (exists_π hX hSheaf P x E O hO htriv hvO ha i)

/-- The chart map restricts to the local maps on the cover. -/
theorem ek_π (i : ι) (k : CI E i) :
    ek hX P x E O hO i k ≫ π hX hSheaf P x E O hO htriv hvO ha i =
      φk hX hSheaf P x E O hO htriv i k :=
  Classical.choose_spec (exists_π hX hSheaf P x E O hO htriv hvO ha i) k

include hx in
/-- The chart maps are étale. -/
theorem etale_π (i : ι) : etale (π hX hSheaf P x E O hO htriv hvO ha i) :=
  etale_of_openImmersion_cover _ _ (ek hX P x E O hO i)
    (openImmersion_ek hX hSheaf P x E O hO htriv i) (ek_cover hX P x E O hO hvO ha i)
    fun k => by
      rw [ek_π]
      exact etale_φk hX hSheaf P x hx E O hO htriv i k

variable (hOr : ∀ m : CM E, O m ⊆
  Set.range (baseMap K (E m.1).Q (Nj hX P x E m.1).R (Nj hX P x E m.1).g))

/-- A point of an analytified intersection over a point of a piece gives a point of the
cover domain mapping to that point of the piece. -/
theorem exists_hk_eq₀ (i : ι) (k : CI E i) (w : Space K (Nj hX P x E ⟨i, k.1⟩).R)
    (z : localizedSpaceFunctor.obj
      ((chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).Z (toM E i k)))
    (hw : baseMap K (E ⟨i, k.1⟩).Q (Nj hX P x E ⟨i, k.1⟩).R (Nj hX P x E ⟨i, k.1⟩).g w =
      Subtype.val (p := (· ∈ (DZ E (fun m : CM E => m.1) O hO (toM E i k)).carrier)) z) :
    ∃ w' : localizedSpaceFunctor.obj (domainObj _ (Dk hX P x E O hO i k)),
      localizedSpaceFunctor.map (hk hX P x E O hO i k) w' = z := by
  have hwD : w ∈ DkSet hX P x E O i k := by
    have h₁ : localizedSpaceFunctor.map (localizedHom K (E ⟨i, k.1⟩).Q (Nj hX P x E ⟨i, k.1⟩).R
        (Nj hX P x E ⟨i, k.1⟩).g) w ∈ O (toM E i k) := by
      rw [localizedSpaceFunctor_map_localizedHom]
      exact (congrArg (· ∈ O (toM E i k)) hw).mpr (Subtype.property _)
    exact h₁
  obtain ⟨w', hw'⟩ : ∃ w' : localizedSpaceFunctor.obj (domainObj _ (Dk hX P x E O hO i k)),
      Subtype.val (p := (· ∈ (Dk hX P x E O hO i k).carrier)) w' = w :=
    ⟨Subtype.mk (p := (· ∈ (Dk hX P x E O hO i k).carrier)) w hwD, rfl⟩
  refine ⟨w', ?_⟩
  have h₁ : localizedSpaceFunctor.map (domainι _ (DZ E (fun m : CM E => m.1) O hO (toM E i k)))
      (localizedSpaceFunctor.map (hk hX P x E O hO i k) w') =
      localizedSpaceFunctor.map (domainι _ (DZ E (fun m : CM E => m.1) O hO (toM E i k))) z := by
    rw [← TopCat.comp_app, ← Functor.map_comp, hk_ι, Functor.map_comp, TopCat.comp_app,
      domainι_apply, hw', localizedSpaceFunctor_map_localizedHom]
    exact hw.trans (domainι_apply _ z).symm
  exact LocalizedOpenRelation.openImmersion.injective (openImmersion_domainι _ _) h₁

/-- A point of a piece in the image of the analytified intersection comes from a point of
the cover domain. -/
theorem exists_hk_eq (i : ι) (k : CI E i)
    (z : localizedSpaceFunctor.obj
      ((chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).Z (toM E i k)))
    (hz : Subtype.val (p := (· ∈ (DZ E (fun m : CM E => m.1) O hO (toM E i k)).carrier)) z ∈
      Set.range (baseMap K (E (toM E i k).1).Q (Nj hX P x E (toM E i k).1).R
        (Nj hX P x E (toM E i k).1).g)) :
    ∃ w' : localizedSpaceFunctor.obj (domainObj _ (Dk hX P x E O hO i k)),
      localizedSpaceFunctor.map (hk hX P x E O hO i k) w' = z := by
  obtain ⟨w, hw⟩ := hz
  exact exists_hk_eq₀ hX hSheaf P x E O hO htriv i k w z hw

include hOr in
/-- The chart maps are jointly surjective onto the glued space. -/
theorem π_surjective (y : localizedSpaceFunctor.obj
    (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).glued) :
    ∃ i, y ∈ Set.range (localizedSpaceFunctor.map (π hX hSheaf P x E O hO htriv hvO ha i)) := by
  obtain ⟨m, z, hz⟩ := LocalizedOpenRelation.exists_ι_eq
    (R := chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf) y
  obtain ⟨i, k, rfl⟩ : ∃ (i : ι) (k : CI E i), toM E i k = m := ⟨m.1.1, ⟨m.1.2, m.2⟩, rfl⟩
  have hzO : Subtype.val (p := (· ∈ (DZ E (fun m : CM E => m.1) O hO (toM E i k)).carrier)) z ∈
      O (toM E i k) := Subtype.property _
  obtain ⟨w', hw'z⟩ := exists_hk_eq (hX := hX) (hSheaf := hSheaf) (P := P) (x := x) (E := E)
    (O := O) (hO := hO) (htriv := htriv) i k z (hOr (toM E i k) hzO)
  refine ⟨i, localizedSpaceFunctor.map (ek hX P x E O hO i k) w', ?_⟩
  have e : localizedSpaceFunctor.map (φk hX hSheaf P x E O hO htriv i k) =
      localizedSpaceFunctor.map (hk hX P x E O hO i k) ≫ localizedSpaceFunctor.map
        ((chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).ιL (toM E i k)) :=
    Functor.map_comp _ _ _
  rw [← TopCat.comp_app, ← Functor.map_comp, ek_π, e, TopCat.comp_app]
  exact (LocalizedOpenRelation.ιL_apply _ _).trans
    ((congrArg ((chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).ι (toM E i k))
      hw'z).trans hz)

section Pullbacks

variable {T : LocalizedCategory.{u, u, u} (K := K)} {i j : ι}

/-- The open subset of a test space over which two maps to analytified charts factor through
given cover domains. -/
def TSet (α : T ⟶ localized K (P i)) (β : T ⟶ localized K (P j)) (l : CI E i × CI E j) :
    Set (localizedSpaceFunctor.obj T) :=
  localizedSpaceFunctor.map α ⁻¹' Set.range (localizedSpaceFunctor.map (ek hX P x E O hO i l.1)) ∩
    localizedSpaceFunctor.map β ⁻¹' Set.range (localizedSpaceFunctor.map (ek hX P x E O hO j l.2))

include hSheaf htriv in
/-- The test-space subsets are open. -/
theorem isOpen_TSet (α : T ⟶ localized K (P i)) (β : T ⟶ localized K (P j))
    (l : CI E i × CI E j) : IsOpen (TSet hX P x E O hO α β l) :=
  ((openImmersion_ek hX hSheaf P x E O hO htriv i l.1).isOpenEmbedding.isOpen_range.preimage
      (localizedSpaceFunctor.map α).hom.continuous).inter
    ((openImmersion_ek hX hSheaf P x E O hO htriv j l.2).isOpenEmbedding.isOpen_range.preimage
      (localizedSpaceFunctor.map β).hom.continuous)

/-- The open domain of a test space over which two maps factor through given cover domains. -/
abbrev TDom (α : T ⟶ localized K (P i)) (β : T ⟶ localized K (P j)) (l : CI E i × CI E j) :
    (presentationOf T).AnalyticDomain :=
  (presentationOf T).openDomain (TSet hX P x E O hO α β l)
    (isOpen_TSet hX hSheaf P x E O hO htriv α β l)

include hvO ha in
/-- The test-space domains cover the test space. -/
theorem tcover (α : T ⟶ localized K (P i)) (β : T ⟶ localized K (P j))
    (t : localizedSpaceFunctor.obj T) :
    ∃ l, t ∈ Set.range (localizedSpaceFunctor.map
      (domainι T (TDom hX hSheaf P x E O hO htriv α β l))) := by
  obtain ⟨k, hk⟩ := ek_cover hX P x E O hO hvO ha i (localizedSpaceFunctor.map α t)
  obtain ⟨k', hk'⟩ := ek_cover hX P x E O hO hvO ha j (localizedSpaceFunctor.map β t)
  obtain ⟨t', ht'⟩ : ∃ t' : localizedSpaceFunctor.obj
      (domainObj T (TDom hX hSheaf P x E O hO htriv α β (k, k'))),
      Subtype.val (p := (· ∈ (TDom hX hSheaf P x E O hO htriv α β (k, k')).carrier)) t' = t :=
    ⟨Subtype.mk (p := (· ∈ (TDom hX hSheaf P x E O hO htriv α β (k, k')).carrier)) t ⟨hk, hk'⟩,
      rfl⟩
  exact ⟨(k, k'), t', (domainι_apply _ _).trans ht'⟩

/-- On its test-space domain the first map factors through the cover map. -/
theorem exists_tlift₁ (α : T ⟶ localized K (P i)) (β : T ⟶ localized K (P j))
    (l : CI E i × CI E j) :
    ∃ a : domainObj T (TDom hX hSheaf P x E O hO htriv α β l) ⟶
        domainObj _ (Dk hX P x E O hO i l.1),
      a ≫ ek hX P x E O hO i l.1 = domainι T (TDom hX hSheaf P x E O hO htriv α β l) ≫ α :=
  openImmersion.exists_lift (openImmersion_ek hX hSheaf P x E O hO htriv i l.1) _ fun t => by
    rw [localizedSpaceFunctor.map_comp (domainι T (TDom hX hSheaf P x E O hO htriv α β l)) α,
      TopCat.comp_app, domainι_apply]
    exact (Subtype.property (p := (· ∈ (TDom hX hSheaf P x E O hO htriv α β l).carrier)) t).1

/-- On its test-space domain the second map factors through the cover map. -/
theorem exists_tlift₂ (α : T ⟶ localized K (P i)) (β : T ⟶ localized K (P j))
    (l : CI E i × CI E j) :
    ∃ b : domainObj T (TDom hX hSheaf P x E O hO htriv α β l) ⟶
        domainObj _ (Dk hX P x E O hO j l.2),
      b ≫ ek hX P x E O hO j l.2 = domainι T (TDom hX hSheaf P x E O hO htriv α β l) ≫ β :=
  openImmersion.exists_lift (openImmersion_ek hX hSheaf P x E O hO htriv j l.2) _ fun t => by
    rw [localizedSpaceFunctor.map_comp (domainι T (TDom hX hSheaf P x E O hO htriv α β l)) β,
      TopCat.comp_app, domainι_apply]
    exact (Subtype.property (p := (· ∈ (TDom hX hSheaf P x E O hO htriv α β l).carrier)) t).2

include hvO ha in
/-- Maps related through a model of the intersection of two charts have equal composites with
the chart maps. -/
theorem π_eq_of_aRel (M : TestModel (pointHom K (x i)) (pointHom K (x j)))
    (α : T ⟶ localized K (P i)) (β : T ⟶ localized K (P j)) (h : M.ARel (P i) (P j) α β) :
    α ≫ π hX hSheaf P x E O hO htriv hvO ha i = β ≫ π hX hSheaf P x E O hO htriv hvO ha j := by
  refine hom_ext_of_etale_cover (hSheaf K T _)
    (fun l => domainObj T (TDom hX hSheaf P x E O hO htriv α β l))
    (fun l => domainι T (TDom hX hSheaf P x E O hO htriv α β l))
    (fun l => etaleOpenDomainStatement _ _ _) (tcover hX hSheaf P x E O hO htriv hvO ha α β) _ _
    fun l => ?_
  obtain ⟨a, hA⟩ := exists_tlift₁ hX hSheaf P x E O hO htriv α β l
  obtain ⟨b, hB⟩ := exists_tlift₂ hX hSheaf P x E O hO htriv α β l
  have hr := rel_hk (hX := hX) (hSheaf := hSheaf) (P := P) (x := x) (E := E) (O := O) (hO := hO)
    (htriv := htriv) a b M (by
      rw [hA, hB]
      exact h.comp _)
  calc domainι T (TDom hX hSheaf P x E O hO htriv α β l) ≫ α ≫
        π hX hSheaf P x E O hO htriv hvO ha i
      = a ≫ ek hX P x E O hO i l.1 ≫ π hX hSheaf P x E O hO htriv hvO ha i := by
        rw [← Category.assoc, ← hA, Category.assoc]
    _ = a ≫ φk hX hSheaf P x E O hO htriv i l.1 := by rw [ek_π]
    _ = b ≫ φk hX hSheaf P x E O hO htriv j l.2 :=
        (Category.assoc _ _ _).symm.trans (hr.ιL_eq.trans (Category.assoc _ _ _))
    _ = domainι T (TDom hX hSheaf P x E O hO htriv α β l) ≫ β ≫
        π hX hSheaf P x E O hO htriv hvO ha j := by
        rw [← ek_π, ← Category.assoc, hB, Category.assoc]

include hvO ha in
/-- Maps with equal composites with the chart maps are related through every model of the
intersection of the two charts. -/
theorem aRel_of_π_eq (M : TestModel (pointHom K (x i)) (pointHom K (x j)))
    (α : T ⟶ localized K (P i)) (β : T ⟶ localized K (P j))
    (h : α ≫ π hX hSheaf P x E O hO htriv hvO ha i = β ≫ π hX hSheaf P x E O hO htriv hvO ha j) :
    M.ARel (P i) (P j) α β := by
  refine TestModel.ARel.of_etale_cover hSheaf M
    (fun l => domainObj T (TDom hX hSheaf P x E O hO htriv α β l))
    (fun l => domainι T (TDom hX hSheaf P x E O hO htriv α β l))
    (fun l => etaleOpenDomainStatement _ _ _) (tcover hX hSheaf P x E O hO htriv hvO ha α β)
    fun l => ?_
  obtain ⟨a, hA⟩ := exists_tlift₁ hX hSheaf P x E O hO htriv α β l
  obtain ⟨b, hB⟩ := exists_tlift₂ hX hSheaf P x E O hO htriv α β l
  rw [← hA, ← hB]
  have e₁ : (a ≫ hk hX P x E O hO i l.1) ≫
      (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).ιL (toM E i l.1) =
      (b ≫ hk hX P x E O hO j l.2) ≫
        (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).ιL (toM E j l.2) :=
    calc (a ≫ hk hX P x E O hO i l.1) ≫
          (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).ιL (toM E i l.1)
        = a ≫ φk hX hSheaf P x E O hO htriv i l.1 := Category.assoc _ _ _
      _ = a ≫ ek hX P x E O hO i l.1 ≫ π hX hSheaf P x E O hO htriv hvO ha i := by rw [ek_π]
      _ = domainι T (TDom hX hSheaf P x E O hO htriv α β l) ≫ α ≫
          π hX hSheaf P x E O hO htriv hvO ha i := by rw [← Category.assoc, hA, Category.assoc]
      _ = domainι T (TDom hX hSheaf P x E O hO htriv α β l) ≫ β ≫
          π hX hSheaf P x E O hO htriv hvO ha j := by rw [h]
      _ = b ≫ ek hX P x E O hO j l.2 ≫ π hX hSheaf P x E O hO htriv hvO ha j := by
          rw [← Category.assoc, ← hB, Category.assoc]
      _ = b ≫ φk hX hSheaf P x E O hO htriv j l.2 := by rw [ek_π]
      _ = (b ≫ hk hX P x E O hO j l.2) ≫
          (chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf).ιL (toM E j l.2) :=
          (Category.assoc _ _ _).symm
  have sq := LocalizedOpenRelation.isPullback_ιL
    (R := chartRelation hX E (fun m : CM E => m.1) O hO htriv hSheaf) (toM E i l.1) (toM E j l.2)
  obtain ⟨t, ht₁, ht₂⟩ := aRel_of_lift hX E (fun m : CM E => m.1) O hO (sq.lift _ _ e₁)
    (sq.lift_fst _ _ e₁) (sq.lift_snd _ _ e₁)
  have f₁ : (a ≫ hk hX P x E O hO i l.1) ≫
      domainι _ (DZ E (fun m : CM E => m.1) O hO (toM E i l.1)) =
      a ≫ domainι _ _ ≫ localizedHom K (E ⟨i, l.1.1⟩).Q (Nj hX P x E ⟨i, l.1.1⟩).R
        (Nj hX P x E ⟨i, l.1.1⟩).g := by
    rw [Category.assoc, hk_ι]
  have f₂ : (b ≫ hk hX P x E O hO j l.2) ≫
      domainι _ (DZ E (fun m : CM E => m.1) O hO (toM E j l.2)) =
      b ≫ domainι _ _ ≫ localizedHom K (E ⟨j, l.2.1⟩).Q (Nj hX P x E ⟨j, l.2.1⟩).R
        (Nj hX P x E ⟨j, l.2.1⟩).g := by
    rw [Category.assoc, hk_ι]
  have A₂ : (Wm hX E (fun m : CM E => m.1) (toM E i l.1) (toM E j l.2)).ARel
      (E ⟨i, l.1.1⟩).Q (E ⟨j, l.2.1⟩).Q
      (a ≫ domainι _ _ ≫ localizedHom K (E ⟨i, l.1.1⟩).Q (Nj hX P x E ⟨i, l.1.1⟩).R
        (Nj hX P x E ⟨i, l.1.1⟩).g)
      (b ≫ domainι _ _ ≫ localizedHom K (E ⟨j, l.2.1⟩).Q (Nj hX P x E ⟨j, l.2.1⟩).R
        (Nj hX P x E ⟨j, l.2.1⟩).g) :=
    ⟨t, ht₁.trans f₁, ht₂.trans f₂⟩
  have A₁ : (Nj hX P x E ⟨i, l.1.1⟩).ARel (P i) (E ⟨i, l.1.1⟩).Q (a ≫ ek hX P x E O hO i l.1)
      (a ≫ domainι _ _ ≫ localizedHom K (E ⟨i, l.1.1⟩).Q (Nj hX P x E ⟨i, l.1.1⟩).R
        (Nj hX P x E ⟨i, l.1.1⟩).g) :=
    ⟨a ≫ domainι _ _, Category.assoc _ _ _, Category.assoc _ _ _⟩
  have A₃ : (Nj hX P x E ⟨j, l.2.1⟩).flip.ARel (E ⟨j, l.2.1⟩).Q (P j)
      (b ≫ domainι _ _ ≫ localizedHom K (E ⟨j, l.2.1⟩).Q (Nj hX P x E ⟨j, l.2.1⟩).R
        (Nj hX P x E ⟨j, l.2.1⟩).g)
      (b ≫ ek hX P x E O hO j l.2) :=
    TestModel.ARel.symm ⟨b ≫ domainι _ _, Category.assoc _ _ _, Category.assoc _ _ _⟩
  exact TestModel.ARel.trans M
    (TestModel.ARel.trans (pointModel hX (P i) (E ⟨j, l.2.1⟩).Q (x i) (E ⟨j, l.2.1⟩).y) A₁ A₂) A₃

include hvO ha in
/-- Every affine fibre square of two charts becomes a pullback square of chart maps. -/
theorem isPullback_π {B : Type u} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
    (f : A i →ₐ[K] B) (g : A j →ₐ[K] B)
    (hfg : IsPullback ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K f))
      ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K g))
      (pointHom K (x i)) (pointHom K (x j))) :
    IsPullback (localizedHom K (P i) Q f) (localizedHom K (P j) Q g)
      (π hX hSheaf P x E O hO htriv hvO ha i) (π hX hSheaf P x E O hO htriv hvO ha j) := by
  let MB : TestModel (pointHom K (x i)) (pointHom K (x j)) :=
    { C := CommAlgCat.of K B, R := Q, f := f, g := g, isPullback := hfg }
  exact TestModel.isPullback_of_aRel MB _ _
    (π_eq_of_aRel hX hSheaf P x E O hO htriv hvO ha MB _ _
      ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩)
    fun α β h => aRel_of_π_eq hX hSheaf P x E O hO htriv hvO ha MB α β h

end Pullbacks

end Langlands.Analytic.SpaceAnalytification.ChartQuotient

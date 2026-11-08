import Langlands.Geometry.Analytic.FullRecognitionPairComposition
import Langlands.Geometry.Analytic.FiniteEtaleAlgebra
import Langlands.Geometry.Analytic.FiniteBanachModule

/-! # Finite and finite étale morphisms through full-recognition pair systems -/

noncomputable section

universe u v w v' w'

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

namespace BoundedAlgHom

section FiniteBanach

variable {K : Type u} {R : Type v} {S : Type w} {T : Type v'}
  [NormedField K] [NormedCommRing R] [NormedCommRing S] [NormedCommRing T]
  [NormedAlgebra K R] [NormedAlgebra K S] [NormedAlgebra K T]

/-- Berkovich's finite Banach algebras: the target is a finite Banach module
over the source through `f`, that is, some finite coefficient map from the
finite free module with its maximum norm is an admissible epimorphism. The
admissibility is expressed by norm-controlled preimages; the coefficient map is
already bounded. -/
def IsFiniteBanach (f : BoundedAlgHom K R S) : Prop :=
  ∃ (n : ℕ) (b : Fin n → S) (C : ℝ), 0 < C ∧
    ∀ y : S, ∃ c : Fin n → R, f.coefficientMap b c = y ∧ ‖c‖ ≤ C * ‖y‖

/-- A finite Banach algebra is in particular module-finite. -/
theorem IsFiniteBanach.finite {f : BoundedAlgHom K R S} (hf : f.IsFiniteBanach) :
    f.toAlgHom.toRingHom.Finite := by
  obtain ⟨n, b, C, -, hb⟩ := hf
  refine (f.finite_iff_exists_surjective_coefficientMap).2 ⟨n, b, fun y => ?_⟩
  obtain ⟨c, hc, -⟩ := hb y
  exact ⟨c, hc⟩

/-- The identity is a finite Banach algebra map, with the single generator `1`. -/
theorem isFiniteBanach_id : (BoundedAlgHom.id K R).IsFiniteBanach := by
  refine ⟨1, fun _ => 1, 1, zero_lt_one, fun y => ⟨fun _ => y, ?_, ?_⟩⟩
  · simp [coefficientMap_apply]
  · rw [one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun _ => le_rfl

/-- Finite Banach algebra maps compose: products of the two generating tuples
generate, with the product of the two lifting constants. -/
theorem IsFiniteBanach.comp {g : BoundedAlgHom K S T} {f : BoundedAlgHom K R S}
    (hg : g.IsFiniteBanach) (hf : f.IsFiniteBanach) : (g.comp f).IsFiniteBanach := by
  classical
  obtain ⟨n, b, C1, hC1, hb⟩ := hf
  obtain ⟨m, d, C2, hC2, hd⟩ := hg
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  refine ⟨m * n, fun k => g (b (e.symm k).2) * d (e.symm k).1, C1 * C2,
    mul_pos hC1 hC2, fun z => ?_⟩
  obtain ⟨c, hcz, hcn⟩ := hd z
  choose a ha han using fun j : Fin m => hb (c j)
  refine ⟨fun k => a (e.symm k).1 (e.symm k).2, ?_, ?_⟩
  · rw [coefficientMap_apply]
    rw [← hcz, coefficientMap_apply]
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha j, coefficientMap_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change g (f (a j i)) * (g (b i) * d j) = g (f (a j i) * b i) * d j
    rw [map_mul, mul_assoc]
  · refine (pi_norm_le_iff_of_nonneg
      (mul_nonneg (mul_nonneg hC1.le hC2.le) (norm_nonneg z))).2 fun k => ?_
    calc ‖a (e.symm k).1 (e.symm k).2‖ ≤ ‖a (e.symm k).1‖ := norm_le_pi_norm _ _
      _ ≤ C1 * ‖c (e.symm k).1‖ := han _
      _ ≤ C1 * ‖c‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) hC1.le
      _ ≤ C1 * (C2 * ‖z‖) := mul_le_mul_of_nonneg_left hcn hC1.le
      _ = C1 * C2 * ‖z‖ := (mul_assoc _ _ _).symm

end FiniteBanach

end BoundedAlgHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

namespace AdmissiblePairSystem

variable {A : AffinoidAtlasPresentation.{u, v, w} K} {B : AffinoidAtlasPresentation.{u, v', w'} K}

/-- Equal pair systems have equal bounded maps on every admissible pair. -/
theorem pullback_congr {p q : AdmissiblePairSystem A B} (e : p = q)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (hp : p.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hq : q.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    p.pullback i j hp = q.pullback i j hq := by
  subst e
  rfl

end AdmissiblePairSystem

namespace StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- `g` induces a finite morphism from `V` to `U`: it maps `V` into `U`, and
for every recognized affinoid subset `W` inside `U`, the preimage of `W` in `V`
is a recognized affinoid subset whose bounded map from `W` is finite. -/
def IsFiniteOver (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : Set A.space) (U : Set B.space) : Prop :=
  g.baseMap '' V ⊆ U ∧
    ∀ W : B.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ U →
      ∃ (V' : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus ∧
          (g.fullRecognitionPairs.pullback V' W h).IsFiniteBanach

/-- The same condition with algebraically finite étale bounded maps. -/
def IsFiniteEtaleOver (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : Set A.space) (U : Set B.space) : Prop :=
  g.baseMap '' V ⊆ U ∧
    ∀ W : B.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ U →
      ∃ (V' : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus ∧
          ((g.fullRecognitionPairs.pullback V' W h).IsFiniteBanach ∧
            (g.fullRecognitionPairs.pullback V' W h).AlgebraicallyFiniteEtale)

/-- Berkovich's finite morphisms: the preimage of every affinoid domain is an
affinoid domain, finite over it. -/
def IsFinite (g : StrongHom A.saturatedPresentation B.saturatedPresentation) : Prop :=
  g.IsFiniteOver Set.univ Set.univ

/-- Finite morphisms whose affinoid maps are algebraically finite étale. -/
def IsFiniteEtale (g : StrongHom A.saturatedPresentation B.saturatedPresentation) : Prop :=
  g.IsFiniteEtaleOver Set.univ Set.univ

/-- Finiteness at a point: open neighborhoods of the point and of its image
between which `g` induces a finite morphism. -/
def IsFiniteAt (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (y : A.space) : Prop :=
  ∃ (V : Set A.space) (U : Set B.space), IsOpen V ∧ IsOpen U ∧ y ∈ V ∧ g.IsFiniteOver V U

/-- Quasifinite morphisms are finite at every point. -/
def IsQuasifinite (g : StrongHom A.saturatedPresentation B.saturatedPresentation) : Prop :=
  ∀ y : A.space, g.IsFiniteAt y

/-- Open neighborhoods of the point and of its image between which `g` induces
a finite morphism with algebraically finite étale affinoid maps. -/
def IsLocallyFiniteEtaleAt (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (y : A.space) : Prop :=
  ∃ (V : Set A.space) (U : Set B.space), IsOpen V ∧ IsOpen U ∧ y ∈ V ∧
    g.IsFiniteEtaleOver V U

section Basic

variable {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {V : Set A.space} {U : Set B.space}

theorem IsFiniteEtaleOver.isFiniteOver (hg : g.IsFiniteEtaleOver V U) :
    g.IsFiniteOver V U := by
  refine ⟨hg.1, fun W hW => ?_⟩
  obtain ⟨V', h, hV', hfe⟩ := hg.2 W hW
  exact ⟨V', h, hV', hfe.1⟩

theorem IsFiniteEtale.isFinite (hg : g.IsFiniteEtale) : g.IsFinite :=
  IsFiniteEtaleOver.isFiniteOver hg

theorem IsFinite.isFiniteAt (hg : g.IsFinite) (y : A.space) : g.IsFiniteAt y :=
  ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ, Set.mem_univ y, hg⟩

theorem IsFinite.isQuasifinite (hg : g.IsFinite) : g.IsQuasifinite :=
  hg.isFiniteAt

theorem IsLocallyFiniteEtaleAt.isFiniteAt {y : A.space} (hg : g.IsLocallyFiniteEtaleAt y) :
    g.IsFiniteAt y := by
  obtain ⟨V, U, hV, hU, hy, hfe⟩ := hg
  exact ⟨V, U, hV, hU, hy, hfe.isFiniteOver⟩

end Basic

section Identity

variable (A)

/-- On recognized subsets, the identity of the local-domain enlargement has the
identity bounded map. -/
theorem fullRecognitionPairs_id_pullback_self (W : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : (StrongHom.id A.saturatedPresentation).baseMap '' Set.range W.chart ⊆
      Set.range W.chart) :
    (StrongHom.id A.saturatedPresentation).fullRecognitionPairs.pullback W W h =
      BoundedAlgHom.id K W.algebra := by
  have h' : (StrongHom.id A.fullRecognitionPresentation).toAdmissiblePairSystem.baseMap ''
      Set.range (A.fullRecognitionPresentation.atlas.chart W) ⊆
        Set.range (A.fullRecognitionPresentation.atlas.chart W) := h
  exact (AdmissiblePairSystem.pullback_congr (fullRecognitionPairs_id A) W W h h').trans
    W.restriction_self

theorem isFiniteEtaleOver_id (V : Set A.space) :
    (StrongHom.id A.saturatedPresentation).IsFiniteEtaleOver V V := by
  refine ⟨fun _ ⟨x, hx, e⟩ => e ▸ hx, fun W hW => ?_⟩
  have h : (StrongHom.id A.saturatedPresentation).baseMap '' Set.range W.chart ⊆
      Set.range W.chart := fun _ ⟨x, hx, e⟩ => e ▸ hx
  refine ⟨W, h, (Set.inter_eq_right.2 hW).symm, ?_⟩
  rw [fullRecognitionPairs_id_pullback_self A W h]
  exact ⟨BoundedAlgHom.isFiniteBanach_id, BoundedAlgHom.algebraicallyFiniteEtale_id⟩

theorem isFiniteOver_id (V : Set A.space) :
    (StrongHom.id A.saturatedPresentation).IsFiniteOver V V :=
  (isFiniteEtaleOver_id A V).isFiniteOver

theorem isFiniteEtale_id : (StrongHom.id A.saturatedPresentation).IsFiniteEtale :=
  isFiniteEtaleOver_id A Set.univ

theorem isFinite_id : (StrongHom.id A.saturatedPresentation).IsFinite :=
  isFiniteOver_id A Set.univ

end Identity

section Composition

variable {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {g' : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {V : Set A.space} {U : Set B.space} {T : Set C.space}

/-- The preimage loci compose. -/
private theorem finiteComp_locus (hgVU : g.baseMap '' V ⊆ U)
    {V1 : B.atlas.saturatedAtlas.RecognizedSubset} {W : C.atlas.saturatedAtlas.RecognizedSubset}
    {V2 : A.atlas.saturatedAtlas.RecognizedSubset}
    (hV1 : V1.locus = U ∩ g'.baseMap ⁻¹' W.locus) (hV2 : V2.locus = V ∩ g.baseMap ⁻¹' V1.locus) :
    V2.locus = V ∩ (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap ⁻¹' W.locus := by
  rw [hV2, hV1]
  ext x
  constructor
  · rintro ⟨hx, _, hxW⟩
    exact ⟨hx, hxW⟩
  · rintro ⟨hx, hxW⟩
    exact ⟨hx, hgVU ⟨x, hx, rfl⟩, hxW⟩

private theorem finiteComp_admissible
    {V1 : B.atlas.saturatedAtlas.RecognizedSubset} {W : C.atlas.saturatedAtlas.RecognizedSubset}
    {V2 : A.atlas.saturatedAtlas.RecognizedSubset}
    (h21 : g.baseMap '' Set.range V2.chart ⊆ Set.range V1.chart)
    (h1W : g'.baseMap '' Set.range V1.chart ⊆ Set.range W.chart) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap '' Set.range V2.chart ⊆
        Set.range W.chart := by
  rintro _ ⟨x, hx, rfl⟩
  exact h1W ⟨g.baseMap x, h21 ⟨x, hx, rfl⟩, rfl⟩

private theorem finiteComp_image (hgVU : g.baseMap '' V ⊆ U) (hg'UT : g'.baseMap '' U ⊆ T) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap '' V ⊆ T := by
  rintro _ ⟨x, hx, rfl⟩
  exact hg'UT ⟨g.baseMap x, hgVU ⟨x, hx, rfl⟩, rfl⟩

/-- Finite morphisms compose, through the composition law of pair systems. -/
theorem IsFiniteOver.comp (hg : g.IsFiniteOver V U) (hg' : g'.IsFiniteOver U T) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteOver V T := by
  refine ⟨finiteComp_image hg.1 hg'.1, fun W hW => ?_⟩
  obtain ⟨V1, h1W, hV1, hfin1⟩ := hg'.2 W hW
  have hV1U : V1.locus ⊆ U := hV1.trans_subset Set.inter_subset_left
  obtain ⟨V2, h21, hV2, hfin2⟩ := hg.2 V1 hV1U
  have h2W := finiteComp_admissible h21 h1W
  refine ⟨V2, h2W, finiteComp_locus hg.1 hV1 hV2, ?_⟩
  rw [fullRecognitionPairs_comp g g' V2 V1 W h21 h1W h2W]
  exact hfin2.comp hfin1

/-- Finite étale morphisms compose. -/
theorem IsFiniteEtaleOver.comp (hg : g.IsFiniteEtaleOver V U)
    (hg' : g'.IsFiniteEtaleOver U T) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteEtaleOver V T := by
  refine ⟨finiteComp_image hg.1 hg'.1, fun W hW => ?_⟩
  obtain ⟨V1, h1W, hV1, hfe1⟩ := hg'.2 W hW
  have hV1U : V1.locus ⊆ U := hV1.trans_subset Set.inter_subset_left
  obtain ⟨V2, h21, hV2, hfe2⟩ := hg.2 V1 hV1U
  have h2W := finiteComp_admissible h21 h1W
  refine ⟨V2, h2W, finiteComp_locus hg.1 hV1 hV2, ?_⟩
  rw [fullRecognitionPairs_comp g g' V2 V1 W h21 h1W h2W]
  exact ⟨hfe2.1.comp hfe1.1, hfe2.2.comp hfe1.2⟩

theorem IsFinite.comp (hg : g.IsFinite) (hg' : g'.IsFinite) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFinite :=
  IsFiniteOver.comp hg hg'

theorem IsFiniteEtale.comp (hg : g.IsFiniteEtale) (hg' : g'.IsFiniteEtale) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteEtale :=
  IsFiniteEtaleOver.comp hg hg'

end Composition

end StrongHom

end AffinoidAtlasPresentation

end Langlands.Analytic

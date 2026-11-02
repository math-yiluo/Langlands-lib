import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionProduct
import Mathlib.CategoryTheory.Extensive

/-! # A relation assembled from finitely many scheme charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- Each component of a scheme coproduct is a closed immersion as well as an
open immersion. -/
theorem isClosedImmersion_sigma_ι {I : Type} [Finite I] (X : I → Scheme.{u}) (i : I) :
    IsClosedImmersion (Sigma.ι X i) := by
  apply IsClosedImmersion.of_isPreimmersion
  have heq : (Set.range (Sigma.ι X i))ᶜ =
      ⋃ j : {j : I // j ≠ i}, Set.range (Sigma.ι X j.1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨j⟩, y, hy⟩ :=
        Scheme.IsLocallyDirected.ι_jointly_surjective (Discrete.functor X) x
      have hj : j ≠ i := by
        rintro rfl
        exact hx ⟨y, hy⟩
      exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, y, hy⟩
    · intro hx
      obtain ⟨⟨j, hj⟩, y, hy⟩ := Set.mem_iUnion.mp hx
      rintro ⟨z, hz⟩
      have : i = j := congrArg Sigma.fst ((sigmaι_eq_iff X i j z y).mp (hz.trans hy.symm))
      exact hj this.symm
  rw [← isOpen_compl_iff, heq]
  exact isOpen_iUnion fun j => (Sigma.ι X j.1).isOpenEmbedding.isOpen_range

/-- A map out of a finite coproduct is a closed immersion if it is injective
and its restrictions to all components are closed immersions. -/
theorem isClosedImmersion_of_finite_coproduct
    {I : Type} [Finite I] {X : I → Scheme.{u}} {Y : Scheme.{u}}
    (f : (∐ X) ⟶ Y) (hf : ∀ i, IsClosedImmersion (Sigma.ι X i ≫ f))
    (hi : Function.Injective f) : IsClosedImmersion f := by
  have : SurjectiveOnStalks f := by
    apply IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks) (sigmaOpenCover X)
    intro i
    exact (hf i).toSurjectiveOnStalks
  refine ⟨IsClosedEmbedding.of_continuous_injective_isClosedMap f.continuous hi ?_⟩
  intro Z hZ
  have heq : f '' Z = ⋃ i, (Sigma.ι X i ≫ f) '' ((Sigma.ι X i) ⁻¹' Z) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨⟨i⟩, x, rfl⟩ :=
        Scheme.IsLocallyDirected.ι_jointly_surjective (Discrete.functor X) x
      exact Set.mem_iUnion.mpr ⟨i, ⟨x, by simpa using hx, by simp⟩⟩
    · intro hy
      obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
      exact ⟨Sigma.ι X i x, hx, by simp⟩
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro i
  let := hf i
  exact (Sigma.ι X i ≫ f).isClosedEmbedding.isClosedMap _
    (hZ.preimage (Sigma.ι X i).continuous)

/-- Finite chart data for a scheme equivalence relation. The relation between
chart `i` and chart `j` is represented by `R i j`; all laws are required on
points valued in arbitrary schemes. -/
structure FiniteSchemeRelation (I : Type) where
  U : I → Scheme.{u}
  R : I → I → Scheme.{u}
  t : ∀ i j, R i j ⟶ U i
  s : ∀ i j, R i j ⟶ U j
  closed_lift : ∀ i j, IsClosedImmersion (prod.lift (t i j) (s i j))
  etale_t : ∀ i j, Etale (t i j)
  etale_s : ∀ i j, Etale (s i j)
  refl : ∀ i (T : Scheme.{u}) (a : T ⟶ U i),
    ∃ r : T ⟶ R i i, r ≫ t i i = a ∧ r ≫ s i i = a
  symm : ∀ i j (T : Scheme.{u}) (r : T ⟶ R i j),
    ∃ r' : T ⟶ R j i, r' ≫ t j i = r ≫ s i j ∧ r' ≫ s j i = r ≫ t i j
  trans : ∀ i j k (T : Scheme.{u}) (r : T ⟶ R i j) (r' : T ⟶ R j k),
    r ≫ s i j = r' ≫ t j k →
      ∃ r'' : T ⟶ R i k, r'' ≫ t i k = r ≫ t i j ∧ r'' ≫ s i k = r' ≫ s j k

namespace FiniteSchemeRelation

variable {I : Type} [Finite I] (D : FiniteSchemeRelation.{u} I)

/-- The coproduct of object charts. -/
abbrev objectScheme : Scheme.{u} := ∐ D.U

/-- The coproduct of all cross-chart relation schemes. -/
abbrev relationScheme : Scheme.{u} := ∐ fun p : I × I => D.R p.1 p.2

/-- The first endpoint on the finite coproduct. -/
def first : D.relationScheme ⟶ D.objectScheme :=
  Sigma.desc fun p : I × I => D.t p.1 p.2 ≫ Sigma.ι D.U p.1

/-- The second endpoint on the finite coproduct. -/
def second : D.relationScheme ⟶ D.objectScheme :=
  Sigma.desc fun p : I × I => D.s p.1 p.2 ≫ Sigma.ι D.U p.2

omit [Finite I] in
@[reassoc (attr := simp)]
theorem ι_first (i j : I) :
    Sigma.ι (fun p : I × I => D.R p.1 p.2) (i, j) ≫ D.first =
      D.t i j ≫ Sigma.ι D.U i := by
  simp [first]

omit [Finite I] in
@[reassoc (attr := simp)]
theorem ι_second (i j : I) :
    Sigma.ι (fun p : I × I => D.R p.1 p.2) (i, j) ≫ D.second =
      D.s i j ≫ Sigma.ι D.U j := by
  simp [second]

instance first_etale : Etale D.first := by
  apply IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
  intro p
  let := D.etale_t p.1 p.2
  infer_instance

instance second_etale : Etale D.second := by
  apply IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
  intro p
  let := D.etale_s p.1 p.2
  infer_instance

theorem component_joint_isClosedImmersion (p : I × I) :
    IsClosedImmersion
      (Sigma.ι (fun p : I × I => D.R p.1 p.2) p ≫ prod.lift D.first D.second) := by
  let := D.closed_lift p.1 p.2
  let := isClosedImmersion_sigma_ι D.U p.1
  let := isClosedImmersion_sigma_ι D.U p.2
  have : IsClosedImmersion (prod.map (Sigma.ι D.U p.1) (Sigma.ι D.U p.2)) :=
    schemeMorphismProperty_prod_map (@IsClosedImmersion) _ _ inferInstance inferInstance
  convert (IsClosedImmersion.comp (prod.lift (D.t p.1 p.2) (D.s p.1 p.2))
    (prod.map (Sigma.ι D.U p.1) (Sigma.ι D.U p.2))) using 1
  apply prod.hom_ext <;> simp [first, second]

instance joint_isClosedImmersion : IsClosedImmersion (prod.lift D.first D.second) := by
  apply isClosedImmersion_of_finite_coproduct (X := fun p : I × I => D.R p.1 p.2)
    _ D.component_joint_isClosedImmersion
  intro x y hxy
  obtain ⟨⟨⟨i, j⟩⟩, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (Discrete.functor (fun p : I × I => D.R p.1 p.2)) x
  obtain ⟨⟨⟨k, l⟩⟩, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (Discrete.functor (fun p : I × I => D.R p.1 p.2)) y

  have ht := congrArg (fun z => (prod.fst : D.objectScheme ⨯ D.objectScheme ⟶ _) z) hxy
  have hs := congrArg (fun z => (prod.snd : D.objectScheme ⨯ D.objectScheme ⟶ _) z) hxy
  dsimp only [objectScheme] at ht hs
  have ht' : Sigma.ι D.U i (D.t i j x) = Sigma.ι D.U k (D.t k l y) := by
    simpa only [← Scheme.Hom.comp_apply, prod.lift_fst, D.ι_first, Category.assoc] using ht
  have hs' : Sigma.ι D.U j (D.s i j x) = Sigma.ι D.U l (D.s k l y) := by
    simpa only [← Scheme.Hom.comp_apply, prod.lift_snd, D.ι_second, Category.assoc] using hs
  have hik : i = k := congrArg Sigma.fst ((sigmaι_eq_iff D.U i k _ _).mp ht')
  have hjl : j = l := congrArg Sigma.fst ((sigmaι_eq_iff D.U j l _ _).mp hs')
  subst k
  subst l
  let := D.component_joint_isClosedImmersion (i, j)
  have h : x = y := (Sigma.ι (fun p : I × I => D.R p.1 p.2) (i, j) ≫
    prod.lift D.first D.second).isClosedEmbedding.injective (by
      simpa only [Sigma.ι, Scheme.Hom.comp_apply] using hxy)
  exact congrArg (Sigma.ι (fun p : I × I => D.R p.1 p.2) (i, j)) h

omit [Finite I] in
/-- Cross-chart composition after inclusion in the total relation. If the
middle indices differ, the test scheme is empty. -/
theorem exists_composite (i j k l : I) {T : Scheme.{u}}
    (r : T ⟶ D.R i j) (r' : T ⟶ D.R k l)
    (h : r ≫ D.s i j ≫ Sigma.ι D.U j = r' ≫ D.t k l ≫ Sigma.ι D.U k) :
    ∃ c : T ⟶ D.relationScheme,
      c ≫ D.first = r ≫ D.t i j ≫ Sigma.ι D.U i ∧
      c ≫ D.second = r' ≫ D.s k l ≫ Sigma.ι D.U l := by
  classical
  by_cases hjk : j = k
  · subst k
    have hm : r ≫ D.s i j = r' ≫ D.t j l :=
      (cancel_mono (Sigma.ι D.U j)).mp (by simpa only [Category.assoc] using h)
    obtain ⟨c, hc, hc'⟩ := D.trans i j l T r r' hm
    refine ⟨c ≫ Sigma.ι (fun p : I × I => D.R p.1 p.2) (i, l), ?_, ?_⟩
    · simpa only [Category.assoc, D.ι_first] using
        congrArg (· ≫ Sigma.ι D.U i) hc
    · simpa only [Category.assoc, D.ι_second] using
        congrArg (· ≫ Sigma.ι D.U l) hc'
  · have : IsEmpty T := isEmpty_of_commSq_sigmaι_of_ne (g := D.U)
      (a := r ≫ D.s i j) (b := r' ≫ D.t k l) ⟨by simpa only [Category.assoc] using h⟩ hjk
    let hT : IsInitial T := (isInitial_iff_isEmpty (X := T)).mpr inferInstance |>.some
    exact ⟨hT.to _, hT.hom_ext _ _, hT.hom_ext _ _⟩

/-- The actual equivalence relation on the finite coproduct of charts. Finite
extensivity decomposes composable arrows before applying the chartwise law. -/
def toEtaleEquivalenceRelation : EtaleEquivalenceRelation.{u} where
  U := D.objectScheme
  R := D.relationScheme
  t := D.first
  s := D.second
  mono_lift := inferInstance
  etale_t := inferInstance
  etale_s := inferInstance
  refl T a := by
    let unit : D.objectScheme ⟶ D.relationScheme :=
      Sigma.desc fun i => (D.refl i (D.U i) (𝟙 _)).choose ≫
        Sigma.ι (fun p : I × I => D.R p.1 p.2) (i, i)
    have hu : unit ≫ D.first = 𝟙 _ := by
      apply Sigma.hom_ext
      intro i
      simpa [unit] using congrArg (· ≫ Sigma.ι D.U i)
        (D.refl i (D.U i) (𝟙 _)).choose_spec.1
    have hu' : unit ≫ D.second = 𝟙 _ := by
      apply Sigma.hom_ext
      intro i
      simpa [unit] using congrArg (· ≫ Sigma.ι D.U i)
        (D.refl i (D.U i) (𝟙 _)).choose_spec.2
    exact ⟨a ≫ unit, by simp [hu], by simp [hu']⟩
  symm T r := by
    let swap : D.relationScheme ⟶ D.relationScheme :=
      Sigma.desc fun p : I × I => (D.symm p.1 p.2 (D.R p.1 p.2) (𝟙 _)).choose ≫
        Sigma.ι (fun p : I × I => D.R p.1 p.2) (p.2, p.1)
    have hv : swap ≫ D.first = D.second := by
      apply Sigma.hom_ext
      intro p
      simpa [swap, first, second] using congrArg (· ≫ Sigma.ι D.U p.2)
        (D.symm p.1 p.2 (D.R p.1 p.2) (𝟙 _)).choose_spec.1
    have hv' : swap ≫ D.second = D.first := by
      apply Sigma.hom_ext
      intro p
      simpa [swap, first, second] using congrArg (· ≫ Sigma.ι D.U p.1)
        (D.symm p.1 p.2 (D.R p.1 p.2) (𝟙 _)).choose_spec.2
    exact ⟨r ≫ swap, by simp [hv], by simp [hv']⟩
  trans T r r' hrr' := by
    let f := fun p : I × I => D.s p.1 p.2 ≫ Sigma.ι D.U p.2
    let g := fun p : I × I => D.t p.1 p.2 ≫ Sigma.ι D.U p.1
    let P := fun p : (I × I) × (I × I) => pullback (f p.1) (g p.2)
    have hc (p : (I × I) × (I × I)) :
        ∃ c : P p ⟶ D.relationScheme,
          c ≫ D.first = pullback.fst (f p.1) (g p.2) ≫
            D.t p.1.1 p.1.2 ≫ Sigma.ι D.U p.1.1 ∧
          c ≫ D.second = pullback.snd (f p.1) (g p.2) ≫
            D.s p.2.1 p.2.2 ≫ Sigma.ι D.U p.2.2 :=
      D.exists_composite _ _ _ _ (pullback.fst _ _) (pullback.snd _ _)
        (by simpa [f, g] using pullback.condition (f := f p.1) (g := g p.2))
    let c : (∐ P) ⟶ D.relationScheme := Sigma.desc fun p => (hc p).choose
    have hp := FinitaryPreExtensive.isPullback_sigmaDesc f g
    let lift : T ⟶ ∐ P := hp.lift r r' hrr'
    refine ⟨lift ≫ c, ?_, ?_⟩
    · have he : c ≫ D.first =
          (Sigma.desc fun p : (I × I) × (I × I) =>
            pullback.fst (f p.1) (g p.2) ≫
              Sigma.ι (fun p : I × I => D.R p.1 p.2) p.1) ≫ D.first := by
        apply Sigma.hom_ext
        intro p
        simpa [c, P, first, Category.assoc] using (hc p).choose_spec.1
      rw [Category.assoc, he, ← Category.assoc]
      exact congrArg (· ≫ D.first) (hp.lift_fst r r' hrr')
    · have he : c ≫ D.second =
          (Sigma.desc fun p : (I × I) × (I × I) =>
            pullback.snd (f p.1) (g p.2) ≫
              Sigma.ι (fun p : I × I => D.R p.1 p.2) p.2) ≫ D.second := by
        apply Sigma.hom_ext
        intro p
        simpa [c, P, second, Category.assoc] using (hc p).choose_spec.2
      rw [Category.assoc, he, ← Category.assoc]
      exact congrArg (· ≫ D.second) (hp.lift_snd r r' hrr')

instance toEtaleEquivalenceRelation_joint_isClosedImmersion :
    IsClosedImmersion
      (prod.lift D.toEtaleEquivalenceRelation.t D.toEtaleEquivalenceRelation.s) :=
  D.joint_isClosedImmersion

instance objectScheme_isAffine [∀ i, IsAffine (D.U i)] : IsAffine D.objectScheme := by
  dsimp [objectScheme]
  infer_instance

instance relationScheme_isAffine [∀ i j, IsAffine (D.R i j)] : IsAffine D.relationScheme := by
  dsimp [relationScheme]
  infer_instance

instance toEtaleEquivalenceRelation_object_isAffine [∀ i, IsAffine (D.U i)] :
    IsAffine D.toEtaleEquivalenceRelation.U :=
  D.objectScheme_isAffine

instance toEtaleEquivalenceRelation_relation_isAffine [∀ i j, IsAffine (D.R i j)] :
    IsAffine D.toEtaleEquivalenceRelation.R :=
  D.relationScheme_isAffine

end FiniteSchemeRelation
end Langlands.AlgebraicGeometry

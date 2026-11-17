import Langlands.GroupScheme.Reductive.SimpleFactorPoints
import Langlands.GroupScheme.Reductive.AlmostSimpleNormalSubgroup
import Langlands.GroupScheme.Reductive.NormalSemisimpleProof
import Langlands.GroupScheme.Reductive.Noncommutativity
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.SubgroupRangeTransport

/-! # Almost-simple covers of semisimple groups over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SimpleFactor

section General

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- A homomorphism carries commuting points to commuting points. -/
theorem commute_comp (f : H ⟶ G) {T : Over S} {x y : T ⟶ H.X} (h : Commute x y) :
    Commute (x ≫ f.hom.hom) (y ≫ f.hom.hom) := by
  unfold Commute SemiconjBy at h ⊢
  rw [← MonObj.mul_comp, ← MonObj.mul_comp, h]

/-- A monomorphic homomorphism reflects commutation of points. -/
theorem commute_of_commute_comp (f : H ⟶ G) [Mono f.hom.hom] {T : Over S} {x y : T ⟶ H.X}
    (h : Commute (x ≫ f.hom.hom) (y ≫ f.hom.hom)) : Commute x y := by
  unfold Commute SemiconjBy at h ⊢
  apply (cancel_mono f.hom.hom).1
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact h

/-- A monomorphic homomorphism out of a group whose points do not all commute has nontrivial
range. -/
theorem range_ne_bot_of_noncommutative (j : H ⟶ G) [Mono j.hom.hom]
    (h : ¬ ∀ (T : Over S) (x y : T ⟶ H.X), Commute x y) :
    SubgroupFunctor.range j ≠ ⊥ := by
  intro hj
  apply h
  intro T x y
  have h1 : SubgroupFunctor.range (𝟙 H) = ⊥ :=
    (SubgroupFunctor.range_comp_eq_bot_iff (𝟙 H) j).1 (by rwa [Category.id_comp])
  rw [SubgroupFunctor.range_id] at h1
  have hx : x ∈ (⊤ : SubgroupFunctor H).carrier T := by simp
  have hy : y ∈ (⊤ : SubgroupFunctor H).carrier T := by simp
  rw [h1, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx hy
  subst hx hy
  exact Commute.refl _

end General

variable {k : Type u} [Field k]

/-- A smooth connected closed normal subgroup, in the sense of the decomposition statement. -/
def IsNormalSmooth {H K : GroupScheme (Spec (CommRingCat.of k))} (n : K ⟶ H) : Prop :=
  IsClosedSubgroup n ∧ Smooth K.X.hom ∧ ConnectedSpace K.X.left ∧
    (SubgroupFunctor.range n).IsNormal

/-- A minimal nontrivial smooth connected closed normal subgroup, in the sense of the
decomposition statement. -/
def IsMinimalNormalSmooth {H K : GroupScheme (Spec (CommRingCat.of k))} (n : K ⟶ H) : Prop :=
  IsNormalSmooth n ∧ SubgroupFunctor.range n ≠ ⊥ ∧
    ∀ (K' : GroupScheme (Spec (CommRingCat.of k))) (n' : K' ⟶ H),
      IsNormalSmooth n' → SubgroupFunctor.range n' ≠ ⊥ →
      SubgroupFunctor.range n' ≤ SubgroupFunctor.range n →
      SubgroupFunctor.range n' = SubgroupFunctor.range n

variable {G H K : GroupScheme (Spec (CommRingCat.of k))}

/-- A monomorphic homomorphism out of a semisimple group whose image is commutative is
trivial. -/
theorem range_eq_bot_of_commute (hH : IsSemisimple H) (j : H ⟶ G) [Mono j.hom.hom]
    (h : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ H.X),
      Commute (x ≫ j.hom.hom) (y ≫ j.hom.hom)) :
    SubgroupFunctor.range j = ⊥ := by
  have h1 : SubgroupFunctor.range (𝟙 H) = ⊥ := by
    by_contra hne
    exact hH.noncommutative_of_nontrivial hne fun T x y => commute_of_commute_comp j (h T x y)
  have h2 := (SubgroupFunctor.range_comp_eq_bot_iff (𝟙 H) j).2 h1
  rwa [Category.id_comp] at h2

/-- A smooth connected closed normal subgroup of a semisimple group that lies in its own
commutant is trivial. -/
theorem range_eq_bot_of_le_commutant (hG : IsSemisimple G) (n : K ⟶ G) (hn : IsNormalSmooth n)
    (h : SubgroupFunctor.range n ≤ commutant (SubgroupFunctor.range n)) :
    SubgroupFunctor.range n = ⊥ := by
  obtain ⟨hc, hs, hcon, hnor⟩ := hn
  have hK : IsSemisimple K := hG.of_normalSubgroup n hc hnor
  have := hc.mono_overHom
  apply range_eq_bot_of_commute hK n
  intro T x y
  exact (range_le_commutant_iff n _).1 h T x (y ≫ n.hom.hom)
    (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)

/-- Points of a subgroup functor lying in the commutant of a range commute with the points of
that range. -/
theorem le_commutant_range_iff (F : SubgroupFunctor G) (n : K ⟶ G) :
    F ≤ commutant (SubgroupFunctor.range n) ↔
      ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (y : T ⟶ K.X),
        g ∈ F.carrier T → Commute g (y ≫ n.hom.hom) := by
  constructor
  · intro h T g y hg
    exact commute_of_mem_commutant (h T hg) (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
  · intro h T g hg T' a x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    exact h T' (a ≫ g) y (F.comp_mem a hg)

/-- A finite family of almost-simple groups together with a quasi-compact, flat, surjective
homomorphism from their product onto `G` that embeds each factor as a closed subgroup. -/
structure AlmostSimpleCover (G : GroupScheme (Spec (CommRingCat.of k))) where
  /-- The index set of the factors. -/
  Index : Type u
  [finite : Finite Index]
  /-- The almost-simple factors. -/
  factor : Index → GroupScheme (Spec (CommRingCat.of k))
  isAlmostSimple : ∀ i, IsAlmostSimple (factor i)
  /-- The multiplication homomorphism from the product of the factors. -/
  mul : pi factor ⟶ G
  [quasiCompact : QuasiCompact mul.hom.hom.left]
  [flat : Flat mul.hom.hom.left]
  [surjective : Surjective mul.hom.hom.left]
  isClosedSubgroup : ∀ i, IsClosedSubgroup (piFactorInclusionHom factor i ≫ mul)

attribute [instance] AlmostSimpleCover.finite AlmostSimpleCover.quasiCompact
  AlmostSimpleCover.flat AlmostSimpleCover.surjective

namespace AlmostSimpleCover

variable (D : AlmostSimpleCover G)

/-- The embedding of a factor into `G`. -/
def inclusion (i : D.Index) : D.factor i ⟶ G :=
  piFactorInclusionHom D.factor i ≫ D.mul

theorem isClosedSubgroup_inclusion (i : D.Index) : IsClosedSubgroup (D.inclusion i) :=
  D.isClosedSubgroup i

instance mono_inclusion (i : D.Index) : Mono (D.inclusion i).hom.hom :=
  (D.isClosedSubgroup_inclusion i).mono_overHom

theorem smooth_factor (i : D.Index) : Smooth (D.factor i).X.hom :=
  (D.isAlmostSimple i).isSemisimple.isConnectedReductive.smooth

theorem connectedSpace_factor (i : D.Index) : ConnectedSpace (D.factor i).X.left :=
  (D.isAlmostSimple i).isSemisimple.isConnectedReductive.connectedSpace

theorem comp_inclusion_hom (i : D.Index) {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (D.factor i).X) :
    x ≫ (D.inclusion i).hom.hom =
      (x ≫ (piFactorInclusionHom D.factor i).hom.hom) ≫ D.mul.hom.hom := by
  rw [inclusion, Grp.comp_hom_hom, Category.assoc]

/-- Each factor is normal in `G`. -/
theorem isNormal_range_inclusion (i : D.Index) :
    (SubgroupFunctor.range (D.inclusion i)).IsNormal := by
  apply isNormal_range_of_lift D.mul (D.inclusion i)
  intro T z x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.1
    (isNormal_range_piFactorInclusionHom D.factor i T z
      (y ≫ (piFactorInclusionHom D.factor i).hom.hom) trivial
      (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩))
  refine SubgroupFunctor.mem_range.2 ⟨y', ?_⟩
  rw [comp_inclusion_hom, hy', comp_inclusion_hom, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp]

/-- Distinct factors commute. -/
theorem commute_inclusion {i j : D.Index} (hij : i ≠ j) {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (D.factor i).X) (y : T ⟶ (D.factor j).X) :
    Commute (x ≫ (D.inclusion i).hom.hom) (y ≫ (D.inclusion j).hom.hom) := by
  rw [comp_inclusion_hom, comp_inclusion_hom]
  exact commute_comp D.mul (commute_piFactorInclusionHom D.factor hij x y)

/-- Distinct factors lie in each other's commutants. -/
theorem range_inclusion_le_commutant {i j : D.Index} (hij : i ≠ j) :
    SubgroupFunctor.range (D.inclusion i) ≤
      commutant (SubgroupFunctor.range (D.inclusion j)) := by
  rw [le_commutant_range_iff]
  intro T g y hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hg
  exact D.commute_inclusion hij x y

theorem range_inclusion_ne_bot (i : D.Index) : SubgroupFunctor.range (D.inclusion i) ≠ ⊥ :=
  range_ne_bot_of_noncommutative (D.inclusion i) (D.isAlmostSimple i).noncommutative

theorem isNormalSmooth_inclusion (i : D.Index) : IsNormalSmooth (D.inclusion i) :=
  ⟨D.isClosedSubgroup_inclusion i, D.smooth_factor i, D.connectedSpace_factor i,
    D.isNormal_range_inclusion i⟩

/-- A factor either lies in a smooth connected closed normal subgroup or lies in its
commutant. -/
theorem range_le_or_le_commutant (hG : IsSemisimple G) (i : D.Index) (n : K ⟶ G)
    (hn : IsNormalSmooth n) :
    SubgroupFunctor.range (D.inclusion i) ≤ SubgroupFunctor.range n ∨
      SubgroupFunctor.range (D.inclusion i) ≤ commutant (SubgroupFunctor.range n) := by
  obtain ⟨hc, hs, hcon, hnor⟩ := hn
  have : Smooth G.X.hom := hG.isConnectedReductive.smooth
  have : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  rcases (D.isAlmostSimple i).range_le_or_commute_of_normal (D.inclusion i) n
    (D.isClosedSubgroup_inclusion i) hc (D.isNormal_range_inclusion i) hnor with h | h
  · exact Or.inl h
  · refine Or.inr ((le_commutant_range_iff _ n).2 ?_)
    intro T g y hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    exact h T x y

/-- Each factor is a minimal nontrivial smooth connected closed normal subgroup. -/
theorem isMinimalNormalSmooth_inclusion (hG : IsSemisimple G) (i : D.Index) :
    IsMinimalNormalSmooth (D.inclusion i) := by
  refine ⟨D.isNormalSmooth_inclusion i, D.range_inclusion_ne_bot i, ?_⟩
  intro K' n' hn' hne hle
  rcases D.range_le_or_le_commutant hG i n' hn' with h | h
  · exact le_antisymm hle h
  · exact absurd (range_eq_bot_of_le_commutant hG n' hn' (hle.trans h)) hne

/-- If every factor lies in the commutant of a subgroup functor, so does all of `G`. -/
theorem top_le_commutant (F : SubgroupFunctor G)
    (h : ∀ i, SubgroupFunctor.range (D.inclusion i) ≤ commutant F) :
    (⊤ : SubgroupFunctor G) ≤ commutant F := by
  have hmul : SubgroupFunctor.range D.mul ≤ commutant F :=
    range_le_of_forall_factor D.factor D.mul _ h
  have h1 := range_le_commutant_of_comp D.mul (𝟙 G) F (by rwa [Category.comp_id])
  rwa [SubgroupFunctor.range_id] at h1

/-- Every minimal nontrivial smooth connected closed normal subgroup is one of the factors. -/
theorem exists_range_eq_inclusion (hG : IsSemisimple G) (n : K ⟶ G)
    (hn : IsMinimalNormalSmooth n) :
    ∃ i, SubgroupFunctor.range n = SubgroupFunctor.range (D.inclusion i) := by
  by_contra hne
  push Not at hne
  have h : ∀ i, SubgroupFunctor.range (D.inclusion i) ≤ commutant (SubgroupFunctor.range n) := by
    intro i
    rcases D.range_le_or_le_commutant hG i n hn.1 with h | h
    · exact absurd (hn.2.2 _ (D.inclusion i) (D.isNormalSmooth_inclusion i)
        (D.range_inclusion_ne_bot i) h).symm (hne i)
    · exact h
  exact hn.2.1 (range_eq_bot_of_le_commutant hG n hn.1
    (fun T x _ => D.top_le_commutant _ h T trivial))

/-- Distinct factors have distinct images. -/
theorem injective_range_inclusion (hG : IsSemisimple G) :
    Function.Injective (fun i => SubgroupFunctor.range (D.inclusion i)) := by
  intro i j h
  by_contra hij
  have h' : SubgroupFunctor.range (D.inclusion i) ≤
      commutant (SubgroupFunctor.range (D.inclusion i)) := by
    have := D.range_inclusion_le_commutant hij
    simp only at h
    rwa [← h] at this
  exact D.range_inclusion_ne_bot i
    (range_eq_bot_of_le_commutant hG _ (D.isNormalSmooth_inclusion i) h')

/-- The set of factors contained in a given subgroup. -/
def support (n : K ⟶ G) : Set D.Index :=
  {i | SubgroupFunctor.range (D.inclusion i) ≤ SubgroupFunctor.range n}

theorem mem_support {n : K ⟶ G} {i : D.Index} :
    i ∈ D.support n ↔ SubgroupFunctor.range (D.inclusion i) ≤ SubgroupFunctor.range n :=
  Iff.rfl

/-- The factors outside the support of a smooth connected closed normal subgroup lie in its
commutant. -/
theorem range_le_commutant_of_notMem_support (hG : IsSemisimple G) {n : K ⟶ G}
    (hn : IsNormalSmooth n) {i : D.Index} (hi : i ∉ D.support n) :
    SubgroupFunctor.range (D.inclusion i) ≤ commutant (SubgroupFunctor.range n) :=
  (D.range_le_or_le_commutant hG i n hn).resolve_left hi

/-- A commuting complement with central-isogeny multiplication contains exactly the factors
not contained in the given subgroup. -/
theorem mem_support_complement_iff (hG : IsSemisimple G) {n : K ⟶ G} (hn : IsNormalSmooth n)
    {K' : GroupScheme (Spec (CommRingCat.of k))} {n' : K' ⟶ G} (hn' : IsNormalSmooth n')
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ K.X) (y : T ⟶ K'.X),
      Commute (x ≫ n.hom.hom) (y ≫ n'.hom.hom))
    (hm : IsCentralIsogeny (commutingSubgroupMultiplicationHom n n' hc)) (i : D.Index) :
    i ∈ D.support n' ↔ i ∉ D.support n := by
  have hcomm : SubgroupFunctor.range n' ≤ commutant (SubgroupFunctor.range n) := by
    rw [le_commutant_range_iff]
    intro T g y hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    exact (hc T y x).symm
  constructor
  · intro hi' hi
    have h : SubgroupFunctor.range (D.inclusion i) ≤
        commutant (SubgroupFunctor.range (D.inclusion i)) :=
      (hi'.trans hcomm).trans (commutant_anti hi)
    exact D.range_inclusion_ne_bot i
      (range_eq_bot_of_le_commutant hG _ (D.isNormalSmooth_inclusion i) h)
  · intro hi
    by_contra hi'
    have h1 := D.range_le_commutant_of_notMem_support hG hn hi
    have h2 := D.range_le_commutant_of_notMem_support hG hn' hi'
    have : QuasiCompact (commutingSubgroupMultiplicationHom n n' hc).hom.hom.left := by
      have := hm.isFinite
      infer_instance
    have := hm.flat
    have := hm.surjective
    have h : SubgroupFunctor.range (D.inclusion i) ≤
        commutant (SubgroupFunctor.range (D.inclusion i)) := by
      rw [range_le_commutant_iff]
      intro T x y _
      apply commute_of_lift (commutingSubgroupMultiplicationHom n n' hc)
      intro W w z
      rw [comp_commutingSubgroupMultiplicationHom]
      have hx : w ≫ x ≫ (D.inclusion i).hom.hom ∈
          (SubgroupFunctor.range (D.inclusion i)).carrier W :=
        SubgroupFunctor.mem_range.2 ⟨w ≫ x, by rw [Category.assoc]⟩
      exact Commute.mul_right
        ((le_commutant_range_iff _ n).1 h1 W _ _ hx)
        ((le_commutant_range_iff _ n').1 h2 W _ _ hx)
    exact D.range_inclusion_ne_bot i
      (range_eq_bot_of_le_commutant hG _ (D.isNormalSmooth_inclusion i) h)

end AlmostSimpleCover

end Langlands.GroupScheme.SimpleFactor

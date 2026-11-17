import Langlands.GroupScheme.Reductive.FppfProductUnipotent
import Langlands.GroupScheme.Reductive.ReductiveSimpleFactorDecompositionStatement
import Langlands.GroupScheme.Reductive.SimpleFactorDecompositionStatement
import Langlands.GroupScheme.Reductive.MaximalCentralTorusFieldMultiplication
import Langlands.GroupScheme.Reductive.MultiplicationBaseChange
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Derived.StructureProof
import Langlands.GroupScheme.Derived.Action
import Langlands.GroupScheme.Derived.AlmostSimplePerfect
import Langlands.GroupScheme.Rational.NormalSolvableCentrality
import Langlands.GroupScheme.Absolute.RegularCocharacterSolvable
import Langlands.GroupScheme.CentralIsogeny.PerfectComposition
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.UnitSubgroup
import Langlands.GroupScheme.ProductCoordinateSmooth
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleConjugateProductGalois
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorGaloisAction
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Derived.ConnectedSmoothness
import Langlands.GroupScheme.Derived.CommutatorEnvelope

/-! # The reductive simple-factor decomposition from the semisimple one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme

namespace ReductiveSimpleFactorDecomposition

section Base

variable {S : Scheme.{u}}

/-- Tensoring a slice morphism on the left with an identity is its cartesian base change. -/
theorem isPullback_id_tensorHom {X Y : Over S} (f : X ⟶ Y) (Z : Over S) :
    IsPullback (𝟙 Z ⊗ₘ f) (snd Z X) (snd Z Y) f := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => lift (c.fst ≫ fst Z Y) c.snd) ?_ ?_ ?_⟩⟩
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa only [Category.assoc, tensorHom_snd, lift_snd_assoc] using c.condition.symm
  · intro c
    exact lift_snd _ _
  · intro c m hm hn
    apply CartesianMonoidalCategory.hom_ext
    · have hs := congrArg (fun a => a ≫ fst Z Y) hm
      simpa only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst] using hs
    · simpa using hn

/-- Taking a product with an identity on the left preserves central isogenies. -/
theorem isCentralIsogeny_id_tensor {C H : GroupScheme S} {f : C ⟶ H}
    (hf : IsCentralIsogeny f) (K : GroupScheme S) : IsCentralIsogeny (𝟙 K ⊗ₘ f) := by
  have hpb := ((isPullback_id_tensorHom f.hom.hom K.X).map (Over.forget S)).flip
  refine ⟨⟨MorphismProperty.of_isPullback hpb hf.isFinite,
    MorphismProperty.of_isPullback hpb hf.flat,
    MorphismProperty.of_isPullback hpb hf.surjective⟩,
    MorphismProperty.of_isPullback hpb hf.locallyOfFinitePresentation, ?_⟩
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  change x ≫ (𝟙 K.X ⊗ₘ f.hom.hom) = 1 at hx
  have hxC : (x ≫ snd K.X C.X) ≫ f.hom.hom = 1 := by
    have h := congrArg (fun w => w ≫ snd K.X H.X) hx
    simpa only [Category.assoc, tensorHom_snd, MonObj.one_comp] using h
  have hxK : x ≫ fst K.X C.X = 1 := by
    have h := congrArg (fun w => w ≫ fst K.X H.X) hx
    simpa only [Category.assoc, tensorHom_fst, Category.comp_id, MonObj.one_comp] using h
  intro T' a y
  change (a ≫ x) * y = y * (a ≫ x)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MonObj.mul_comp, Category.assoc, hxK, MonObj.comp_one, one_mul, mul_one]
  · simp only [MonObj.mul_comp, Category.assoc]
    exact (hf.mem_center_of_comp_eq_one hxC T' a (y ≫ snd K.X C.X)).eq

/-- Postcomposition with a monomorphism reflects inclusions of ranges. -/
theorem range_comp_le_range_comp_iff {H H' K G : GroupScheme S} (m : H ⟶ K) (m' : H' ⟶ K)
    (d : K ⟶ G) [Mono d.hom.hom] :
    SubgroupFunctor.range (m ≫ d) ≤ SubgroupFunctor.range (m' ≫ d) ↔
      SubgroupFunctor.range m ≤ SubgroupFunctor.range m' := by
  constructor
  · intro h T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp
      (h T (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩))
    refine SubgroupFunctor.mem_range.mpr ⟨y', ?_⟩
    apply (cancel_mono d.hom.hom).mp
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy'
  · intro h T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp
      (h T (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩))
    refine SubgroupFunctor.mem_range.mpr ⟨y', ?_⟩
    simp only [Grp.comp_hom_hom, ← Category.assoc, hy']

/-- Postcomposition with a monomorphism reflects equality of ranges. -/
theorem range_comp_eq_range_comp_iff {H H' K G : GroupScheme S} (m : H ⟶ K) (m' : H' ⟶ K)
    (d : K ⟶ G) [Mono d.hom.hom] :
    SubgroupFunctor.range (m ≫ d) = SubgroupFunctor.range (m' ≫ d) ↔
      SubgroupFunctor.range m = SubgroupFunctor.range m' := by
  constructor
  · intro h
    exact le_antisymm ((range_comp_le_range_comp_iff m m' d).mp h.le)
      ((range_comp_le_range_comp_iff m' m d).mp h.ge)
  · intro h
    exact le_antisymm ((range_comp_le_range_comp_iff m m' d).mpr h.le)
      ((range_comp_le_range_comp_iff m' m d).mpr h.ge)

/-- A homomorphism with trivial range is central. -/
theorem isCentral_of_range_eq_bot {H G : GroupScheme S} (n : H ⟶ G)
    (h : SubgroupFunctor.range n = ⊥) : IsCentral n := by
  intro T x
  have hx : x ≫ n.hom.hom ∈ (SubgroupFunctor.range n).carrier T :=
    SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  rw [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
  rw [hx]
  exact ((center G).carrier T).one_mem

/-- Centrality in the ambient group descends along a monic inclusion. -/
theorem commute_of_isCentral_comp {H K G : GroupScheme S} (m : H ⟶ K) (d : K ⟶ G)
    [Mono (m ≫ d).hom.hom] (hc : IsCentral (m ≫ d)) {T : Over S} (x y : T ⟶ H.X) :
    Commute x y := by
  apply (cancel_mono (m ≫ d).hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact commute_of_mem_center (hc T x) _

end Base

section Perfect

variable {k : Type u} [Field k] {H' H G : GroupScheme (Spec (CommRingCat.of k))}

/-- A variant of `IsCentralIsogeny.comp_of_derivedSubgroup_eq_top`: the composite of two
central isogenies is central as soon as every point of the source is a central point times
a point of the derived subgroup. -/
theorem isCentralIsogeny_comp_of_center_mul_derived {f : H' ⟶ H} {q : H ⟶ G}
    (hgen : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ H'.X), ∃ c e : T ⟶ H'.X,
      c ∈ (center H').carrier T ∧ e ∈ (derivedSubgroup H').carrier T ∧ g = c * e)
    (hf : IsCentralIsogeny f) (hq : IsCentralIsogeny q) : IsCentralIsogeny (f ≫ q) := by
  have hiso : IsIsogeny (f ≫ q) := IsIsogeny.comp hf.isIsogeny hq.isIsogeny
  have hlfp : LocallyOfFinitePresentation (f ≫ q).hom.hom.left := by
    have := hf.locallyOfFinitePresentation
    have := hq.locallyOfFinitePresentation
    change LocallyOfFinitePresentation (f.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  refine ⟨hiso, hlfp, ?_⟩
  have hfin : IsFinite (kernel (f ≫ q)).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme (f ≫ q)) hiso.1
  let a := AutomorphicAction.conjugation (kernelι (f ≫ q))
  obtain ⟨C, j, hj, hjc⟩ :=
    fieldFixedSubgroupRepresentability k (kernel (f ≫ q)) H' inferInstance a
  have hcomm : (SubgroupFunctor.range j).ContainsCommutators := by
    intro T x y
    rw [hj.2, AutomorphicAction.mem_fixedSubgroup]
    intro T' b h
    have hz : (h ≫ (kernelι (f ≫ q)).hom.hom) ≫ (f ≫ q).hom.hom = 1 :=
      (mem_range_kernelι_iff (f ≫ q) _).mp ⟨h, rfl⟩
    have hc := IsCentralIsogeny.commute_commutator_of_comp_eq_one hf hq hz (b ≫ x) (b ≫ y)
    rw [AutomorphicAction.conjugation_act]
    have hb : b ≫ (x * y * x⁻¹ * y⁻¹) = ⁅b ≫ x, b ≫ y⁆ := by
      rw [commutatorElement_def, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul,
        GrpObj.comp_inv, GrpObj.comp_inv]
    rw [hb, hc.eq, mul_inv_cancel_right]
  have hle : derivedSubgroup H' ≤ a.fixedSubgroup := by
    rw [← hj.2]
    exact derivedSubgroup_le_range j hjc hcomm
  apply (isCentral_kernelι_iff (f ≫ q)).mpr
  intro T x hx T' b g
  obtain ⟨c, e, hc, he, rfl⟩ := hgen T' g
  have hg : e ∈ a.fixedSubgroup.carrier T' := hle T' he
  have hbx : (b ≫ x) ≫ (f ≫ q).hom.hom = 1 := by
    rw [Category.assoc, hx, MonObj.comp_one]
  let h : T' ⟶ (kernel (f ≫ q)).X := (kernelPointsEquiv (f ≫ q) T').symm ⟨b ≫ x, hbx⟩
  have hh : h ≫ (kernelι (f ≫ q)).hom.hom = b ≫ x :=
    congrArg Subtype.val ((kernelPointsEquiv (f ≫ q) T').apply_symm_apply ⟨b ≫ x, hbx⟩)
  have e' := hg T' (𝟙 T') h
  simp only [a] at e'
  rw [Category.id_comp, AutomorphicAction.conjugation_act, hh] at e'
  exact Commute.mul_right (commute_of_mem_center hc (b ≫ x)).symm
    (mul_inv_eq_iff_eq_mul.mp e')

end Perfect

section Product

variable {S : Scheme.{u}} {I : Type u} [Finite I] (A : I → GroupScheme S)

/-- The scheme-level factor insertion is the underlying map of the homomorphic one. -/
theorem piFactorInclusion_eq_hom (j : I) :
    piFactorInclusion A j = (piFactorInclusionHom A j).hom.hom := by
  apply (piPointsEquiv A _).injective
  funext l
  rw [piPointsEquiv_apply, piPointsEquiv_apply]
  by_cases h : j = l
  · subst l
    rw [piFactorInclusion_self]
    simpa only [Category.id_comp] using
      (piFactorInclusionHom_points_self A j (𝟙 (A j).X)).symm
  · rw [piFactorInclusion_ne A j l h]
    simpa only [Category.id_comp] using
      (piFactorInclusionHom_points_ne A j l h (𝟙 (A j).X)).symm

/-- A finite product of perfect group schemes is perfect. -/
theorem derivedSubgroup_pi_eq_top (hA : ∀ i, derivedSubgroup (A i) = ⊤) :
    derivedSubgroup (pi A) = ⊤ := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  apply SubgroupFunctor.ext
  intro T
  rw [SubgroupFunctor.top_carrier, eq_top_iff]
  intro y _
  have hy : y = ((Finset.univ : Finset I).toList.map
      (fun j => (y ≫ (Pi.π A j).hom.hom) ≫ piFactorInclusion A j)).prod := by
    rw [← piPointsEquiv_symm_eq_list_prod A T (fun j => y ≫ (Pi.π A j).hom.hom) _
      (Finset.nodup_toList _) (fun j => Finset.mem_toList.mpr (Finset.mem_univ j))]
    exact ((piPointsEquiv A T).symm_apply_apply y).symm
  rw [hy]
  apply Subgroup.list_prod_mem
  intro w hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  rw [piFactorInclusion_eq_hom]
  apply mem_derivedSubgroup_comp
  rw [hA j]
  exact Subgroup.mem_top _

end Product

section Normality

variable {S : Scheme.{u}} {Z D G K : GroupScheme S}

/-- If the multiplication `Z × D ⟶ G` of a central subgroup `z` and a subgroup `d` is a
central isogeny, then every normal subgroup of `D` is normal in `G`: fpqc-locally every point
of `G` is `z(c) d(e)`, the central factor acts trivially and `d(e)` preserves the subgroup. -/
theorem isNormal_range_comp_of_isCentralIsogeny_mul (z : Z ⟶ G) (d : D ⟶ G)
    (hz : IsCentral z)
    (hc : ∀ (T : Over S) (h : T ⟶ Z.X) (x : T ⟶ D.X), Commute (h ≫ z.hom.hom) (x ≫ d.hom.hom))
    (hq : IsCentralIsogeny (commutingSubgroupMultiplicationHom z d hc))
    (n : K ⟶ D) [Mono (n ≫ d).hom.hom] (hn : (SubgroupFunctor.range n).IsNormal) :
    (SubgroupFunctor.range (n ≫ d)).IsNormal := by
  have := hq.flat
  have := hq.surjective
  have : QuasiCompact (commutingSubgroupMultiplicationHom z d hc).hom.hom.left := by
    have := hq.isFinite
    infer_instance
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply SubgroupFunctor.mem_range_of_local_quotient_lift
    (commutingSubgroupMultiplicationHom z d hc) (n ≫ d) g
  intro V a w hw
  rw [commutingSubgroupMultiplicationHom_hom, subgroupMultiplication, MonObj.comp_mul,
    ← Category.assoc, ← Category.assoc] at hw
  obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp
    (hn V (w ≫ snd Z.X D.X) ((a ≫ y) ≫ n.hom.hom) (Subgroup.mem_top _)
      (SubgroupFunctor.mem_range.mpr ⟨a ≫ y, rfl⟩))
  refine SubgroupFunctor.mem_range.mpr ⟨y', ?_⟩
  have hcen := commute_of_mem_center (hz V (w ≫ fst Z.X D.X))
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hw, Grp.comp_hom_hom,
    ← Category.assoc, hy', MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, mul_inv_rev]
  set c := (w ≫ fst Z.X D.X) ≫ z.hom.hom
  set e := (w ≫ snd Z.X D.X) ≫ d.hom.hom
  set m := ((a ≫ y) ≫ n.hom.hom) ≫ d.hom.hom
  have h1 : a ≫ y ≫ n.hom.hom ≫ d.hom.hom = m := by
    simp only [m, Category.assoc]
  rw [h1, show c * e * m * (e⁻¹ * c⁻¹) = c * (e * m * e⁻¹) * c⁻¹ by group,
    (hcen _).eq, mul_inv_cancel_right]

end Normality

section Multiplication

variable {S : Scheme.{u}}

/-- In `Z × P` with `Z` commutative and `P` perfect, every point is a central point times a
point of the derived subgroup: `(c, y) = (c, 1) * (1, y)`. -/
theorem tensor_center_mul_derived {Z P : GroupScheme S}
    (hZ : ∀ (T : Over S) (x y : T ⟶ Z.X), Commute x y) (hP : derivedSubgroup P = ⊤)
    (T : Over S) (g : T ⟶ (Z ⊗ P).X) : ∃ c e : T ⟶ (Z ⊗ P).X,
      c ∈ (center (Z ⊗ P)).carrier T ∧ e ∈ (derivedSubgroup (Z ⊗ P)).carrier T ∧
        g = c * e := by
  refine ⟨(productPointsEquiv Z P T).symm (g ≫ fst Z.X P.X, 1),
    (g ≫ snd Z.X P.X) ≫ (prodInr Z P).hom.hom, ?_, ?_, ?_⟩
  · intro T' a h
    apply (productPointsEquiv Z P T').injective
    rw [map_mul, map_mul, productPointsEquiv_naturality, MulEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · exact (hZ T' _ _).eq
    · simp only [Prod.snd_mul, MonObj.comp_one, one_mul, mul_one]
  · apply mem_derivedSubgroup_comp
    rw [hP]
    exact Subgroup.mem_top _
  · apply (productPointsEquiv Z P T).injective
    rw [map_mul, MulEquiv.apply_symm_apply, prodInr, comp_homOfPoints]
    simp [inrPoints]
    rfl

/-- Over a field, the multiplication `Z × P ⟶ G`, `(c, y) ↦ z(c) d(p(y))`, is a central
isogeny when `Z × D ⟶ G` is, `p : P ⟶ D` is a central isogeny, `z` is a central monomorphism
and `P` is perfect. -/
theorem isCentralIsogeny_prodHom_comp {k : Type u} [Field k]
    {Z D G P : GroupScheme (Spec (CommRingCat.of k))}
    (z : Z ⟶ G) (d : D ⟶ G) (hz : IsCentral z) [Mono z.hom.hom]
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ Z.X) (x : T ⟶ D.X),
      Commute (h ≫ z.hom.hom) (x ≫ d.hom.hom))
    (hq : IsCentralIsogeny (commutingSubgroupMultiplicationHom z d hc))
    (p : P ⟶ D) (hp : IsCentralIsogeny p) (hP : derivedSubgroup P = ⊤) :
    IsCentralIsogeny (prodHom z (p ≫ d) (hz.commute_values (p ≫ d))) := by
  have heq : prodHom z (p ≫ d) (hz.commute_values (p ≫ d)) =
      (𝟙 Z ⊗ₘ p) ≫ commutingSubgroupMultiplicationHom z d hc := by
    apply hom_ext_points
    intro T x
    rw [comp_prodHom]
    change _ = (x ≫ (𝟙 Z.X ⊗ₘ p.hom.hom)) ≫ subgroupMultiplication z d
    rw [subgroupMultiplication, MonObj.comp_mul]
    simp only [productPointsEquiv_fst, productPointsEquiv_snd, tensorHom_fst_assoc,
      tensorHom_snd_assoc, Category.id_comp, Grp.comp_hom_hom, Category.assoc]
  have hZ : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ Z.X), Commute x y := by
    intro T x y
    apply (cancel_mono z.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    exact (commute_of_mem_center (hz T x) _).eq
  rw [heq]
  exact isCentralIsogeny_comp_of_center_mul_derived (tensor_center_mul_derived hZ hP)
    (isCentralIsogeny_id_tensor hp Z) hq

/-- Precomposing the second factor of a product homomorphism with an isomorphism. -/
theorem prodHom_iso_comp {Z P P' G : GroupScheme S} (z : Z ⟶ G) (hz : IsCentral z)
    (Φ : P ≅ P') (p : P' ⟶ G) :
    prodHom z (Φ.hom ≫ p) (hz.commute_values _) =
      (tensorIso (Iso.refl Z) Φ).hom ≫ prodHom z p (hz.commute_values p) := by
  apply hom_ext_points
  intro T x
  rw [comp_prodHom]
  change _ = (x ≫ (𝟙 Z.X ⊗ₘ Φ.hom.hom.hom)) ≫ (prodHom z p (hz.commute_values p)).hom.hom
  rw [comp_prodHom]
  simp only [productPointsEquiv_fst, productPointsEquiv_snd, tensorHom_fst_assoc,
    tensorHom_snd_assoc, Category.id_comp, Grp.comp_hom_hom, Category.assoc]

end Multiplication

section Transport

/-- Two injective families with the same values are related by a bijection of indices. -/
theorem exists_equiv_of_injective {α : Sort*} {I I' : Type*} (f : I → α) (g : I' → α)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ i, ∃ j, f i = g j) (hgf : ∀ j, ∃ i, g j = f i) :
    ∃ ε : I ≃ I', ∀ i, f i = g (ε i) := by
  choose σ hσ using hfg
  choose τ hτ using hgf
  exact ⟨⟨σ, τ, fun i => hf ((hτ (σ i)).symm.trans (hσ i).symm),
    fun j => hg ((hσ (τ j)).symm.trans (hτ j).symm)⟩, hσ⟩

variable {S : Scheme.{u}}

/-- Two families of closed subgroups with equal images, matched by a bijection of indices,
have isomorphic products, compatibly with the factor insertions. -/
theorem exists_pi_iso_of_range_eq {I I' : Type u} [Finite I] [Finite I']
    {A : I → GroupScheme S} {A' : I' → GroupScheme S} {D : GroupScheme S}
    (a : ∀ i, A i ⟶ D) (a' : ∀ j, A' j ⟶ D)
    (ha : ∀ i, IsClosedSubgroup (a i)) (ha' : ∀ j, IsClosedSubgroup (a' j)) (ε : I ≃ I')
    (h : ∀ i, SubgroupFunctor.range (a i) = SubgroupFunctor.range (a' (ε i))) :
    ∃ (w : ∀ i, A i ≅ A' (ε i)) (Φ : pi A ≅ pi A'),
      (∀ i, (w i).hom ≫ a' (ε i) = a i) ∧
      ∀ i, piFactorInclusionHom A i ≫ Φ.hom = (w i).hom ≫ piFactorInclusionHom A' (ε i) := by
  let w : ∀ i, A i ≅ A' (ε i) := fun i => (ha i).sourceIsoOfRangeEq (ha' (ε i)) (h i)
  refine ⟨w, Pi.mapIso w ≪≫ Pi.reindex ε A' ≪≫ Iso.refl _,
    fun i => IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ _, fun i => ?_⟩
  rw [piFactorInclusionHom_comparison A A' ε w (Iso.refl _) i, Iso.refl_hom, Category.comp_id]

end Transport

section Main

variable {k : Type u} [Field k]

/-- A smooth connected closed normal subgroup (the predicate `IsNormalSubgroup` of the
statements). -/
def IsSmoothConnectedNormal {H K : GroupScheme (Spec (CommRingCat.of k))} (n : K ⟶ H) : Prop :=
  IsClosedSubgroup n ∧ Smooth K.X.hom ∧ ConnectedSpace K.X.left ∧
    (SubgroupFunctor.range n).IsNormal

/-- A minimal nontrivial smooth connected closed normal subgroup (the predicate
`IsMinimalNormalSubgroup` of the statements). -/
def IsMinimalSmoothConnectedNormal {H K : GroupScheme (Spec (CommRingCat.of k))}
    (n : K ⟶ H) : Prop :=
  IsSmoothConnectedNormal n ∧ SubgroupFunctor.range n ≠ ⊥ ∧
    ∀ (K' : GroupScheme (Spec (CommRingCat.of k))) (n' : K' ⟶ H),
      IsSmoothConnectedNormal n' → SubgroupFunctor.range n' ≠ ⊥ →
      SubgroupFunctor.range n' ≤ SubgroupFunctor.range n →
      SubgroupFunctor.range n' = SubgroupFunctor.range n

/-- A minimal non-central smooth connected closed normal subgroup (the predicate
`IsMinimalNoncentralNormalSubgroup` of the target statement). -/
def IsMinimalNoncentralSmoothConnectedNormal {H K : GroupScheme (Spec (CommRingCat.of k))}
    (n : K ⟶ H) : Prop :=
  IsSmoothConnectedNormal n ∧ ¬ IsCentral n ∧
    ∀ (K' : GroupScheme (Spec (CommRingCat.of k))) (n' : K' ⟶ H),
      IsSmoothConnectedNormal n' → ¬ IsCentral n' →
      SubgroupFunctor.range n' ≤ SubgroupFunctor.range n →
      SubgroupFunctor.range n' = SubgroupFunctor.range n

/-- If `a` is a minimal nontrivial smooth connected closed normal subgroup of `D` and
`d : D ⟶ G` is a closed subgroup, every non-central smooth connected closed normal subgroup of
`G` contained in `a ≫ d` equals it. -/
theorem range_eq_of_le_comp {G D A K' : GroupScheme (Spec (CommRingCat.of k))}
    (d : D ⟶ G) (hd : IsClosedSubgroup d) (a : A ⟶ D) (ha : IsMinimalSmoothConnectedNormal a)
    (n' : K' ⟶ G) (hn' : IsSmoothConnectedNormal n') (hnc : ¬ IsCentral n')
    (hle : SubgroupFunctor.range n' ≤ SubgroupFunctor.range (a ≫ d)) :
    SubgroupFunctor.range n' = SubgroupFunctor.range (a ≫ d) := by
  have : IsClosedImmersion d.hom.hom.left := hd
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have hrep : (SubgroupFunctor.range d).IsRepresentedBy d := ⟨inferInstance, rfl⟩
  have hle' : SubgroupFunctor.range n' ≤ SubgroupFunctor.range d := by
    intro T x hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hle T hx)
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ a.hom.hom, ?_⟩
    rw [← hy, Grp.comp_hom_hom, Category.assoc]
  obtain ⟨m, rfl⟩ : ∃ m, m ≫ d = n' := ⟨_, hrep.factorHom_comp n' hle'⟩
  have hmc : IsClosedSubgroup m := IsClosedSubgroup.of_comp hd hn'.1
  have hmn : (SubgroupFunctor.range m).IsNormal :=
    SubgroupFunctor.isNormal_range_of_mono_comp m d hn'.2.2.2
  have hmle : SubgroupFunctor.range m ≤ SubgroupFunctor.range a :=
    (range_comp_le_range_comp_iff m a d).mp hle
  have hmne : SubgroupFunctor.range m ≠ ⊥ := by
    intro hbot
    apply hnc
    intro T x
    have hx : x ≫ m.hom.hom ∈ (SubgroupFunctor.range m).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    rw [Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]
    exact ((center G).carrier T).one_mem
  exact (range_comp_eq_range_comp_iff m a d).mpr
    (ha.2.2 K' m ⟨hmc, hn'.2.1, hn'.2.2.1, hmn⟩ hmne hmle)

/-- The reductive simple-factor decomposition for a fixed group, assuming the semisimple
decomposition theorem, with the statement's local predicates replaced by named ones. -/
theorem main (hS1 : SimpleFactorDecompositionStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {Z : GroupScheme (Spec (CommRingCat.of k))} (z : Z ⟶ G) (hz : IsCentral z)
    (hzc : IsClosedSubgroup z) (hZ : IsTorus Z)
    (hzmax : ∀ (Z' : GroupScheme (Spec (CommRingCat.of k))) (z' : Z' ⟶ G),
      IsClosedSubgroup z' → IsCentral z' → IsTorus Z' →
      SubgroupFunctor.range z' ≤ SubgroupFunctor.range z)
    {D : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (I : Type u) [Finite I] (A : I → GroupScheme (Spec (CommRingCat.of k)))
    (a : ∀ i, A i ⟶ D)
    (ha_min : ∀ i, IsMinimalSmoothConnectedNormal (a i))
    (ha_inj : Function.Injective (fun i => SubgroupFunctor.range (a i)))
    (ha_exh : ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (n : K ⟶ D),
      IsMinimalSmoothConnectedNormal n →
        ∃ i, SubgroupFunctor.range n = SubgroupFunctor.range (a i)) :
    (∀ i, IsMinimalNoncentralSmoothConnectedNormal (a i ≫ d)) ∧
    (∀ (K : GroupScheme (Spec (CommRingCat.of k))) (n : K ⟶ G),
      IsMinimalNoncentralSmoothConnectedNormal n →
        ∃ i, SubgroupFunctor.range n = SubgroupFunctor.range (a i ≫ d)) ∧
    (∃ p : pi A ⟶ G, (∀ i, piFactorInclusionHom A i ≫ p = a i ≫ d) ∧
      IsCentralIsogeny (prodHom z p (hz.commute_values p))) ∧
    ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (n : K ⟶ D),
      IsSmoothConnectedNormal n → IsSemisimple K → (SubgroupFunctor.range (n ≫ d)).IsNormal := by
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion z.hom.hom.left := hzc
  have : Mono z.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have hDss : IsSemisimple D := derivedSubgroupSemisimple k G D d hG hd
  have hzT : IsMaximalCentralRelativeTorus z :=
    ⟨hzc, hz, hZ.isRelativeTorus, fun Z' z' h1 h2 h3 => hzmax Z' z' h1 h2 h3.isTorus⟩
  have hq := hzT.isCentralIsogeny_commutingMultiplication hG d hd.1 hd.containsCommutators
    hDss.hasFiniteCenter
  -- clause 3: normal subgroups of `D` are normal in `G`
  have h3 : ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (n : K ⟶ D),
      IsSmoothConnectedNormal n → (SubgroupFunctor.range (n ≫ d)).IsNormal := by
    intro K n hn
    have : IsClosedImmersion (n ≫ d).hom.hom.left := hn.1.comp hd.1
    have : Mono (n ≫ d).hom.hom := Over.mono_of_mono_left _
    exact isNormal_range_comp_of_isCentralIsogeny_mul z d hz _ hq n hn.2.2.2
  -- the semisimple decomposition of `D`
  obtain ⟨I', hI', A', a', ha'_min, ha'_inj, ha'_exh, hAS, -, ⟨p', hp'inc, hp'⟩, B, b, -, hBle,
    hBlub, -, -, hJ, -⟩ := hS1 k D hDss
  obtain ⟨ε, hε⟩ := exists_equiv_of_injective (fun i => SubgroupFunctor.range (a i))
    (fun j => SubgroupFunctor.range (a' j)) ha_inj ha'_inj
    (fun i => ha'_exh (A i) (a i) (ha_min i)) (fun j => ha_exh (A' j) (a' j) (ha'_min j))
  obtain ⟨w, Φ, hw, hΦ⟩ := exists_pi_iso_of_range_eq a a' (fun i => (ha_min i).1.1)
    (fun j => (ha'_min j).1.1) ε hε
  have hA : ∀ i, IsAlmostSimple (A i) := fun i => (hAS (ε i)).of_iso (w i)
  -- clause 1, first half
  have h1a : ∀ i, IsMinimalNoncentralSmoothConnectedNormal (a i ≫ d) := by
    intro i
    have : IsClosedImmersion (a i ≫ d).hom.hom.left := (ha_min i).1.1.comp hd.1
    have : Mono (a i ≫ d).hom.hom := Over.mono_of_mono_left _
    refine ⟨⟨(ha_min i).1.1.comp hd.1, (ha_min i).1.2.1, (ha_min i).1.2.2.1,
      h3 _ _ (ha_min i).1⟩, ?_, ?_⟩
    · intro hc
      exact (hA i).noncommutative fun T x y => commute_of_isCentral_comp (a i) d hc x y
    · intro K' n' hn' hnc hle
      exact range_eq_of_le_comp d hd.1 (a i) (ha_min i) n' hn' hnc hle
  refine ⟨h1a, ?_, ?_, fun K n hn _ => h3 K n hn⟩
  · -- clause 1, second half
    intro K n hn
    obtain ⟨⟨hnc, hnsm, hnconn, hnn⟩, hncen, hnmin⟩ := hn
    have : IsClosedImmersion n.hom.hom.left := hnc
    have : Mono n.hom.hom := Over.mono_of_mono_left _
    have : IsAffineHom K.X.hom := by
      rw [← Over.w n.hom.hom]
      infer_instance
    have : Smooth K.X.hom := hnsm
    let E := smoothConnectedCommutatorImage k K hnsm inferInstance hnconn
    have hE := E.val.isDerivedSubgroup
    have : GeometricallyConnected E.val.group.X.hom := E.property.2.2.1
    have hEconn : ConnectedSpace E.val.group.X.left :=
      GeometricallyConnected.connectedSpace_of_subsingleton (f := E.val.group.X.hom)
    -- the derived subgroup of `K` is nontrivial, since `K` is not central
    have hEne : SubgroupFunctor.range E.val.inclusion ≠ ⊥ := by
      intro hbot
      apply hncen
      have hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ K.X), Commute x y := by
        intro T x y
        have h := hE.containsCommutators T x y
        rw [hbot] at h
        change x * y * x⁻¹ * y⁻¹ = 1 at h
        change x * y = y * x
        rwa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
      have hsol : IsSolvableGroupScheme K :=
        isSolvableGroupScheme_of_isSolvable_points
          (Group.isSolvable_of_comm fun x y => (hcomm _ x y).eq)
      exact hsol.isCentral_of_normal_of_isConnectedReductive_field hG n hnc hnn
    -- it lies in the derived subgroup of `G`, hence factors through `d`
    have hle_d : SubgroupFunctor.range (E.val.inclusion ≫ n) ≤ SubgroupFunctor.range d := by
      rw [hd.2]
      intro T x hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      rw [Grp.comp_hom_hom, ← Category.assoc]
      apply mem_derivedSubgroup_comp
      rw [← hE.2]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    have hrep : (SubgroupFunctor.range d).IsRepresentedBy d := ⟨inferInstance, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, m ≫ d = E.val.inclusion ≫ n := ⟨_, hrep.factorHom_comp _ hle_d⟩
    have hmc : IsClosedSubgroup m := IsClosedSubgroup.of_comp hd.1 (hm ▸ hE.1.comp hnc)
    have hen : (SubgroupFunctor.range (E.val.inclusion ≫ n)).IsNormal :=
      hE.isNormal_comp n hnc hnn
    have hmn : (SubgroupFunctor.range m).IsNormal :=
      SubgroupFunctor.isNormal_range_of_mono_comp m d (hm ▸ hen)
    obtain ⟨J, hJm, -⟩ := hJ E.val.group m ⟨hmc, E.property.1, hEconn, hmn⟩
    -- `J` is nonempty, since the image of `m` is nontrivial
    obtain ⟨j, hj⟩ : J.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro rfl
      apply hEne
      have : IsAffineHom D.X.hom := hDss.isConnectedReductive.isAffineHom
      have hb : SubgroupFunctor.range (b ∅) ≤ SubgroupFunctor.range (kernelUnit D) :=
        hBlub ∅ _ (kernelUnit D) (kernelUnit_isClosedSubgroup (G := D))
          (fun i hi => absurd hi (Set.notMem_empty i))
      rw [range_kernelUnit, ← hJm] at hb
      apply SubgroupFunctor.ext
      intro T
      rw [SubgroupFunctor.bot_carrier, eq_bot_iff]
      intro x hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      have hy : y ≫ m.hom.hom ∈ (SubgroupFunctor.range m).carrier T :=
        SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
      have hy1 : y ≫ m.hom.hom = 1 := by
        simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hb T hy
      rw [Subgroup.mem_bot]
      apply (cancel_mono n.hom.hom).mp
      have h := congrArg (fun f => y ≫ f.hom.hom) hm
      simp only [Grp.comp_hom_hom] at h
      rw [MonObj.one_comp, Category.assoc, ← h, ← Category.assoc, hy1, MonObj.one_comp]
    -- the factor indexed by `j` lies in `n`, so equals it by minimality
    have hle_ai : SubgroupFunctor.range (a (ε.symm j)) ≤ SubgroupFunctor.range m := by
      rw [hε, Equiv.apply_symm_apply, hJm]
      exact hBle J j hj
    have hle_n : SubgroupFunctor.range (a (ε.symm j) ≫ d) ≤ SubgroupFunctor.range n := by
      refine ((range_comp_le_range_comp_iff _ m d).mpr hle_ai).trans ?_
      rw [hm]
      intro T x hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      refine SubgroupFunctor.mem_range.mpr ⟨y ≫ E.val.inclusion.hom.hom, ?_⟩
      rw [Grp.comp_hom_hom, Category.assoc]
    exact ⟨ε.symm j, (hnmin _ (a (ε.symm j) ≫ d) (h1a _).1 (h1a _).2.1 hle_n).symm⟩
  · -- clause 2: the multiplication map is a central isogeny
    refine ⟨Φ.hom ≫ p' ≫ d, fun i => ?_, ?_⟩
    · rw [← Category.assoc, hΦ i, Category.assoc, ← Category.assoc (piFactorInclusionHom A' (ε i)),
        hp'inc, ← Category.assoc, hw]
    · rw [prodHom_iso_comp z hz Φ (p' ≫ d)]
      exact (isCentralIsogeny_prodHom_comp z d hz _ hq p' hp'
        (derivedSubgroup_pi_eq_top A' fun j => (hAS j).derivedSubgroup_eq_top)).iso_comp _

end Main

end ReductiveSimpleFactorDecomposition

/-- The reduction of Conrad's Exercise 5.5.2 (`ReductiveSimpleFactorDecompositionStatement`) to
the semisimple decomposition theorem 5.1.19 (`SimpleFactorDecompositionStatement`). -/
def ReductiveSimpleFactorDecompositionReductionStatement : Prop :=
  SimpleFactorDecompositionStatement.{u} → ReductiveSimpleFactorDecompositionStatement.{u}

/-- The semisimple decomposition theorem implies the reductive one. -/
theorem reductiveSimpleFactorDecomposition_reduction :
    ReductiveSimpleFactorDecompositionReductionStatement.{u} := by
  intro hS1 k _ G hG Z z hz hzc hZ hzmax D d hd
  exact ReductiveSimpleFactorDecomposition.main hS1 hG z hz hzc hZ hzmax d hd

end Langlands.GroupScheme

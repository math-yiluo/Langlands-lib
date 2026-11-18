import Langlands.GroupScheme.ReducedSubgroup
import Mathlib
import Langlands.AlgebraicGeometry.SmoothGeometricallyReducedProof
import Langlands.AlgebraicGeometry.GeometricallyReducedImage
import Langlands.AlgebraicGeometry.SectionComponentNoetherianReduction
import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion
import Langlands.AlgebraicGeometry.ReducedSubscheme
import Langlands.GroupScheme.FppfQuotientTargetSmooth

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-! # Geometric reducedness of reductions after a finite field extension

For a quasi-compact, locally finite-type scheme `Y` over a field, we prove that after a
finite extension of the base field the canonical reduced closed subscheme becomes
geometrically reduced. This module contains the affine case together with the general
lemmas needed to pass to the quasi-compact case:

* `geometricallyReduced_of_perfectField`: a reduced quasi-compact locally finite-type scheme
  over a perfect field is geometrically reduced;
* `Good f`: some reduced closed subscheme of the source with full support is geometrically
  reduced over the base, together with its invariance and descent properties;
* `exists_isReduced_algebraicClosure`: descent of finitely many generators of the nilradical
  of `K̄ ⊗[K] A` to a finite subextension (the coefficient-chasing step in the proof of
  Conrad's Lemma A.5 in the appendix to Prasad–Yu, *On quasi-reductive group schemes*);
* `exists_good_affine`: the affine case.
-/

noncomputable section

namespace Langlands.AlgebraicGeometry.PotentialGeometricReduction

/-- A reduced quasi-compact locally finite-type scheme over a perfect field is geometrically
reduced: its smooth locus is dense and smooth morphisms are geometrically reduced. -/
theorem geometricallyReduced_of_perfectField {F : Type u} [Field F] [PerfectField F]
    {Y : Scheme.{u}} [IsReduced Y] (f : Y ⟶ Spec (CommRingCat.of F))
    [QuasiCompact f] [LocallyOfFiniteType f] : GeometricallyReduced f := by
  have : LocallyOfFinitePresentation f :=
    NoetherianValuativeCriterion.locallyOfFinitePresentation_of_isNoetherianRing f
  have hU : Dense (f.smoothLocus : Set Y) := f.dense_smoothLocus_of_perfectField
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian Y := {}
  have : QuasiCompact f.smoothLocus.ι := inferInstance
  have : IsDominant f.smoothLocus.ι := by
    constructor
    rw [DenseRange, Scheme.Opens.range_ι]
    exact hU
  have : IsSchemeTheoreticallyDominant f.smoothLocus.ι := .of_isDominant _
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have : GeometricallyReduced (f.smoothLocus.ι ≫ f) :=
    smoothGeometricallyReduced _ _ _ this
  exact SchemeImageGeometry.geometricallyReduced_of_schematicallyDominant f.smoothLocus.ι f

/-- The canonical reduced closed subscheme of `Y`. -/
abbrev red (Y : Scheme.{u}) : Scheme.{u} :=
  Langlands.GroupScheme.ReducedSubgroup.red Y

/-- The inclusion of the canonical reduced closed subscheme. -/
abbrev redι (Y : Scheme.{u}) : red Y ⟶ Y :=
  Langlands.GroupScheme.ReducedSubgroup.redι Y

instance (Y : Scheme.{u}) : IsReduced (red Y) :=
  ReducedSubscheme.isReduced_vanishingIdeal_subscheme _

instance (Y : Scheme.{u}) : Surjective (redι Y) :=
  ⟨Langlands.GroupScheme.ReducedSubgroup.redι_surjective Y⟩

/-- A surjective closed immersion from a reduced scheme factors through `redι Y` by an
isomorphism. -/
theorem exists_isIso_lift_red {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [Surjective i] [IsReduced Z] : ∃ e : Z ⟶ red Y, IsIso e ∧ e ≫ redι Y = i := by
  obtain ⟨e, he⟩ := ReducedSubscheme.exists_lift_vanishingIdeal i ⊤ (by simp)
  change e ≫ redι Y = i at he
  have : IsClosedImmersion (e ≫ redι Y) := he ▸ inferInstance
  have : IsClosedImmersion e := IsClosedImmersion.of_comp_isClosedImmersion e (redι Y)
  have : Surjective e := by
    constructor
    intro q
    obtain ⟨z, hz⟩ := i.surjective (redι Y q)
    refine ⟨z, (redι Y).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, he, hz]
  exact ⟨e, isIso_of_isClosedImmersion_of_surjective e, he⟩

/-- Geometric reducedness of a composite through a reduced surjective closed subscheme does not
depend on the choice of that subscheme. -/
theorem geometricallyReduced_comp_iff_red {Y Z S : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [Surjective i] [IsReduced Z] (f : Y ⟶ S) :
    GeometricallyReduced (i ≫ f) ↔ GeometricallyReduced (redι Y ≫ f) := by
  obtain ⟨e, he, hei⟩ := exists_isIso_lift_red i
  rw [← hei, Category.assoc]
  exact MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyReduced) e _

/-- `f` has a reduced closed subscheme with full support that is geometrically reduced
over the base. -/
def Good {Y S : Scheme.{u}} (f : Y ⟶ S) : Prop :=
  ∃ (Z : Scheme.{u}) (i : Z ⟶ Y), IsClosedImmersion i ∧ Surjective i ∧ IsReduced Z ∧
    GeometricallyReduced (i ≫ f)

/-- `Good f` holds exactly when the canonical reduced closed subscheme is geometrically reduced
over the base. -/
theorem good_iff {Y S : Scheme.{u}} (f : Y ⟶ S) :
    Good f ↔ GeometricallyReduced (redι Y ≫ f) := by
  refine ⟨fun ⟨Z, i, h1, h2, h3, h4⟩ => (geometricallyReduced_comp_iff_red i f).mp h4,
    fun h => ⟨red Y, redι Y, inferInstance, inferInstance, inferInstance, h⟩⟩

/-- `Good` is invariant under precomposition with an isomorphism. -/
theorem Good.iso_comp {Y Y' S : Scheme.{u}} {f : Y ⟶ S} (hf : Good f) (e : Y' ⟶ Y)
    [IsIso e] : Good (e ≫ f) := by
  obtain ⟨Z, i, h1, h2, h3, h4⟩ := hf
  refine ⟨Z, i ≫ inv e, inferInstance, inferInstance, h3, ?_⟩
  simpa using h4

/-- Base change of a good morphism along the spectrum of a field. -/
theorem Good.pullback_snd {Y S : Scheme.{u}} {f : Y ⟶ S} (hf : Good f) {M : Type u}
    [Field M] (g : Spec (.of M) ⟶ S) : Good (pullback.snd f g) := by
  obtain ⟨Z, i, h1, h2, h3, h4⟩ := hf
  let e := pullbackRightPullbackFstIso f g i
  have hred : IsReduced (pullback (i ≫ f) g) :=
    pullback_of_geometrically h4.geometrically_isReduced M g
  have : IsReduced (pullback i (pullback.fst f g)) := isReduced_of_isOpenImmersion e.hom
  refine ⟨pullback i (pullback.fst f g), pullback.snd i (pullback.fst f g), inferInstance,
    inferInstance, this, ?_⟩
  rw [← pullbackRightPullbackFstIso_hom_snd f g i]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyReduced) e.hom _).mpr
    inferInstance

/-- `Good` for a base change along a composite agrees with `Good` for the iterated base
change. -/
theorem good_pullback_snd_comp_iff {X Y Z W : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (g' : W ⟶ Y) :
    Good (pullback.snd f (g' ≫ g)) ↔ Good (pullback.snd (pullback.snd f g) g') := by
  constructor
  · intro h
    have := h.iso_comp (pullbackLeftPullbackSndIso f g g').hom
    rwa [pullbackLeftPullbackSndIso_hom_snd] at this
  · intro h
    have := h.iso_comp (pullbackLeftPullbackSndIso f g g').inv
    rwa [pullbackLeftPullbackSndIso_inv_snd_snd] at this

/-- `Good` descends along flat surjective geometrically reduced morphisms onto a locally
noetherian scheme. -/
theorem Good.of_comp {P Y S : Scheme.{u}} (p : P ⟶ Y) (f : Y ⟶ S) [Flat p] [Surjective p]
    [GeometricallyReduced p] [IsLocallyNoetherian Y] (h : Good (p ≫ f)) : Good f := by
  rw [good_iff] at h ⊢
  have : IsLocallyNoetherian (red Y) := LocallyOfFiniteType.isLocallyNoetherian (redι Y)
  have : IsReduced (pullback (redι Y) p) := inferInstance
  have hW : GeometricallyReduced (pullback.snd (redι Y) p ≫ p ≫ f) :=
    (geometricallyReduced_comp_iff_red (pullback.snd (redι Y) p) (p ≫ f)).mpr h
  rw [← pullback.condition_assoc] at hW
  have : Flat (pullback.fst (redι Y) p) := inferInstance
  have : Surjective (pullback.fst (redι Y) p) := inferInstance
  exact geometricallyReduced_of_surjective_flat_comp (pullback.fst (redι Y) p) (redι Y ≫ f)

/-- Over a perfect field every quasi-compact locally finite-type scheme is good. -/
theorem good_of_perfectField {F : Type u} [Field F] [PerfectField F] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of F)) [QuasiCompact f] [LocallyOfFiniteType f] : Good f := by
  rw [good_iff]
  exact geometricallyReduced_of_perfectField _

/-- A quasi-compact locally finite-type scheme over a field `L` is geometrically reduced if its
base change to some perfect extension field `M` is reduced. -/
theorem geometricallyReduced_of_isReduced_pullback {L M : Type u} [Field L] [Field M]
    [PerfectField M] [Algebra L M] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of L)) [QuasiCompact f]
    [LocallyOfFiniteType f]
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap L M))))] :
    GeometricallyReduced f := by
  let σ : Spec (.of M) ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom (algebraMap L M))
  have : Surjective σ := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have : GeometricallyReduced (pullback.snd f σ) := geometricallyReduced_of_perfectField _
  exact geometricallyReduced_of_surjective_baseChange f σ

section Algebra

open TensorProduct

/-- If the nilradical of `E ⊗[L] B` is contained in the extension of the nilradical of `B`,
then `E ⊗[L] (B ⧸ nilradical B)` is reduced. -/
theorem isReduced_tensor_quotient_nilradical {L E B : Type u} [Field L] [CommRing E]
    [Algebra L E] [CommRing B] [Algebra L B]
    (h : nilradical (E ⊗[L] B) ≤
      (nilradical B).map (Algebra.TensorProduct.includeRight : B →ₐ[L] E ⊗[L] B)) :
    IsReduced (E ⊗[L] (B ⧸ nilradical B)) := by
  let π : E ⊗[L] B →ₐ[L] E ⊗[L] (B ⧸ nilradical B) :=
    Algebra.TensorProduct.map (AlgHom.id L E) (Ideal.Quotient.mkₐ L (nilradical B))
  have hπ : Function.Surjective π :=
    Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩)
      (Ideal.Quotient.mkₐ_surjective L _)
  have hker : RingHom.ker π = (nilradical B).map
      (Algebra.TensorProduct.includeRight : B →ₐ[L] E ⊗[L] B) := by
    rw [Algebra.TensorProduct.lTensor_ker _ (Ideal.Quotient.mkₐ_surjective L _)]
    congr 1
    ext x
    rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  have hle : (nilradical B).map (Algebra.TensorProduct.includeRight : B →ₐ[L] E ⊗[L] B) ≤
      nilradical (E ⊗[L] B) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact mem_nilradical.mpr ((mem_nilradical.mp hb).map _)
  constructor
  rintro x ⟨n, hn⟩
  obtain ⟨y, rfl⟩ := hπ x
  have hyn : y ^ n ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_pow]
    exact hn
  rw [hker] at hyn
  have hy : y ∈ nilradical (E ⊗[L] B) := by
    obtain ⟨m, hm⟩ := mem_nilradical.mp (hle hyn)
    exact mem_nilradical.mpr ⟨n * m, by rw [pow_mul, hm]⟩
  have := h hy
  rw [← hker] at this
  exact this

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]

/-- The comparison map `L ⊗[K] A → K̄ ⊗[K] A` for an intermediate field `L` of `K̄ / K`. -/
abbrev psi (L : IntermediateField K (AlgebraicClosure K)) :
    L ⊗[K] A →ₐ[K] AlgebraicClosure K ⊗[K] A :=
  Algebra.TensorProduct.map L.val (AlgHom.id K A)

/-- Every element of `K̄ ⊗[K] A` comes from `L' ⊗[K] A` for every intermediate field `L'`
containing some finite-dimensional intermediate field `L`. -/
theorem exists_finite_mem_range_psi (c : AlgebraicClosure K ⊗[K] A) :
    ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧
      ∀ L' : IntermediateField K (AlgebraicClosure K), L ≤ L' → c ∈ (psi K A L').range := by
  induction c using TensorProduct.inductionOn with
  | tmul x a =>
    refine ⟨IntermediateField.adjoin K {x},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x),
      fun L' hL' => ⟨⟨x, hL' (IntermediateField.mem_adjoin_simple_self K x)⟩ ⊗ₜ a, ?_⟩⟩
    simp [psi]
  | add c₁ c₂ h₁ h₂ =>
    obtain ⟨L₁, hL₁, H₁⟩ := h₁
    obtain ⟨L₂, hL₂, H₂⟩ := h₂
    exact ⟨L₁ ⊔ L₂, inferInstance, fun L' hL' =>
      add_mem (H₁ L' (le_sup_left.trans hL')) (H₂ L' (le_sup_right.trans hL'))⟩

/-- Finitely many elements of `K̄ ⊗[K] A` come from `L ⊗[K] A` for one finite-dimensional
intermediate field `L`. -/
theorem exists_finite_subset_range_psi (s : Finset (AlgebraicClosure K ⊗[K] A)) :
    ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧
      ∀ c ∈ s, c ∈ (psi K A L).range := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, by simp⟩
  | insert c s _ ih =>
    obtain ⟨L₁, hL₁, H₁⟩ := ih
    obtain ⟨L₂, hL₂, H₂⟩ := exists_finite_mem_range_psi K A c
    refine ⟨L₁ ⊔ L₂, inferInstance, ?_⟩
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact H₂ _ le_sup_right
    · obtain ⟨b, rfl⟩ := H₁ d hd
      have hcomp : (psi K A (L₁ ⊔ L₂)).comp (Algebra.TensorProduct.map
          (IntermediateField.inclusion le_sup_left) (AlgHom.id K A)) = psi K A L₁ := by
        apply Algebra.TensorProduct.ext'
        intro l a
        simp [psi]
      exact ⟨_, AlgHom.congr_fun hcomp b⟩

/-- The comparison map `L ⊗[K] A → K̄ ⊗[K] A` for a field `L` between `K` and `K̄`. -/
abbrev psi' (L : Type u) [Field L] [Algebra K L] [Algebra L (AlgebraicClosure K)]
    [IsScalarTower K L (AlgebraicClosure K)] :
    L ⊗[K] A →ₐ[K] AlgebraicClosure K ⊗[K] A :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L (AlgebraicClosure K)) (AlgHom.id K A)

/-- The comparison map is injective, since `A` is flat over the field `K`. -/
theorem psi'_injective (L : Type u) [Field L] [Algebra K L] [Algebra L (AlgebraicClosure K)]
    [IsScalarTower K L (AlgebraicClosure K)] :
    Function.Injective (psi' K A L) :=
  Module.Flat.rTensor_preserves_injective_linearMap
    (IsScalarTower.toAlgHom K L (AlgebraicClosure K)).toLinearMap
    (IsScalarTower.toAlgHom K L (AlgebraicClosure K)).injective

/-- For an intermediate field the two comparison maps agree. -/
theorem psi'_eq_psi (L : IntermediateField K (AlgebraicClosure K)) :
    psi' K A L = psi K A L := by
  apply Algebra.TensorProduct.ext'
  intro l a
  rfl

/-- If finitely many generators of the nilradical of `K̄ ⊗[K] A` come from `L ⊗[K] A`, then
the reduction of `L ⊗[K] A` stays reduced over `K̄`. -/
theorem isReduced_of_nilradical_generators (L : Type u) [Field L] [Algebra K L]
    [Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]
    (s : Set (AlgebraicClosure K ⊗[K] A))
    (hs : Ideal.span s = nilradical (AlgebraicClosure K ⊗[K] A))
    (hsL : ∀ g ∈ s, g ∈ (psi' K A L).range) :
    IsReduced (AlgebraicClosure K ⊗[L] ((L ⊗[K] A) ⧸ nilradical (L ⊗[K] A))) := by
  refine isReduced_tensor_quotient_nilradical ?_
  let e := Algebra.TensorProduct.cancelBaseChange K L (AlgebraicClosure K)
    (AlgebraicClosure K) A
  have he : ∀ b : L ⊗[K] A,
      e (Algebra.TensorProduct.includeRight b) = psi' K A L b := by
    intro b
    induction b using TensorProduct.inductionOn with
    | tmul l a => simp [e, psi', Algebra.smul_def]
    | add b₁ b₂ e₁ e₂ => simp only [map_add, e₁, e₂]
  intro y hy
  have hey : e y ∈ nilradical (AlgebraicClosure K ⊗[K] A) :=
    mem_nilradical.mpr ((mem_nilradical.mp hy).map e)
  rw [← hs] at hey
  have hspan : Ideal.span s ≤
      Ideal.comap e.symm ((nilradical (L ⊗[K] A)).map
        (Algebra.TensorProduct.includeRight :
          L ⊗[K] A →ₐ[L] AlgebraicClosure K ⊗[L] (L ⊗[K] A))) := by
    rw [Ideal.span_le]
    intro g hg
    obtain ⟨b, hb⟩ := hsL g hg
    change psi' K A L b = g at hb
    have hgnil : IsNilpotent g := by
      rw [← mem_nilradical, ← hs]
      exact Ideal.subset_span hg
    have hbnil : IsNilpotent b := by
      obtain ⟨n, hn⟩ := hgnil
      refine ⟨n, psi'_injective K A L ?_⟩
      rw [map_pow, hb, hn, map_zero]
    rw [SetLike.mem_coe, Ideal.mem_comap, ← hb, ← he, AlgEquiv.symm_apply_apply]
    exact Ideal.mem_map_of_mem _ (mem_nilradical.mpr hbnil)
  have := hspan hey
  rwa [Ideal.mem_comap, AlgEquiv.symm_apply_apply] at this

/-- For a finite-type algebra `A` over a field `K` there are a finite extension `L / K` and a
perfect field `M` over `L` such that `M ⊗[L] ((L ⊗[K] A) ⧸ nilradical)` is reduced (one may
take `M = K̄`). -/
theorem exists_isReduced_algebraicClosure [Algebra.FiniteType K A] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (M : Type u) (_ : Field M) (_ : PerfectField M) (_ : Algebra L M),
      IsReduced (M ⊗[L] ((L ⊗[K] A) ⧸ nilradical (L ⊗[K] A))) := by
  have : IsNoetherianRing (AlgebraicClosure K ⊗[K] A) :=
    Algebra.FiniteType.isNoetherianRing (AlgebraicClosure K) _
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (nilradical (AlgebraicClosure K ⊗[K] A)) :
    (nilradical (AlgebraicClosure K ⊗[K] A)).FG)
  obtain ⟨L, hL, hsL⟩ := exists_finite_subset_range_psi K A s
  refine ⟨L, inferInstance, inferInstance, hL, AlgebraicClosure K, inferInstance, inferInstance,
    inferInstance, isReduced_of_nilradical_generators K A L (s : Set _) hs ?_⟩
  intro g hg
  rw [psi'_eq_psi]
  exact hsL g hg

end Algebra

section Schemes

open TensorProduct

/-- The spectrum of a finite-type algebra over a field is good as soon as the base change of
its reduction to some perfect field is reduced. -/
theorem good_spec {L B M : Type u} [Field L] [CommRing B] [Algebra L B]
    [Algebra.FiniteType L B] [Field M] [PerfectField M] [Algebra L M]
    (h : _root_.IsReduced (M ⊗[L] (B ⧸ nilradical B))) :
    Good (Spec.map (CommRingCat.ofHom (algebraMap L B))) := by
  have hred : _root_.IsReduced (B ⧸ nilradical B) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have : Algebra.FiniteType L (B ⧸ nilradical B) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ L (nilradical B))
      (Ideal.Quotient.mkₐ_surjective L _)
  refine ⟨Spec (.of (B ⧸ nilradical B)),
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical B))),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective,
    ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl).2⟩, inferInstance, ?_⟩
  rw [← Spec.map_comp]
  have hcomp : CommRingCat.ofHom (algebraMap L B) ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (nilradical B)) =
      CommRingCat.ofHom (algebraMap L (B ⧸ nilradical B)) := rfl
  rw [hcomp]
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap L (B ⧸ nilradical B)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : _root_.IsReduced ((B ⧸ nilradical B) ⊗[L] M) :=
    isReduced_of_injective (Algebra.TensorProduct.comm L (B ⧸ nilradical B) M).toRingHom
      (Algebra.TensorProduct.comm L (B ⧸ nilradical B) M).injective
  have : IsReduced (pullback (Spec.map (CommRingCat.ofHom (algebraMap L (B ⧸ nilradical B))))
      (Spec.map (CommRingCat.ofHom (algebraMap L M)))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso L (B ⧸ nilradical B) M).hom
  exact geometricallyReduced_of_isReduced_pullback (M := M) _

/-- The affine case: a finite-type algebra over a field becomes good after a finite
extension. -/
theorem exists_good_affine (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      Good (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
  obtain ⟨L, _, _, _, M, _, _, _, h⟩ := exists_isReduced_algebraicClosure K A
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_⟩
  have hg : Good (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A)))) := good_spec h
  have := hg.iso_comp ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso K L A).hom)
  rwa [Category.assoc, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst] at this

end Schemes

end Langlands.AlgebraicGeometry.PotentialGeometricReduction

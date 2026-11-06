import Langlands.Cohomology.Tate.FreeTensorCohomologicalTrivialityStatement
import Langlands.Cohomology.Tate.TateComparisonProof
import Langlands.Cohomology.Tate.Reindex
import Mathlib.RingTheory.Flat.CategoryTheory

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

universe u

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

namespace FreeTensor

variable {R G : Type u} [CommRing R] [Group G]

/-- The lifted integers have a unique module structure on an additive group. -/
lemma integralModule_eq {M : Type u} [AddCommGroup M]
    (m₁ m₂ : Module IntegralScalar.{u} M) : m₁ = m₂ := by
  apply Module.ext' m₁ m₂
  intro r x
  have hr : r = ((r.down : ℤ) : IntegralScalar.{u}) := by
    apply ULift.ext
    rfl
  rw [hr]
  exact (haveI := m₁; Int.cast_smul_eq_zsmul IntegralScalar.{u} r.down x).trans
    (haveI := m₂; Int.cast_smul_eq_zsmul IntegralScalar.{u} r.down x).symm

/-- Flat underlying coefficients preserve short exact sequences of representations. -/
lemma flat_tensorRight_shortExact (S : ShortComplex (Rep.{u} R G))
    (hS : S.ShortExact) (B : Rep.{u} R G) [Module.Flat R B] :
    (S.map (MonoidalCategory.tensorRight B)).ShortExact := by
  let U := forget₂ (Rep.{u} R G) (ModuleCat.{u} R)
  let : PreservesFiniteColimits (MonoidalCategory.tensorRight (ModuleCat.of R B)) :=
    preservesFiniteColimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of R B))
  have h := (hS.map_of_exact U).map_of_exact
    (MonoidalCategory.tensorRight (ModuleCat.of R B))
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful U h

/-- Subgroupwise Tate vanishing is preserved by restriction to a subgroup. -/
lemma restrict_cohomologicallyTrivial [Finite G] (A : Rep.{u} R G)
    (hA : IsCohomologicallyTrivial A) (H : Subgroup G) :
    IsCohomologicallyTrivial (Rep.res H.subtype A) := by
  intro J _ n
  let H' := J.map H.subtype
  let : Fintype H' := Fintype.ofFinite _
  let e : J ≃* H' := J.equivMapOfInjective H.subtype H.subtype_injective
  let c : Rep.res e.toMonoidHom (Rep.res H'.subtype A) ≅
      Rep.res J.subtype (Rep.res H.subtype A) :=
    Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl R A) (fun _ => rfl))
  exact (hA H' n).of_iso (reindexIso e.symm c n).symm

variable {P : Type u} [Group P] [Fintype P] {p : ℕ} [Fact p.Prime]

open PGroupVanishing

/-- A killed coefficient with zero first cohomology has acyclic tensors. -/
lemma killed_tensor_isZero (hP : IsPGroup p P)
    (A B : Rep.{u} IntegralScalar.{u} P)
    (hA : ∀ a : A, p • a = 0) (h1 : IsZero (groupCohomology A 1)) (n : ℤ) :
    IsZero (tateCohomology (A ⊗ B) n) := by
  obtain ⟨π₁, hπ₁S, hπ₁id⟩ := exists_retraction hA A.ρ.invariants.toAddSubgroup
  let π₀ : A →+ A.ρ.invariants :=
    { toFun := fun a => ⟨π₁ a, hπ₁S a⟩
      map_zero' := Subtype.ext (map_zero π₁)
      map_add' := fun a b => Subtype.ext (map_add π₁ a b) }
  let π := integralLinear π₀
  have hπ : ∀ (a : A) (ha : a ∈ A.ρ.invariants), π a = ⟨a, ha⟩ :=
    fun a ha => Subtype.ext (hπ₁id a ha)
  let Φ := toCoinduced A π
  have : Mono Φ :=
    (Rep.mono_iff_injective Φ).mpr (toCoinduced_injective hP A hA π hπ)
  have : Epi Φ :=
    (Rep.epi_iff_surjective Φ).mpr (toCoinduced_surjective hP A hA h1 π hπ)
  have : IsIso Φ := isIso_of_mono_of_epi Φ
  exact (coinducedTensor_tate_isZero _ B n).of_iso
    ((tateCohomologyFunctor n).mapIso
      ((MonoidalCategory.tensorRight B).mapIso (asIso Φ)))

/-- Tensor acyclicity when multiplication by the prime is injective. -/
lemma torsionFree_tensor_isZero (hP : IsPGroup p P)
    (A B : Rep.{u} IntegralScalar.{u} P) [Module.Flat IntegralScalar.{u} B]
    (hA : Mono (p • 𝟙 A)) (hz : ∀ n : ℤ, IsZero (tateCohomology A n)) (n : ℤ) :
    IsZero (tateCohomology (A ⊗ B) n) := by
  let S := ShortComplex.mk (p • 𝟙 A) (cokernel.π (p • 𝟙 A)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hQk : p • 𝟙 (cokernel (p • 𝟙 A)) = 0 := by
    rw [← cancel_epi (cokernel.π (p • 𝟙 A)), Preadditive.comp_nsmul, Category.comp_id,
      comp_zero, ← cokernel.condition (p • 𝟙 A), Preadditive.nsmul_comp, Category.id_comp]
  have hQ : ∀ m : ℤ, IsZero (tateCohomology S.X₃ m) := fun m =>
    (TateCohomology.exact₃ hS m).isZero_X₂ ((hz m).eq_of_src _ _)
      ((hz (m + 1)).eq_of_tgt _ _)
  have hQ1 : IsZero (groupCohomology S.X₃ 1) :=
    (hQ 1).of_iso ((TateCohomology.isoGroupCohomology 1).app S.X₃).symm
  have hQB := killed_tensor_isZero hP S.X₃ B (killed_apply hQk) hQ1
  have hSB := flat_tensorRight_shortExact S hS B
  have hinj : ∀ (m : ℤ) (x : tateCohomology (A ⊗ B) (m + 1)),
      p • x = 0 → x = 0 := by
    intro m x hx
    have hmono : Mono ((tateCohomologyFunctor (m + 1)).map
        (S.map (MonoidalCategory.tensorRight B)).f) :=
      (TateCohomology.exact₁ hSB m).mono_g ((hQB m).eq_of_src _ _)
    have : (tateCohomologyFunctor (R := IntegralScalar.{u}) (G := P) (m + 1)).Additive :=
      inferInstanceAs (tateComplexFunctor IntegralScalar.{u} P ⋙
        HomologicalComplex.homologyFunctor _ _ (m + 1)).Additive
    have hmap : (tateCohomologyFunctor (m + 1)).map
        (S.map (MonoidalCategory.tensorRight B)).f = p • 𝟙 (tateCohomology (A ⊗ B) (m + 1)) := by
      change (tateCohomologyFunctor (m + 1)).map
        ((MonoidalCategory.tensorRight B).map (p • 𝟙 A)) = _
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id,
        Functor.map_nsmul, CategoryTheory.Functor.map_id]
      rfl
    rw [hmap, ModuleCat.mono_iff_injective] at hmono
    apply hmono
    rw [map_zero]
    exact hx
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hP
  have hall : ∀ m : ℤ, IsZero (tateCohomology (A ⊗ B) (m + 1)) := by
    intro m
    have key : ∀ (k : ℕ) (x : tateCohomology (A ⊗ B) (m + 1)),
        p ^ k • x = 0 → x = 0 := by
      intro k
      induction k with
      | zero =>
        intro x hx
        simpa using hx
      | succ k ih =>
        intro x hx
        apply ih
        apply hinj m
        rw [smul_smul, ← pow_succ']
        exact hx
    have h0 : ∀ x : tateCohomology (A ⊗ B) (m + 1), x = 0 := fun x =>
      key e x (by
        rw [← he, Nat.card_eq_fintype_card]
        exact card_smul_eq_zero (A ⊗ B) (m + 1) x)
    exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => (h0 x).trans (h0 y).symm⟩
  have h' := hall (n - 1)
  rwa [sub_add_cancel] at h'

/-- Retain the coinduced presentation of the torsion-free covering coefficient. -/
lemma exists_coinduced_cover (C : Rep.{u} IntegralScalar.{u} P) :
    ∃ (T : Rep.{u} IntegralScalar.{u} P) (ε : coinduced T ⟶ C),
      Epi ε ∧ Mono (p • 𝟙 (coinduced T)) := by
  classical
  have := integralScalar_isAddTorsionFree.{u}
  let F := (C : Type u) →₀ IntegralScalar.{u}
  let T : Rep.{u} IntegralScalar.{u} P := Rep.trivial IntegralScalar.{u} P F
  let s : F →ₗ[IntegralScalar.{u}] C := Finsupp.linearCombination IntegralScalar.{u} id
  let sR : Rep.res (⊥ : Subgroup P).subtype T ⟶ Rep.res (⊥ : Subgroup P).subtype C :=
    Rep.ofHom ⟨s, fun g => by
      have hg : (g : P) = 1 := Subgroup.mem_bot.mp g.2
      apply LinearMap.ext
      intro a
      change s (T.ρ (g : P) a) = C.ρ (g : P) (s a)
      rw [hg, map_one, map_one, Module.End.one_apply, Module.End.one_apply]⟩
  refine ⟨T, Rep.coindMap (⊥ : Subgroup P).subtype sR ≫ coinducedProjection C,
    ?_, mono_nsmul_coinduced (mono_nsmul_trivial (Fact.out : p.Prime).ne_zero)⟩
  rw [Rep.epi_iff_surjective]
  intro c
  refine ⟨coinducedDelta T (Finsupp.single c 1), ?_⟩
  have hδ : (Rep.coindMap (⊥ : Subgroup P).subtype sR).hom
      (coinducedDelta T (Finsupp.single c 1)) = coinducedDelta C c := by
    apply Subtype.ext
    funext x
    change s ((coinducedDelta T (Finsupp.single c 1)).1 x) = (coinducedDelta C c).1 x
    rw [coinducedDelta_apply, coinducedDelta_apply]
    split_ifs
    · change Finsupp.linearCombination IntegralScalar.{u} id (Finsupp.single c 1) = c
      rw [Finsupp.linearCombination_single, one_smul]
      rfl
    · exact map_zero s
  change (coinducedProjection C).hom ((Rep.coindMap (⊥ : Subgroup P).subtype sR).hom
    (coinducedDelta T (Finsupp.single c 1))) = c
  rw [hδ, coinducedProjection_delta]

/-- For a finite p-group, acyclicity survives tensoring by flat integral coefficients. -/
lemma pGroup_tensor_isZero (hP : IsPGroup p P)
    (A B : Rep.{u} IntegralScalar.{u} P) [Module.Flat IntegralScalar.{u} B]
    (hz : ∀ n : ℤ, IsZero (tateCohomology A n)) (n : ℤ) :
    IsZero (tateCohomology (A ⊗ B) n) := by
  obtain ⟨T, ε, hε, hT⟩ := exists_coinduced_cover (p := p) A
  let S := ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel ε }
  have hK : Mono (p • 𝟙 (kernel ε)) := by
    have hcomm : (p • 𝟙 (kernel ε)) ≫ kernel.ι ε =
        kernel.ι ε ≫ (p • 𝟙 (coinduced T)) := by
      rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
    have : Mono ((p • 𝟙 (kernel ε)) ≫ kernel.ι ε) := by
      rw [hcomm]
      exact mono_comp _ _
    exact mono_of_mono _ (kernel.ι ε)
  have hKz : ∀ m : ℤ, IsZero (tateCohomology (kernel ε) m) := by
    intro m
    have h := (TateCohomology.exact₁ hS (m - 1)).isZero_X₂
      ((hz (m - 1)).eq_of_src _ _) ((coinduced_tate_isZero T (m - 1 + 1)).eq_of_tgt _ _)
    simpa only [sub_add_cancel] using h
  have hKB := torsionFree_tensor_isZero hP (kernel ε) B hK hKz
  have hSB := flat_tensorRight_shortExact S hS B
  exact (TateCohomology.exact₃ hSB n).isZero_X₂
    ((coinducedTensor_tate_isZero T B n).eq_of_src _ _) ((hKB (n + 1)).eq_of_tgt _ _)

/-- Sylow detection gives tensor vanishing for an arbitrary finite group. -/
lemma tensor_isZero [Fintype G] (A B : Rep.{u} IntegralScalar.{u} G)
    [Module.Flat IntegralScalar.{u} B] (hA : IsCohomologicallyTrivial A) (n : ℤ) :
    IsZero (tateCohomology (A ⊗ B) n) := by
  apply sylowTateVanishing IntegralScalar.{u} G (A ⊗ B) n
  intro q hq Q _
  let : Fact q.Prime := ⟨hq⟩
  exact pGroup_tensor_isZero Q.isPGroup'
    (Rep.res Q.1.subtype A) (Rep.res Q.1.subtype B) (fun m => hA Q.1 m) n

end FreeTensor

/-- Free integral tensor factors preserve subgroupwise actual Tate vanishing. -/
theorem freeTensorCohomologicalTriviality : FreeTensorCohomologicalTriviality.{u} := by
  intro G _ _ A B hfree hA H _ n
  have hfree' : Module.Free IntegralScalar.{u} B := by
    have hm := FreeTensor.integralModule_eq
      (ULift.module : Module IntegralScalar.{u} B) B.hV2
    exact hm ▸ hfree
  let : Module.Flat IntegralScalar.{u} B := Module.Flat.of_free
  exact FreeTensor.tensor_isZero (Rep.res H.subtype A) (Rep.res H.subtype B)
    (FreeTensor.restrict_cohomologicallyTrivial A hA H) n

end Langlands.Tate

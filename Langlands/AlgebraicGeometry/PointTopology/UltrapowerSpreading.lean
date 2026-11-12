import Langlands.AlgebraicGeometry.PointTopology.LocalFieldUltrapower
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointProof

/-!
# Ultrafilter lifting and spreading out of ultrapower points

Two auxiliary results for limits of rational points along ultrafilters.

* An ultrafilter on `α` whose image under `F : α → γ` converges to `D b₀`, for a map
  `D : β → γ` sending neighbourhoods of `b₀` to neighbourhoods of `D b₀`, lifts to an
  ultrafilter on the fibre product of `F` and `D` whose second projection converges to `b₀`.
* Let `L` be an `(I → K)`-algebra, surjected onto by `I → K`, whose kernel consists of the
  families vanishing along an ultrafilter `𝒰` (for example the ultrapower `K^I/𝒰`). Then `L`
  is the filtered colimit of the quotients of `I → K` by the families vanishing on a set of
  `𝒰`, and every `L`-point of a scheme locally of finite presentation over `Spec (I → K)`
  comes from one of these quotients.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology Filter
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

section Lifting

/-- **Lifting ultrafilters to fibre products.** Let `P` surject onto the set-theoretic fibre
product of `F : α → γ` and `D : β → γ`. If `D` sends neighbourhoods of `b₀` to neighbourhoods
of `D b₀` and `F` tends to `D b₀` along `𝒰`, then some ultrafilter on `P` maps to `𝒰` and its
second projection tends to `b₀`. -/
theorem exists_ultrafilter_lift {α β γ P : Type*} [TopologicalSpace β] [TopologicalSpace γ]
    (F : α → γ) (D : β → γ) (fst : P → α) (snd : P → β)
    (hP : ∀ a b, F a = D b → ∃ p, fst p = a ∧ snd p = b)
    (𝒰 : Ultrafilter α) (b₀ : β) (hD : ∀ N ∈ 𝓝 b₀, D '' N ∈ 𝓝 (D b₀))
    (hF : Tendsto F 𝒰 (𝓝 (D b₀))) :
    ∃ 𝒲 : Ultrafilter P, 𝒲.map fst = 𝒰 ∧ Tendsto snd 𝒲 (𝓝 b₀) := by
  have hne : (Filter.comap fst (𝒰 : Filter α) ⊓ Filter.comap snd (𝓝 b₀)).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s hs t ht
    obtain ⟨A, hA, hAs⟩ := Filter.mem_comap.1 hs
    obtain ⟨N, hN, hNt⟩ := Filter.mem_comap.1 ht
    have h1 : F ⁻¹' (D '' N) ∈ (𝒰 : Filter α) := hF (hD N hN)
    obtain ⟨a, haA, b, hbN, hab⟩ := (𝒰.nonempty_of_mem (Filter.inter_mem hA h1))
    obtain ⟨p, hp1, hp2⟩ := hP a b hab.symm
    exact ⟨p, hAs (show fst p ∈ A by rw [hp1]; exact haA),
      hNt (show snd p ∈ N by rw [hp2]; exact hbN)⟩
  refine ⟨Ultrafilter.of (Filter.comap fst (𝒰 : Filter α) ⊓ Filter.comap snd (𝓝 b₀)), ?_, ?_⟩
  · apply Ultrafilter.coe_le_coe.1
    rw [Ultrafilter.coe_map]
    exact (Filter.map_mono ((Ultrafilter.of_le _).trans inf_le_left)).trans Filter.map_comap_le
  · exact Filter.tendsto_iff_comap.2 ((Ultrafilter.of_le _).trans inf_le_right)

end Lifting

section Colimit

variable (K : Type u) [Field K] {I : Type u} (𝒰 : Ultrafilter I)

/-- The ideal of families vanishing on a set. -/
def vanishing (A : Set I) : Ideal (I → K) where
  carrier := {f | ∀ i ∈ A, f i = 0}
  add_mem' {f g} hf hg i hi := by simp [hf i hi, hg i hi]
  zero_mem' _ _ := rfl
  smul_mem' c f hf i hi := by simp [hf i hi]

variable {K} in
theorem mem_vanishing {A : Set I} {f : I → K} : f ∈ vanishing K A ↔ ∀ i ∈ A, f i = 0 :=
  Iff.rfl

theorem vanishing_anti {A B : Set I} (h : B ⊆ A) : vanishing K A ≤ vanishing K B :=
  fun _ hf i hi => hf i (h hi)

/-- The sets of an ultrafilter, ordered by reverse inclusion. -/
def UltraIndex : Type u := {A : Set I // A ∈ 𝒰}

instance : Preorder (UltraIndex 𝒰) where
  le A B := B.1 ⊆ A.1
  le_refl _ := subset_rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁

instance : IsDirectedOrder (UltraIndex 𝒰) where
  directed A B := ⟨⟨A.1 ∩ B.1, Filter.inter_mem A.2 B.2⟩, Set.inter_subset_left,
    Set.inter_subset_right⟩

instance : Nonempty (UltraIndex 𝒰) := ⟨⟨Set.univ, Filter.univ_mem⟩⟩

/-- The diagram of quotients of `I → K` by the families vanishing on sets of `𝒰`. -/
def stageDiagram : UltraIndex 𝒰 ⥤ CommAlgCat.{u} (I → K) where
  obj A := CommAlgCat.of (I → K) ((I → K) ⧸ vanishing K A.1)
  map h := CommAlgCat.ofHom
    (Ideal.Quotient.factorₐ (I → K) (vanishing_anti K (leOfHom h)))
  map_id _ := CommAlgCat.hom_ext (Ideal.Quotient.algHom_ext _ (AlgHom.ext fun _ => rfl))
  map_comp _ _ := CommAlgCat.hom_ext (Ideal.Quotient.algHom_ext _ (AlgHom.ext fun _ => rfl))

variable {L : Type u} [CommRing L] [Algebra (I → K) L]
  (hker : ∀ f : I → K, algebraMap (I → K) L f = 0 ↔ ∀ᶠ i in (𝒰 : Filter I), f i = 0)

include hker in
theorem algebraMap_eq_zero_of_mem_vanishing {A : Set I} (hA : A ∈ 𝒰) (f : I → K)
    (hf : f ∈ vanishing K A) : algebraMap (I → K) L f = 0 :=
  (hker f).2 (Filter.mem_of_superset hA fun i hi => hf i hi)

/-- The map from the stage at `A` to `L`. -/
def stageMap {A : Set I} (hA : A ∈ 𝒰) : ((I → K) ⧸ vanishing K A) →ₐ[I → K] L :=
  Ideal.Quotient.liftₐ _ (Algebra.ofId (I → K) L)
    (algebraMap_eq_zero_of_mem_vanishing K 𝒰 hker hA)

@[simp]
theorem stageMap_mk {A : Set I} (hA : A ∈ 𝒰) (f : I → K) :
    stageMap K 𝒰 hker hA (Ideal.Quotient.mk _ f) = algebraMap (I → K) L f :=
  rfl

/-- The cocone of the stages over `L`. -/
def stageCocone : Cocone (stageDiagram K 𝒰) where
  pt := CommAlgCat.of (I → K) L
  ι :=
    { app A := CommAlgCat.ofHom (stageMap K 𝒰 hker A.2)
      naturality _ _ _ :=
        CommAlgCat.hom_ext (Ideal.Quotient.algHom_ext _ (AlgHom.ext fun _ => rfl)) }

variable {K 𝒰} in
include hker in
theorem ker_le_ker_of_cocone (s : Cocone (stageDiagram K 𝒰)) :
    RingHom.ker (algebraMap (I → K) L) ≤ RingHom.ker (algebraMap (I → K) s.pt) := by
  intro f hf
  have hf' : ∀ᶠ i in (𝒰 : Filter I), f i = 0 := (hker f).1 hf
  let A : UltraIndex 𝒰 := ⟨{i | f i = 0}, hf'⟩
  have hmem : f ∈ vanishing K A.1 := fun i hi => hi
  rw [RingHom.mem_ker]
  calc algebraMap (I → K) s.pt f
      = (s.ι.app A).hom (Ideal.Quotient.mk (vanishing K A.1) f) :=
        ((s.ι.app A).hom.commutes f).symm
    _ = 0 := (congrArg _ (Ideal.Quotient.eq_zero_iff_mem.2 hmem)).trans (map_zero _)

/-- The map out of `L` induced by a cocone of stages. -/
def stageDesc (hsurj : Function.Surjective (algebraMap (I → K) L))
    (s : Cocone (stageDiagram K 𝒰)) : L →ₐ[I → K] s.pt :=
  { (algebraMap (I → K) L).liftOfSurjective hsurj
      ⟨algebraMap (I → K) s.pt, ker_le_ker_of_cocone hker s⟩ with
    commutes' := fun r => (algebraMap (I → K) L).liftOfRightInverse_comp_apply _
      (Function.rightInverse_surjInv hsurj) ⟨_, ker_le_ker_of_cocone hker s⟩ r }

theorem stageDesc_algebraMap (hsurj : Function.Surjective (algebraMap (I → K) L))
    (s : Cocone (stageDiagram K 𝒰)) (f : I → K) :
    stageDesc K 𝒰 hker hsurj s (algebraMap (I → K) L f) = algebraMap (I → K) s.pt f :=
  (stageDesc K 𝒰 hker hsurj s).commutes f

/-- `L` is the colimit of the stages. -/
def stageCoconeIsColimit (hsurj : Function.Surjective (algebraMap (I → K) L)) :
    IsColimit (stageCocone K 𝒰 hker) where
  desc s := CommAlgCat.ofHom (stageDesc K 𝒰 hker hsurj s)
  fac s A := by
    apply CommAlgCat.hom_ext
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro f
    exact (stageDesc_algebraMap K 𝒰 hker hsurj s f).trans ((s.ι.app A).hom.commutes f).symm
  uniq s m _ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro l
    obtain ⟨f, rfl⟩ := hsurj l
    exact (m.hom.commutes f).trans (stageDesc_algebraMap K 𝒰 hker hsurj s f).symm

/-- **Spreading out points over the ultrapower.** Every `L`-point of a scheme locally of finite
presentation over `Spec (I → K)` comes from a stage `(I → K) ⧸ vanishing K A` with `A ∈ 𝒰`. -/
theorem exists_stage_ringPoint (hsurj : Function.Surjective (algebraMap (I → K) L))
    (X : Over (Spec (CommRingCat.of (I → K)))) [LocallyOfFinitePresentation X.hom]
    (p : RingPoint (I → K) X L) :
    ∃ (A : Set I) (hA : A ∈ 𝒰) (q : RingPoint (I → K) X ((I → K) ⧸ vanishing K A)),
      q.changeRing (stageMap K 𝒰 hker hA) = p := by
  obtain ⟨A, q, hq⟩ := ((filteredRingPointComparison (I → K) (UltraIndex 𝒰)
    (stageDiagram K 𝒰) (stageCocone K 𝒰 hker) (stageCoconeIsColimit K 𝒰 hker hsurj) X).2
    inferInstance).1 p
  exact ⟨A.1, A.2, q, hq⟩

end Colimit

end Langlands.AlgebraicGeometry.PointTopology

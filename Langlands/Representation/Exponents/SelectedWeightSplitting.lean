import Langlands.Representation.Exponents.SelectedWeights
import Langlands.Representation.Exponents.SplitComponentDecomposition
import Langlands.Representation.Aubert.General.InductionEmbeddings
import Langlands.Representation.Category.Subquotients
import Mathlib.LinearAlgebra.Projection

/-! # Selected weight parts of a split representation

If a representation `π` is split as `i₀ ∘ p₀ + i₁ ∘ p₁ = id` through two representations,
the first entirely selected and the second entirely unselected, then the selected part of
`π` is the image of `i₀`. The projection onto an invariant complement summand is an
intertwiner, and normalized induction carries such a splitting to a splitting.
-/

noncomputable section

namespace Langlands

universe uR uA uM uV uV₀ uV₁

section Selected

variable {R : Type uR} [Field R] {A : Type uA} [Group A]
  {M : Type uM} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  [WeaklyLocallyCompactSpace M]
  {V : Type uV} [AddCommGroup V] [Module R V]
  (π : Representation R M V) (ι : A →* M)
  (hι : ∀ a : A, ι a ∈ Subgroup.center M) (P : (A →* Rˣ) → Prop)

omit [WeaklyLocallyCompactSpace M] in
/-- If the generalized weight spaces span and every character with a nonzero weight space
is selected, the selected part is everything. -/
theorem selectedWeightPart_eq_top_of_forall
    (hspan : (⨆ χ : A →* Rˣ, (generalizedWeightSpace π ι χ hι).toSubmodule) = ⊤)
    (hP : ∀ χ, generalizedWeightSpace π ι χ hι ≠ ⊥ → P χ) :
    selectedWeightPart π ι hι P = ⊤ := by
  apply _root_.Subrepresentation.toSubmodule_injective
  change (selectedWeightPart π ι hι P).toSubmodule = ⊤
  rw [selectedWeightPart_toSubmodule, ← hspan]
  apply le_antisymm
  · exact iSup_le fun χ => iSup_le fun _ => le_iSup
      (fun ψ : A →* Rˣ => (generalizedWeightSpace π ι ψ hι).toSubmodule) χ
  · refine iSup_le fun χ => ?_
    by_cases h : generalizedWeightSpace π ι χ hι = ⊥
    · rw [h]
      exact bot_le
    · exact le_iSup₂_of_le (f := fun ψ (_ : P ψ) =>
        (generalizedWeightSpace π ι ψ hι).toSubmodule) χ (hP χ h) le_rfl

variable {π}
variable {V₀ : Type uV₀} [AddCommGroup V₀] [Module R V₀]
  {V₁ : Type uV₁} [AddCommGroup V₁] [Module R V₁]
  {π₀ : Representation R M V₀} {π₁ : Representation R M V₁}

/-- Let `π` split as `i₀ (p₀ v) + i₁ (p₁ v) = v`, where every vector of `π₀` is selected
and every vector of `π₁` is unselected. Then the selected part of `π` is the range
of `i₀`. The maps `p₀` and `p₁` need not be linear. -/
theorem selectedWeightPart_toSubmodule_eq_range (hπ : IsSmooth π)
    (i₀ : π₀.IntertwiningMap π) (i₁ : π₁.IntertwiningMap π) (p₀ : V → V₀) (p₁ : V → V₁)
    (hsum : ∀ v, i₀ (p₀ v) + i₁ (p₁ v) = v)
    (h₀ : selectedWeightPart π₀ ι hι P = ⊤)
    (h₁ : selectedWeightPart π₁ ι hι (fun χ => ¬ P χ) = ⊤) :
    (selectedWeightPart π ι hι P).toSubmodule = LinearMap.range i₀.toLinearMap := by
  apply le_antisymm
  · intro v hv
    have hsel₀ : i₀ (p₀ v) ∈ selectedWeightPart π ι hι P :=
      map_mem_selectedWeightPart ι hι P i₀ (by rw [h₀]; trivial)
    have hsel₁ : i₁ (p₁ v) ∈ selectedWeightPart π ι hι (fun χ => ¬ P χ) :=
      map_mem_selectedWeightPart ι hι _ i₁ (by rw [h₁]; trivial)
    have hdiff : i₁ (p₁ v) ∈ (selectedWeightPart π ι hι P).toSubmodule := by
      have he : i₁ (p₁ v) = v - i₀ (p₀ v) := eq_sub_of_add_eq' (hsum v)
      rw [he]
      exact Submodule.sub_mem _ hv hsel₀
    have hzero : i₁ (p₁ v) = 0 :=
      Submodule.disjoint_def.mp (selectedWeightPart_disjoint π ι hι P hπ) _ hdiff hsel₁
    refine ⟨p₀ v, ?_⟩
    change i₀ (p₀ v) = v
    simpa only [hzero, add_zero] using hsum v
  · rintro _ ⟨w, rfl⟩
    exact map_mem_selectedWeightPart ι hι P i₀ (by rw [h₀]; trivial)

/-- Under the hypotheses of `selectedWeightPart_toSubmodule_eq_range`, an injective `i₀`
identifies `π₀` with the selected part of `π`. -/
theorem nonempty_selectedWeightPart_equiv (hπ : IsSmooth π)
    (i₀ : π₀.IntertwiningMap π) (i₁ : π₁.IntertwiningMap π) (p₀ : V → V₀) (p₁ : V → V₁)
    (hsum : ∀ v, i₀ (p₀ v) + i₁ (p₁ v) = v) (hi₀ : Function.Injective i₀)
    (h₀ : selectedWeightPart π₀ ι hι P = ⊤)
    (h₁ : selectedWeightPart π₁ ι hι (fun χ => ¬ P χ) = ⊤) :
    Nonempty ((selectedWeightPart π ι hι P).toRepresentation.Equiv π₀) := by
  have hrange := selectedWeightPart_toSubmodule_eq_range ι hι P hπ i₀ i₁ p₀ p₁ hsum h₀ h₁
  have hmem : ∀ w, i₀ w ∈ (selectedWeightPart π ι hι P).toSubmodule := fun w => by
    rw [hrange]
    exact LinearMap.mem_range_self _ w
  let f : π₀.IntertwiningMap (selectedWeightPart π ι hι P).toRepresentation :=
    LinearMap.intertwiningMap_of_isIntertwiningMap π₀ _
      (LinearMap.codRestrict _ i₀.toLinearMap hmem) (fun g w => Subtype.ext
        (Representation.IntertwiningMap.isIntertwining π₀ π i₀ g w))
  have hf : Function.Bijective f := by
    refine ⟨fun w w' h => hi₀ (congrArg Subtype.val h), fun v => ?_⟩
    have hv : (v : V) ∈ LinearMap.range i₀.toLinearMap := hrange ▸ v.property
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, Subtype.ext hw⟩
  exact ⟨(f.ofBijective hf).symm⟩

end Selected

section Projection

variable {R : Type uR} [Ring R] {G : Type uM} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module R V] {ρ : Representation R G V}

/-- The projection onto one of two complementary subrepresentations, along the other,
is an intertwiner. -/
def subrepresentationProjection (S T : _root_.Subrepresentation ρ)
    (h : IsCompl S.toSubmodule T.toSubmodule) :
    ρ.IntertwiningMap S.toRepresentation :=
  LinearMap.intertwiningMap_of_isIntertwiningMap ρ S.toRepresentation
    (Submodule.projectionOnto S.toSubmodule T.toSubmodule h) (fun g v => by
      conv_lhs => rw [← Submodule.projection_add_projection_eq_self h v]
      have h₀ := S.apply_mem_toSubmodule g
        (Submodule.projection_apply_mem (p := S.toSubmodule) h v)
      have h₁ := T.apply_mem_toSubmodule g
        (Submodule.projection_apply_mem (p := T.toSubmodule) h.symm v)
      rw [map_add, map_add, Submodule.projectionOnto_apply_of_mem_left h h₀,
        Submodule.projectionOnto_apply_of_mem_right h h₁, add_zero]
      rfl)

@[simp]
theorem subrepresentationProjection_apply (S T : _root_.Subrepresentation ρ)
    (h : IsCompl S.toSubmodule T.toSubmodule) (v : V) :
    (subrepresentationProjection S T h v : V) = S.toSubmodule.projection T.toSubmodule h v :=
  rfl

/-- The two complementary projections followed by the inclusions sum to the identity. -/
theorem subrepresentationProjection_add (S T : _root_.Subrepresentation ρ)
    (h : IsCompl S.toSubmodule T.toSubmodule) (v : V) :
    (subrepresentationProjection S T h v : V) + subrepresentationProjection T S h.symm v = v :=
  Submodule.projection_add_projection_eq_self h v

/-- The inclusion of a subrepresentation is an intertwiner, also after restricting the
action along any monoid map `ι : H →* G`. -/
def subrepresentationInclusion {H : Type*} [Monoid H] (S : _root_.Subrepresentation ρ)
    (ι : H →* G) : Representation.IntertwiningMap (S.toRepresentation.comp ι) (ρ.comp ι) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (S.toRepresentation.comp ι) (ρ.comp ι)
    S.toSubmodule.subtype (fun _ _ => rfl)

@[simp]
theorem subrepresentationInclusion_apply {H : Type*} [Monoid H] (S : _root_.Subrepresentation ρ)
    (ι : H →* G) (v : S.toSubmodule) : subrepresentationInclusion S ι v = (v : V) :=
  rfl

end Projection

namespace SmoothRep

variable {R : Type uR} [CommRing R] {G : Type uM} [Group G] [TopologicalSpace G]
  (A : SmoothRep.{uR, uM, uV} R G)

/-- The projection of a smooth representation onto one of two complementary invariant
subspaces, along the other, as a morphism to the smooth subrepresentation. -/
def subrepresentationProjection (S T : _root_.Subrepresentation A.representation)
    (h : IsCompl S.toSubmodule T.toSubmodule) : A ⟶ SmoothRep.subrepresentation A S :=
  SmoothRep.ofHom (Langlands.subrepresentationProjection S T h)

/-- The two complementary projections followed by the two inclusions sum to the
identity. -/
theorem subtype_subrepresentationProjection_add
    (S T : _root_.Subrepresentation A.representation)
    (h : IsCompl S.toSubmodule T.toSubmodule) (v : A) :
    SmoothRep.hom (SmoothRep.subtype A S)
        (SmoothRep.hom (subrepresentationProjection A S T h) v) +
      SmoothRep.hom (SmoothRep.subtype A T)
        (SmoothRep.hom (subrepresentationProjection A T S h.symm) v) = v :=
  Langlands.subrepresentationProjection_add S T h v

end SmoothRep

namespace Aubert.General

variable {G : Type uM} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))

/-- Normalized induction carries a splitting `i₀ ∘ p₀ + i₁ ∘ p₁ = id` of smooth
representations of `M` to the same splitting of the induced representations. -/
theorem normalizedInductionFunctor_map_add_map {X Y₀ Y₁ : SmoothRep.{0, uM, uV} ℂ M}
    (i₀ : Y₀ ⟶ X) (i₁ : Y₁ ⟶ X) (p₀ : X ⟶ Y₀) (p₁ : X ⟶ Y₁)
    (hsum : ∀ x, SmoothRep.hom i₀ (SmoothRep.hom p₀ x) +
      SmoothRep.hom i₁ (SmoothRep.hom p₁ x) = x)
    (f : (normalizedInductionFunctor h hU).obj X) :
    SmoothRep.hom ((normalizedInductionFunctor h hU).map i₀)
        (SmoothRep.hom ((normalizedInductionFunctor h hU).map p₀) f) +
      SmoothRep.hom ((normalizedInductionFunctor h hU).map i₁)
        (SmoothRep.hom ((normalizedInductionFunctor h hU).map p₁) f) = f :=
  Subtype.ext (Subtype.ext (funext fun x =>
    hsum (Induction.eval P (inducingRepresentation h hU X) f x)))

/-- Normalized induction preserves injectivity of morphisms. -/
theorem normalizedInductionFunctor_map_injective {X Y : SmoothRep.{0, uM, uV} ℂ M}
    (i : Y ⟶ X) (hi : Function.Injective (SmoothRep.hom i)) :
    Function.Injective (SmoothRep.hom ((normalizedInductionFunctor h hU).map i)) :=
  normalizedInductionMap_injective h hU (SmoothRep.hom i) hi

end Aubert.General

end Langlands

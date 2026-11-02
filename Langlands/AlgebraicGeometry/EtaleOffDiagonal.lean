import Langlands.AlgebraicGeometry.AffineEtaleUniformPointBound
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.SetTheory.Cardinal.NatCard

/-! # Off-diagonal induction for separated étale morphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

variable {T Y : Scheme.{u}}

/-- A bound on every field-valued fibre, including its finiteness. -/
def HasFieldFibreBound (e : T ⟶ Y) (n : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y),
    Finite {g : Spec (.of K) ⟶ T // g ≫ e = a} ∧
      Nat.card {g : Spec (.of K) ⟶ T // g ≫ e = a} ≤ n

theorem hasFieldFibreBound_affineEtalePointBound [IsAffine T] [IsAffine Y]
    (e : T ⟶ Y) [Etale e] : HasFieldFibreBound e (affineEtalePointBound e) :=
  affineEtale_fibrePoints_finite_card_le e

/-- A field-fibre bound of one forces an étale morphism to be an open immersion. -/
theorem isOpenImmersion_of_hasFieldFibreBound_one (e : T ⟶ Y) [Etale e]
    (h : HasFieldFibreBound e 1) : IsOpenImmersion e := by
  have hinj : ∀ (K : Type u) [Field K],
      Function.Injective (fun g : Spec (.of K) ⟶ T => g ≫ e) := by
    intro K _ g₁ g₂ heq
    obtain ⟨hfin, hcard⟩ := h K (g₁ ≫ e)
    let := hfin
    have : Subsingleton {g : Spec (.of K) ⟶ T // g ≫ e = g₁ ≫ e} :=
      Finite.card_le_one_iff_subsingleton.mp hcard
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨g₁, rfl⟩ : {g : Spec (.of K) ⟶ T // g ≫ e = g₁ ≫ e})
        ⟨g₂, heq.symm⟩)
  have : UniversallyInjective e := (tfae_universallyInjective e).out 2 1 |>.mp hinj
  have : Surjective (pullback.diagonal e) :=
    (UniversallyInjective.iff_diagonal e).mp inferInstance
  have : IsIso (pullback.diagonal e) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : Mono e := (pullback.isIso_diagonal_iff e).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono e

namespace EtaleOffDiagonal

variable (e : T ⟶ Y) [Etale e] [IsSeparated e]

/-- The complement of the open and closed diagonal in the actual self-pullback. -/
def openComplement : (pullback e e).Opens :=
  ⟨(Set.range (pullback.diagonal e))ᶜ,
    (pullback.diagonal e).isClosedEmbedding.isClosed_range.isOpen_compl⟩

theorem openComplement_isClopen :
    IsClopen (openComplement e : Set (pullback e e : Scheme.{u})) :=
  ⟨(pullback.diagonal e).isOpenEmbedding.isOpen_range.isClosed_compl,
    (openComplement e).isOpen⟩

/-- The actual off-diagonal scheme. -/
abbrev scheme : Scheme.{u} := (openComplement e).toScheme

instance : IsClosedImmersion (openComplement e).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact (openComplement_isClopen e).isClosed)

instance [IsAffine T] [IsAffine Y] : IsAffine (scheme e) :=
  isAffine_of_isAffineHom (openComplement e).ι

/-- The first projection, restricted to the off-diagonal. -/
abbrev projection : scheme e ⟶ T :=
  (openComplement e).ι ≫ pullback.fst e e

instance : Etale (projection e) := by
  unfold projection
  infer_instance

instance : IsSeparated (projection e) := by
  unfold projection
  infer_instance

omit [Etale e] in
theorem fieldPoint_snd_ne_fst (K : Type u) [Field K]
    (g : Spec (.of K) ⟶ scheme e) :
    g ≫ (openComplement e).ι ≫ pullback.snd e e ≠ g ≫ projection e := by
  intro h
  have hg : g ≫ (openComplement e).ι =
      (g ≫ projection e) ≫ pullback.diagonal e := by
    apply pullback.hom_ext
    · simp [projection]
    · simpa [projection] using h
  let x := IsLocalRing.closedPoint K
  have hmem := (g x).property
  change (g ≫ (openComplement e).ι) x ∉ Set.range (pullback.diagonal e) at hmem
  rw [hg] at hmem
  exact hmem ⟨(g ≫ projection e) x, rfl⟩

omit [Etale e] in
/-- Removing the diagonal removes one field-valued lift in every fibre. -/
theorem hasFieldFibreBound (n : ℕ) (h : HasFieldFibreBound e (n + 1)) :
    HasFieldFibreBound (projection e) n := by
  intro K _ a
  let A := {g : Spec (.of K) ⟶ scheme e // g ≫ projection e = a}
  let B := {g : Spec (.of K) ⟶ T // g ≫ e = a ≫ e}
  let ev : A → B := fun g =>
    ⟨g.val ≫ (openComplement e).ι ≫ pullback.snd e e, by
      simpa only [projection, Category.assoc, pullback.condition] using
        congrArg (fun f => f ≫ e) g.property⟩
  have hev : Function.Injective ev := by
    intro g₁ g₂ heq
    apply Subtype.ext
    apply (cancel_mono (openComplement e).ι).mp
    apply pullback.hom_ext
    · exact g₁.property.trans g₂.property.symm
    · exact congrArg Subtype.val heq
  have hne (g : A) : ev g ≠ (⟨a, rfl⟩ : B) := by
    intro heq
    apply fieldPoint_snd_ne_fst e K g.val
    exact (congrArg Subtype.val heq).trans g.property.symm
  obtain ⟨hfin, hbound⟩ := h K (a ≫ e)
  let := hfin
  let : Finite A := Finite.of_injective ev hev
  let aug : Option A → B
    | none => ⟨a, rfl⟩
    | some g => ev g
  have haug : Function.Injective aug := by
    intro x y heq
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some g => exact False.elim (hne g heq.symm)
    | some g =>
      cases y with
      | none => exact False.elim (hne g heq)
      | some g' => exact congrArg some (hev heq)
  have hcard := (Nat.card_le_card_of_injective aug haug).trans hbound
  rw [Finite.card_option] at hcard
  exact ⟨inferInstance, by dsimp [A] at hcard ⊢; omega⟩

end EtaleOffDiagonal

end Langlands.AlgebraicGeometry

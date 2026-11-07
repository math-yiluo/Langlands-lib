import Langlands.CategoryTheory.Renard.NoetherianReflection

/-!
# Noetherianity detected by a finite family of functors

Renard VI.7.5 pulls back ascending chains along the faithful exact functor
`R` of VI.7.2, whose target is a product of categories. Here the product is
replaced by a finite family of functors: when the family jointly reflects
isomorphisms between monomorphisms, Noetherianity of every image reflects to
the source.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

namespace Langlands.Renard

universe w uC vC uD vD

variable {C : Type uC} [Category.{vC} C] {ι : Type w}
  {D : ι → Type uD} [∀ i, Category.{vD} (D i)] (F : ∀ i, C ⥤ D i)

/-- A monomorphism sent to an isomorphism by every member of the family is
itself an isomorphism. -/
def JointlyReflectsMonoIsos : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Mono f → (∀ i, IsIso ((F i).map f)) → IsIso f

/-- No nonzero object is sent to zero by every member of the family. -/
def JointlyDetectsZero : Prop :=
  ∀ X : C, (∀ i, IsZero ((F i).obj X)) → IsZero X

section PreservesMono

variable [∀ i, (F i).PreservesMonomorphisms]

/-- A strict inclusion of actual subobjects stays strict under some member
of a family jointly reflecting isomorphisms between monomorphisms. -/
theorem exists_functorSubobjectMap_lt (hF : JointlyReflectsMonoIsos F)
    {X : C} {P Q : Subobject X} (hPQ : P < Q) :
    ∃ i, functorSubobjectMap (F i) X P < functorSubobjectMap (F i) X Q := by
  by_contra h
  simp only [not_exists] at h
  have hIso : IsIso (Subobject.ofLE P Q hPQ.le) := by
    refine hF _ inferInstance (fun i => ?_)
    by_contra hi
    exact h i ((Subobject.mk_lt_mk_iff_of_comm
      ((F i).map (Subobject.ofLE P Q hPQ.le)) (by
        rw [← (F i).map_comp, Subobject.ofLE_arrow])).mpr hi)
  exact hPQ.ne (Subobject.eq_of_comm
    (asIso (Subobject.ofLE P Q hPQ.le)) (Subobject.ofLE_arrow hPQ.le))

/-- Noetherianity of every image under a finite family of
monomorphism-preserving functors that jointly reflects isomorphisms between
monomorphisms reflects to the source. -/
theorem noetherianObject_of_finite_family [Finite ι]
    (hF : JointlyReflectsMonoIsos F) (X : C)
    (hX : ∀ i, IsNoetherianObject ((F i).obj X)) : IsNoetherianObject X := by
  apply (noetherianMathlibComparison C X).mpr
  apply (CategoryTheory.isNoetherianObject_iff_not_strictMono X).mpr
  intro f hf
  have hstab : ∀ i, ∃ n : ℕ, ∀ m, n ≤ m →
      functorSubobjectMap (F i) X (f n) = functorSubobjectMap (F i) X (f m) := by
    intro i
    have : CategoryTheory.IsNoetherianObject ((F i).obj X) :=
      (noetherianMathlibComparison (D i) ((F i).obj X)).mp (hX i)
    exact CategoryTheory.monotone_chain_condition_of_isNoetherianObject
      ((functorSubobjectMap (F i) X).comp ⟨f, hf.monotone⟩)
  choose n hn using hstab
  obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
  obtain ⟨i, hi⟩ := exists_functorSubobjectMap_lt F hF (hf (Nat.lt_succ_self N))
  have hle : n i ≤ N := hN ⟨i, rfl⟩
  rw [← hn i N hle, ← hn i (N + 1) (hle.trans (Nat.le_succ N))] at hi
  exact lt_irrefl _ hi

/-- The category-level transfer: once source unions exist, a finite family
jointly reflecting isomorphisms between monomorphisms whose images of
finite-type objects are Noetherian makes the source category Noetherian. -/
theorem noetherianCategory_of_finite_family [Finite ι]
    (hF : JointlyReflectsMonoIsos F) (hUnions : HasAllSubobjectUnions C)
    (hX : ∀ X : C, IsFiniteTypeObject X → ∀ i, IsNoetherianObject ((F i).obj X)) :
    IsNoetherianCategory C :=
  ⟨hUnions, fun X hX' => noetherianObject_of_finite_family F hF X (hX X hX')⟩

end PreservesMono

section Abelian

variable [Abelian C] [∀ i, Abelian (D i)] [∀ i, (F i).Additive]

/-- Between abelian categories, epimorphism-preserving functors that jointly
detect zero objects jointly reflect isomorphisms between monomorphisms. -/
theorem jointlyReflectsMonoIsos_of_jointlyDetectsZero
    [∀ i, (F i).PreservesEpimorphisms] (hZ : JointlyDetectsZero F) :
    JointlyReflectsMonoIsos F := by
  intro X Y f hf hiso
  have hcok : IsZero (cokernel f) := by
    refine hZ _ (fun i => ?_)
    have hzero : (F i).map (cokernel.π f) = 0 := by
      rw [← cancel_epi ((F i).map f), ← (F i).map_comp, cokernel.condition,
        (F i).map_zero, comp_zero]
    exact IsZero.of_epi_eq_zero _ hzero
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hcok
  exact isIso_of_mono_of_epi f

/-- Renard's exactness for each member of a finite family jointly detecting
zero objects suffices for the chain argument of VI.7.5. -/
theorem noetherianObject_of_finite_exact_family [Finite ι]
    (hF : ∀ i, SequenceExact (F i)) (hZ : JointlyDetectsZero F) (X : C)
    (hX : ∀ i, IsNoetherianObject ((F i).obj X)) : IsNoetherianObject X := by
  have : ∀ i, (F i).PreservesMonomorphisms := fun i =>
    Functor.preservesMonomorphisms_of_preserves_shortExact_left (F i)
      (fun S hS => (hF i).1 S ⟨hS.exact, hS.mono_f⟩)
  have : ∀ i, (F i).PreservesEpimorphisms := fun i =>
    Functor.preservesEpimorphisms_of_preserves_shortExact_right (F i)
      (fun S hS => (hF i).2 S ⟨hS.exact, hS.epi_g⟩)
  exact noetherianObject_of_finite_family F
    (jointlyReflectsMonoIsos_of_jointlyDetectsZero F hZ) X hX

/-- Category-level form of `noetherianObject_of_finite_exact_family`. -/
theorem noetherianCategory_of_finite_exact_family [Finite ι]
    (hF : ∀ i, SequenceExact (F i)) (hZ : JointlyDetectsZero F)
    (hUnions : HasAllSubobjectUnions C)
    (hX : ∀ X : C, IsFiniteTypeObject X → ∀ i, IsNoetherianObject ((F i).obj X)) :
    IsNoetherianCategory C :=
  ⟨hUnions, fun X hX' => noetherianObject_of_finite_exact_family F hF hZ X (hX X hX')⟩

end Abelian

end Langlands.Renard

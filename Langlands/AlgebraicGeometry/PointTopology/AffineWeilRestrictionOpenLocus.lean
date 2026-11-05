import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionRepresentabilityProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Weil restriction of an open subscheme of an affine scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The locus whose entire fibre maps into a chosen open subscheme. -/
def universallyClosedFactorizationOpen {Z W X : Scheme.{u}} (π : Z ⟶ W)
    [UniversallyClosed π] (e : Z ⟶ X) (U : X.Opens) : W.Opens :=
  ⟨(π '' (e ⁻¹' (U : Set X)ᶜ))ᶜ,
    (π.isClosedMap _ (U.isOpen.isClosed_compl.preimage e.continuous)).isOpen_compl⟩

theorem mem_universallyClosedFactorizationOpen {Z W X : Scheme.{u}}
    (π : Z ⟶ W) [UniversallyClosed π] (e : Z ⟶ X) (U : X.Opens) (w : W) :
    w ∈ universallyClosedFactorizationOpen π e U ↔
      ∀ z : Z, π z = w → e z ∈ U := by
  classical
  change (w ∉ π '' (e ⁻¹' (U : Set X)ᶜ)) ↔ _
  constructor
  · intro h z hz
    by_contra hn
    exact h ⟨z, hn, hz⟩
  · rintro h ⟨z, hz, hzw⟩
    exact hz (h z hzw)

/-- The open locus detects factorization after every base change, including
nonaffine test schemes. -/
theorem range_subset_factorizationOpen_iff {Z W X T P : Scheme.{u}}
    (π : Z ⟶ W) [UniversallyClosed π] (e : Z ⟶ X) (U : X.Opens)
    (p : T ⟶ W) (q : P ⟶ Z) (πT : P ⟶ T)
    (h : IsPullback q πT π p) :
    Set.range p ⊆ universallyClosedFactorizationOpen π e U ↔
      Set.range (q ≫ e) ⊆ U := by
  constructor
  · rintro hp _ ⟨a, rfl⟩
    apply (mem_universallyClosedFactorizationOpen π e U _).mp
      (hp ⟨πT a, rfl⟩) (q a)
    exact congrArg (fun f : P ⟶ W => f a) h.w
  · rintro hq _ ⟨t, rfl⟩
    apply (mem_universallyClosedFactorizationOpen π e U _).mpr
    intro z hz
    obtain ⟨a, ha, _⟩ := Scheme.exists_preimage_of_isPullback h z t hz
    have he : e (q a) ∈ U := hq ⟨a, rfl⟩
    simpa [ha] using he

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Base change of a morphism gives the cartesian square over its source
and target, with the actual first projections. -/
theorem ringBaseChange_map_isPullback
    {T W : Over (Spec (CommRingCat.of A))} (p : T ⟶ W) :
    IsPullback ((Over.pullback (Spec.algebraMap A B)).map p).left
      (pullback.fst T.hom (Spec.algebraMap A B))
      (pullback.fst W.hom (Spec.algebraMap A B)) p.left := by
  let q := ((Over.pullback (Spec.algebraMap A B)).map p).left
  have hs : IsPullback
      (q ≫ pullback.snd W.hom (Spec.algebraMap A B))
      (pullback.fst T.hom (Spec.algebraMap A B))
      (Spec.algebraMap A B) (p.left ≫ W.hom) := by
    simpa only [q, Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback T.hom (Spec.algebraMap A B)).flip
  exact hs.of_right (by
      dsimp only [q, Over.pullback_map_left]
      exact pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback W.hom (Spec.algebraMap A B)).flip

variable [Module.Finite A B] [Module.Projective A B]
variable (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left]
  [LocallyOfFiniteType X.hom]

/-- An actual open subscheme of the constructed affine Weil restriction. -/
def affineWeilRestrictionOpenLocus (U : X.left.Opens) :
    (affineWeilRestriction A B X).left.Opens := by
  let : IsFinite (Spec.algebraMap A B) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  exact universallyClosedFactorizationOpen
    (pullback.fst (affineWeilRestriction A B X).hom (Spec.algebraMap A B))
    (affineWeilRestrictionCounit A B X).left U

/-- The canonical comparison lands in an open precisely when the test
morphism lands in the constructed open locus. -/
theorem range_subset_affineWeilRestrictionOpenLocus_iff
    (U : X.left.Opens) (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineWeilRestriction A B X) :
    Set.range p.left ⊆ affineWeilRestrictionOpenLocus A B X U ↔
      Set.range (affineWeilRestrictionComparison A B X T p).left ⊆ U := by
  let : IsFinite (Spec.algebraMap A B) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  exact range_subset_factorizationOpen_iff _ _ U p.left _ _
    (ringBaseChange_map_isPullback A B p)

/-- Weil restriction of any open subscheme of an affine finite-type scheme,
constructed as an actual open subscheme rather than as a point carrier. -/
def openAffineWeilRestriction (U : X.left.Opens) :
    Over (Spec (CommRingCat.of A)) :=
  openOver A (affineWeilRestriction A B X) (affineWeilRestrictionOpenLocus A B X U)

/-- The canonical universal-property map for the constructed open scheme. -/
def openAffineWeilRestrictionComparison (U : X.left.Opens)
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ openAffineWeilRestriction A B X U) :
    ringBaseChange A B T ⟶ openOver B X U := by
  let j := openOverι A (affineWeilRestriction A B X)
    (affineWeilRestrictionOpenLocus A B X U)
  have hp : Set.range (p ≫ j).left ⊆ affineWeilRestrictionOpenLocus A B X U := by
    rintro _ ⟨t, rfl⟩
    exact ((p.left t).property)
  exact relativeOpenLift B
    (affineWeilRestrictionComparison A B X T (p ≫ j)) U
    ((range_subset_affineWeilRestrictionOpenLocus_iff A B X U T (p ≫ j)).mp hp)

@[simp]
theorem openAffineWeilRestrictionComparison_fac (U : X.left.Opens)
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ openAffineWeilRestriction A B X U) :
    openAffineWeilRestrictionComparison A B X U T p ≫ openOverι B X U =
      affineWeilRestrictionComparison A B X T
        (p ≫ openOverι A (affineWeilRestriction A B X)
          (affineWeilRestrictionOpenLocus A B X U)) :=
  by
    unfold openAffineWeilRestrictionComparison
    exact relativeOpenLift_fac _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The comparison commutes with arbitrary morphisms of test schemes. -/
theorem openAffineWeilRestrictionComparison_natural (U : X.left.Opens)
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S)
    (p : S ⟶ openAffineWeilRestriction A B X U) :
    openAffineWeilRestrictionComparison A B X U T (f ≫ p) =
      (Over.pullback (Spec.algebraMap A B)).map f ≫
        openAffineWeilRestrictionComparison A B X U S p := by
  let i := openOverι B X U
  let j := openOverι A (affineWeilRestriction A B X)
    (affineWeilRestrictionOpenLocus A B X U)
  let : Mono i.left := inferInstanceAs (Mono U.ι)
  let : Mono i := Over.mono_of_mono_left i
  apply (cancel_mono i).mp
  calc
    _ = affineWeilRestrictionComparison A B X T ((f ≫ p) ≫ j) :=
      openAffineWeilRestrictionComparison_fac A B X U T (f ≫ p)
    _ = affineWeilRestrictionComparison A B X T (f ≫ (p ≫ j)) :=
      congrArg (affineWeilRestrictionComparison A B X T) (Category.assoc f p j)
    _ = (Over.pullback (Spec.algebraMap A B)).map f ≫
        affineWeilRestrictionComparison A B X S (p ≫ j) :=
      affineWeilRestrictionComparison_natural A B X f (p ≫ j)
    _ = (Over.pullback (Spec.algebraMap A B)).map f ≫
        (openAffineWeilRestrictionComparison A B X U S p ≫ i) :=
      congrArg (fun g => (Over.pullback (Spec.algebraMap A B)).map f ≫ g)
        (openAffineWeilRestrictionComparison_fac A B X U S p).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The open scheme represents restriction of scalars on every test scheme.
The open subscheme of the original affine scheme need not itself be affine. -/
theorem openAffineWeilRestrictionComparison_bijective (U : X.left.Opens)
    (T : Over (Spec (CommRingCat.of A))) :
    Function.Bijective (openAffineWeilRestrictionComparison A B X U T) := by
  let j := openOverι A (affineWeilRestriction A B X)
    (affineWeilRestrictionOpenLocus A B X U)
  let i := openOverι B X U
  let : Mono j.left :=
    inferInstanceAs (Mono (affineWeilRestrictionOpenLocus A B X U).ι)
  let : Mono i.left := inferInstanceAs (Mono U.ι)
  let : Mono j := Over.mono_of_mono_left j
  let : Mono i := Over.mono_of_mono_left i
  constructor
  · intro p q hpq
    apply (cancel_mono j).mp
    apply affineWeilRestrictionComparison_injective A B X T
    exact (openAffineWeilRestrictionComparison_fac A B X U T p).symm.trans
      ((congrArg (fun f => f ≫ i) hpq).trans
        (openAffineWeilRestrictionComparison_fac A B X U T q))
  · intro q
    obtain ⟨p, hp⟩ := affineWeilRestrictionComparison_surjective A B X T (q ≫ i)
    have hq : Set.range (q ≫ i).left ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact (q.left t).property
    have hr : Set.range p.left ⊆ affineWeilRestrictionOpenLocus A B X U :=
      (range_subset_affineWeilRestrictionOpenLocus_iff A B X U T p).mpr (hp ▸ hq)
    let p' : T ⟶ openAffineWeilRestriction A B X U :=
      relativeOpenLift A p (affineWeilRestrictionOpenLocus A B X U) hr
    refine ⟨p', ?_⟩
    apply (cancel_mono i).mp
    rw [openAffineWeilRestrictionComparison_fac]
    have hp' : p' ≫ j = p := relativeOpenLift_fac _ _ _ _
    rw [show p' ≫ openOverι A (affineWeilRestriction A B X)
      (affineWeilRestrictionOpenLocus A B X U) = p from hp']
    exact hp

end Langlands.AlgebraicGeometry.PointTopology

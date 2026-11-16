import Langlands.GroupScheme.Reductive.LocalRankOneWeylNormalization
import Langlands.GroupScheme.Reductive.LocalRootGroupTorusCoordinate
import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismAssembly

/-! # Weyl-normalized simple-root families over arbitrary local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open LocalSplitCell LocalWeylNormalization

/-- The simple roots and their negatives admit compatible actual root
parametrizations and simple-reflection Weyl points over every local ring. -/
theorem localSplitSimpleRootGroupLocal : LocalSplitSimpleRootGroupLocalStatement.{u} := by
  intro R _ _ G _ hG I _ _ i hi hmax J P hP b
  classical
  choose u hu using fun α => LocalRootGroup.exists_rootParametrization_of_flat i hG hmax hP α
  have hneg (a : J) : P.root (P.reflectionPerm a a) = -P.root a := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  choose d hd using fun a : b.support =>
    exists_unit_weylNormalization hG i hi hmax hP (a : J) (hu a)
      (by simpa only [hneg] using hu (P.reflectionPerm a a))
  let v : b.support → (Ga R ⟶ G) := fun a =>
    scaleHom (d a : R) ≫ u (P.reflectionPerm a a)
  have hv (a : b.support) :
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (v a) ∧
        IsWeylPoint i (weylPoint (u a) (v a)) (P.reflection a) :=
    ⟨(hu (P.reflectionPerm a a)).scale (d a), hd a⟩
  have hnm : ∀ a : b.support, P.reflectionPerm a a ∉ b.support := fun a h => by
    have hne : P.reflectionPerm a a ≠ a := fun h' => P.ne_neg (i := (a : J)) h'.symm
    apply b.root_ne_neg_of_ne h a.2 hne
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have hinj : ∀ a a' : b.support, P.reflectionPerm a' a' = P.reflectionPerm a a → a' = a := by
    intro a a' h
    apply Subtype.ext
    apply P.root.injective
    have h' := congrArg P.root h
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
      RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, neg_inj] at h'
    exact h'
  let u' : J → (Ga R ⟶ G) := fun α =>
    if h : ∃ a : b.support, P.reflectionPerm a a = α then v h.choose else u α
  have hs : ∀ a ∈ b.support, u' a = u a := by
    intro a ha
    refine dite_eq_right ?_
    rintro ⟨a', ha'⟩
    exact hnm a' (ha' ▸ ha)
  have hn : ∀ a : b.support, u' (P.reflectionPerm a a) = v a := by
    intro a
    have h : ∃ a' : b.support, P.reflectionPerm a' a' = P.reflectionPerm a a := ⟨a, rfl⟩
    change (if h : ∃ a' : b.support, P.reflectionPerm a' a' = P.reflectionPerm a a
      then v h.choose else u (P.reflectionPerm a a)) = v a
    rw [dite_eq_left h, hinj a _ h.choose_spec]
  refine ⟨u', fun a ha => ⟨?_, ?_⟩, fun a ha => ?_⟩
  · rw [hs a ha]
    exact hu a
  · have hn' : u' (P.reflectionPerm a a) = v ⟨a, ha⟩ := hn ⟨a, ha⟩
    rw [hn']
    exact (hv ⟨a, ha⟩).1
  · have hn' : u' (P.reflectionPerm a a) = v ⟨a, ha⟩ := hn ⟨a, ha⟩
    rw [hs a ha, hn']
    exact (hv ⟨a, ha⟩).2

namespace LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (hG : IsReductive G) {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)

/-- A chosen family of simple-root and negative-simple-root parametrizations
whose Weyl points realize the simple reflections. -/
def simpleRootFamilyLocal : J → (Ga R ⟶ G) :=
  (localSplitSimpleRootGroupLocal R G hG I i hi hmax J P hP b).choose

/-- The chosen family has the required parametrizations at every simple root
and its negative, and its Weyl products act by the simple reflections. -/
theorem simpleRootFamilyLocal_spec :
    (∀ a ∈ b.support,
      IsRootParametrization i (P.root a) (simpleRootFamilyLocal hG i hi hmax hP b a) ∧
      IsRootParametrization i (P.root (P.reflectionPerm a a))
        (simpleRootFamilyLocal hG i hi hmax hP b (P.reflectionPerm a a))) ∧
    ∀ a ∈ b.support, IsWeylPoint i
      (weylPoint (simpleRootFamilyLocal hG i hi hmax hP b a)
        (simpleRootFamilyLocal hG i hi hmax hP b (P.reflectionPerm a a)))
      (P.reflection a) :=
  (localSplitSimpleRootGroupLocal R G hG I i hi hmax J P hP b).choose_spec

end LocalSplitCell

end Langlands.GroupScheme

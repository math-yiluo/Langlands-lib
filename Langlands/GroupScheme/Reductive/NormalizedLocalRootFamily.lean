import Langlands.GroupScheme.Reductive.LocalRankOneWeylNormalization
import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismAssembly
import Langlands.GroupScheme.Reductive.LocalSplitSimpleRootGroupLocal

/-! # Weyl-normalized root families over arbitrary local rings -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (hG : IsReductive G)
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)

include hG hi hmax hP in
/-- Every root has a parametrization, simultaneously normalized at the
simple opposite pairs, over an arbitrary local ring. -/
theorem exists_normalizedLocalRootFamily :
    ∃ u : J → (Ga R ⟶ G),
      (∀ α, IsRootParametrization i (P.root α) (u α)) ∧
      ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a) := by
  classical
  choose u hu using fun α : J =>
    LocalRootGroup.exists_rootParametrization_of_flat i hG hmax hP α
  have hex (a : b.support) :
      ∃ v : Ga R ⟶ G,
        IsRootParametrization i (P.root (P.reflectionPerm a a)) v ∧
        IsWeylPoint i (weylPoint (u a) v) (P.reflection a) := by
    have hm : IsRootParametrization i (-P.root a) (u (P.reflectionPerm a a)) := by
      simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
        using hu (P.reflectionPerm a a)
    obtain ⟨d, hd⟩ := exists_unit_weylNormalization hG i hi hmax hP (a : J) (hu a) hm
    exact ⟨scaleHom (d : R) ≫ u (P.reflectionPerm a a),
      (hu (P.reflectionPerm a a)).scale d, hd⟩
  choose v hv using hex
  have hnm : ∀ a : b.support, P.reflectionPerm a a ∉ b.support := fun a h => by
    have hne : P.reflectionPerm a a ≠ a := fun h' => P.ne_neg (i := (a : J)) h'.symm
    apply b.root_ne_neg_of_ne h a.2 hne
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have hinj : ∀ a a' : b.support,
      P.reflectionPerm a' a' = P.reflectionPerm a a → a' = a := by
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
  refine ⟨u', ?_, fun a ha => ?_⟩
  · intro α
    by_cases h : ∃ a : b.support, P.reflectionPerm a a = α
    · change IsRootParametrization i (P.root α)
        (if h : ∃ a : b.support, P.reflectionPerm a a = α then v h.choose else u α)
      rw [dite_eq_left h]
      simpa only [h.choose_spec] using (hv h.choose).1
    · change IsRootParametrization i (P.root α)
        (if h : ∃ a : b.support, P.reflectionPerm a a = α then v h.choose else u α)
      rw [dite_eq_right h]
      exact hu α
  · have hn' : u' (P.reflectionPerm a a) = v ⟨a, ha⟩ := hn ⟨a, ha⟩
    change IsWeylPoint i (weylPoint (u' a) (u' (P.reflectionPerm a a))) _
    rw [hs a ha, hn']
    exact (hv ⟨a, ha⟩).2

/-- A chosen actual root family with the simple pairs Weyl-normalized. -/
def normalizedLocalRootFamily : J → (Ga R ⟶ G) :=
  (exists_normalizedLocalRootFamily hG i hi hmax hP b).choose

theorem isRootParametrization_normalizedLocalRootFamily (α : J) :
    IsRootParametrization i (P.root α) (normalizedLocalRootFamily hG i hi hmax hP b α) :=
  (exists_normalizedLocalRootFamily hG i hi hmax hP b).choose_spec.1 α

theorem isWeylPoint_normalizedLocalRootFamily {a : J} (ha : a ∈ b.support) :
    IsWeylPoint i (rootWeylPoint P (normalizedLocalRootFamily hG i hi hmax hP b) a)
      (P.reflection a) :=
  (exists_normalizedLocalRootFamily hG i hi hmax hP b).choose_spec.2 a ha

end Langlands.GroupScheme.LocalSplitCell

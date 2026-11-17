import Langlands.GroupScheme.Reductive.AffineOppositeRootNormalization
import Langlands.GroupScheme.Reductive.GlobalSplitRootParametrization
import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismAssembly

/-! # Weyl-normalized root families over arbitrary affine bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R]
    {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)

include hG hi hmax hP in
/-- Normalize the simple opposite pairs of any actual global root
family, preserving all its simple positive root maps. -/
theorem exists_normalizedAffineRootFamily_of_maps
    (u : J → (Ga R ⟶ G))
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α)) :
    ∃ v : J → (Ga R ⟶ G),
      (∀ α, IsRootParametrization i (P.root α) (v α)) ∧
      (∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P v a) (P.reflection a)) ∧
      ∀ a ∈ b.support, v a = u a := by
  classical
  have hex (a : b.support) :
      ∃ v : Ga R ⟶ G,
        IsRootParametrization i (P.root (P.reflectionPerm a a)) v ∧
        IsWeylPoint i (weylPoint (u a) v) (P.reflection a) := by
    have hm : IsRootParametrization i (-P.root a) (u (P.reflectionPerm a a)) := by
      simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
        using hu (P.reflectionPerm a a)
    obtain ⟨d, hd⟩ :=
      exists_unit_weylNormalization_affine hG i hi hmax hP (a : J) (hu a) hm
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
  refine ⟨u', ?_, ?_, hs⟩
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
  · intro a ha
    have hn' : u' (P.reflectionPerm a a) = v ⟨a, ha⟩ := hn ⟨a, ha⟩
    change IsWeylPoint i (weylPoint (u' a) (u' (P.reflectionPerm a a))) _
    rw [hs a ha, hn']
    exact (hv ⟨a, ha⟩).2

/-- Normalize supplied global root maps, preserving their simple maps. -/
def normalizedAffineRootFamilyOfMaps
    (u : J → (Ga R ⟶ G))
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α)) :
    J → (Ga R ⟶ G) :=
  (exists_normalizedAffineRootFamily_of_maps hG i hi hmax hP b u hu).choose

theorem isRootParametrization_normalizedAffineRootFamilyOfMaps
    (u : J → (Ga R ⟶ G))
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α)) (α : J) :
    IsRootParametrization i (P.root α)
      (normalizedAffineRootFamilyOfMaps hG i hi hmax hP b u hu α) :=
  (exists_normalizedAffineRootFamily_of_maps hG i hi hmax hP b u hu).choose_spec.1 α

theorem isWeylPoint_normalizedAffineRootFamilyOfMaps
    (u : J → (Ga R ⟶ G))
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α))
    {a : J} (ha : a ∈ b.support) :
    IsWeylPoint i
      (rootWeylPoint P (normalizedAffineRootFamilyOfMaps hG i hi hmax hP b u hu) a)
      (P.reflection a) :=
  (exists_normalizedAffineRootFamily_of_maps hG i hi hmax hP b u hu).choose_spec.2.1 a ha

theorem normalizedAffineRootFamilyOfMaps_eq_simple
    (u : J → (Ga R ⟶ G))
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α))
    {a : J} (ha : a ∈ b.support) :
    normalizedAffineRootFamilyOfMaps hG i hi hmax hP b u hu a = u a :=
  (exists_normalizedAffineRootFamily_of_maps hG i hi hmax hP b u hu).choose_spec.2.2 a ha

variable (hfree : ∀ α : J, Nonempty
    (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
      CommRingCat.of R))

/-- Actual root parametrizations from free root spaces, with every
simple opposite pair Weyl-normalized over the original affine base. -/
def normalizedAffineRootFamily : J → (Ga R ⟶ G) :=
  normalizedAffineRootFamilyOfMaps hG i hi hmax hP b
    (LocalRootGroup.rootParametrizationsOfFreeWeights i hG hmax hP hfree)
    (LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights
      i hG hmax hP hfree)

theorem isRootParametrization_normalizedAffineRootFamily (α : J) :
    IsRootParametrization i (P.root α)
      (normalizedAffineRootFamily hG i hi hmax hP b hfree α) :=
  isRootParametrization_normalizedAffineRootFamilyOfMaps hG i hi hmax hP b _ _ α

theorem isWeylPoint_normalizedAffineRootFamily {a : J} (ha : a ∈ b.support) :
    IsWeylPoint i
      (rootWeylPoint P (normalizedAffineRootFamily hG i hi hmax hP b hfree) a)
      (P.reflection a) :=
  isWeylPoint_normalizedAffineRootFamilyOfMaps hG i hi hmax hP b _ _ ha

end Langlands.GroupScheme.LocalSplitCell

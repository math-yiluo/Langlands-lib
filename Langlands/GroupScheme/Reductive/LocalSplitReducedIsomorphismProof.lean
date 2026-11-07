import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationProof
import Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismReduction

/-! # Proof: the Isomorphism Theorem for split reductive groups over a reduced local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open LocalSplitCell

/-- **Root groups at the simple roots over a reduced local ring.** Every root has a root
parametrization (`LocalRootGroup.exists_rootParametrization`); for each simple root `a` the
parametrization of `-a` is replaced by the Weyl-normalized one of
`localWeylNormalization_of_field fieldWeylNormalization`. -/
theorem localSplitSimpleRootGroup : LocalSplitSimpleRootGroupStatement.{u} := by
  intro R _ _ _ G _ hG I _ _ i hi hmax J P hP b
  classical
  have hW := localWeylNormalization_of_field fieldWeylNormalization
  choose u hu using fun α => LocalRootGroup.exists_rootParametrization hG i hmax hP α
  choose v hv using fun a : b.support => hW R G hG I i hi hmax J P hP b a a.2 (u a) (hu a)
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

/-- **The Isomorphism Theorem over a reduced local ring.** -/
theorem localSplitReducedIsomorphismTheorem : LocalSplitReducedIsomorphismTheoremStatement.{u} :=
  localSplitReducedIsomorphismTheorem_of_simpleRootGroups localSplitSimpleRootGroup

end Langlands.GroupScheme

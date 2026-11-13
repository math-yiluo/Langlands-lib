import Langlands.GroupScheme.SectionComparisonNaturality
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Maximal split tori under isomorphisms of fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

/-- Pullback along a field isomorphism `e : k ≃+* K` preserves maximal split tori. A
factorization of the base change through a split subtorus over `K` is pulled back along
`e⁻¹`, where maximality over `k` applies, and pulled back along `e` again. -/
theorem IsMaximalSplitTorus.baseChange_fieldIso (hi : IsMaximalSplitTorus i) (e : k ≃+* K) :
    IsMaximalSplitTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom e.toRingHom))).obj T)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom e.toRingHom))).map i) := by
  let b := Spec.map (CommRingCat.ofHom e.toRingHom)
  let a := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have ha : a ≫ b = 𝟙 (Spec (CommRingCat.of k)) := by
    dsimp [a, b]
    rw [← Spec.map_comp]
    have he : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom =
        𝟙 (CommRingCat.of k) := by
      ext x
      exact e.symm_apply_apply x
    exact (congrArg Spec.map he).trans (Spec.map_id _)
  have hb : b ≫ a = 𝟙 (Spec (CommRingCat.of K)) := by
    dsimp [a, b]
    rw [← Spec.map_comp]
    have he : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom e.toRingHom =
        𝟙 (CommRingCat.of K) := by
      ext x
      exact e.apply_symm_apply x
    exact (congrArg Spec.map he).trans (Spec.map_id _)
  refine ⟨⟨hi.1.1.baseChange b, IsClosedSubgroup.baseChange b hi.1.2⟩, ?_⟩
  intro T' i' hi' f hf
  -- pull the factorization back to `k` along `a`
  let T₀ := (CommGroupScheme.baseChange a).obj T'
  let i₀ : T₀.toGrp ⟶ G :=
    (GroupScheme.baseChange a).map i' ≫ (baseChangeSectionIso b a ha G).hom
  have hi₀ : IsSplitSubtorus i₀ :=
    ⟨hi'.1.baseChange a, (IsClosedSubgroup.baseChange a hi'.2).comp_iso _⟩
  let f₀ : T.toGrp ⟶ T₀.toGrp :=
    (baseChangeSectionIso b a ha T.toGrp).inv ≫ (GroupScheme.baseChange a).map f
  have hf₀ : f₀ ≫ i₀ = i := by
    simp only [f₀, i₀, Category.assoc]
    rw [← Category.assoc ((GroupScheme.baseChange a).map f), ← Functor.map_comp, hf,
      RadicalFieldTransport.sectionIso_naturality b a ha i, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  have : IsIso f₀ := hi.2 T₀ i₀ hi₀ f₀ hf₀
  have : IsIso ((GroupScheme.baseChange a).map f) := by
    have hfa : (GroupScheme.baseChange a).map f =
        (baseChangeSectionIso b a ha T.toGrp).hom ≫ f₀ := by
      simp only [f₀, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hfa]
    infer_instance
  -- pull back along `b` to recover `f`
  have hfb : f = (baseChangeSectionIso a b hb _).inv ≫
      (GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map f) ≫
        (baseChangeSectionIso a b hb T'.toGrp).hom := by
    rw [RadicalFieldTransport.sectionIso_naturality a b hb f, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  rw [hfb]
  infer_instance

end Langlands.GroupScheme

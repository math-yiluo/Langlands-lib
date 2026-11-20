import Langlands.GroupScheme.Trigonalizable.UnipotentKernelMaximal
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois

/-! # Greatest unipotent closed subgroups under field isomorphisms and Galois transport -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]

/-- A closed subgroup `i : U ⟶ G` with unipotent source that contains every unipotent closed
subgroup of `G`, on every test scheme. No smoothness or connectedness is required. -/
structure IsGreatestUnipotentSubgroup {U G : GroupScheme (Spec (CommRingCat.of k))}
    (i : U ⟶ G) : Prop where
  isClosedSubgroup : IsClosedSubgroup i
  isUnipotent : IsUnipotent U
  greatest : ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G),
    IsClosedSubgroup j → IsUnipotent V → SubgroupFunctor.range j ≤ SubgroupFunctor.range i

namespace IsGreatestUnipotentSubgroup

variable {U V G G' : GroupScheme (Spec (CommRingCat.of k))} {i : U ⟶ G}

/-- Two greatest unipotent closed subgroups have the same range. -/
theorem range_eq (hi : IsGreatestUnipotentSubgroup i) {j : V ⟶ G}
    (hj : IsGreatestUnipotentSubgroup j) :
    SubgroupFunctor.range i = SubgroupFunctor.range j :=
  le_antisymm (hj.greatest U i hi.isClosedSubgroup hi.isUnipotent)
    (hi.greatest V j hj.isClosedSubgroup hj.isUnipotent)

/-- Transport along an isomorphism of ambient groups. -/
theorem comp_iso (hi : IsGreatestUnipotentSubgroup i) (e : G ≅ G') :
    IsGreatestUnipotentSubgroup (i ≫ e.hom) := by
  refine ⟨hi.isClosedSubgroup.comp_iso e, hi.isUnipotent, ?_⟩
  intro H j hj hu
  have hle := hi.greatest H (j ≫ e.inv) (hj.comp_iso e.symm) hu
  have hle' := SubgroupFunctor.range_comp_mono hle e.hom
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hle'

/-- A greatest unipotent closed subgroup is preserved by base change along an isomorphism of
ground fields. -/
theorem baseChange_ringEquiv {K : Type u} [Field K] [IsAffineHom G.X.hom]
    (hi : IsGreatestUnipotentSubgroup i) (f : k ≃+* K) :
    IsGreatestUnipotentSubgroup ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom f.toRingHom))).map i) := by
  let b := Spec.map (CommRingCat.ofHom f.toRingHom)
  let a := Spec.map (CommRingCat.ofHom f.symm.toRingHom)
  have ha : a ≫ b = 𝟙 _ := by
    dsimp [a, b]
    rw [← Spec.map_comp]
    change Spec.map
      (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom f.symm.toRingHom) = _
    have h : CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom f.symm.toRingHom =
        𝟙 (CommRingCat.of k) := by
      ext x
      exact f.symm_apply_apply x
    rw [h, Spec.map_id]
  have : IsIso b := isIso_SpecMap_iff.mpr f.bijective
  have : IsIso a := isIso_SpecMap_iff.mpr f.symm.bijective
  have : IsAffineHom U.X.hom := hi.isClosedSubgroup.isAffineHom
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  refine ⟨hi.isClosedSubgroup.baseChange b,
    RadicalFieldTransport.isUnipotent_map f.toRingHom hi.isUnipotent, ?_⟩
  intro H j hj hu
  have : IsAffineHom H.X.hom := hj.isAffineHom
  let e := baseChangeSectionIso b a ha G
  have hj' := (hj.baseChange a).comp_iso e
  have hle := hi.greatest ((GroupScheme.baseChange a).obj H)
    ((GroupScheme.baseChange a).map j ≫ e.hom) hj'
    (RadicalFieldTransport.isUnipotent_map f.symm.toRingHom hu)
  have : IsClosedImmersion ((GroupScheme.baseChange b).map i).hom.hom.left :=
    hi.isClosedSubgroup.baseChange b
  have : Mono ((GroupScheme.baseChange b).map i).hom.hom := Over.mono_of_mono_left _
  exact RadicalFieldTransport.range_le_of_section b a ha i j hle

end IsGreatestUnipotentSubgroup

/-- Milne 16.6, uniqueness part, in packaged form: the kernel of an fppf quotient onto a group of
multiplicative type is a greatest unipotent closed subgroup when its source is unipotent. -/
theorem IsUnipotent.isGreatestUnipotentSubgroup
    {G U M : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {i : U ⟶ G} {q : G ⟶ M} (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hM : IsMultiplicativeType M) : IsGreatestUnipotentSubgroup i :=
  ⟨hi, hU, fun _ j hj hV => IsUnipotent.range_le_of_isFppfQuotient i q hq hM j hj hV⟩

end Field

section Galois

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of K))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G}

/-- A greatest unipotent closed subgroup over `K` of a group defined over `k` is invariant under
every `k`-automorphism of `K`. -/
theorem IsGreatestUnipotentSubgroup.range_radicalGaloisHom [IsAffineHom G.X.hom]
    (hi : IsGreatestUnipotentSubgroup i) (σ : K ≃ₐ[k] K) :
    SubgroupFunctor.range (radicalGaloisHom i σ) = SubgroupFunctor.range i := by
  have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
    infer_instance
  exact ((hi.baseChange_ringEquiv σ.toRingEquiv).comp_iso
    (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G)).range_eq hi

end Galois

end Langlands.GroupScheme

import Langlands.GroupScheme.Torus.ClosedSubgroupPresentationStatement
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Closed subgroups of diagonalizable groups are diagonalizable -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.Diagonalizable

/-- A Hopf-algebra map whose relative spectrum is a closed subgroup is surjective. -/
theorem surjective_of_isClosedSubgroup_hopfSpec {R : CommRingCat.{u}}
    {A B : CommHopfAlgCat.{u} R} (φ : A ⟶ B)
    (h : IsClosedSubgroup ((hopfSpec R).map φ.op)) :
    Function.Surjective φ.hom := by
  set ψ := ((commAlgCatEquivUnder R).functor.map
    (CommAlgCat.ofHom (φ.hom : A →ₐ[R] B))).right
  have hψ : Spec.map ψ = ((hopfSpec R).map φ.op).hom.hom.left := rfl
  have : IsClosedImmersion (Spec.map ψ) := hψ ▸ h
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ψ)).2
  have hψ' : ψ = (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫ (Scheme.ΓSpecIso _).hom := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hs : Function.Surjective ψ := by
    rw [hψ']
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp
      (hsurj.comp (ConcreteCategory.bijective_of_isIso _).2)
  exact hs

/-- Over a field, a set of group-like elements spanning a coalgebra contains every
group-like element. -/
theorem groupLike_mem_of_span_eq_top {k : Type u} [Field k] {C : Type v} [AddCommGroup C]
    [Module k C] [Coalgebra k C] {T : Set C} (hT : T ⊆ {c : C | IsGroupLikeElem k c})
    (hspan : Submodule.span k T = ⊤) {g : C} (hg : IsGroupLikeElem k g) : g ∈ T := by
  by_contra h
  have hli : LinearIndepOn k id (insert g T) :=
    linearIndepOn_isGroupLikeElem.mono (Set.insert_subset hg hT)
  exact hli.notMem_span_of_insert h (by simp [hspan])

/-- Milne (2022), Theorems 12.8 and 12.9: every closed subgroup of `D(Λ)` over a field
is isomorphic to `D(Λ')` for a finitely generated abelian group `Λ'`. -/
theorem closedSubgroupPresentation : ClosedSubgroupPresentationStatement.{u} := by
  intro k _ Λ _ _ H i hi
  classical
  let R := CommRingCat.of k
  have : IsAffine (groupScheme R Λ).X.left := isAffine_of_isAffineHom (groupScheme R Λ).X.hom
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let B := AffineCoordinates.hopfAlgebra H
  let e₁ := hopfSpecIso R Λ
  let e₂ := AffineCoordinates.hopfSpecIso H
  let φ : hopfAlgebra R Λ ⟶ B := (hopfSpec.fullyFaithful.preimage (e₂.hom ≫ i ≫ e₁.inv)).unop
  have hφ : (hopfSpec R).map φ.op = e₂.hom ≫ i ≫ e₁.inv :=
    hopfSpec.fullyFaithful.map_preimage _
  have hcl : IsClosedSubgroup ((hopfSpec R).map φ.op) := by
    rw [hφ]
    exact IsClosedSubgroup.iso_comp e₂ (hi.comp_iso e₁.symm)
  have hsurj := surjective_of_isClosedSubgroup_hopfSpec φ hcl
  -- The images of the group-like basis of `k[Λ]` span the coordinate algebra of `H`.
  let T : Set B := φ.hom '' {a : AddMonoidAlgebra k Λ | IsGroupLikeElem k a}
  have hTsub : T ⊆ {b : B | IsGroupLikeElem k b} := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha.map φ.hom
  have hTspan : Submodule.span k T = ⊤ := by
    have hm := Submodule.map_span φ.hom.toLinearMap
      {a : AddMonoidAlgebra k Λ | IsGroupLikeElem k a}
    rw [AddMonoidAlgebra.span_isGroupLikeElem, Submodule.map_top,
      LinearMap.range_eq_top.2 hsurj] at hm
    exact hm.symm
  have hspan : Submodule.span k {b : B | IsGroupLikeElem k b} = ⊤ :=
    top_unique (hTspan ▸ Submodule.span_mono hTsub)
  -- The characters of `Λ` map onto the group-like elements of `B`.
  let ψ : Λ →+ Additive (GroupLike k B) :=
    AddMonoidHom.mk' (fun l => Additive.ofMul ⟨φ.hom (AddMonoidAlgebra.single l 1),
      (AddMonoidAlgebra.isGroupLikeElem_single_one (R := k) l).map φ.hom⟩) (by
        intro a b
        apply Additive.toMul.injective
        apply GroupLike.val_injective
        simp only [toMul_ofMul, toMul_add, GroupLike.val_mul, ← map_mul,
          AddMonoidAlgebra.single_mul_single, one_mul])
  have hψ : Function.Surjective ψ := by
    intro g
    obtain ⟨a, ha, hga⟩ :=
      groupLike_mem_of_span_eq_top hTsub hTspan (Additive.toMul g).isGroupLikeElem_val
    obtain ⟨l, rfl⟩ := AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one.1 ha
    exact ⟨l, Additive.toMul.injective (GroupLike.val_injective hga)⟩
  have hfg : AddGroup.FG (Additive (GroupLike k B)) := AddGroup.fg_of_surjective hψ
  -- Reconstruct `B` as the group algebra of its group-like elements.
  let eRec : B ≃ₐc[k] AddMonoidAlgebra k (Additive (GroupLike k B)) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv k k (GroupLike k B))
  let eT := AffineCoordinates.isoOfBialgEquiv H
    (hopfAlgebra R (Additive (GroupLike k B))) eRec
  exact ⟨Additive (GroupLike k B), inferInstance, hfg,
    ⟨eT.symm ≪≫ hopfSpecIso R (Additive (GroupLike k B))⟩⟩

end Langlands.GroupScheme.Diagonalizable

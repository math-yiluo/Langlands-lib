import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismLocality
import Langlands.GroupScheme.HomScheme.AffineTest
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Character locality and faithfulness on arbitrary scheme tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Diagonalizable

open HomScheme

variable {R : CommRingCat.{u}} {M N : Type u} [AddCommGroup M] [AddCommGroup N]

/-- Character restriction is faithful over any nonzero coefficient ring. -/
theorem restrictMap_injective [Nontrivial R] :
    Function.Injective (restrictMap R : (N →+ M) →
      ((groupScheme R M).toGrp ⟶ (groupScheme R N).toGrp)) := by
  intro g h he
  have hs := congrArg (fun f => f.hom.hom.left) he
  rw [restrictMap_left, restrictMap_left] at hs
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  apply AddMonoidHom.ext
  intro n
  apply AddMonoidAlgebra.single_left_injective (R := R) one_ne_zero
  have hh := DFunLike.congr_fun hr (AddMonoidAlgebra.single n 1)
  change AddMonoidAlgebra.mapDomainRingHom R g (AddMonoidAlgebra.single n 1) =
    AddMonoidAlgebra.mapDomainRingHom R h (AddMonoidAlgebra.single n 1) at hh
  simpa only [AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single] using hh

/-- Distinct character maps remain distinct after base change to any nonempty
relative test scheme, including disconnected and nonreduced tests. -/
theorem restrictMap_baseChange_injective (T : Over (Spec R)) [Nonempty T.left] :
    Function.Injective (fun g : N →+ M =>
      (GroupScheme.baseChange T.hom).map (restrictMap R g)) := by
  intro g h he
  let x : T.left := Classical.choice inferInstance
  let K := T.left.residueField x
  let a : Spec K ⟶ T.left := T.left.fromSpecResidueField x
  let V : Over (Spec R) := Over.mk (a ≫ T.hom)
  let v : V ⟶ T := Over.homMk a rfl
  have he' : (GroupScheme.baseChange V.hom).map (restrictMap R g) =
      (GroupScheme.baseChange V.hom).map (restrictMap R h) := by
    have hp := congrArg (evaluate v) he
    simpa only [evaluate, Descent.pullHom_map] using hp
  have hK : restrictMap K g = restrictMap K h := by
    apply (cancel_epi (baseChangeIso V.hom M).hom).mp
    rw [← baseChangeIso_restrictMap, ← baseChangeIso_restrictMap, he']
  exact restrictMap_injective hK

/-- Faithfulness also holds when character maps are indexed by equivalences. -/
theorem restrictEquiv_baseChange_injective (T : Over (Spec R)) [Nonempty T.left] :
    Function.Injective (fun g : N ≃+ M =>
      (GroupScheme.baseChange T.hom).map (restrictMap R g.toAddMonoidHom)) := by
  intro g h he
  apply AddEquiv.toAddMonoidHom_injective
  exact restrictMap_baseChange_injective T he

/-- Transport the affine character locality theorem through the canonical
comparison for a diagonalizable group already pulled to a spectrum. -/
theorem exists_open_neighborhood_eq_restrictMap_on_spec_test
    [AddMonoid.FG N] {C : CommRingCat.{u}} (b : Spec C ⟶ Spec R)
    (e : (GroupScheme.baseChange b).obj (groupScheme R M).toGrp ≅
      (GroupScheme.baseChange b).obj (groupScheme R N).toGrp) (x : Spec C) :
    ∃ (D : CommRingCat.{u}) (a : Spec D ⟶ Spec C) (g : N ≃+ M),
      IsOpenImmersion a ∧ x ∈ Set.range a ∧
        (GroupScheme.baseChange a).map e.hom =
          (GroupScheme.baseChange a).map
            ((GroupScheme.baseChange b).map (restrictMap R g.toAddMonoidHom)) := by
  let iM := baseChangeIso b M
  let iN := baseChangeIso b N
  let e' : (groupScheme C M).toGrp ≅ (groupScheme C N).toGrp := iM.symm ≪≫ e ≪≫ iN
  obtain ⟨D, a, g, ha, hx, he⟩ := exists_open_neighborhood_eq_restrictMap e' x
  refine ⟨D, a, g, ha, hx, ?_⟩
  have he' : e.hom = iM.hom ≫ e'.hom ≫ iN.inv := by
    simp only [e', Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hg : (GroupScheme.baseChange b).map (restrictMap R g.toAddMonoidHom) =
      iM.hom ≫ restrictMap C g.toAddMonoidHom ≫ iN.inv := by
    apply (cancel_mono iN.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      baseChangeIso_restrictMap b g.toAddMonoidHom
  rw [he', hg]
  simp only [Functor.map_comp, he]

/-- Every diagonalizable isomorphism on an arbitrary relative test scheme is
locally induced by a single additive character equivalence. -/
theorem exists_open_neighborhood_eq_restrictMap_on_test
    [AddMonoid.FG N] (T : Over (Spec R))
    (e : (GroupScheme.baseChange T.hom).obj (groupScheme R M).toGrp ≅
      (GroupScheme.baseChange T.hom).obj (groupScheme R N).toGrp) (x : T.left) :
    ∃ (W : Over (Spec R)) (a : W ⟶ T) (g : N ≃+ M),
      IsOpenImmersion a.left ∧ x ∈ Set.range a.left ∧
        evaluate a e.hom =
          (GroupScheme.baseChange W.hom).map (restrictMap R g.toAddMonoidHom) := by
  obtain ⟨k, z, rfl⟩ := T.left.affineCover.exists_eq x
  let V := affineCoverOver T k
  let v := affineCoverHom T k
  let eV := Descent.pullIso v.left (Over.w v) (Over.w v) e
  obtain ⟨D, b, g, hb, hz, he⟩ :=
    exists_open_neighborhood_eq_restrictMap_on_spec_test V.hom eV z
  let W : Over (Spec R) := Over.mk (b ≫ V.hom)
  let w : W ⟶ V := Over.homMk b rfl
  refine ⟨W, w ≫ v, g, ?_, ?_, ?_⟩
  · change IsOpenImmersion (b ≫ T.left.affineCover.f k)
    let : IsOpenImmersion b := hb
    infer_instance
  · obtain ⟨y, hy⟩ := hz
    exact ⟨y, congrArg (T.left.affineCover.f k) hy⟩
  · rw [evaluate_comp]
    have hEval : evaluate w eV.hom =
        evaluate w ((GroupScheme.baseChange V.hom).map
          (restrictMap R g.toAddMonoidHom)) := by
      have hew : (GroupScheme.baseChange w.left).map eV.hom =
          (GroupScheme.baseChange w.left).map
            ((GroupScheme.baseChange V.hom).map (restrictMap R g.toAddMonoidHom)) := he
      unfold evaluate Descent.pullHom
      rw [hew]
    change evaluate w eV.hom = _
    rw [hEval]
    exact Descent.pullHom_map w.left V.hom W.hom (Over.w w)
      (restrictMap R g.toAddMonoidHom)

/-- Character equivalence and neighborhood data for an arbitrary scheme test. -/
structure RelativeLocalCharacterModel (T : Over (Spec R))
    (e : (GroupScheme.baseChange T.hom).obj (groupScheme R M).toGrp ≅
      (GroupScheme.baseChange T.hom).obj (groupScheme R N).toGrp) (x : T.left) where
  scheme : Over (Spec R)
  map : scheme ⟶ T
  character : N ≃+ M
  openImmersion : IsOpenImmersion map.left
  contains : x ∈ Set.range map.left
  equation : evaluate map e.hom =
    (GroupScheme.baseChange scheme.hom).map (restrictMap R character.toAddMonoidHom)

/-- Choose the local character description on an arbitrary relative test. -/
def relativeLocalCharacterModel [AddMonoid.FG N] (T : Over (Spec R))
    (e : (GroupScheme.baseChange T.hom).obj (groupScheme R M).toGrp ≅
      (GroupScheme.baseChange T.hom).obj (groupScheme R N).toGrp) (x : T.left) :
    RelativeLocalCharacterModel T e x :=
  Classical.choice (by
    obtain ⟨W, a, g, ha, hx, he⟩ := exists_open_neighborhood_eq_restrictMap_on_test T e x
    exact ⟨⟨W, a, g, ha, hx, he⟩⟩)

end Langlands.GroupScheme.Diagonalizable

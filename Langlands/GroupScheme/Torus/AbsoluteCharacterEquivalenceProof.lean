import Langlands.GroupScheme.Torus.AbsoluteCharacterEquivalenceStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteEquivalenceProof

/-! # The absolute Galois character anti-equivalence for field tori: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme

/-- Freeness of the absolute characters of a multiplicative-type group implies
that the group is a torus. -/
private theorem isTorus_of_free_absolute_characters {k : Type u} [Field k]
    (T : MultiplicativeTypeGroup k)
    (h : Module.Free ℤ ((MultiplicativeTypeGroup.characterFunctor k).obj (op T))) :
    IsTorus T.obj.toGrp := by
  let K := SeparableClosure k
  let T_K := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T.obj
  obtain ⟨M, hM, hfg, ⟨e⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed T_K.toGrp
      (MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
        k K T.obj.toGrp T.property)
  let e' : T_K ≅ Diagonalizable.groupScheme (CommRingCat.of K) M :=
    CommGroupScheme.isoOfGroupIso e
  let chars : M ≃+ characterLattice T_K :=
    (DiagonalizableCharacter.evalCharacterEquiv K M).trans (characterLattice.congr e').symm
  have : Module.Free ℤ (characterLattice T_K) := h
  have : Module.Free ℤ M := Module.Free.of_equiv chars.symm.toIntLinearEquiv
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr hfg
  exact ⟨K, inferInstance, inferInstance, IsSplitTorus.of_iso e
    (Diagonalizable.isSplitTorus (CommRingCat.of K)
      (Module.Free.chooseBasis ℤ M).equivFun.toAddEquiv)⟩

/-- The actual separable-closure character functor is an anti-equivalence on field tori. -/
theorem torusAbsoluteCharacterEquivalence : TorusAbsoluteCharacterEquivalenceStatement.{u} := by
  intro k _
  let F := MultiplicativeTypeGroup.characterFunctor k
  have : F.IsEquivalence := multiplicativeTypeAbsoluteEquivalence k
  let hInclusion : (FieldTorus.toMultiplicativeTypeGroup k).FullyFaithful :=
    ObjectProperty.fullyFaithfulιOfLE _
  let hRestricted : (FieldTorus.characterFunctor k).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful
      (G := (freeDiscreteGaloisModuleProperty k).ι) (by
        rw [FieldTorus.characterFunctor_forget]
        exact hInclusion.op.comp (Functor.FullyFaithful.ofFullyFaithful F))
  refine { faithful := hRestricted.faithful, full := hRestricted.full, essSurj := ⟨?_⟩ }
  intro A
  let T := F.objPreimage A.obj
  let e : F.obj T ≅ A.obj := F.objObjPreimageIso A.obj
  let eLinear : F.obj T ≃ₗ[ℤ] A.obj :=
    { (FGDiscreteGaloisModule.hom e.hom).toLinearMap with
      invFun := FGDiscreteGaloisModule.hom e.inv
      left_inv x := congrArg (fun f => FGDiscreteGaloisModule.hom f x) e.hom_inv_id
      right_inv x := congrArg (fun f => FGDiscreteGaloisModule.hom f x) e.inv_hom_id }
  have : Module.Free ℤ A.obj := A.property
  have h : Module.Free ℤ (F.obj T) := Module.Free.of_equiv eLinear.symm
  let U : FieldTorus k := ⟨T.unop.obj, isTorus_of_free_absolute_characters T.unop h⟩
  exact ⟨op U, ⟨(freeDiscreteGaloisModuleProperty k).isoMk e⟩⟩

end Langlands.GroupScheme

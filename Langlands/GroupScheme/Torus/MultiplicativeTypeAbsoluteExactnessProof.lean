import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteExactnessStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisExactnessProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof

/-! # Short exactness of the absolute-Galois character functor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open MultiplicativeTypeGaloisExactness MultiplicativeTypeSplitting in
/-- A closed subgroup with its represented fppf quotient corresponds under the actual
absolute-Galois character functor to a short exact sequence. -/
theorem multiplicativeTypeAbsoluteExactness :
    MultiplicativeTypeAbsoluteExactnessStatement.{u} := by
  intro k _ N E Q i q X pullQ pullN
  let Ω := SeparableClosure k
  let BC := CommGroupScheme.baseChange (algebraBaseMap k Ω)
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k Ω
  have split (T : MultiplicativeTypeGroup k) :
      ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
        Nonempty (BC.obj T.obj ≅ Diagonalizable.groupScheme (CommRingCat.of Ω) M) := by
    obtain ⟨M, hM, hfg, ⟨e⟩⟩ := isFGDiagonalizable_of_isSepClosed _
      (isMultiplicativeType_baseChange_of_isAlgebraic k Ω T.obj.toGrp T.property)
    exact ⟨M, hM, hfg, ⟨CommGroupScheme.isoOfGroupIso e⟩⟩
  obtain ⟨MN, hMN, _, ⟨eN⟩⟩ := split N
  obtain ⟨ME, hME, hfgE, ⟨eE⟩⟩ := split E
  obtain ⟨MQ, hMQ, hfgQ, ⟨eQ⟩⟩ := split Q
  obtain ⟨f, hf⟩ := (DiagonalizableCharacter.restrictMap_bijective Ω MN ME).2
    (CommGroupScheme.groupHom (eN.inv ≫ BC.map i.hom ≫ eE.hom))
  obtain ⟨g, hg⟩ := (DiagonalizableCharacter.restrictMap_bijective Ω ME MQ).2
    (CommGroupScheme.groupHom (eE.inv ≫ BC.map q.hom ≫ eQ.hom))
  beta_reduce at hf hg
  have hiModel : (grpIso eN).inv ≫ (GroupScheme.baseChange (algebraBaseMap k Ω)).map
      (CommGroupScheme.groupHom i.hom) ≫ (grpIso eE).hom =
      Diagonalizable.restrictMap (CommRingCat.of Ω) f := hf.symm
  have hqModel : (grpIso eE).inv ≫ (GroupScheme.baseChange (algebraBaseMap k Ω)).map
      (CommGroupScheme.groupHom q.hom) ≫ (grpIso eQ).hom =
      Diagonalizable.restrictMap (CommRingCat.of Ω) g := hg.symm
  refine (descent_iff (algebraBaseMap k Ω) (CommGroupScheme.groupHom i.hom)
      (CommGroupScheme.groupHom q.hom)).symm.trans
    ((transport_iff (grpIso eN) (grpIso eE) (grpIso eQ) _ _ hiModel hqModel).symm.trans
      ((splitCore Ω f g).trans ?_))
  let PQ : characterLattice (BC.obj Q.obj) →+ characterLattice (BC.obj E.obj) :=
    Preadditive.leftComp _ (BC.map q.hom)
  let PN : characterLattice (BC.obj E.obj) →+ characterLattice (BC.obj N.obj) :=
    Preadditive.leftComp _ (BC.map i.hom)
  change _ ↔ Function.Injective PQ ∧ Function.Exact PQ PN ∧ Function.Surjective PN
  let evalN := (DiagonalizableCharacter.evalCharacterEquiv Ω MN).trans
    (characterLattice.congr eN).symm
  let evalE := (DiagonalizableCharacter.evalCharacterEquiv Ω ME).trans
    (characterLattice.congr eE).symm
  let evalQ := (DiagonalizableCharacter.evalCharacterEquiv Ω MQ).trans
    (characterLattice.congr eQ).symm
  have hiRestrict : restrictHom Ω f = eN.inv ≫ BC.map i.hom ≫ eE.hom :=
    congrArg Additive.ofMul hf
  have hqRestrict : restrictHom Ω g = eE.inv ≫ BC.map q.hom ≫ eQ.hom :=
    congrArg Additive.ofMul hg
  have ladderN : ∀ m : ME, PN (evalE m) = evalN (f m) := by
    intro m
    change BC.map i.hom ≫ eE.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of Ω) ME m =
      eN.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of Ω) MN (f m)
    rw [← restrictHom_comp_evalCharacter Ω f m, hiRestrict]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have ladderQ : ∀ m : MQ, PQ (evalQ m) = evalE (g m) := by
    intro m
    change BC.map q.hom ≫ eQ.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of Ω) MQ m =
      eE.hom ≫ DiagonalizableCharacter.evalCharacter (CommRingCat.of Ω) ME (g m)
    rw [← restrictHom_comp_evalCharacter Ω g m, hqRestrict]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hex : Function.Exact PQ PN ↔ Function.Exact g f :=
    Function.Exact.iff_of_ladder_addEquiv evalQ evalE evalN (f₁₂ := g) (f₂₃ := f)
      (g₁₂ := PQ) (g₂₃ := PN) (AddMonoidHom.ext ladderQ) (AddMonoidHom.ext ladderN)
  have hinj : Function.Injective PQ ↔ Function.Injective g := by
    have h : PQ ∘ evalQ = evalE ∘ g := funext ladderQ
    rw [← EquivLike.injective_comp evalQ PQ, h, EquivLike.comp_injective]
  have hsur : Function.Surjective PN ↔ Function.Surjective f := by
    have h : PN ∘ evalE = evalN ∘ f := funext ladderN
    rw [← EquivLike.surjective_comp evalE PN, h, EquivLike.comp_surjective]
  rw [hinj, hex, hsur]

end Langlands.GroupScheme

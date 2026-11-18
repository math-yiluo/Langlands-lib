import Langlands.GroupScheme.Torus.MultiplicativeTypeCompleteLocalDeformationStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisExactnessProof
import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismLocality
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.FppfExtensionComparison

/-! # Conditional comparison for complete-local multiplicative-type extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.CompleteLocalExtension

/-- The local character classification needed below, retained as an explicit
premise until its independently reviewed proof is published. -/
def LocalCharacterSurjectivity (A : Type u) [CommRing A] : Prop :=
  ∀ (M N : Type u) [AddCommGroup M] [AddCommGroup N],
    Function.Surjective (fun g : N →+ M => Diagonalizable.restrictMap (CommRingCat.of A) g)

/-- For a map between diagonalizable groups whose characters are constant,
flatness and surjectivity after a field base change force those properties
over the original nonzero coefficient ring. -/
theorem flat_surjective_of_fieldBaseChange
    {A : Type u} [CommRing A] [Nontrivial A]
    (hchar : LocalCharacterSurjectivity A)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (f : (Diagonalizable.groupScheme (CommRingCat.of A) M).toGrp ⟶
      (Diagonalizable.groupScheme (CommRingCat.of A) N).toGrp)
    [Flat ((baseChange b).map f).hom.hom.left]
    [Surjective ((baseChange b).map f).hom.hom.left] :
    Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  obtain ⟨g, rfl⟩ := hchar M N f
  let eM := Diagonalizable.baseChangeIso b M
  let eN := Diagonalizable.baseChangeIso b N
  let q := eM.inv ≫ (baseChange b).map (Diagonalizable.restrictMap (CommRingCat.of A) g) ≫
    eN.hom
  have hq : q = Diagonalizable.restrictMap (CommRingCat.of k) g := by
    dsimp only [q]
    rw [Diagonalizable.baseChangeIso_restrictMap, Iso.inv_hom_id_assoc]
  have hflat : Flat q.hom.hom.left := by
    change Flat (eM.inv.hom.hom.left ≫
      ((baseChange b).map (Diagonalizable.restrictMap (CommRingCat.of A) g)).hom.hom.left ≫
        eN.hom.hom.hom.left)
    infer_instance
  have hsurj : Surjective q.hom.hom.left := by
    change Surjective (eM.inv.hom.hom.left ≫
      ((baseChange b).map (Diagonalizable.restrictMap (CommRingCat.of A) g)).hom.hom.left ≫
        eN.hom.hom.hom.left)
    infer_instance
  rw [hq] at hflat hsurj
  exact Diagonalizable.flat_and_surjective_restrictMap (CommRingCat.of A) g
    ((MultiplicativeTypeGaloisExactness.flat_surjective_restrictMap_iff k g).mp
      ⟨hflat, hsurj⟩)

private theorem finiteEtaleSplit_of_isDiagonalizable
    {S : Scheme.{u}} {H : GroupScheme S}
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        RelativeMultiplicativeType.IsDiagonalizable ((baseChange p).obj H) :=
  ⟨S, 𝟙 S, inferInstance, inferInstance, inferInstance, hH.baseChange (𝟙 S)⟩

variable (hdef : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hchar : LocalCharacterSurjectivity A)
    {N G Q : GroupScheme (Spec (CommRingCat.of A))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Flat G.X.hom]
    (i : N ⟶ G) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : RelativeMultiplicativeType.IsDiagonalizable N)
    (hQ : RelativeMultiplicativeType.IsDiagonalizable Q)
    (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (e₀ :
      (baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj
          (Diagonalizable.groupScheme (CommRingCat.of A) M).toGrp ≅
        (baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G)

include hdef hchar i q hq hN hQ e₀

/-- Given the complete-local deformation theorem and local character
classification, a specified diagonalization of the special fibre extends
to an actual diagonalization of the middle group in the exact extension. -/
theorem exists_diagonalizingIso :
    ∃ e : (Diagonalizable.groupScheme (CommRingCat.of A) M).toGrp ≅ G,
      (baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map e.hom = e₀.hom := by
  let sp := Spec.algebraMap A (IsLocalRing.ResidueField A)
  let F := baseChange sp
  let D := (Diagonalizable.groupScheme (CommRingCat.of A) M).toGrp
  have : IsAffineHom D.X.hom := inferInstanceAs
    (IsAffineHom (Diagonalizable.groupScheme (CommRingCat.of A) M).X.hom)
  have : LocallyOfFiniteType D.X.hom := inferInstanceAs
    (LocallyOfFiniteType (Diagonalizable.groupScheme (CommRingCat.of A) M).X.hom)
  have : Flat D.X.hom := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap A (AddMonoidAlgebra A M))))
    exact ((flat_and_surjective_SpecMap_iff _).2
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).1
  have hD : RelativeMultiplicativeType.IsDiagonalizable D :=
    Diagonalizable.isDiagonalizable_groupScheme (CommRingCat.of A) M
  have hD₀ : RelativeMultiplicativeType.IsMultiplicativeType (F.obj D) :=
    RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable (hD.baseChange sp)
  have hG₀ : RelativeMultiplicativeType.IsMultiplicativeType (F.obj G) :=
    RelativeMultiplicativeType.IsMultiplicativeType.of_iso e₀.symm hD₀
  have hGD := hdef A G D (finiteEtaleSplit_of_isDiagonalizable hD) hG₀
  obtain ⟨j, hj, -⟩ := hGD.1 e₀.hom
  have hj₀ : IsIso (F.map j) := by rw [hj]; infer_instance
  obtain ⟨hjopen, hjclosed⟩ := hGD.2 j hj₀
  have : IsOpenImmersion j.hom.hom.left := hjopen
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hDN := hdef A D N (finiteEtaleSplit_of_isDiagonalizable hN) hD₀
  obtain ⟨a, ha, -⟩ := hDN.1 (F.map i ≫ e₀.inv)
  have ha₀ : F.map (a ≫ j) = F.map i := by
    rw [F.map_comp, ha, hj, Category.assoc, e₀.inv_hom_id, Category.comp_id]
  have ha : a ≫ j = i :=
    ((hdef A G N (finiteEtaleSplit_of_isDiagonalizable hN) hG₀).1 (F.map i)).unique ha₀ rfl
  obtain ⟨L, hL, hfg, ⟨eQ⟩⟩ := hQ
  let : AddCommGroup L := hL
  let : AddGroup.FG L := hfg
  let dQ : Q ≅ (Diagonalizable.groupScheme (CommRingCat.of A) L).toGrp :=
    eQ ≪≫ (Diagonalizable.relativeModelIso (CommRingCat.of A) L).symm
  have : IsAffineHom Q.X.hom := by
    rw [← Over.w dQ.hom.hom.hom]
    infer_instance
  let r := j ≫ q ≫ dQ.hom
  have hr₀ : F.map r = e₀.hom ≫ F.map q ≫ F.map dQ.hom := by
    change F.map (j ≫ q ≫ dQ.hom) = _
    rw [F.map_comp, F.map_comp]
    exact congrArg (fun v => v ≫ F.map q ≫ F.map dQ.hom) hj
  have : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) sp q.hom.hom hq.1
  have : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) sp q.hom.hom hq.2.1
  have : Flat (F.map r).hom.hom.left := by
    rw [hr₀]
    change Flat (e₀.hom.hom.hom.left ≫ (F.map q).hom.hom.left ≫
      (F.map dQ.hom).hom.hom.left)
    infer_instance
  have : Surjective (F.map r).hom.hom.left := by
    rw [hr₀]
    change Surjective (e₀.hom.hom.hom.left ≫ (F.map q).hom.hom.left ≫
      (F.map dQ.hom).hom.hom.left)
    infer_instance
  obtain ⟨hrflat, hrsurj⟩ := flat_surjective_of_fieldBaseChange hchar sp r
  have : Flat (j ≫ q).hom.hom.left :=
    (MorphismProperty.cancel_right_of_respectsIso (@Flat : MorphismProperty Scheme.{u})
      (j ≫ q).hom.hom.left dQ.hom.hom.hom.left).mp hrflat
  have : Surjective (j ≫ q).hom.hom.left :=
    (MorphismProperty.cancel_right_of_respectsIso (@Surjective : MorphismProperty Scheme.{u})
      (j ≫ q).hom.hom.left dQ.hom.hom.hom.left).mp hrsurj
  have : QuasiCompact (j ≫ q).hom.hom.left := by
    have : QuasiCompact ((j ≫ q).hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp _ Q.X.hom
  refine ⟨FppfExtensionComparison.isoOfMonoContainingKernel i a j q hq ha, ?_⟩
  rw [FppfExtensionComparison.isoOfMonoContainingKernel_hom]
  exact hj

/-- Choose the actual complete-local diagonalization under the two explicit
deformation and character-classification premises. -/
def diagonalizingIso :
    (Diagonalizable.groupScheme (CommRingCat.of A) M).toGrp ≅ G :=
  Classical.choose (exists_diagonalizingIso hdef hchar i q hq hN hQ M e₀)

/-- The constructed diagonalization restricts to the specified special-fibre map. -/
@[simp]
theorem diagonalizingIso_special :
    (baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map
        (diagonalizingIso hdef hchar i q hq hN hQ M e₀).hom = e₀.hom :=
  Classical.choose_spec (exists_diagonalizingIso hdef hchar i q hq hN hQ M e₀)

end Langlands.GroupScheme.CompleteLocalExtension

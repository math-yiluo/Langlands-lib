import Langlands.GroupScheme.Dynamic.SolvableCellStatement
import Langlands.GroupScheme.Dynamic.FieldOppositeCellProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.OppositeBaseChange
import Langlands.GroupScheme.SubgroupFunctor.UnipotentKernelCell
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectProof
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction
import Langlands.GroupScheme.Rational.SplitTorusImage
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation

/-! # Proof: the dynamic cell of a smooth connected solvable group is the whole group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SolvableDynamicCell

section Pullback

variable {S : Scheme.{u}} {G U P N : GroupScheme S}
    (iU : U ⟶ G) (iP : P ⟶ G) (n : N ⟶ G) (a : U ⟶ N) (ha : a ≫ n = iU)

/-- The square exhibiting `pullback n iP` as the actual group-scheme preimage, viewed in
schemes over the base. -/
theorem preimage_isPullback :
    IsPullback (pullback.fst n iP).hom.hom (pullback.snd n iP).hom.hom n.hom.hom iP.hom.hom :=
  IsPullback.map (Grp.forget (Over S)) (IsPullback.of_hasPullback n iP)

/-- Composing a point of `U × P` with the cell multiplication. -/
theorem comp_cellMultiplication {T : Over S} (m : T ⟶ U.X ⊗ P.X) :
    m ≫ SubgroupFunctor.cellMultiplication iU iP =
      (m ≫ fst U.X P.X ≫ iU.hom.hom) * (m ≫ snd U.X P.X ≫ iP.hom.hom) := by
  conv_lhs => rw [← lift_comp_fst_snd m]
  rw [SubgroupFunctor.lift_cellMultiplication, Category.assoc, Category.assoc]

include ha in
/-- If the first factor `iU` lands in `n : N ⟶ G`, the cell of `a` and the preimage of `iP`
in `N` is the pullback of the cell of `iU` and `iP` along `n`. -/
theorem cell_isPullback :
    IsPullback (SubgroupFunctor.cellMultiplication a (pullback.fst n iP))
      (U.X ◁ (pullback.snd n iP).hom.hom) n.hom.hom
      (SubgroupFunctor.cellMultiplication iU iP) := by
  have hPB := preimage_isPullback iP n
  have hcond : (pullback.fst n iP).hom.hom ≫ n.hom.hom =
      (pullback.snd n iP).hom.hom ≫ iP.hom.hom := hPB.w
  have han : a.hom.hom ≫ n.hom.hom = iU.hom.hom := by rw [← Grp.comp_hom_hom, ha]
  have hw : SubgroupFunctor.cellMultiplication a (pullback.fst n iP) ≫ n.hom.hom =
      (U.X ◁ (pullback.snd n iP).hom.hom) ≫ SubgroupFunctor.cellMultiplication iU iP := by
    rw [comp_cellMultiplication, SubgroupFunctor.cellMultiplication, MonObj.mul_comp,
      Category.assoc, Category.assoc, hcond, han, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => lift (s.snd ≫ fst U.X P.X)
      (hPB.lift (((s.snd ≫ fst U.X P.X) ≫ a.hom.hom)⁻¹ * s.fst) (s.snd ≫ snd U.X P.X) ?_))
    ?_ ?_ ?_)
  · -- the lifted point of `N` lies over the second coordinate
    have hs : s.fst ≫ n.hom.hom =
        (s.snd ≫ fst U.X P.X ≫ iU.hom.hom) * (s.snd ≫ snd U.X P.X ≫ iP.hom.hom) := by
      rw [s.condition, comp_cellMultiplication]
    have h3 : ((s.snd ≫ fst U.X P.X) ≫ a.hom.hom) ≫ n.hom.hom =
        s.snd ≫ fst U.X P.X ≫ iU.hom.hom := by
      rw [Category.assoc, Category.assoc, han]
    rw [MonObj.mul_comp, GrpObj.inv_comp, h3, hs, inv_mul_cancel_left, Category.assoc]
  · intro s
    rw [SubgroupFunctor.lift_cellMultiplication, hPB.lift_fst, mul_inv_cancel_left]
  · intro s
    rw [lift_whiskerLeft, hPB.lift_snd, lift_comp_fst_snd]
  · intro s m h₁ h₂
    have hfst : m ≫ fst U.X _ = s.snd ≫ fst U.X P.X := by
      rw [← h₂, Category.assoc, whiskerLeft_fst]
    apply CartesianMonoidalCategory.hom_ext
    · rw [hfst, lift_fst]
    · rw [lift_snd]
      apply hPB.hom_ext
      · rw [hPB.lift_fst, Category.assoc]
        apply eq_inv_mul_of_mul_eq
        rw [← h₁, comp_cellMultiplication, ← hfst, Category.assoc]
      · rw [hPB.lift_snd, Category.assoc, ← whiskerLeft_snd, ← Category.assoc, h₂]

end Pullback

section Smooth

variable {S : Scheme.{u}} {U P N : GroupScheme S} (a : U ⟶ N) (p : P ⟶ N)

/-- If an open multiplication cell of a smooth quasi-compact first factor lands in a smooth
group, the second factor is smooth, provided it is locally of finite presentation. -/
theorem smooth_of_isOpenImmersion_cellMultiplication
    [Smooth U.X.hom] [QuasiCompact U.X.hom] [Smooth N.X.hom]
    [LocallyOfFinitePresentation P.X.hom]
    (h : IsOpenImmersion (SubgroupFunctor.cellMultiplication a p).left) :
    Smooth P.X.hom := by
  have : Smooth (snd U.X P.X).left :=
    inferInstanceAs (Smooth (pullback.snd U.X.hom P.X.hom))
  have : QuasiCompact (snd U.X P.X).left :=
    inferInstanceAs (QuasiCompact (pullback.snd U.X.hom P.X.hom))
  have : Surjective (snd U.X P.X).left := by
    have hs : (lift (toUnit P.X ≫ η[U.X]) (𝟙 P.X)).left ≫ (snd U.X P.X).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_snd, Over.id_left]
    have : Surjective ((lift (toUnit P.X ≫ η[U.X]) (𝟙 P.X)).left ≫ (snd U.X P.X).left) := by
      rw [hs]; infer_instance
    exact Surjective.of_comp (lift (toUnit P.X ≫ η[U.X]) (𝟙 P.X)).left (snd U.X P.X).left
  have : IsOpenImmersion (SubgroupFunctor.cellMultiplication a p).left := h
  have : Smooth ((snd U.X P.X).left ≫ P.X.hom) := by
    rw [Over.w (snd U.X P.X), ← Over.w (SubgroupFunctor.cellMultiplication a p)]
    infer_instance
  exact AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation
    (snd U.X P.X).left P.X.hom

end Smooth

section AlgClosed

variable {k : Type u} [Field k]

/-- A torus factoring a cocharacter centralizes it, hence lies in its dynamic parabolic. -/
theorem range_le_parabolic_of_factor {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (s : T.toGrp ⟶ G)
    (c : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp) :
    SubgroupFunctor.range s ≤ Dynamic.parabolic (c ≫ s) := by
  refine le_trans ?_ (Dynamic.centralizer_le_parabolic (c ≫ s))
  intro V x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [Dynamic.mem_centralizer, Dynamic.orbit]
  have key : (snd V (Gm (Spec (CommRingCat.of k))).X ≫ c.hom.hom) * (fst V _ ≫ t) *
      (snd V (Gm (Spec (CommRingCat.of k))).X ≫ c.hom.hom)⁻¹ = fst V _ ≫ t := by
    rw [mul_comm (snd _ _ ≫ _), mul_assoc, mul_inv_cancel, mul_one]
  have key' := congrArg (· ≫ s.hom.hom) key
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc] at key'
  simpa only [Grp.comp_hom_hom, Category.assoc] using key'

/-- The algebraically closed case of Milne 16.35. -/
theorem isIso_cellMultiplication_of_isAlgClosed [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsSolvableGroupScheme G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (U P : GroupScheme (Spec (CommRingCat.of k))) (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy
        iU)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP) :
    IsIso (SubgroupFunctor.cellMultiplication iU iP) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hopen : IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iP).left :=
    dynamicFieldOppositeCell k G χ U P iU iP hU hP
  -- a maximal torus through which `χ` factors
  obtain ⟨D, π, i, hi, hπ, -⟩ :=
    (isSplitTorus_gm (S := Spec (CommRingCat.of k))).exists_factor_isSplitSubtorus χ
  obtain ⟨T, s, f, hs, hf⟩ :=
    EnvelopeInfiniteReduction.exists_isMaximalTorus_factor G i hi.1.isTorus hi.2
  have hχ : (π ≫ f) ≫ s = χ := by rw [Category.assoc, hf, hπ]
  -- the unipotent part
  obtain ⟨N, n, hnC, hnS, hnConn, hnU, -, hnMax, hiso⟩ :=
    solvableMaximalTorusSemidirect k G hG T s hs
  have : IsClosedImmersion n.hom.hom.left := hnC
  have : Smooth N.X.hom := hnS
  have : ConnectedSpace N.X.left := hnConn
  have : IsAffineHom N.X.hom := by rw [← Over.w n.hom.hom]; infer_instance
  have hnR : (SubgroupFunctor.range n).IsRepresentedBy n := ⟨Over.mono_of_mono_left _, rfl⟩
  -- the first factor
  have hUc : IsClosedSubgroup iU :=
    Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent _ hU
  have : IsClosedImmersion iU.hom.hom.left := hUc
  have : Smooth U.X.hom := (dynamicSmooth k G _ U iU).2.2 hU
  have : IsAffineHom U.X.hom := by rw [← Over.w iU.hom.hom]; infer_instance
  have hUu : IsUnipotent U := dynamicUnipotentUnipotence k G _ U iU hU
  let a : U ⟶ N := hnR.factorHom iU (hnMax U iU hUc hUu)
  have ha : a ≫ n = iU := hnR.factorHom_comp _ _
  -- the second factor of the cell in `N`
  have hPc : IsClosedSubgroup iP :=
    Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic _ hP
  have : IsClosedImmersion iP.hom.hom.left := hPc
  have hPB := preimage_isPullback iP n
  have hPBs : IsPullback (pullback.fst n iP).hom.hom.left (pullback.snd n iP).hom.hom.left
      n.hom.hom.left iP.hom.hom.left := IsPullback.map (Over.forget _) hPB
  have : IsClosedImmersion (pullback.fst n iP).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hPBs.flip ‹_›
  have hp'c : IsClosedSubgroup (pullback.fst n iP) := ‹_›
  have : IsAffineHom (pullback n iP).X.hom := by
    rw [← Over.w (pullback.fst n iP).hom.hom]; infer_instance
  have : LocallyOfFiniteType (pullback n iP).X.hom := by
    rw [← Over.w (pullback.fst n iP).hom.hom]; infer_instance
  have hP'u : IsUnipotent (pullback n iP) :=
    unipotentClosedSubgroup k N (pullback n iP) (pullback.fst n iP) hp'c hnU
  have hopen' : IsOpenImmersion
      (SubgroupFunctor.cellMultiplication a (pullback.fst n iP)).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.map (Over.forget _) (cell_isPullback iU iP n a ha)).flip hopen
  have : Smooth (pullback n iP).X.hom :=
    smooth_of_isOpenImmersion_cellMultiplication a (pullback.fst n iP) hopen'
  have hiso' : IsIso (SubgroupFunctor.cellMultiplication a (pullback.fst n iP)) :=
    SubgroupFunctor.isIso_cellMultiplication_of_unipotent a (pullback.fst n iP) hUu hP'u hopen'
  -- the maximal torus lies in the dynamic parabolic
  have hTP : SubgroupFunctor.range s ≤ Dynamic.parabolic χ := by
    rw [← hχ]; exact range_le_parabolic_of_factor s (π ≫ f)
  let τ : T.toGrp ⟶ P := hP.factorHom s hTP
  have hτ : τ ≫ iP = s := hP.factorHom_comp _ _
  -- a section of the cell
  let w : G.X ⟶ N.X ⊗ T.toGrp.X := inv (subgroupMultiplication n s)
  let e : G.X ⟶ U.X ⊗ (pullback n iP).X :=
    w ≫ fst _ _ ≫ inv (SubgroupFunctor.cellMultiplication a (pullback.fst n iP))
  let σ : G.X ⟶ U.X ⊗ P.X :=
    lift (e ≫ fst _ _) ((e ≫ snd _ _ ≫ (pullback.snd n iP).hom.hom) *
      (w ≫ snd _ _ ≫ τ.hom.hom))
  have he : e ≫ SubgroupFunctor.cellMultiplication a (pullback.fst n iP) = w ≫ fst _ _ := by
    simp only [e, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hσ : σ ≫ SubgroupFunctor.cellMultiplication iU iP = 𝟙 G.X := by
    have hcond : (pullback.fst n iP).hom.hom ≫ n.hom.hom =
        (pullback.snd n iP).hom.hom ≫ iP.hom.hom := hPB.w
    have h1 : (e ≫ fst _ _ ≫ iU.hom.hom) * (e ≫ snd _ _ ≫ (pullback.snd n iP).hom.hom ≫
        iP.hom.hom) = w ≫ fst _ _ ≫ n.hom.hom := by
      have han : a.hom.hom ≫ n.hom.hom = iU.hom.hom := by rw [← Grp.comp_hom_hom, ha]
      rw [← Category.assoc w, ← he, comp_cellMultiplication, MonObj.mul_comp]
      simp only [Category.assoc, hcond, han]
    calc σ ≫ SubgroupFunctor.cellMultiplication iU iP
        = ((e ≫ fst _ _ ≫ iU.hom.hom) * (e ≫ snd _ _ ≫ (pullback.snd n iP).hom.hom ≫
            iP.hom.hom)) * (w ≫ snd _ _ ≫ τ.hom.hom ≫ iP.hom.hom) := by
          rw [SubgroupFunctor.lift_cellMultiplication, MonObj.mul_comp, mul_assoc]
          simp only [Category.assoc]
      _ = (w ≫ fst _ _ ≫ n.hom.hom) * (w ≫ snd _ _ ≫ s.hom.hom) := by
          rw [h1, ← Grp.comp_hom_hom, hτ]
      _ = w ≫ subgroupMultiplication n s := by
          rw [subgroupMultiplication, MonObj.comp_mul]
      _ = 𝟙 G.X := IsIso.inv_hom_id _
  have : IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iP).left := hopen
  have : Mono (SubgroupFunctor.cellMultiplication iU iP) := Over.mono_of_mono_left _
  have : IsSplitEpi (SubgroupFunctor.cellMultiplication iU iP) := IsSplitEpi.mk' ⟨σ, hσ⟩
  exact isIso_of_mono_of_isSplitEpi _

end AlgClosed

end SolvableDynamicCell

open SolvableDynamicCell in
/-- **Milne 2017, Proposition 16.35.** For a smooth connected solvable affine group over a field,
multiplication `U_G(-χ) × P_G(χ) → G` is an isomorphism for every cocharacter `χ` and all
representatives of the two dynamic subgroups. -/
theorem solvableDynamicCell : SolvableDynamicCellStatement.{u} := by
  intro k _ G _ _ _ hG χ U P iU iP hU hP
  have hopen : IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iP).left :=
    dynamicFieldOppositeCell k G χ U P iU iP hU hP
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  have hb : Surjective b := (fieldExtension_fpqc k K).1
  have : Smooth (B.obj G).X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : IsAffineHom (B.obj G).X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : ConnectedSpace (B.obj G).X.left := connectedSpace_baseChange_of_connected G b
  have hGK : IsSolvableGroupScheme (B.obj G) :=
    solvableFieldExtensionStatement k K b G inferInstance hG
  have hUK : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of K)) (-1)) ≫ Dynamic.baseChangeCocharacter b χ)).IsRepresentedBy
      (B.map iU) := by
    rw [← Dynamic.baseChangeCocharacter_powerHom, Dynamic.unipotent_baseChange]
    exact hU.baseChange b
  have hPK : (Dynamic.parabolic (Dynamic.baseChangeCocharacter b χ)).IsRepresentedBy
      (B.map iP) := by
    rw [Dynamic.parabolic_baseChange]
    exact hP.baseChange b
  have : IsIso (SubgroupFunctor.cellMultiplication (B.map iU) (B.map iP)) :=
    isIso_cellMultiplication_of_isAlgClosed (B.obj G) hGK _ _ _ _ _ hUK hPK
  have : IsIso (SubgroupFunctor.cellMultiplication (B.map iU) (B.map iP)).left :=
    (Over.forget (Spec (CommRingCat.of K))).map_isIso
      (SubgroupFunctor.cellMultiplication (B.map iU) (B.map iP))
  have hcIso : IsIso (CartesianMonoidalCategory.prodComparison (Over.pullback b) U.X P.X).left := by
    change IsIso ((Over.forget (Spec (CommRingCat.of K))).map
      (CartesianMonoidalCategory.prodComparison (Over.pullback b) U.X P.X))
    infer_instance
  have hsurj : Surjective
      ((Over.pullback b).map (SubgroupFunctor.cellMultiplication iU iP)).left := by
    rw [DynamicBaseOppositeCell.baseChange_cellMultiplication, Over.comp_left]
    infer_instance
  have : Surjective (SubgroupFunctor.cellMultiplication iU iP).left :=
    surjective_overHom_of_baseChange b (SubgroupFunctor.cellMultiplication iU iP) hsurj
  have : IsIso (SubgroupFunctor.cellMultiplication iU iP).left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, inferInstance⟩
  have : IsIso ((Over.forget _).map (SubgroupFunctor.cellMultiplication iU iP)) :=
    ‹IsIso (SubgroupFunctor.cellMultiplication iU iP).left›
  exact isIso_of_reflects_iso _ (Over.forget _)

end Langlands.GroupScheme

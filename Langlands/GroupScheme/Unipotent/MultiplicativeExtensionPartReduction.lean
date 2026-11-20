import Langlands.GroupScheme.Unipotent.MultiplicativeExtensionPartStatement
import Langlands.GroupScheme.Trigonalizable.ExtensionSplitStatement
import Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityProof
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcTransfer
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.CentralExtensionSplit
import Langlands.GroupScheme.SplitKernelRetractGeometry
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties

/-! # The unipotent part of an extension of a multiplicative group: reduction to 16.26(a) -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace MultiplicativeExtensionUnipotentPart

/-- The algebraically closed case of Milne 2017, Theorem 16.26(a), used as the premise of this
reduction: over an algebraically closed field, an fppf quotient onto a diagonalizable group by a
closed normal unipotent subgroup has a homomorphic section. It is case (a) of
`TrigonalizableExtensionSplitStatement` (see `algClosedSplitting_of_trigonalizableExtensionSplit`). -/
def AlgClosedSplitting : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (G U : GroupScheme (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] (i : U ⟶ G)
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp),
    IsClosedSubgroup i → IsUnipotent U → (SubgroupFunctor.range i).IsNormal →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
        ∃ s : (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp ⟶ G, s ≫ q = 𝟙 _

/-- Case (a) of the published statement `TrigonalizableExtensionSplitStatement` is the premise
`AlgClosedSplitting`. -/
theorem algClosedSplitting_of_trigonalizableExtensionSplit
    (h : TrigonalizableExtensionSplitStatement.{u}) : AlgClosedSplitting.{u} :=
  fun K _ _ G U _ _ i Λ _ _ q hi hU hn hq => h K G U i Λ q hi hU hn hq (Or.inl ‹_›)

variable {S : Scheme.{u}}

/-- A closed subgroup of a group scheme of locally finite type is of locally finite type. -/
theorem locallyOfFiniteType_of_isClosedSubgroup {H G : GroupScheme S} (i : H ⟶ G)
    (hi : IsClosedSubgroup i) [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType H.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  rw [← Over.w i.hom.hom]
  infer_instance

/-- A closed subgroup of an affine group scheme is affine. -/
theorem isAffineHom_of_isClosedSubgroup {H G : GroupScheme S} (i : H ⟶ G)
    (hi : IsClosedSubgroup i) [IsAffineHom G.X.hom] :
    IsAffineHom H.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  rw [← Over.w i.hom.hom]
  infer_instance

variable {k : Type u} [Field k]

/-- Milne 14.18 in the form used for 16.8: a homomorphism from an affine algebraic unipotent
group into `G` lands in the kernel of every fppf quotient of `G` onto a group of multiplicative
type. -/
theorem range_le_of_isUnipotent {U G M : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType U.X.hom] [IsAffineHom U.X.hom]
    (i : U ⟶ G) (q : G ⟶ M) {N : SubgroupFunctor G}
    (hU : IsUnipotent U) (hM : IsMultiplicativeType M)
    (hq : RelativeRoot.IsFppfQuotient N q) :
    SubgroupFunctor.range i ≤ N := by
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have : LocallyOfFiniteType M.X.hom := hM.locallyOfFiniteType
  have hbot : SubgroupFunctor.range (i ≫ q) = ⊥ :=
    ((unipotentMultiplicativeTriviality k).2.2 U M hU hM).1 (i ≫ q)
  rw [← hq.2.2.2, SubgroupFunctor.le_def]
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [mem_range_kernelι_iff]
  have hy : y ≫ (i ≫ q).hom.hom ∈ (SubgroupFunctor.range (i ≫ q)).carrier T := ⟨y, rfl⟩
  rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hy
  simpa only [Grp.comp_hom_hom, Category.assoc] using hy

/-- Part 1 (Milne 16.8(c)): a unipotent closed subgroup lies in every normal closed subgroup
with an fppf quotient onto a group of multiplicative type. -/
theorem part_one {G U : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (i : U ⟶ G) (hi : IsClosedSubgroup i) (hU : IsUnipotent U) :
    ∀ (N M' : GroupScheme (Spec (CommRingCat.of k))) (j : N ⟶ G) (q' : G ⟶ M'),
      IsClosedSubgroup j → (SubgroupFunctor.range j).IsNormal →
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q' → IsMultiplicativeType M' →
          SubgroupFunctor.range i ≤ SubgroupFunctor.range j := by
  intro N M' j q' _ _ hq' hM'
  have := locallyOfFiniteType_of_isClosedSubgroup i hi
  have := isAffineHom_of_isClosedSubgroup i hi
  exact range_le_of_isUnipotent i q' hU hM' hq'

/-- Part 2 (Milne 16.8, base change): after every field extension `K`, `U_K` is unipotent and
contains every unipotent closed subgroup of `G_K`. -/
theorem part_two {G U M : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (i : U ⟶ G) (q : G ⟶ M) (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hM : IsMultiplicativeType M) (K : Type u) [Field K] [Algebra k K] :
    let F := GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    IsUnipotent (F.obj U) ∧
      ∀ (V : GroupScheme (Spec (CommRingCat.of K))) (j : V ⟶ F.obj G),
        IsClosedSubgroup j → IsUnipotent V →
          SubgroupFunctor.range j ≤ SubgroupFunctor.range (F.map i) := by
  intro F
  have := isAffineHom_of_isClosedSubgroup i hi
  refine ⟨hU.baseChange, ?_⟩
  intro V j hj hV
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : LocallyOfFiniteType (F.obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) G.X.hom b ‹_›
  have : IsAffineHom (F.obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) G.X.hom b ‹_›
  have := locallyOfFiniteType_of_isClosedSubgroup j hj
  have := isAffineHom_of_isClosedSubgroup j hj
  have hqK : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (F.map i)) (F.map q) := by
    have h := hq.baseChange b
    rwa [← SubgroupFunctor.range_baseChangeHom] at h
  exact range_le_of_isUnipotent j (F.map q) hV hM.fieldExtension hqK

/-- A group of multiplicative type over `k` becomes diagonalizable over an algebraically closed
extension of `k` (an algebraic closure of a splitting field). -/
theorem exists_isAlgClosed_diagonalization {M : GroupScheme (Spec (CommRingCat.of k))}
    (hM : IsMultiplicativeType M) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K)
      (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj M ≅
        (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) := by
  obtain ⟨L, _, _, Λ, _, _, ⟨e⟩⟩ := hM
  exact ⟨AlgebraicClosure L, inferInstance, inferInstance, inferInstance, Λ, inferInstance,
    inferInstance, ⟨baseChangeFieldTowerIso k L (AlgebraicClosure L) M ≪≫
      (GroupScheme.baseChange (algebraBaseMap L (AlgebraicClosure L))).mapIso e ≪≫
      Diagonalizable.baseChangeIso (algebraBaseMap L (AlgebraicClosure L)) Λ⟩⟩

/-- A section of an fppf quotient by the range of a closed subgroup `i` makes the subgroup a
scheme retract: `g ↦ g · s(q g)⁻¹` factors through `i`. The retraction need not be a group
homomorphism. -/
theorem exists_retraction {S : Scheme.{u}} {G U Q : GroupScheme S} (i : U ⟶ G) (q : G ⟶ Q)
    (s : Q ⟶ G) [Mono i.hom.hom]
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) (hs : s ≫ q = 𝟙 Q) :
    ∃ r : G.X ⟶ U.X, i.hom.hom ≫ r = 𝟙 U.X := by
  have hker : ∀ {T : Over S} (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range i).carrier T ↔ x ≫ q.hom.hom = 1 := by
    intro T x
    rw [← hq, mem_range_kernelι_iff]
  obtain ⟨r, hr⟩ := SubgroupFunctor.mem_range.mp
    ((hker _).2 (SplitKernelRetract.adjustment_comp q s hs))
  have hiq : i.hom.hom ≫ q.hom.hom = 1 :=
    (hker _).1 (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)
  refine ⟨r, ?_⟩
  apply (cancel_mono i.hom.hom).mp
  rw [Category.assoc, hr, SplitKernelRetract.adjustment, MonObj.comp_mul, GrpObj.comp_inv,
    Category.comp_id, ← Category.assoc, hiq, MonObj.one_comp, inv_one, mul_one,
    Category.id_comp]

/-- Parts 3 and 4 over an algebraically closed extension `K` that diagonalizes `M`, assuming
Milne 16.26(a) in the form `AlgClosedSplitting`: `U_K` is a scheme retract of `G_K`, so smoothness and connectedness pass to
`U_K` and descend to `U`. -/
theorem parts_three_four_of_diagonalization (hsplit : AlgClosedSplitting.{u})
    {G U M : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (i : U ⟶ G) (q : G ⟶ M) (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (eK : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj M ≅
      (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) :
    (Smooth G.X.hom → Smooth U.X.hom) ∧ (ConnectedSpace G.X.left → ConnectedSpace U.X.left) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := GroupScheme.baseChange b
  have : IsAffineHom U.X.hom := isAffineHom_of_isClosedSubgroup i hi
  have : LocallyOfFiniteType (F.obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) G.X.hom b ‹_›
  have : IsAffineHom (F.obj G).X.hom :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) G.X.hom b ‹_›
  have hi' : IsClosedSubgroup (F.map i) := hi.baseChange b
  have hU' : IsUnipotent (F.obj U) := hU.baseChange
  have hn' : (SubgroupFunctor.range (F.map i)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (F.map i)) (F.map q ≫ eK.hom) := by
    have h := hq.baseChange b
    rw [← SubgroupFunctor.range_baseChangeHom] at h
    exact h.comp_iso eK
  obtain ⟨s, hs⟩ := hsplit K (F.obj G) (F.obj U) (F.map i) Λ (F.map q ≫ eK.hom) hi' hU' hn' hq'
  have : IsClosedImmersion (F.map i).hom.hom.left := hi'
  have : Mono (F.map i).hom.hom := Over.mono_of_mono_left _
  obtain ⟨r, hret⟩ := exists_retraction (F.map i) (F.map q ≫ eK.hom) s hq'.2.2.2 hs
  obtain ⟨hb₁, hb₂, hb₃⟩ := fieldExtension_fpqc k K
  have : Surjective b := hb₁
  have : Flat b := hb₂
  have : QuasiCompact b := hb₃
  have : IsAffineHom (F.obj U).X.hom := isAffineHom_of_isClosedSubgroup (F.map i) hi'
  have : IsAffine (F.obj G).X.left := isAffine_of_isAffineHom (F.obj G).X.hom
  have : IsAffine (F.obj U).X.left := isAffine_of_isAffineHom (F.obj U).X.hom
  refine ⟨fun hG => ?_, fun hG => ?_⟩
  · have : Smooth (F.obj G).X.hom := MorphismProperty.pullback_snd (P := @Smooth) G.X.hom b hG
    exact Langlands.GroupScheme.smooth_of_baseChange b U
      (AffineRetractGeometry.smooth_of_retract (F.map i).hom.hom r hret)
  · have : ConnectedSpace (F.obj G).X.left := connectedSpace_baseChange_of_connected G b
    exact Langlands.GroupScheme.connectedSpace_of_baseChange b U
      (AffineRetractGeometry.connectedSpace_of_retract (F.map i).hom.hom r hret)

/-- Parts 3 and 4 (Milne 16.10), assuming Milne 16.26(a). -/
theorem parts_three_four (hsplit : AlgClosedSplitting.{u})
    {G U M : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (i : U ⟶ G) (q : G ⟶ M) (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hM : IsMultiplicativeType M) :
    (Smooth G.X.hom → Smooth U.X.hom) ∧ (ConnectedSpace G.X.left → ConnectedSpace U.X.left) := by
  obtain ⟨K, _, _, _, Λ, _, _, ⟨eK⟩⟩ := exists_isAlgClosed_diagonalization hM
  exact parts_three_four_of_diagonalization hsplit i q hi hU hn hq K Λ eK

end MultiplicativeExtensionUnipotentPart

open MultiplicativeExtensionUnipotentPart in
/-- Milne 16.8 and 16.10, assuming the algebraically closed case of the splitting theorem
16.26(a); parts 1 and 2 do not use the premise. -/
theorem multiplicativeExtensionUnipotentPart_of_algClosedSplitting
    (hsplit : AlgClosedSplitting.{u}) :
    MultiplicativeExtensionUnipotentPartStatement.{u} := by
  intro k _ G _ _ U M i q hi hU hn hq hM
  exact ⟨part_one i hi hU, fun K _ _ => part_two i q hi hU hq hM K,
    (parts_three_four hsplit i q hi hU hn hq hM).1,
    (parts_three_four hsplit i q hi hU hn hq hM).2⟩

open MultiplicativeExtensionUnipotentPart in
/-- Milne 16.8 and 16.10, assuming the published splitting statement 16.26 (only its case (a) is
used). -/
theorem multiplicativeExtensionUnipotentPart_of_trigonalizableExtensionSplit
    (hsplit : TrigonalizableExtensionSplitStatement.{u}) :
    MultiplicativeExtensionUnipotentPartStatement.{u} :=
  multiplicativeExtensionUnipotentPart_of_algClosedSplitting
    (algClosedSplitting_of_trigonalizableExtensionSplit hsplit)

end Langlands.GroupScheme

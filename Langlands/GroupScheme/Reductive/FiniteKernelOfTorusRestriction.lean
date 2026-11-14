import Langlands.GroupScheme.Absolute.KernelMaximalTorusUnipotent
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.ReducedSubgroupAction
import Langlands.GroupScheme.Reductive.FiniteCenterOfNoCentralSubgroups
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Finite full kernels from a finite restriction to a maximal torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

section AlgClosed

variable [IsAlgClosed k]

/-- A homomorphism out of a connected reductive group has finite full kernel
if it kills no nontrivial cocharacter. The kernel need not be smooth. -/
theorem kernel_isFinite_of_cocharacter_injective_algClosed
    (hG : IsConnectedReductive G) (q : G ⟶ H) [IsSeparated H.X.hom]
    (hinj : ∀ z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      z ≫ q = 0 → z = 0) : IsFinite (kernel q).X.hom := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let N := kernel q
  let : IsClosedImmersion (kernelι q).hom.hom.left := inferInstance
  let : IsAffineHom N.X.hom := by
    change IsAffineHom (kernel q).X.hom
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  let : LocallyOfFiniteType N.X.hom := by
    change LocallyOfFiniteType (kernel q).X.hom
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  let C := ReducedSubgroup.identityCore N
  let : GrpObj C.X := C.grp
  let j : C ⟶ N := ReducedSubgroup.identityCoreι N
  have hj : IsClosedSubgroup (j ≫ kernelι q) := by
    change IsClosedImmersion (j.hom.hom.left ≫ (kernelι q).hom.hom.left)
    infer_instance
  have hn : (SubgroupFunctor.range (j ≫ kernelι q)).IsNormal :=
    ReducedSubgroup.isNormal_range_identityCoreι_comp (kernelι q)
      (show IsClosedImmersion (kernelι q).hom.hom.left from inferInstance)
      (HopfPrimitive.isNormal_range_kernelι q)
  have hu : IsUnipotent C := by
    apply algClosedNoCocharacterUnipotent k C
    intro z
    have hz : z ≫ j ≫ kernelι q = 0 := by
      apply hinj
      rw [Category.assoc, Category.assoc, kernelι_comp_eq_zero, comp_zero, comp_zero]
    have : Mono (j ≫ kernelι q).hom.hom := by
      let : IsClosedImmersion (j ≫ kernelι q).hom.hom.left := hj
      exact Over.mono_of_mono_left _
    have : Mono (j ≫ kernelι q) :=
      (Grp.forget _).mono_of_mono_map (f := j ≫ kernelι q)
        ‹Mono (j ≫ kernelι q).hom.hom›
    apply (cancel_mono (j ≫ kernelι q)).mp
    simpa only [Category.assoc, zero_comp] using hz
  have hbot := hG.hasTrivialUnipotentRadical C (j ≫ kernelι q) hj
    inferInstance inferInstance hu hn
  have : Mono (j ≫ kernelι q).hom.hom := by
    let : IsClosedImmersion (j ≫ kernelι q).hom.hom.left := hj
    exact Over.mono_of_mono_left _
  have hone : (𝟙 C.X : C.X ⟶ C.X) = 1 := by
    apply (cancel_mono (j ≫ kernelι q).hom.hom).mp
    have h1 : 𝟙 C.X ≫ (j ≫ kernelι q).hom.hom ∈
        (SubgroupFunctor.range (j ≫ kernelι q)).carrier C.X :=
      SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h1
    rw [h1, MonObj.one_comp]
  have : Subsingleton C.X.left := by
    constructor
    intro a b
    have he : ∀ x : C.X.left, x = η[C.X].left ((toUnit C.X).left x) :=
      fun x => congrArg (fun φ : C.X ⟶ C.X => φ.left x) hone
    have hk : (toUnit C.X).left a = (toUnit C.X).left b :=
      @Subsingleton.elim (PrimeSpectrum k) _ _ _
    rw [he a, he b, hk]
  have hopen : IsOpen (Set.range j.hom.hom.left) := by
    change IsOpen (Set.range
      ((identityComponentι (reducedSubgroup N)).hom.hom.left ≫
        ReducedSubgroup.redι N.X.left))
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact ReducedSubgroup.isOpen_image_redι _
      (IsOpenImmersion.isOpen_range (identityComponentι (reducedSubgroup N)).hom.hom.left)
  obtain ⟨x⟩ := (inferInstance : Nonempty C.X.left)
  have hrange : Set.range j.hom.hom.left = {j.hom.hom.left x} := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact congrArg j.hom.hom.left (Subsingleton.elim w x)
    · rintro rfl
      exact ⟨x, rfl⟩
  rw [hrange] at hopen
  exact FiniteCenterOfNoCentralSubgroups.isFinite_of_open_singleton N _ hopen

/-- A finite actual torus restriction rules out all killed cocharacters, by
maximal-torus conjugacy and cancellation through the finite torus map. -/
theorem cocharacter_injective_of_finite_torus_restriction_algClosed
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ H) (s : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H) (t : T ⟶ T')
    (hs : IsMaximalTorus s) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left]
    (hsq : s ≫ q = CommGroupScheme.groupHom t ≫ i')
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (hz : z ≫ q = 0) :
    z = 0 := by
  apply cocharacter_eq_zero_of_homConjugate q
    (exists_homConjugate_of_isMaximalTorus hs) ?_ z hz
  intro w hw
  have hw' : w ≫ CommGroupScheme.groupHom t = 0 := by
    have : IsClosedImmersion i'.hom.hom.left := hi'
    have : Mono i'.hom.hom := Over.mono_of_mono_left _
    have : Mono i' := (Grp.forget _).mono_of_mono_map (f := i') ‹Mono i'.hom.hom›
    apply (cancel_mono i').mp
    have hh : (w ≫ CommGroupScheme.groupHom t) ≫ i' = 0 := by
      rw [Category.assoc, ← hsq]
      exact hw
    simpa only [zero_comp] using hh
  let : Smooth (Gm (Spec (CommRingCat.of k))).toGrp.X.hom := isSplitTorus_gm.smooth
  let : IsAffineHom (Gm (Spec (CommRingCat.of k))).toGrp.X.hom :=
    isSplitTorus_gm.isAffineHom
  let : ConnectedSpace (Gm (Spec (CommRingCat.of k))).toGrp.X.left :=
    isSplitTorus_gm.connectedSpace
  apply finiteHom_cancel (CommGroupScheme.groupHom t)
  simpa only [zero_comp] using hw'

/-- Finite restriction to a maximal torus of a connected reductive source
forces its full scheme-theoretic kernel to be finite. -/
theorem kernel_isFinite_of_finite_torus_restriction_algClosed
    (hG : IsConnectedReductive G) (q : G ⟶ H) [IsSeparated H.X.hom]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (s : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H) (t : T ⟶ T')
    (hs : IsMaximalTorus s) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left]
    (hsq : s ≫ q = CommGroupScheme.groupHom t ≫ i') :
    IsFinite (kernel q).X.hom := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  exact kernel_isFinite_of_cocharacter_injective_algClosed hG q
    (cocharacter_injective_of_finite_torus_restriction_algClosed q s i' t hs hi' hsq)

end AlgClosed

/-- The finite maximal-torus restriction criterion holds over every field.
Only the proof passes to an algebraic closure; its conclusion concerns the
original full scheme-theoretic kernel. -/
theorem kernel_isFinite_of_finite_torus_restriction
    (hG : IsConnectedReductive G) (q : G ⟶ H) [IsSeparated H.X.hom]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (s : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H) (t : T ⟶ T')
    (hs : IsMaximalTorus s) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left]
    (hsq : s ≫ q = CommGroupScheme.groupHom t ≫ i') :
    IsFinite (kernel q).X.hom := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let B := GroupScheme.baseChange b
  let A := CommGroupScheme.baseChange b
  have hG' : IsConnectedReductive (B.obj G) := hG.baseChange_toAlgebraicClosure
  have hs' : IsMaximalTorus (T := A.obj T) (B.map s) :=
    (maximalTorusBaseChange k K G T s hs.1 hs.2.1).mp hs
  have hi'' : IsClosedSubgroup (B.map i') := hi'.baseChange b
  have : IsSeparated (B.obj H).X.hom := by
    change IsSeparated (pullback.snd H.X.hom b)
    infer_instance
  have : IsFinite (CommGroupScheme.groupHom (A.map t)).hom.hom.left := by
    change IsFinite (B.map (CommGroupScheme.groupHom t)).hom.hom.left
    exact MorphismProperty.overPullbackMap (P := @IsFinite) b
      (CommGroupScheme.groupHom t).hom.hom inferInstance
  have hsq' : B.map s ≫ B.map q = CommGroupScheme.groupHom (A.map t) ≫ B.map i' := by
    change B.map s ≫ B.map q = B.map (CommGroupScheme.groupHom t) ≫ B.map i'
    rw [← B.map_comp, ← B.map_comp, hsq]
  have : IsFinite (kernel (B.map q)).X.hom :=
    kernel_isFinite_of_finite_torus_restriction_algClosed
      (k := K) (G := B.obj G) (H := B.obj H) (T := A.obj T) (T' := A.obj T')
      hG' (B.map q) (B.map s) (B.map i') (A.map t) hs' hi'' hsq'
  let a := kernelBaseChangeIso b q
  have : IsIso a.hom.hom.hom.left :=
    ((Grp.forget _) ⋙ Over.forget _).map_isIso a.hom
  have hfin : IsFinite (B.obj (kernel q)).X.hom := by
    rw [← Over.w a.hom.hom.hom]
    infer_instance
  change IsFinite (pullback.snd (kernel q).X.hom b) at hfin
  obtain ⟨hsb, hfb, hqcb⟩ := fieldExtension_fpqc k K
  let : Surjective b := hsb
  let : Flat b := hfb
  let : QuasiCompact b := hqcb
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfin

/-- An fpqc homomorphism from a connected reductive group is an isogeny when
its restriction to a specified maximal torus is finite. -/
theorem isIsogeny_of_finite_torus_restriction
    (hG : IsConnectedReductive G) (q : G ⟶ H) [IsSeparated H.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (s : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ H) (t : T ⟶ T')
    (hs : IsMaximalTorus s) (hi' : IsClosedSubgroup i')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left]
    (hsq : s ≫ q = CommGroupScheme.groupHom t ≫ i') : IsIsogeny q := by
  let : IsFinite (kernel q).X.hom :=
    kernel_isFinite_of_finite_torus_restriction hG q s i' t hs hi' hsq
  exact ⟨isFinite_of_finite_kernel q, inferInstance, inferInstance⟩

end Langlands.GroupScheme

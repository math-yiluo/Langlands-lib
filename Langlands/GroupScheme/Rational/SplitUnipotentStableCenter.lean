import Langlands.GroupScheme.Rational.SplitUnipotentCommutativeEnvelope
import Langlands.GroupScheme.Rational.UnipotentSmoothCenter
import Langlands.GroupScheme.Rational.UnipotentTorsionCenter
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Rational.VectorCoordinateGeometry
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorStatement
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Rational.SplitSeriesUnipotent

/-! # Split stable central subgroups of split unipotent groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry commutatorElement
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RationalDensity

open Langlands.AlgebraicGeometry.PointTopology RelativeRoot

/-- If `⁅c, y⁆` is central, then `x ↦ ⁅c, x⁆` is multiplicative at `x * y`. -/
theorem commutatorElement_mul_of_commute {Γ : Type*} [Group Γ] (c x y : Γ)
    (h : ∀ g, Commute ⁅c, y⁆ g) : ⁅c, x * y⁆ = ⁅c, x⁆ * ⁅c, y⁆ := by
  have hd : y * c⁻¹ = c⁻¹ * ⁅c, y⁆ * y := by
    rw [commutatorElement_def]
    group
  calc ⁅c, x * y⁆ = c * x * (y * c⁻¹) * y⁻¹ * x⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = c * x * c⁻¹ * (⁅c, y⁆ * x⁻¹) := by
        rw [hd]
        group
    _ = c * x * c⁻¹ * (x⁻¹ * ⁅c, y⁆) := by rw [(h x⁻¹).eq]
    _ = ⁅c, x⁆ * ⁅c, y⁆ := by
        rw [commutatorElement_def c x]
        group

variable {k : Type u} [Field k]

/-- Every smooth connected affine unipotent group over `k` is split. Over a perfect field this
is `PerfectFieldUnipotentSplitStatement`; it is used only for fields which are not infinite. -/
def UnipotentSplitOver (k : Type u) [Field k] : Prop :=
  ∀ (Z : GroupScheme (Spec (CommRingCat.of k))) [Smooth Z.X.hom] [IsAffineHom Z.X.hom],
    ConnectedSpace Z.X.left → IsUnipotent Z → IsSplitUnipotent Z

/-- The points of the source of a central monomorphism commute. -/
theorem mul_comm_of_isCentral {Z G : GroupScheme (Spec (CommRingCat.of k))} (z : Z ⟶ G)
    [Mono z.hom.hom] (hz : IsCentral z) (T : Over (Spec (CommRingCat.of k)))
    (a b : T ⟶ Z.X) : a * b = b * a := by
  apply (cancel_mono z.hom.hom).1
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact (commute_of_mem_center (hz T a) (b ≫ z.hom.hom)).eq

/-- A commutative envelope of a morphism `Y ⊗ S ⟶ G` which is a homomorphism on every
rational fibre `{y} × S` is split unipotent, when `S` is smooth, connected, affine and split
and rational points detect functions on `Y ⊗ S`. -/
theorem isSplitUnipotent_of_fibrewise {G S : GroupScheme (Spec (CommRingCat.of k))}
    {V Y : Over (Spec (CommRingCat.of k))} {f : V ⟶ G.X} (D : GeneratedImage f)
    [Smooth D.group.X.hom] [IsAffineHom D.group.X.hom]
    (hD : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ D.group.X), a * b = b * a)
    [Smooth S.X.hom] [ConnectedSpace S.X.left] [IsAffineHom S.X.hom]
    (hS : IsSplitUnipotent S) (e : Y ⊗ S.X ≅ V)
    (hdet : RationalPointsDetectFunctions (Y ⊗ S.X))
    (hφ : ∀ y : RationalPoint k Y, IsMonHom (pointSection S.X y ≫ e.hom ≫ f)) :
    IsSplitUnipotent D.group := by
  have : Mono D.inclusion.hom.hom := D.represents.1
  obtain ⟨I, κ, hκ, g, hg⟩ := exists_splitClosed_factor hD hS (e.hom ≫ D.factor) hdet
    (fun y => by
      have := hφ y
      have : IsMonHom (pointSection S.X y ≫ e.hom ≫ D.factor) :=
        SplitSemidirect.isMonHom_of_comp_eq D.inclusion _ (pointSection S.X y ≫ e.hom ≫ f)
          (by rw [Category.assoc, Category.assoc, D.factor_comp])
      exact ⟨Grp.homMk (pointSection S.X y ≫ e.hom ≫ D.factor), rfl⟩)
  have : IsClosedImmersion κ.hom.hom.left := hκ.isClosedSubgroup
  have : Mono κ.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  have hc : IsClosedSubgroup (κ ≫ D.inclusion) := by
    change IsClosedImmersion (κ.hom.hom.left ≫ D.inclusion.hom.hom.left)
    infer_instance
  have hf : FactorsThrough f (κ ≫ D.inclusion) := ⟨e.inv ≫ g, by
    rw [Grp.comp_hom_hom, Category.assoc, reassoc_of% hg, D.factor_comp,
      Iso.inv_hom_id_assoc]⟩
  let m := D.minimalHom (κ ≫ D.inclusion) hc hf
  have hm : m ≫ κ ≫ D.inclusion = D.inclusion := D.minimalHom_comp _ hc hf
  have h1 : m ≫ κ = 𝟙 D.group := by
    apply Grp.hom_ext
    apply (cancel_mono D.inclusion.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc, hm, Category.id_comp]
  have h2 : κ ≫ m = 𝟙 I := by
    apply Grp.hom_ext
    apply (cancel_mono κ.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc, h1, Category.comp_id,
      Category.id_comp]
  exact IsSplitUnipotent.of_iso ⟨κ, m, h2, h1⟩ hκ.isSplitUnipotent

/-- Iterated commutator sources of a smooth group are smooth. -/
theorem smooth_source {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] :
    ∀ n : ℕ, Smooth (IteratedCommutator.source G n).hom
  | 0 => inferInstanceAs (Smooth G.X.hom)
  | n + 1 => by
    have := smooth_source (G := G) n
    exact show Smooth (pullback.fst (IteratedCommutator.source G n).hom G.X.hom ≫
      (IteratedCommutator.source G n).hom) by infer_instance

/-- Over an infinite field, iterated commutator sources of a smooth affine split group have
dense rational points. -/
theorem hasDenseRationalPoints_source [Infinite k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hG : IsSplitUnipotent G) :
    ∀ n : ℕ, HasDenseRationalPoints k (IteratedCommutator.source G n)
  | 0 => IsSplitUnipotent.hasDenseRationalPoints hG
  | n + 1 => HasDenseRationalPoints.tensor isOpenMap_fst (hasDenseRationalPoints_source hG n)
      (IsSplitUnipotent.hasDenseRationalPoints hG)

/-- Over an infinite field, the closed envelope of a central iterated commutator word of a
smooth connected affine split group is split, as soon as it is smooth, affine and central. -/
theorem isSplitUnipotent_generatedImage_word [Infinite k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (hS : IsSplitUnipotent G) (n : ℕ)
    (hctr : (center G).ContainsImage (IteratedCommutator.word G n))
    (D : GeneratedImage (IteratedCommutator.word G n))
    [Smooth D.group.X.hom] [IsAffineHom D.group.X.hom] (hDc : IsCentral D.inclusion) :
    IsSplitUnipotent D.group := by
  have : Mono D.inclusion.hom.hom := D.represents.1
  have hDcomm := mul_comm_of_isCentral D.inclusion hDc
  cases n with
  | zero =>
    have hdet : RationalPointsDetectFunctions (𝟙_ (Over (Spec (CommRingCat.of k))) ⊗ G.X) :=
      RationalPointsDetectFunctions.of_iso (λ_ G.X).symm
        (rationalPointsDetectFunctions_of_smooth (IsSplitUnipotent.hasDenseRationalPoints hS))
    refine isSplitUnipotent_of_fibrewise D hDcomm hS (λ_ G.X) hdet fun y => ?_
    have h : pointSection G.X y ≫ (λ_ G.X).hom ≫ IteratedCommutator.word G 0 = 𝟙 G.X := by
      rw [leftUnitor_hom, pointSection_snd_assoc]
      rfl
    rw [h]
    infer_instance
  | succ m =>
    have : Smooth (IteratedCommutator.source G (m + 1)).hom := smooth_source (m + 1)
    have hdet : RationalPointsDetectFunctions (IteratedCommutator.source G m ⊗ G.X) :=
      rationalPointsDetectFunctions_of_smooth (hasDenseRationalPoints_source hS (m + 1))
    refine isSplitUnipotent_of_fibrewise D hDcomm hS (Iso.refl _) hdet fun y => ?_
    have hw : ∀ {X : Over (Spec (CommRingCat.of k))} (v : X ⟶ G.X),
        v ≫ pointSection G.X y ≫ IteratedCommutator.word G (m + 1) =
          ⁅toUnit X ≫ y ≫ IteratedCommutator.word G m, v⁆ := by
      intro X v
      rw [← Category.assoc, IteratedCommutator.word_succ_points]
      simp only [Category.assoc, pointSection_fst_assoc, pointSection_snd, Category.comp_id,
        comp_toUnit_assoc]
    rw [Iso.refl_hom, Category.id_comp]
    refine Semidirect.isMonHom_of_mul_comp _ fun {X} x x' => ?_
    rw [hw, hw, hw]
    apply commutatorElement_mul_of_commute
    intro g
    have h := commute_of_mem_center (hctr X (x' ≫ pointSection G.X y)) g
    rwa [Category.assoc, hw] at h

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

/-- Over an infinite field, or a field over which smooth connected unipotent groups are split,
a nontrivial smooth connected affine unipotent split group has a nontrivial smooth connected
split central closed subgroup stable under any action of an affine group, together with its
restricted action and equivariant inclusion. -/
theorem exists_splitStableCentralSubgroup (hk : Infinite k ∨ UnipotentSplitOver k)
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (b : AutomorphicAction H G) (hH : IsAffineHom H.X.hom)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥) (hU : IsUnipotent G) (hS : IsSplitUnipotent G) :
    ∃ (Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G)
      (bZ : AutomorphicAction H Z),
      IsClosedSubgroup z ∧ Smooth Z.X.hom ∧ IsAffineHom Z.X.hom ∧
      ConnectedSpace Z.X.left ∧ IsCentral z ∧
      b.IsStable (SubgroupFunctor.range z) ∧ SubgroupFunctor.range z ≠ ⊥ ∧
      IsSplitUnipotent Z ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ Z.X),
        bZ.act h v ≫ z.hom.hom = b.act h (v ≫ z.hom.hom) := by
  obtain ⟨d, hd⟩ := exists_hasUniformNilpotentPoints_of_isUnipotent hU
  obtain ⟨n, hn, hn'⟩ := IteratedCommutator.exists_last_nontrivial_word hG
    ⟨d, IteratedCommutator.word_eq_one_of_uniformNilpotence hd⟩
  have hgood := IteratedCommutator.source_good (G := G) n
  have : GeometricallyReduced (IteratedCommutator.source G n).hom := hgood.2.2.1
  have : GeometricallyIrreducible (IteratedCommutator.source G n).hom := hgood.2.2.2
  have hInt : GeometricallyIntegral (IteratedCommutator.source G n).hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G inferInstance inferInstance
    (IteratedCommutator.source G n) hgood.1 hgood.2.1 hInt
    (IteratedCommutator.origin G n) (IteratedCommutator.word G n)
    (IteratedCommutator.origin_word G n)
  have hStable := b.closedImageEnvelope_isStable hH (IteratedCommutator.action b n)
    (IteratedCommutator.word G n) (IteratedCommutator.word_equivariant b n)
  have hctr := IteratedCommutator.center_containsImage_of_succ_eq_one n hn'
  have hcent := closedImageEnvelope_le_center (IteratedCommutator.word G n) hctr
  have hRange : SubgroupFunctor.range D.inclusion ≠ ⊥ := by
    intro hz
    have hf : IteratedCommutator.word G n ∈
        (SubgroupFunctor.range D.inclusion).carrier (IteratedCommutator.source G n) :=
      SubgroupFunctor.mem_range.2 ⟨D.factor, D.factor_comp⟩
    rw [hz, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hf
    exact hn hf
  have : GeometricallyConnected D.group.X.hom := hD.2.2.1
  have : Smooth D.group.X.hom := hD.1
  have : IsAffineHom D.group.X.hom := hD.2.1
  have hDc : IsCentral D.inclusion := by
    intro T v
    apply hcent T
    rw [← D.represents.2]
    exact SubgroupFunctor.mem_range.2 ⟨v, rfl⟩
  have hDco : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom
  have hDs : IsSplitUnipotent D.group := by
    rcases hk with hk | hk
    · exact isSplitUnipotent_generatedImage_word hS n hctr D hDc
    · exact hk D.group hDco (unipotentClosedSubgroup k G D.group D.inclusion D.closed hU)
  refine ⟨D.group, D.inclusion, D.action b hStable, D.closed, hD.1, hD.2.1, hDco, hDc, ?_,
    hRange, hDs, ?_⟩
  · rwa [D.represents.2]
  · intro T h v
    exact D.action_act_comp b hStable h v

/-- Over an infinite field, or a field over which smooth connected unipotent groups are split,
a nontrivial smooth connected affine commutative split central subgroup of bounded `q`-power
exponent contains a nontrivial smooth connected split stable central subgroup killed by `q`. -/
theorem exists_splitStableTorsionCentralSubgroup (hk : Infinite k ∨ UnipotentSplitOver k)
    {H G Z : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth Z.X.hom] [IsAffineHom Z.X.hom] [ConnectedSpace Z.X.left]
    [IsCommMonObj Z.X]
    (b : AutomorphicAction H G) (bZ : AutomorphicAction H Z)
    (hH : IsAffineHom H.X.hom) (z : Z ⟶ G) (hz : IsClosedSubgroup z)
    (hcent : IsCentral z) (hnt : SubgroupFunctor.range z ≠ ⊥)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ Z.X),
      bZ.act h v ≫ z.hom.hom = b.act h (v ≫ z.hom.hom))
    (hZs : IsSplitUnipotent Z) (q : ℕ) (hq : ∃ r, HasUniformPowerExponent Z (q ^ r)) :
    ∃ (W : CommGroupScheme (Spec (CommRingCat.of k))) (w : W.toGrp ⟶ G)
      (bW : AutomorphicAction H W.toGrp),
      IsClosedSubgroup w ∧ Smooth W.X.hom ∧ IsAffineHom W.X.hom ∧
      ConnectedSpace W.X.left ∧ IsCentral w ∧
      b.IsStable (SubgroupFunctor.range w) ∧ SubgroupFunctor.range w ≠ ⊥ ∧
      IsSplitUnipotent W.toGrp ∧ HasUniformPowerExponent W.toGrp q ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ W.X),
        bW.act h v ≫ w.hom.hom = b.act h (v ≫ w.hom.hom) := by
  let : IsClosedImmersion z.hom.hom.left := hz
  let : Mono z.hom.hom := Over.mono_of_mono_left _
  have hZ : SubgroupFunctor.range (𝟙 Z) ≠ ⊥ := by
    intro hzero
    apply hnt
    apply SubgroupFunctor.ext
    intro T
    change (SubgroupFunctor.range z).carrier T = ⊥
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hy
    have hx : x ∈ (SubgroupFunctor.range (𝟙 Z)).carrier T :=
      SubgroupFunctor.mem_range.2 ⟨x, by simp⟩
    rw [hzero, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    change x ≫ z.hom.hom = 1
    rw [hx, MonObj.one_comp]
  obtain ⟨n, hn, hn'⟩ := PowerImage.exists_last_nontrivial_multiplication q hZ hq
  let f := (multiplication Z (q ^ n : ℕ)).hom.hom
  have hInt := smoothConnectedAffineGeometry.1 k Z
    inferInstance inferInstance inferInstance
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k Z
    inferInstance inferInstance Z.X inferInstance inferInstance hInt 1 f
    (by exact MonObj.one_comp f)
  have hStable := bZ.closedImageEnvelope_isStable hH bZ.toPointwiseSchemeAction f
    (PowerImage.multiplication_equivariant bZ (q ^ n))
  let bW := D.action bZ hStable
  let w := D.inclusion ≫ z
  have hw : IsClosedSubgroup w := by
    let : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
    change IsClosedImmersion (D.inclusion.hom.hom.left ≫ z.hom.hom.left)
    infer_instance
  let : IsClosedImmersion w.hom.hom.left := hw
  let : Mono w.hom.hom := Over.mono_of_mono_left _
  have hwcent : IsCentral w := hcent.comp D.inclusion
  have hweq : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (v : T ⟶ D.group.X),
      bW.act h v ≫ w.hom.hom = b.act h (v ≫ w.hom.hom) := by
    intro T h v
    change bW.act h v ≫ D.inclusion.hom.hom ≫ z.hom.hom =
      b.act h (v ≫ D.inclusion.hom.hom ≫ z.hom.hom)
    rw [← Category.assoc, D.action_act_comp, heq, Category.assoc]
  have hwnt : SubgroupFunctor.range w ≠ ⊥ := by
    intro hzero
    have hf : f ≫ z.hom.hom ∈ (SubgroupFunctor.range w).carrier Z.X :=
      SubgroupFunctor.mem_range.2 ⟨D.factor, by
        change D.factor ≫ D.inclusion.hom.hom ≫ z.hom.hom = f ≫ z.hom.hom
        rw [← Category.assoc, D.factor_comp]⟩
    rw [hzero, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hf
    apply hn
    apply hom_ext_points
    intro T x
    have hf' : f = 1 := by
      apply (cancel_mono z.hom.hom).1
      rw [MonObj.one_comp]
      exact hf
    change x ≫ f = x ≫ (1 : Z ⟶ Z).hom.hom
    rw [hf', Grp.Hom.hom_one, Mon.Hom.hom_one]
  have hWt := PowerImage.GeneratedImage.hasUniformPowerExponent D q
    (PowerImage.image_killed_of_succ_eq_one q n hn')
  have hWco : ConnectedSpace D.group.X.left := by
    have : GeometricallyConnected D.group.X.hom := hD.2.2.1
    exact GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom
  have hsplit : IsSplitUnipotent D.group := by
    have : Smooth D.group.X.hom := hD.1
    have : IsAffineHom D.group.X.hom := hD.2.1
    rcases hk with hk | hk
    swap
    · exact hk D.group hWco
        (unipotentClosedSubgroup k Z D.group D.inclusion D.closed
          (IsSplitUnipotent.isUnipotent hZs))
    have hdet : RationalPointsDetectFunctions (𝟙_ (Over (Spec (CommRingCat.of k))) ⊗ Z.X) :=
      RationalPointsDetectFunctions.of_iso (λ_ Z.X).symm
        (rationalPointsDetectFunctions_of_smooth (IsSplitUnipotent.hasDenseRationalPoints hZs))
    refine isSplitUnipotent_of_fibrewise D (mul_comm_of_isCentral w hwcent) hZs (λ_ Z.X) hdet
      fun y => ?_
    rw [leftUnitor_hom, pointSection_snd_assoc]
    exact (inferInstance : IsMonHom (multiplication Z (q ^ n : ℕ)).hom.hom)
  refine ⟨hwcent.commGroupScheme, w, bW, hw, hD.1, hD.2.1, hWco, hwcent, ?_, hwnt, hsplit,
    hWt, hweq⟩
  rintro T h y ⟨v, rfl⟩
  exact SubgroupFunctor.mem_range.2 ⟨bW.act h v, hweq T h v⟩

/-- A uniform `ringChar k`-power exponent of some power for the
closed subgroups of a unipotent group: in characteristic zero `0 ^ 1 = 0` is an exponent of
every group, and in characteristic `p` a power of `p` is an exponent. -/
theorem exists_hasUniformPowerExponent_ringChar
    {Z G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hU : IsUnipotent G) (z : Z ⟶ G) [Mono z.hom.hom] :
    ∃ r, HasUniformPowerExponent Z (ringChar k ^ r) := by
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · have := hzero
    refine ⟨1, fun T x => ?_⟩
    rw [ringChar.eq_zero, pow_one, pow_zero]
  · have : Fact p.Prime := hp
    rw [ringChar.eq k p]
    obtain ⟨r, hr⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hU
    exact ⟨r, hr.of_mono z⟩

/-- Over an infinite field, or a field over which smooth connected unipotent groups are split,
the target conclusion follows from the classification of smooth connected commutative split
unipotent groups killed by the characteristic exponent. -/
theorem splitUnipotentStableVectorSubgroup_of_isVectorGroup
    (hvec : ∀ (W : GroupScheme (Spec (CommRingCat.of k))) [Smooth W.X.hom]
      [IsAffineHom W.X.hom] [ConnectedSpace W.X.left] [IsCommMonObj W.X],
      IsSplitUnipotent W → HasUniformPowerExponent W (ringChar k) → IsVectorGroup W)
    (hk : Infinite k ∨ UnipotentSplitOver k) (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    (hU : IsUnipotent U) (hS : IsSplitUnipotent U) (hnt : SubgroupFunctor.range (𝟙 U) ≠ ⊥)
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
    (a : AutomorphicAction H U) :
    ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (z : V ⟶ U)
      (aV : AutomorphicAction H V) (n : ℕ)
      (e : ∀ T : Over (Spec (CommRingCat.of k)),
        (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))),
      IsClosedSubgroup z ∧ Smooth V.X.hom ∧ IsAffineHom V.X.hom ∧
      ConnectedSpace V.X.left ∧ IsUnipotent V ∧ IsSplitUnipotent V ∧
      IsCentral z ∧ a.IsStable (SubgroupFunctor.range z) ∧
      SubgroupFunctor.range z ≠ ⊥ ∧ 0 < n ∧
      SmoothOfRelativeDimension n V.X.hom ∧ IsNaturalVectorCoordinates e ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ V.X),
        aV.act h v ≫ z.hom.hom = a.act h (v ≫ z.hom.hom) := by
  obtain ⟨Z, z, bZ, hc, hs, ha, hco, hcent, -, hnt', hZs, heq⟩ :=
    exists_splitStableCentralSubgroup hk a inferInstance hnt hU hS
  have : IsClosedImmersion z.hom.hom.left := hc
  have : Mono z.hom.hom := Over.mono_of_mono_left _
  have := hs
  have := ha
  have := hco
  have := hcent.isCommMonObj
  obtain ⟨W, w, bW, hw, hws, hwa, hwco, hwcent, hwstable, hwnt, hWs, hWq, hweq⟩ :=
    exists_splitStableTorsionCentralSubgroup hk a bZ inferInstance z hc hcent hnt' heq hZs _
      (exists_hasUniformPowerExponent_ringChar hU z)
  have := hws
  have := hwa
  have := hwco
  have := W.comm
  obtain ⟨n, e, he⟩ := hvec W.toGrp hWs hWq
  have hdim : IsVectorGroupOfDimension W.toGrp n := ⟨e, he⟩
  exact ⟨W.toGrp, w, bW, n, e, hw, hws, hwa, hwco, hdim.isUnipotent, hWs, hwcent, hwstable,
    hwnt, hdim.pos_of_range_ne_bot_overRing w hwnt, hdim.smoothOfRelativeDimension_overRing,
    he, hweq⟩

end Langlands.GroupScheme.RationalDensity

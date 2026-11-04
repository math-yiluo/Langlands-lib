import Langlands.GroupScheme.ImageGenerationReducedStatement
import Langlands.GroupScheme.ImageGenerationJointInjective
import Langlands.GroupScheme.ImageGenerationPointed

/-! # Smooth generation by a geometrically reduced affine source -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ImageGeneration

section ReducedPowers

/-- Objects over a base whose structure morphism is affine, locally of finite type and
geometrically reduced. -/
def ReducedPowerGood (B : Scheme.{u}) : ObjectProperty (Over B) := fun X =>
  IsAffineHom X.hom ∧ LocallyOfFiniteType X.hom ∧ GeometricallyReduced X.hom

variable {k : Type u} [Field k]

theorem reducedPowerGood_of_iso {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y)
    (h : ReducedPowerGood _ Y) : ReducedPowerGood _ X := by
  have : IsAffineHom Y.hom := h.1
  have : LocallyOfFiniteType Y.hom := h.2.1
  have : GeometricallyReduced Y.hom := h.2.2
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : GeometricallyReduced e.hom.left := geometricallyReduced_of_isIso e.hom.left
  unfold ReducedPowerGood
  rw [← Over.w e.hom]
  exact ⟨inferInstance, inferInstance, geometricallyReduced_comp _ _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor products of affine finite-type objects over a field are affine of finite type. -/
theorem affineFiniteType_tensor (X Y : Over (Spec (CommRingCat.of k))) [IsAffineHom X.hom]
    [LocallyOfFiniteType X.hom] [IsAffineHom Y.hom] [LocallyOfFiniteType Y.hom] :
    IsAffineHom (X ⊗ Y).hom ∧ LocallyOfFiniteType (X ⊗ Y).hom := by
  have : IsAffineHom (pullback.fst X.hom Y.hom) := MorphismProperty.pullback_fst _ _ ‹_›
  exact ⟨inferInstanceAs (IsAffineHom (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom Y.hom ≫ X.hom))⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem reducedPowerGood_tensor (X Y : Over (Spec (CommRingCat.of k)))
    (hX : ReducedPowerGood _ X) (hY : ReducedPowerGood _ Y) : ReducedPowerGood _ (X ⊗ Y) := by
  have : IsAffineHom X.hom := hX.1
  have : LocallyOfFiniteType X.hom := hX.2.1
  have : GeometricallyReduced X.hom := hX.2.2
  have : IsAffineHom Y.hom := hY.1
  have : LocallyOfFiniteType Y.hom := hY.2.1
  have : GeometricallyReduced Y.hom := hY.2.2
  have : IsAffineHom (pullback.fst X.hom Y.hom) := MorphismProperty.pullback_fst _ _ ‹_›
  change ReducedPowerGood _ (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom))
  exact ⟨inferInstanceAs (IsAffineHom (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom Y.hom ≫ X.hom)),
    geometricallyReduced_comp _ _⟩

private instance reducedPowerGood_closedUnderEmpty :
    (ReducedPowerGood (Spec (CommRingCat.of k))).IsClosedUnderLimitsOfShape
      (Discrete.{0} PEmpty) where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    refine reducedPowerGood_of_iso
      (hX.uniqueUpToIso (isTerminalTensorUnit (C := Over (Spec (CommRingCat.of k))))) ?_
    change ReducedPowerGood _ (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    exact ⟨inferInstanceAs (IsAffineHom (𝟙 _)), inferInstanceAs (LocallyOfFiniteType (𝟙 _)),
      geometricallyReduced_of_isIso (𝟙 _)⟩

private instance reducedPowerGood_closedUnderBinary :
    (ReducedPowerGood (Spec (CommRingCat.of k))).IsClosedUnderBinaryProducts where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    let Y := p.diag.obj ⟨WalkingPair.left⟩
    let Z := p.diag.obj ⟨WalkingPair.right⟩
    let c : BinaryFan Y Z := BinaryFan.mk (p.π.app ⟨WalkingPair.left⟩)
      (p.π.app ⟨WalkingPair.right⟩)
    have hc : IsLimit c :=
      (IsLimit.equivOfNatIsoOfIso (diagramIsoPair p.diag) _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨_ | _⟩ <;> simp [c]))).1 p.isLimit
    exact reducedPowerGood_of_iso (hc.conePointUniqueUpToIso (tensorProductIsBinaryProduct Y Z))
      (reducedPowerGood_tensor Y Z (p.prop_diag_obj ⟨WalkingPair.left⟩)
        (p.prop_diag_obj ⟨WalkingPair.right⟩))

/-- Finite powers of an affine, finite type, geometrically reduced scheme over a field are
again affine, of finite type and geometrically reduced. -/
theorem reducedPowerGood_finitePower (V : Over (Spec (CommRingCat.of k)))
    (hV : ReducedPowerGood _ V) (n : ℕ) : ReducedPowerGood _ (finitePower V n) := by
  have : (ReducedPowerGood (Spec (CommRingCat.of k))).IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  exact ObjectProperty.prop_product _ fun _ => hV

end ReducedPowers

section WordClosure

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {V : Over (Spec (CommRingCat.of k))} (f : V ⟶ G.X)

/-- The intersection over all `n` of the kernels of the global-section maps of the ordered
products `V^n ⟶ G`. -/
def wordKernel : Ideal Γ(G.X.left, ⊤) := ⨅ n : ℕ, productKernel f n

/-- The closed subscheme of `G` cut out by `wordKernel f`, as an object over the base. -/
def wordClosure : Over (Spec (CommRingCat.of k)) :=
  Over.mk ((Scheme.IdealSheafData.ofIdealTop (wordKernel f)).subschemeι ≫ G.X.hom)

/-- The closed immersion of `wordClosure f` into the group. -/
def wordClosureι : wordClosure f ⟶ G.X :=
  Over.homMk (Scheme.IdealSheafData.ofIdealTop (wordKernel f)).subschemeι rfl

instance : IsClosedImmersion (wordClosureι f).left :=
  inferInstanceAs
    (IsClosedImmersion (Scheme.IdealSheafData.ofIdealTop (wordKernel f)).subschemeι)

theorem ker_wordClosureι :
    (wordClosureι f).left.ker = Scheme.IdealSheafData.ofIdealTop (wordKernel f) :=
  Scheme.IdealSheafData.ker_subschemeι _

variable [IsAffine G.X.left]

instance : IsAffine (wordClosure f).left :=
  isAffine_of_isAffineHom (wordClosureι f).left

theorem ker_appTop_wordClosureι :
    RingHom.ker (wordClosureι f).left.appTop.hom = wordKernel f :=
  (Scheme.IdealSheafData.ker_subschemeι_app (Scheme.IdealSheafData.ofIdealTop (wordKernel f))
    ⟨⊤, isAffineOpen_top _⟩).trans
    (Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply (wordKernel f))

theorem appTop_wordClosureι_surjective :
    Function.Surjective (wordClosureι f).left.appTop.hom :=
  Scheme.Hom.app_surjective _ ⊤ (isAffineOpen_top _)

/-- Every ordered product of `f` vanishes on the ideal of `wordClosure f`. -/
theorem ker_wordClosureι_le_ker {X : Over (Spec (CommRingCat.of k))} (g : X ⟶ G.X)
    (hg : wordKernel f ≤ RingHom.ker g.left.appTop.hom) :
    (wordClosureι f).left.ker ≤ g.left.ker := by
  rw [ker_wordClosureι, Scheme.ker_of_isAffine]
  exact (map_le_map_iff Scheme.IdealSheafData.equivOfIsAffine.symm).2 hg

theorem exists_wordPoint (n : ℕ) :
    ∃ t : finitePower V n ⟶ wordClosure f, t ≫ wordClosureι f = orderedPowerMap f n :=
  exists_over_factor_of_ker_le _ _ (ker_wordClosureι_le_ker f _ (iInf_le _ n))

/-- The factorization of the `n`-th ordered product through `wordClosure f`. -/
def wordPoint (n : ℕ) : finitePower V n ⟶ wordClosure f := (exists_wordPoint f n).choose

@[reassoc (attr := simp)]
theorem wordPoint_comp (n : ℕ) : wordPoint f n ≫ wordClosureι f = orderedPowerMap f n :=
  (exists_wordPoint f n).choose_spec

/-- The global-section maps of all `wordPoint f n` are jointly injective. -/
theorem wordPoint_appTop_eq_zero (s : Γ((wordClosure f).left, ⊤))
    (hs : ∀ n, (wordPoint f n).left.appTop.hom s = 0) : s = 0 := by
  obtain ⟨a, rfl⟩ := appTop_wordClosureι_surjective f s
  rw [← RingHom.mem_ker, ker_appTop_wordClosureι]
  refine (Submodule.mem_iInf _).2 fun n => ?_
  rw [productKernel, RingHom.mem_ker, ← wordPoint_comp f n, Over.comp_left,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact hs n

/-- A closed subgroup through which `f` factors contains `wordClosure f`. -/
theorem exists_wordClosure_factor {K : GroupScheme (Spec (CommRingCat.of k))} (j : K ⟶ G)
    [IsClosedImmersion j.hom.hom.left] (q : V ⟶ K.X) (hq : q ≫ j.hom.hom = f) :
    ∃ a : wordClosure f ⟶ K.X, a ≫ j.hom.hom = wordClosureι f := by
  refine exists_over_factor_of_ker_le _ _ ?_
  rw [ker_wordClosureι, Scheme.ker_of_isAffine]
  refine (map_le_map_iff Scheme.IdealSheafData.equivOfIsAffine.symm).2 fun s hs => ?_
  refine (Submodule.mem_iInf _).2 fun n => ?_
  rw [productKernel, RingHom.mem_ker, ← hq, ← orderedPowerMap_comp, Over.comp_left,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, RingHom.mem_ker.1 hs, map_zero]

variable {f} (hV : ReducedPowerGood _ V)
include hV

/-- `wordClosure f` is closed under multiplication. -/
theorem exists_mul_wordClosure :
    ∃ m : wordClosure f ⊗ wordClosure f ⟶ wordClosure f,
      m ≫ wordClosureι f = (fst _ _ ≫ wordClosureι f) * (snd _ _ ≫ wordClosureι f) := by
  have : ∀ n, IsAffine (finitePower V n).left := fun n => by
    have := (reducedPowerGood_finitePower V hV n).1
    exact isAffine_of_isAffineHom (finitePower V n).hom
  refine exists_over_factor_of_ker_le _ _ (ker_wordClosureι_le_ker f _ fun s hs => ?_)
  rw [RingHom.mem_ker]
  refine appTop_tensorHom_eq_zero (wordPoint f) (wordPoint f) (wordPoint_appTop_eq_zero f)
    (wordPoint_appTop_eq_zero f) _ fun n m => ?_
  have hg : (wordPoint f n ⊗ₘ wordPoint f m) ≫
      ((fst _ _ ≫ wordClosureι f) * (snd _ _ ≫ wordClosureι f)) =
        appendPoint (fst _ _) (snd _ _) ≫ orderedPowerMap f (n + m) := by
    rw [MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc, wordPoint_comp,
      wordPoint_comp, appendPoint_orderedPowerMap]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left, hg,
    Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 hs (n + m)), map_zero]

/-- `wordClosure f` is geometrically reduced over the base field. -/
theorem geometricallyReduced_wordClosure : GeometricallyReduced (wordClosure f).hom := by
  have hP : ∀ n, IsAffine (finitePower V n).left := fun n => by
    have := (reducedPowerGood_finitePower V hV n).1
    exact isAffine_of_isAffineHom (finitePower V n).hom
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  let Y : Over (Spec (CommRingCat.of k)) := Over.mk x
  have : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have hR : ∀ n, IsReduced (finitePower V n ⊗ Y).left := fun n => by
    have := (reducedPowerGood_finitePower V hV n).2.2
    exact pullback_of_geometrically GeometricallyReduced.geometrically_isReduced K x
  change IsReduced (wordClosure f ⊗ Y).left
  have : _root_.IsReduced Γ((wordClosure f ⊗ Y).left, ⊤) := by
    refine ⟨fun s hs => appTop_tensorHom_eq_zero (wordPoint f) (fun _ : Unit => 𝟙 Y)
      (wordPoint_appTop_eq_zero f) (fun s hs => by simpa using hs ()) s fun n _ => ?_⟩
    have := hR n
    exact (hs.map (wordPoint f n ⊗ₘ 𝟙 Y).left.appTop.hom).eq_zero
  have : IsAffine (wordClosure f ⊗ Y).left :=
    inferInstanceAs (IsAffine (pullback (wordClosure f).hom Y.hom))
  exact isReduced_of_isAffine_isReduced _

end WordClosure

/-- A geometrically reduced affine finite-type source generates a smooth closed subgroup of
any affine finite-type group over a field. -/
theorem geometricallyReducedAffineImageGeneration :
    GeometricallyReducedAffineImageGenerationStatement.{u} := by
  intro k _ G _ _ V hVAff hVFin hVRed f
  have hV : ReducedPowerGood _ V := ⟨hVAff, hVFin, hVRed⟩
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨m, hm⟩ := exists_mul_wordClosure hV (f := f)
  let e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ wordClosure f :=
    (Pi.lift fun i : Fin 0 => i.elim0) ≫ wordPoint f 0
  have he : e ≫ wordClosureι f = 1 := by
    rw [Category.assoc, wordPoint_comp, orderedPowerMap_zero, MonObj.comp_one]
  have : IsAffineHom (wordClosure f).hom :=
    inferInstanceAs (IsAffineHom ((wordClosureι f).left ≫ G.X.hom))
  have : LocallyOfFiniteType (wordClosure f).hom :=
    inferInstanceAs (LocallyOfFiniteType ((wordClosureι f).left ≫ G.X.hom))
  have hHH := affineFiniteType_tensor (wordClosure f) (wordClosure f)
  have : IsAffine (wordClosure f ⊗ wordClosure f).left := by
    have := hHH.1
    exact isAffine_of_isAffineHom (wordClosure f ⊗ wordClosure f).hom
  have : IsLocallyNoetherian (wordClosure f ⊗ wordClosure f).left := by
    have := hHH.2
    exact LocallyOfFiniteType.isLocallyNoetherian (wordClosure f ⊗ wordClosure f).hom
  let i := closedSubgroupHom (wordClosureι f) m hm e he
  have hi : IsClosedSubgroup i := isClosedSubgroup_closedSubgroupHom _ m hm e he
  have hfi : FactorsThrough f i :=
    ⟨singlePoint V ≫ wordPoint f 1, by
      rw [closedSubgroupHom_hom, Category.assoc, wordPoint_comp, singlePoint_orderedPowerMap]⟩
  refine ⟨⟨_, i, hi, ⟨?_, le_antisymm ?_ (closedImageEnvelope_le f i hi hfi)⟩⟩, ?_⟩
  · rw [closedSubgroupHom_hom]
    exact mono_of_isClosedImmersion_left _
  · intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro K j hj hfj
    obtain ⟨q, hq⟩ := hfj
    let : IsClosedImmersion j.hom.hom.left := hj
    obtain ⟨a, ha⟩ := exists_wordClosure_factor f j q hq
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ a, by
      rw [Category.assoc, ha, closedSubgroupHom_hom]⟩
  · have : GeometricallyReduced (wordClosure f).hom := geometricallyReduced_wordClosure hV
    let : GrpObj (Over.mk (wordClosure f).hom) := (closedSubgroup (wordClosureι f) m hm e he).grp
    exact smooth_of_grpObj (wordClosure f).hom

end Langlands.GroupScheme.ImageGeneration

import Langlands.GroupScheme.Rational.ClosedImmersionPullbackStatement
import Langlands.GroupScheme.Rational.DominantPullbackProof
import Langlands.GroupScheme.Rational.PointedCoordinateDecompositionProof

/-! # Closed immersions and actual equivariant weight quotients -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.PointedCoordinateWeights

/-- In a modular lattice, an independent family is not enlarged by any smaller
family which still spans. -/
theorem eq_of_iSupIndep_of_le_of_iSup_eq_top {ι α : Type*} [CompleteLattice α]
    [IsModularLattice α] {M N : ι → α} (hM : iSupIndep M) (hle : ∀ i, N i ≤ M i)
    (htop : ⨆ i, N i = ⊤) (i : ι) : N i = M i := by
  refine le_antisymm (hle i) ?_
  have hrest : (⨆ (j) (_ : j ≠ i), N j) ≤ ⨆ (j) (_ : j ≠ i), M j :=
    iSup₂_mono fun j _ => hle j
  have hdis : M i ⊓ ⨆ (j) (_ : j ≠ i), N j = ⊥ :=
    ((hM i).mono_right hrest).eq_bot
  have h : M i = N i :=
    calc M i = (N i ⊔ ⨆ (j) (_ : j ≠ i), N j) ⊓ M i := by
          rw [← iSup_split_single N i, htop, top_inf_eq]
      _ = N i ⊔ (⨆ (j) (_ : j ≠ i), N j) ⊓ M i := sup_inf_assoc_of_le _ (hle i)
      _ = N i := by rw [inf_comm, hdis, sup_bot_eq]
  exact h.le

variable {k : Type u} [Field k]
variable {V W : Over (Spec (CommRingCat.of k))} [IsAffineHom V.hom] [IsAffineHom W.hom]

/-- A closed immersion of actual affine schemes has surjective coordinate pullback. -/
theorem pullback_surjective_of_isClosedImmersion (f : V ⟶ W)
    (hf : IsClosedImmersion f.left) : Function.Surjective (pullback f) := by
  have hleft := congrArg CommaMorphism.left (algSpec_map_pullback f)
  simp only [Over.comp_left, algSpec_map_left, Quiver.Hom.unop_op] at hleft
  set ψ := ((commAlgCatEquivUnder (CommRingCat.of k)).functor.map
    (CommAlgCat.ofHom (pullback f))).right
  have hψ : Spec.map ψ =
      (coordinateIso V).hom.left ≫ f.left ≫ (coordinateIso W).inv.left := by
    rw [← Category.assoc, ← hleft, Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.comp_id]
  have : IsClosedImmersion (Spec.map ψ) := by
    rw [hψ]
    infer_instance
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ψ)).2
  have hnat := Scheme.ΓSpecIso_naturality ψ
  have hψ' : ψ = (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫ (Scheme.ΓSpecIso _).hom := by
    rw [hnat, Iso.inv_hom_id_assoc]
  have hs : Function.Surjective ψ := by
    rw [hψ']
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp
      (hsurj.comp (ConcreteCategory.bijective_of_isIso _).2)
  exact hs

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Over a field, the equivariant pullback along a closed immersion maps each
weight space onto the corresponding weight space, provided both actual
coordinate rings decompose into their weight spaces. -/
theorem map_weightSpace_eq_of_isInternal (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) (hf : IsPointedEquivariant a b f) (hsurj : Function.Surjective (pullback f))
    (hV : iSupIndep (weightSpace a)) (hW : ⨆ χ, weightSpace b χ = ⊤)
    (χ : characterLattice S) :
    (weightSpace b χ).map (pullback f).toLinearMap = weightSpace a χ := by
  refine eq_of_iSupIndep_of_le_of_iSup_eq_top
    (N := fun ψ => (weightSpace b ψ).map (pullback f).toLinearMap) hV ?_ ?_ χ
  · intro ψ
    rintro _ ⟨y, hy, rfl⟩
    exact pullback_mem_weightSpace a b f hf ψ hy
  · rw [← Submodule.map_iSup, hW, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hsurj

/-- A coordinate lift of a function in the augmentation lies in the augmentation. -/
theorem mem_augmentation_of_pullback (a : PointedAction S V) (b : PointedAction S W)
    (f : V ⟶ W) (hf : IsPointedEquivariant a b f) {y : Coord W}
    (hy : pullback f y ∈ augmentation a) : y ∈ augmentation b := by
  change coordinateOrigin b y = 0
  rw [← pullback_origin a b f hf, AlgHom.comp_apply]
  exact hy

/-- The target statement, conditional on the split-torus weight decomposition
of actual pointed coordinate rings. -/
theorem closedImmersionPullback_of_decomposition
    (hdec : PointedCoordinateDecompositionStatement.{u}) :
    ClosedImmersionPullbackStatement.{u} := by
  classical
  intro k _ S hS V W _ _ a b f hf hcl
  have hsurj := pullback_surjective_of_isClosedImmersion f hcl
  have hweight : ∀ χ : characterLattice S,
      (weightSpace b χ).map (pullback f).toLinearMap = weightSpace a χ :=
    map_weightSpace_eq_of_isInternal a b f hf hsurj
      (hdec k S hS V a).1.submodule_iSupIndep (hdec k S hS W b).1.submodule_iSup_eq_top
  have hlift : HasWeightwiseLifts a b f hf := by
    intro χ z hz
    have hz' : z.val ∈ (weightSpace b χ).map (pullback f).toLinearMap := by
      rw [hweight χ]
      exact hz
    obtain ⟨y, hy, hyz⟩ := hz'
    have hya : y ∈ augmentation b := by
      apply mem_augmentation_of_pullback a b f hf
      rw [show pullback f y = z.val from hyz]
      exact z.property
    exact ⟨⟨y, hya⟩, hy, Subtype.ext hyz⟩
  refine ⟨hsurj, ?_, hweight, hlift, support_subset_of_weightwise_lifts a b f hf hlift⟩
  intro z
  obtain ⟨y, hyz⟩ := hsurj z.val
  have hya : y ∈ augmentation b := by
    apply mem_augmentation_of_pullback a b f hf
    rw [hyz]
    exact z.property
  exact ⟨⟨y, hya⟩, Subtype.ext hyz⟩

/-- Split-torus equivariant closed immersions give the actual coordinate and
augmentation quotients, including weightwise lifts. -/
theorem closedImmersionPullback : ClosedImmersionPullbackStatement.{u} :=
  closedImmersionPullback_of_decomposition pointedCoordinateDecomposition

end Langlands.GroupScheme.PointedCoordinateWeights

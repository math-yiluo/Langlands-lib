import Langlands.GroupScheme.Reductive.SplitIsomorphismUniquenessStatement
import Langlands.GroupScheme.Reductive.PinnedWeylInner
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Torus.CharacterIsomorphism

/-! # Unpinned uniqueness for split reductive isomorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsAdjointQuotient

variable {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))}
    {q : G ⟶ A} (hq : IsAdjointQuotient q)

/-- A point of the adjoint quotient acting trivially after every restriction is
the identity. The argument lifts locally, so no rational lift is assumed. -/
theorem point_eq_one_of_innerAction_trivial
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ A.X)
    (hx : ∀ (V : Over (Spec (CommRingCat.of k))) (b : V ⟶ T) (g : V ⟶ G.X),
      hq.innerAction.act (b ≫ x) g = g) : x = 1 := by
  let := hq.flat
  let := hq.surjective
  let := hq.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q x x 1
  intro V b y hy
  have hc : y ∈ (center G).carrier V := by
    intro W c z
    have hz := hx W (c ≫ b) z
    rw [Category.assoc, hy, ← Category.assoc, hq.innerAction_act_lift] at hz
    exact (mul_inv_eq_iff_eq_mul.mp hz : _ * _ = _ * _)
  rw [hy, hq.killsCenter V y hc, MonObj.comp_one]

/-- The actual inner action is faithful as a natural action on all tests. -/
theorem point_eq_of_innerAction_eq
    {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ A.X)
    (hxy : ∀ (V : Over (Spec (CommRingCat.of k))) (b : V ⟶ T) (g : V ⟶ G.X),
      hq.innerAction.act (b ≫ x) g = hq.innerAction.act (b ≫ y) g) : x = y := by
  apply div_eq_one.mp
  apply hq.point_eq_one_of_innerAction_trivial (x / y)
  intro V b g
  rw [GrpObj.comp_div, div_eq_mul_inv, hq.innerAction.act_mul_left, hxy,
    hq.innerAction.act_act_inv]

/-- Equality of evaluated inner automorphisms determines the adjoint base point. -/
theorem innerAction_basePointIso_injective :
    Function.Injective hq.innerAction.basePointIso := by
  intro x y hxy
  apply hq.point_eq_of_innerAction_eq x y
  intro V b g
  have hb : b = Over.homMk V.hom (by simp) := by
    apply Over.OverMorphism.ext
    simpa using b.w
  rw [hb]
  change hq.innerAction.act (A.constantPoint x V) g =
    hq.innerAction.act (A.constantPoint y V) g
  rw [← AutomorphicAction.comp_basePointIso_hom, hxy,
    AutomorphicAction.comp_basePointIso_hom]

end IsAdjointQuotient

namespace SplitPinning

variable {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    {T_ad : CommGroupScheme (Spec (CommRingCat.of k))}
    {q : G ⟶ A} {j : T_ad.toGrp ⟶ A} {π : p.torus ⟶ T_ad}
    (h : IsAdjointSplitTorusImage q p.inclusion j π)

/-- The simple-root scaling map into the adjoint group factors through the
supplied actual image torus. -/
theorem exists_rootScalingTorusImageHom :
    ∃ d : p.rootScalingTorus.toGrp ⟶ T_ad.toGrp,
      d ≫ j = p.rootScalingAdjointHom h.isAdjointQuotient := by
  let := p.isSplitTorus.isAffineHom
  let := p.rootScalingTorus_isSplit.isAffineHom
  let := isAffine_of_isAffineHom p.torus.X.hom
  let := isAffine_of_isAffineHom p.rootScalingTorus.X.hom
  let := p.rootScalingProjection_fppf.1
  let := p.rootScalingProjection_fppf.2.1
  have : IsAffineHom
      (CommGroupScheme.groupHom p.rootScalingProjection).hom.hom.left := inferInstance
  have hk : kernelι (CommGroupScheme.groupHom p.rootScalingProjection) ≫
      CommGroupScheme.groupHom π = 0 := by
    apply Grp.hom_ext
    change (kernelι (CommGroupScheme.groupHom p.rootScalingProjection)).hom.hom ≫
      (CommGroupScheme.groupHom π).hom.hom = 1
    apply (h.comp_eq_one_iff_mem_center _ _).mpr
    simpa only [Category.id_comp, Grp.comp_hom_hom] using
      p.rootScalingProjection_kernel_central _
        (𝟙 (kernel (CommGroupScheme.groupHom p.rootScalingProjection)).X)
  let d := FpqcHomDescent.hom (CommGroupScheme.groupHom p.rootScalingProjection)
    (CommGroupScheme.groupHom π) hk
  refine ⟨d, ?_⟩
  have hd : CommGroupScheme.groupHom p.rootScalingProjection ≫ (d ≫ j) =
      p.inclusion ≫ q := by
    rw [← Category.assoc, FpqcHomDescent.fac, h.comp_eq]
  exact FpqcHomDescent.unique _ _ (p.rootScalingProjection_kernel_comp_adjoint
    h.isAdjointQuotient) _ hd

/-- An automorphism fixing the supplied pinned torus comes from a base point
of its supplied adjoint image torus. -/
theorem exists_torusImagePoint_of_inclusion_fixed (f : G ≅ G)
    (hf : p.inclusion ≫ f.hom = p.inclusion) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T_ad.toGrp.X,
      h.isAdjointQuotient.innerAction.basePointIso (x ≫ j.hom.hom) = f := by
  obtain ⟨c, hc⟩ := p.exists_eq_rootScalingIso f hf
  obtain ⟨d, hd⟩ := p.exists_rootScalingTorusImageHom h
  refine ⟨p.rootScalingPoint c ≫ d.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hd,
    p.innerAction_basePointIso_rootScaling h.isAdjointQuotient, ← hc]

end SplitPinning

/-- Unpinned uniqueness in the split Isomorphism Theorem, with a unique
rational point of the actual target torus modulo its full centre. -/
theorem splitIsomorphismUniqueness : SplitIsomorphismUniquenessStatement.{u} := by
  intro k _ G G' A _ T T' T'_ad _ i i' q j π h _ hi' φ₁ φ₂ t₁ t₂ h₁ h₂ hchar
  have ht : t₁.hom = t₂.hom :=
    h.sourceMaximal.1.1.hom_ext_of_characters hchar
  have hG' := h.isAdjointQuotient.isConnectedReductive
  let := hG'.isAffineHom
  obtain ⟨J, hJ, P, hP, hred⟩ :=
    rootDatumExistence k G' hG' T' h.sourceMaximal.1.1 i' hi'
  let : Finite J := hJ
  let p := SplitPinning.ofRootDatum hG' h.sourceMaximal.1.1 i' hi' P hP hred
    (splitRootLieLine k G' hG' T' h.sourceMaximal.1.1 i' hi')
  have hback : i' ≫ φ₁.inv = CommGroupScheme.groupHom t₁.inv ≫ i := by
    rw [Iso.comp_inv_eq, Category.assoc, h₁, ← Category.assoc]
    change i' = CommGroupScheme.groupHom (t₁.inv ≫ t₁.hom) ≫ i'
    rw [t₁.inv_hom_id]
    exact (Category.id_comp i').symm
  have hf : p.inclusion ≫ (φ₁.symm ≪≫ φ₂).hom = p.inclusion := by
    change i' ≫ (φ₁.inv ≫ φ₂.hom) = i'
    rw [← Category.assoc, hback, Category.assoc, h₂, ← ht, ← Category.assoc]
    change CommGroupScheme.groupHom (t₁.inv ≫ t₁.hom) ≫ i' = i'
    rw [t₁.inv_hom_id]
    exact Category.id_comp i'
  obtain ⟨x, hx⟩ := p.exists_torusImagePoint_of_inclusion_fixed h _ hf
  have hx' : φ₁ ≪≫ h.isAdjointQuotient.innerAction.basePointIso
      (x ≫ j.hom.hom) = φ₂ := by
    rw [hx]
    ext
    simp
  refine ⟨x, hx', ?_⟩
  intro y hy
  let : IsClosedImmersion j.hom.hom.left := h.targetMaximal.1.2
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono j.hom.hom).mp
  apply h.isAdjointQuotient.innerAction_basePointIso_injective
  apply Iso.ext
  apply (cancel_epi φ₁.hom).mp
  exact congrArg Iso.hom (hy.trans hx'.symm)

end Langlands.GroupScheme

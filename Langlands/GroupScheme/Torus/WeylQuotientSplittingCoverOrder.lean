import Langlands.GroupScheme.Torus.UniversalSplitWeylFibreOrder
import Langlands.GroupScheme.Torus.Relative

/-! # Constant local-base orders on a Weyl quotient's splitting cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Lifts into a pulled-back group scheme are lifts of the composite into the
original total scheme. -/
def groupSchemeBaseChangeLiftsEquiv {S S' V : Scheme.{u}}
    (b : S' ⟶ S) (W : GroupScheme S) (a : V ⟶ S') :
    {x : V ⟶ ((baseChange b).obj W).X.left //
      x ≫ ((baseChange b).obj W).X.hom = a} ≃
    {x : V ⟶ W.X.left // x ≫ W.X.hom = a ≫ b} where
  toFun x := ⟨x.val ≫ Limits.pullback.fst W.X.hom b, by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
    exact congrArg (fun f => f ≫ b) x.property⟩
  invFun x := ⟨Limits.pullback.lift x.val a x.property, by
    change Limits.pullback.lift x.val a _ ≫ Limits.pullback.snd W.X.hom b = a
    simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Limits.pullback.hom_ext
    · simp
    · change Limits.pullback.lift (x.val ≫ Limits.pullback.fst W.X.hom b) a _ ≫
        Limits.pullback.snd W.X.hom b = x.val ≫ Limits.pullback.snd W.X.hom b
      rw [Limits.pullback.lift_snd]
      exact x.property.symm
  right_inv x := Subtype.ext (by simp)

section SuppliedQuotient

variable {S S' : Scheme.{u}} {T : CommGroupScheme S} {G N W : GroupScheme S}
  (hG : IsReductive G) (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
  (hmax : IsFibrewiseMaximalTorus t) {n : N ⟶ G}
  (hn : (torusNormalizer t).IsRepresentedBy n)
  (q : N ⟶ W) (hq : Surjective q.hom.hom.left)
  [LocallyOfFiniteType N.X.hom] [LocallyOfFiniteType W.X.hom]
  (hker : ∀ (U : Over S) (y : U ⟶ N.X),
    y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U)

include hG ht hmax hn q hq hker

/-- If the pulled-back torus is split, the pulled-back quotient satisfies the
universal local-base constant-cardinality condition. -/
theorem exists_natCard_quotientFibre_constant_on_split_base
    (b : S' ⟶ S) (hT : IsSplitTorus ((baseChange b).obj T.toGrp))
    (R : Type u) [CommRing R] [IsLocalRing R] (a : Spec (CommRingCat.of R) ⟶ S') :
    ∃ d : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      Nat.card {x : Spec (CommRingCat.of k) ⟶ ((baseChange b).obj W).X.left //
        x ≫ ((baseChange b).obj W).X.hom = algebraBaseMap R k ≫ a} = d := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : LocallyOfFiniteType ((baseChange b).obj N).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd N.X.hom b)
    infer_instance
  let : LocallyOfFiniteType ((baseChange b).obj W).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd W.X.hom b)
    infer_instance
  have ht' : IsClosedSubgroup (e.inv ≫ (baseChange b).map t) :=
    (IsClosedSubgroup.of_iso e.symm).comp (ht.baseChange b)
  have hn' : (torusNormalizer (T := splitTorus.commGroupScheme S' I)
      (e.inv ≫ (baseChange b).map t)).IsRepresentedBy ((baseChange b).map n) := by
    have he := torusNormalizer_iso_comp
      (T := (CommGroupScheme.baseChange b).obj T)
      (T' := splitTorus.commGroupScheme S' I) e.symm ((baseChange b).map t)
    simp only [Iso.symm_hom] at he
    rw [he]
    exact torusNormalizer_isRepresentedBy_baseChange b t hn
  have hker' : ∀ (U : Over S') (y : U ⟶ ((baseChange b).obj N).X),
      y ≫ ((baseChange b).map q).hom.hom = 1 ↔
        y ≫ ((baseChange b).map n).hom.hom ∈
          (torusCentralizer (T := splitTorus.commGroupScheme S' I)
            (e.inv ≫ (baseChange b).map t)).carrier U := by
    intro U y
    have he := torusCentralizer_iso_comp
      (T := (CommGroupScheme.baseChange b).obj T)
      (T' := splitTorus.commGroupScheme S' I) e.symm ((baseChange b).map t)
    simp only [Iso.symm_hom] at he
    rw [he]
    exact torusCentralizerKernel_baseChange b t q hker U y
  exact exists_natCard_quotientFibre_constant_on_local_base I (hG.baseChange b)
    (e.inv ≫ (baseChange b).map t) ht'
    ((hmax.baseChange b).iso_comp
      (T := (CommGroupScheme.baseChange b).obj T)
      (T' := splitTorus.commGroupScheme S' I) e.symm)
    hn' ((baseChange b).map q)
    (MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom hq) hker' R a

/-- The same common order counts composite field-valued lifts into the original
quotient on a split base change. -/
theorem exists_natCard_quotientFibre_constant_after_split_base
    (b : S' ⟶ S) (hT : IsSplitTorus ((baseChange b).obj T.toGrp))
    (R : Type u) [CommRing R] [IsLocalRing R] (a : Spec (CommRingCat.of R) ⟶ S') :
    ∃ d : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      Nat.card {x : Spec (CommRingCat.of k) ⟶ W.X.left //
        x ≫ W.X.hom = (algebraBaseMap R k ≫ a) ≫ b} = d := by
  obtain ⟨d, hd⟩ := exists_natCard_quotientFibre_constant_on_split_base
    hG t ht hmax hn q hq hker b hT R a
  refine ⟨d, fun k => ?_⟩
  exact (Nat.card_congr
    (groupSchemeBaseChangeLiftsEquiv b W (algebraBaseMap R k ≫ a)).symm).trans (hd k)

/-- A relative maximal torus supplies one étale splitting cover on whose every
member the quotient satisfies the universal local-base cardinal condition. -/
theorem exists_splittingCover_natCard_quotientFibre_constant
    (hT : RelativeTorus.IsTorus T.toGrp) :
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ j : 𝒰.I₀, ∀ (R : Type u) [CommRing R] [IsLocalRing R]
        (a : Spec (CommRingCat.of R) ⟶ 𝒰.X j),
        ∃ d : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
          Nat.card {x : Spec (CommRingCat.of k) ⟶ ((baseChange (𝒰.f j)).obj W).X.left //
            x ≫ ((baseChange (𝒰.f j)).obj W).X.hom = algebraBaseMap R k ≫ a} = d := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  exact ⟨𝒰, fun j R _ _ a =>
    exists_natCard_quotientFibre_constant_on_split_base
      hG t ht hmax hn q hq hker (𝒰.f j) (h𝒰 j) R a⟩

end SuppliedQuotient

end Langlands.GroupScheme

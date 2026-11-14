import Langlands.AlgebraicGeometry.FppfKernelPairDescent
import Langlands.AlgebraicGeometry.QuasiAffineApproximation.Skeleton
import Langlands.AlgebraicGeometry.AlgebraicSpace.FinitePresentationRelationQuotient
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.AlgebraicSpace.TupleOrbitInduction
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # The quotient space of a Noetherian level and the Noetherian case -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.QuasiAffineApproximation

open AlgebraicSpace EtaleEquivalenceRelation

variable {S : Scheme.{u}}

section Cartesian

variable {F : Presheaf S} {U R U' R' M : Over S} {t s : R ⟶ U} {t' s' : R' ⟶ U'}
  {a : (schemeYoneda S).obj U ⟶ F} {q : U' ⟶ M} {φ : U' ⟶ U} {g : R' ⟶ R}

/-- Two points of `U'` with the same images in `M` and in `U` agree, when `R'` is the kernel
pair of `q` and also the base change along `φ` of the kernel pair `R` of `a`. -/
theorem eq_of_isCartesian
    (ha : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hq : IsPullback t' s' q q) (hg : g ≫ t = t' ≫ φ) (hcart : IsPullback g s' s φ)
    {Z : Over S} {w w' : Z ⟶ U'} (h₁ : w ≫ q = w' ≫ q) (h₂ : w ≫ φ = w' ≫ φ) : w = w' := by
  have key : hq.lift w w' h₁ = hq.lift w' w' rfl := by
    apply hcart.hom_ext
    · apply hom_ext_of_isPullback ha
      · simp only [Category.assoc, hg, IsPullback.lift_fst_assoc, h₂]
      · simp only [Category.assoc, hcart.w, IsPullback.lift_snd_assoc]
    · simp only [IsPullback.lift_snd]
  calc w = hq.lift w w' h₁ ≫ t' := (hq.lift_fst _ _ _).symm
    _ = hq.lift w' w' rfl ≫ t' := by rw [key]
    _ = w' := hq.lift_fst _ _ _

/-- A point of `M` and a point of `U` with the same image in `F` lift to a point of `U'`:
lift locally on the fppf cover obtained by base change of `q`, then descend. -/
theorem exists_lift_of_isCartesian
    (ha : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hq : IsPullback t' s' q q) (hg : g ≫ t = t' ≫ φ) (hcart : IsPullback g s' s φ)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left]
    (f : (schemeYoneda S).obj M ⟶ F)
    (hf : (schemeYoneda S).map q ≫ f = (schemeYoneda S).map φ ≫ a)
    {T : Over S} (x : T ⟶ M) (u : T ⟶ U)
    (hxu : (schemeYoneda S).map x ≫ f = (schemeYoneda S).map u ≫ a) :
    ∃ w : T ⟶ U', w ≫ q = x ∧ w ≫ φ = u := by
  let Y := schemeYoneda S
  let P : Over S := Over.mk (pullback.fst x.left q.left ≫ T.hom)
  let π : P ⟶ T := Over.homMk (pullback.fst x.left q.left)
  have hw₀ : pullback.snd x.left q.left ≫ U'.hom = P.hom := by
    change _ = pullback.fst x.left q.left ≫ T.hom
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x]
  let w₀ : P ⟶ U' := Over.homMk (pullback.snd x.left q.left) hw₀
  have hπw₀ : π ≫ x = w₀ ≫ q := by
    ext
    exact pullback.condition
  have e₁ : Y.map (π ≫ u) ≫ a = Y.map (w₀ ≫ φ) ≫ a := by
    rw [Y.map_comp, Category.assoc, ← hxu, ← Category.assoc, ← Y.map_comp, hπw₀, Y.map_comp,
      Category.assoc, hf, Y.map_comp, Category.assoc]
  obtain ⟨r, hr₁, hr₂⟩ := exists_lift_of_isPullback ha (π ≫ u) (w₀ ≫ φ) e₁
  let r' : P ⟶ R' := hcart.lift r w₀ hr₂
  obtain ⟨w₁, hw₁q, hw₁φ⟩ : ∃ w₁ : P ⟶ U', w₁ ≫ q = π ≫ x ∧ w₁ ≫ φ = π ≫ u :=
    ⟨r' ≫ t', by simp only [r', Category.assoc, hq.w, IsPullback.lift_snd_assoc, hπw₀],
      by simp only [r', Category.assoc, ← hg, IsPullback.lift_fst_assoc, hr₁]⟩
  have hc : ∀ {Z : Scheme.{u}} (k₁ k₂ : Z ⟶ P.left), k₁ ≫ π.left = k₂ ≫ π.left →
      k₁ ≫ w₁.left = k₂ ≫ w₁.left := by
    intro Z k₁ k₂ hk
    let k₁' : Over.mk (k₁ ≫ P.hom) ⟶ P := Over.homMk k₁
    let k₂' : Over.mk (k₁ ≫ P.hom) ⟶ P := Over.homMk k₂ (by
      change k₂ ≫ P.hom = k₁ ≫ P.hom
      rw [← Over.w π, ← Category.assoc, ← Category.assoc, hk])
    have hk' : k₁' ≫ π = k₂' ≫ π := by
      ext
      exact hk
    have := eq_of_isCartesian ha hq hg hcart (w := k₁' ≫ w₁) (w' := k₂' ≫ w₁)
      (by rw [Category.assoc, Category.assoc, hw₁q, ← Category.assoc, hk', Category.assoc])
      (by rw [Category.assoc, Category.assoc, hw₁φ, ← Category.assoc, hk', Category.assoc])
    exact congrArg CommaMorphism.left this
  have : EffectiveEpi π.left := (inferInstance : EffectiveEpi (pullback.fst x.left q.left))
  let d : T.left ⟶ U'.left := EffectiveEpi.desc π.left w₁.left hc
  have hd : π.left ≫ d = w₁.left := EffectiveEpi.fac π.left w₁.left hc
  have hdS : d ≫ U'.hom = T.hom := by
    rw [← cancel_epi π.left, ← Category.assoc, hd, Over.w w₁, Over.w π]
  refine ⟨Over.homMk d hdS, ?_, ?_⟩
  · ext
    change d ≫ q.left = x.left
    rw [← cancel_epi π.left, ← Category.assoc, hd]
    exact congrArg CommaMorphism.left hw₁q
  · ext
    change d ≫ φ.left = u.left
    rw [← cancel_epi π.left, ← Category.assoc, hd]
    exact congrArg CommaMorphism.left hw₁φ

/-- The square formed by `q`, `φ`, a factorization `f` through `q` and the atlas `a` is
cartesian, when `R'` is the kernel pair of `q` and the base change of `R` along `φ`. -/
theorem isPullback_of_isCartesian
    (ha : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hq : IsPullback t' s' q q) (hg : g ≫ t = t' ≫ φ) (hcart : IsPullback g s' s φ)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left]
    (f : (schemeYoneda S).obj M ⟶ F)
    (hf : (schemeYoneda S).map q ≫ f = (schemeYoneda S).map φ ≫ a) :
    IsPullback ((schemeYoneda S).map q) ((schemeYoneda S).map φ) f a := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app T) hf, ?_, ?_⟩
  · rintro x₁ y₁ ⟨h₁, h₂⟩
    apply ULift.ext
    exact eq_of_isCartesian ha hq hg hcart (congrArg ULift.down h₁) (congrArg ULift.down h₂)
  · intro x₂ x₃ h
    obtain ⟨w, hw₁, hw₂⟩ := exists_lift_of_isCartesian ha hq hg hcart f hf x₂.down x₃.down (by
      apply uliftYonedaEquiv.{u + 1}.injective
      rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map,
        uliftYonedaEquiv_uliftYoneda_map]
      exact h)
    exact ⟨⟨w⟩, ULift.ext _ _ hw₁, ULift.ext _ _ hw₂⟩

end Cartesian

set_option backward.isDefEq.respectTransparency.types false in
/-- `QuotientInterface` over an affine terminal base scheme `S`. -/
theorem quotientInterface_of_isTerminal {S : Scheme.{u}} (hS : IsTerminal S) [IsAffine S]
    (hN : NoetherianSchemeQuasiAffineSourceAFStatement.{u})
    (E₁ E₁' : EtaleEquivalenceRelation.{u}) (φ₁ : E₁'.U ⟶ E₁.U) (g₁ : E₁'.R ⟶ E₁.R)
    (M₁ : Scheme.{u}) (q₁ : E₁'.U ⟶ M₁) (hU : IsAffine E₁.U) (hR : IsAffine E₁.R)
    (hcart : IsCartesianHom E₁' E₁ φ₁ g₁) (hφf : _root_.AlgebraicGeometry.IsFinite φ₁)
    (hφs : Surjective φ₁) (hMqa : M₁.IsQuasiAffine) (hMn : IsNoetherian M₁)
    (hpb : IsPullback E₁'.t E₁'.s q₁ q₁) (hfl : Flat q₁) (hlfp : LocallyOfFinitePresentation q₁)
    (hsu : Surjective q₁) :
    ∃ (P : Scheme.{u}) (ψ : M₁ ⟶ P) (ψV : E₁.U ⟶ P),
      PointTopology.HasFiniteAffineNeighborhoods P ∧ IsAffineHom ψ ∧ q₁ ≫ ψ = φ₁ ≫ ψV := by
  let Y := schemeYoneda S
  let b : E₁.U ⟶ S := hS.from E₁.U
  have hb : E₁.t ≫ b = E₁.s ≫ b := hS.hom_ext _ _
  obtain ⟨Q, a, haE, haS, ha⟩ := etaleEquivalenceRelationAlgebraicSpaceQuotient S E₁ b hb
  let U : Over S := Over.mk b
  let R : Over S := Over.mk (E₁.t ≫ b)
  let t : R ⟶ U := Over.homMk E₁.t
  let s : R ⟶ U := Over.homMk E₁.s hb.symm
  let U' : Over S := Over.mk (hS.from E₁'.U)
  let R' : Over S := Over.mk (hS.from E₁'.R)
  let M : Over S := Over.mk (hS.from M₁)
  let t' : R' ⟶ U' := Over.homMk E₁'.t (hS.hom_ext _ _)
  let s' : R' ⟶ U' := Over.homMk E₁'.s (hS.hom_ext _ _)
  let q : U' ⟶ M := Over.homMk q₁ (hS.hom_ext _ _)
  let φ : U' ⟶ U := Over.homMk φ₁ (hS.hom_ext _ _)
  let g : R' ⟶ R := Over.homMk g₁ (hS.hom_ext _ _)
  have ha' : IsPullback (Y.map t) (Y.map s) a a := ha
  have : Flat q.left := hfl
  have : LocallyOfFinitePresentation q.left := hlfp
  have : Surjective q.left := hsu
  have hq : IsPullback t' s' q q := IsPullback.of_map_of_faithful (F := Over.forget S) hpb
  have hc : IsPullback g s' s φ := IsPullback.of_map_of_faithful (F := Over.forget S) hcart.2
  have hg : g ≫ t = t' ≫ φ := by
    ext
    exact hcart.1
  have hfac : Y.map t' ≫ (Y.map φ ≫ a) = Y.map s' ≫ (Y.map φ ≫ a) := by
    rw [← Category.assoc, ← Category.assoc, ← Y.map_comp, ← Y.map_comp, ← hg, ← hc.w,
      Y.map_comp, Y.map_comp, Category.assoc, Category.assoc, ha'.w]
  obtain ⟨f₁, hf₁⟩ := exists_fac_of_kernelPair (F := Q.toSheaf) q hq (Y.map φ ≫ a) hfac
  have hpb₁ : IsPullback (Y.map q) (Y.map φ) f₁ a :=
    isPullback_of_isCartesian ha' hq hg hc f₁ hf₁
  have hdF : MorphismProperty.DescendsAlong @_root_.AlgebraicGeometry.IsFinite.{u}
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
      @_root_.AlgebraicGeometry.IsFinite
  have hdSu : MorphismProperty.DescendsAlong @Surjective.{u}
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
      @Surjective
  have hfin : AlgebraicSpace.IsFinite f₁ :=
    relative_of_isEtale_isSurjective (@_root_.AlgebraicGeometry.IsFinite)
      (Q.representable_from_scheme f₁) haE haS (Y.map q) φ hpb₁ hφf
  have hsurj : IsSurjective f₁ :=
    relative_of_isEtale_isSurjective (@Surjective) (Q.representable_from_scheme f₁) haE haS
      (Y.map q) φ hpb₁ hφs
  have hQc : IsQuasiCompact Q := IsQuasiCompact.of_atlas a haE haS (inferInstanceAs
    (CompactSpace E₁.U))
  have hj : QuasiCompact (prod.lift t s).left := by
    have : _root_.AlgebraicGeometry.IsSeparated U.hom :=
      inferInstanceAs (_root_.AlgebraicGeometry.IsSeparated b)
    have : _root_.AlgebraicGeometry.IsSeparated (prod.fst : U ⨯ U ⟶ U).left :=
      extProd.prod_fst_left (@_root_.AlgebraicGeometry.IsSeparated.{u})
        (inferInstanceAs (_root_.AlgebraicGeometry.IsSeparated b))
    have : _root_.AlgebraicGeometry.IsSeparated (U ⨯ U).hom := by
      rw [← Over.w (prod.fst : U ⨯ U ⟶ U)]
      infer_instance
    have : QuasiCompact ((prod.lift t s).left ≫ (U ⨯ U).hom) := by
      rw [Over.w]
      exact inferInstanceAs (QuasiCompact (E₁.t ≫ b))
    exact QuasiCompact.of_comp (prod.lift t s).left (U ⨯ U).hom
  have hQs : IsQuasiSeparated Q :=
    FinitePresentationRelationQuotient.isQuasiSeparated_of_atlas a haE haS t s ha' hj
  obtain ⟨P, hP, ⟨e⟩⟩ := hN S M Q (AlgebraicSpace.homMk f₁) hQc hQs hMqa hMn hfin hsurj
  let ψ : M ⟶ P := Y.preimage (f₁ ≫ e.inv)
  let ψV : U ⟶ P := Y.preimage (a ≫ e.inv)
  have hψ : _root_.AlgebraicGeometry.IsFinite ψ.left := by
    refine isFinite_left_of_isFinite_map ψ ?_
    rw [Functor.map_preimage]
    exact IsFinite.comp_iso hfin e.symm
  have hcomm : q ≫ ψ = φ ≫ ψV := by
    apply Y.map_injective
    rw [Y.map_comp, Y.map_comp, Functor.map_preimage, Functor.map_preimage, ← Category.assoc,
      hf₁, Category.assoc]
  exact ⟨P.left, ψ.left, ψV.left, hP, inferInstance, congrArg CommaMorphism.left hcomm⟩

/-- Part III of the approximation route. -/
theorem quotientInterface : QuotientInterface.{u} :=
  fun hN E₁ E₁' φ₁ g₁ M₁ q₁ hU hR hcart hφf hφs hMqa hMn hpb hfl hlfp hsu =>
    quotientInterface_of_isTerminal specULiftZIsTerminal hN E₁ E₁' φ₁ g₁ M₁ q₁ hU hR hcart hφf
      hφs hMqa hMn hpb hfl hlfp hsu

end Langlands.AlgebraicGeometry.QuasiAffineApproximation

import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Torus.Multiplication
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Torus centralizers, character descent and maximal tori: general helpers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section General

variable {S : Scheme.{u}}

/-- Precomposition with a quasi-compact, flat, surjective homomorphism of commutative group
schemes does not change a torus centralizer. -/
theorem torusCentralizer_comp_of_fpqc {T₁ T₂ : CommGroupScheme S} {G : GroupScheme S}
    (q : T₁.toGrp ⟶ T₂.toGrp) [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] (x : T₂.toGrp ⟶ G) :
    torusCentralizer (q ≫ x) = torusCentralizer x := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  rw [mem_torusCentralizer, mem_torusCentralizer]
  constructor
  · intro hg V a s
    let W : Over S := Over.mk (pullback.fst s.left q.hom.hom.left ≫ V.hom)
    let w : W ⟶ V := Over.homMk (pullback.fst s.left q.hom.hom.left) rfl
    let r : W ⟶ T₁.X := Over.homMk (pullback.snd s.left q.hom.hom.left) (by
      rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
        Category.assoc, Over.w s]
      rfl)
    have hroot : w ≫ s = r ≫ q.hom.hom := Over.OverMorphism.ext pullback.condition
    have : Flat w.left := by
      change Flat (pullback.fst s.left q.hom.hom.left)
      infer_instance
    have : Surjective w.left := by
      change Surjective (pullback.fst s.left q.hom.hom.left)
      infer_instance
    have : QuasiCompact w.left := by
      change QuasiCompact (pullback.fst s.left q.hom.hom.left)
      infer_instance
    have : Epi w := Over.epi_of_epi_left _
    have hc := hg W (w ≫ a) r
    have e1 : r ≫ (q ≫ x).hom.hom = w ≫ s ≫ x.hom.hom := by
      rw [Grp.comp_hom_hom, ← Category.assoc, ← hroot, Category.assoc]
    rw [e1] at hc
    change (a ≫ g) * (s ≫ x.hom.hom) = (s ≫ x.hom.hom) * (a ≫ g)
    apply (cancel_epi w).mp
    simpa only [MonObj.comp_mul, Category.assoc] using hc.eq
  · intro hg V a t
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact hg V a (t ≫ q.hom.hom)

/-- Multiplying a torus homomorphism pointwise by a map with central values does not change
its torus centralizer. -/
theorem torusCentralizer_eq_of_hom_eq_mul_central {T : CommGroupScheme S} {G : GroupScheme S}
    (x y : T.toGrp ⟶ G) (c : T.X ⟶ G.X)
    (hc : ∀ (V : Over S) (t : V ⟶ T.X), t ≫ c ∈ (center G).carrier V)
    (hxy : y.hom.hom = c * x.hom.hom) :
    torusCentralizer y = torusCentralizer x := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  rw [mem_torusCentralizer, mem_torusCentralizer]
  apply forall_congr'
  intro V
  apply forall_congr'
  intro a
  apply forall_congr'
  intro t
  rw [hxy, MonObj.comp_mul]
  have hcen : Commute (a ≫ g) (t ≫ c) := (commute_of_mem_center (hc V t) (a ≫ g)).symm
  constructor
  · intro h
    have h' := hcen.inv_right.mul_right h
    simpa only [inv_mul_cancel_left] using h'
  · intro h
    exact hcen.mul_right h

/-- Pulling a torus centralizer back along a monomorphic homomorphism. -/
theorem torusCentralizer_comp_comap_of_mono {T : CommGroupScheme S} {H G : GroupScheme S}
    (x : T.toGrp ⟶ H) (d : H ⟶ G) [Mono d.hom.hom] :
    (torusCentralizer (x ≫ d)).comap d = torusCentralizer x := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  change g ≫ d.hom.hom ∈ (torusCentralizer (x ≫ d)).carrier U ↔
    g ∈ (torusCentralizer x).carrier U
  rw [mem_torusCentralizer, mem_torusCentralizer]
  apply forall_congr'
  intro V
  apply forall_congr'
  intro a
  apply forall_congr'
  intro t
  constructor
  · intro h
    change (a ≫ g) * (t ≫ x.hom.hom) = (t ≫ x.hom.hom) * (a ≫ g)
    apply (cancel_mono d.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    simpa only [Grp.comp_hom_hom, Category.assoc] using h.eq
  · intro h
    have h' := h.map (IsMonHom.monoidHom d.hom.hom V)
    simpa only [IsMonHom.monoidHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Grp.comp_hom_hom, Category.assoc] using h'

/-- On points, an `n`-fold multiple of a rational character takes `n`-th powers. -/
theorem rationalCharacters.comp_nsmul {G : GroupScheme S} {T : Over S} (x : T ⟶ G.X)
    (χ : rationalCharacters G) (n : ℕ) :
    x ≫ (n • χ).toMul.hom.hom = (x ≫ χ.toMul.hom.hom) ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact rationalCharacters.comp_zero x
  | succ n ih => rw [succ_nsmul, rationalCharacters.comp_add, ih, pow_succ]

/-- Rational characters descend through a quasi-compact, flat, surjective homomorphism
after multiplication by an integer killing its kernel. -/
theorem exists_characterRestrict_eq_nsmul_of_fpqc {H Q : GroupScheme S} (q : H ⟶ Q)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (N : ℕ) (hN : ∀ (V : Over S) (x : V ⟶ H.X), x ≫ q.hom.hom = 1 → x ^ N = 1)
    (χ : rationalCharacters H) :
    ∃ ψ : rationalCharacters Q, characterRestrict q ψ = N • χ := by
  have hk : kernelι q ≫ (N • χ).toMul = 0 := by
    apply Grp.hom_ext
    change (kernelι q).hom.hom ≫ (N • χ).toMul.hom.hom = 1
    have hκ : (kernelι q).hom.hom ≫ q.hom.hom = 1 :=
      (mem_range_kernelι_iff q (kernelι q).hom.hom).mp
        (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)
    rw [rationalCharacters.comp_nsmul, ← MonObj.pow_comp, hN _ _ hκ, MonObj.one_comp]
  refine ⟨Additive.ofMul (FpqcHomDescent.hom q (N • χ).toMul hk), ?_⟩
  change Additive.ofMul (q ≫ FpqcHomDescent.hom q (N • χ).toMul hk) = N • χ
  rw [FpqcHomDescent.fac]
  rfl

/-- A quasi-compact, flat, surjective homomorphism of locally finite presentation whose
scheme-theoretic kernel is central and killed by a positive integer. -/
structure IsCentralFppfCover {H Q : GroupScheme S} (q : H ⟶ Q) : Prop where
  quasiCompact : QuasiCompact q.hom.hom.left
  flat : Flat q.hom.hom.left
  surjective : Surjective q.hom.hom.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation q.hom.hom.left
  central : ∀ (T : Over S) (x : T ⟶ H.X), x ≫ q.hom.hom = 1 → x ∈ (center H).carrier T
  exponent : ∃ N : ℕ, 0 < N ∧ ∀ (T : Over S) (x : T ⟶ H.X), x ≫ q.hom.hom = 1 → x ^ N = 1

/-- The defining properties pass to the base change along any homomorphism, provided the
comparison map of sources is a monomorphism. -/
theorem IsCentralFppfCover.of_isPullback {P H Q M : GroupScheme S} {q : H ⟶ Q}
    (hq : IsCentralFppfCover q) (i : P ⟶ H) (p : P ⟶ M) (j : M ⟶ Q) [Mono i.hom.hom]
    (hsq : i ≫ q = p ≫ j)
    (hpb : IsPullback i.hom.hom.left p.hom.hom.left q.hom.hom.left j.hom.hom.left) :
    IsCentralFppfCover p := by
  have hker : ∀ (T : Over S) (x : T ⟶ P.X), x ≫ p.hom.hom = 1 →
      (x ≫ i.hom.hom) ≫ q.hom.hom = 1 := by
    intro T x hx
    rw [Category.assoc, ← Grp.comp_hom_hom, hsq, Grp.comp_hom_hom, ← Category.assoc, hx,
      MonObj.one_comp]
  refine ⟨MorphismProperty.of_isPullback hpb hq.quasiCompact,
    MorphismProperty.of_isPullback hpb hq.flat,
    MorphismProperty.of_isPullback hpb hq.surjective,
    MorphismProperty.of_isPullback hpb hq.locallyOfFinitePresentation, ?_, ?_⟩
  · intro T x hx T' a w
    have hc := hq.central T _ (hker T x hx) T' a (w ≫ i.hom.hom)
    change (a ≫ x) * w = w * (a ≫ x)
    apply (cancel_mono i.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    simpa only [Category.assoc] using hc.eq
  · obtain ⟨N, hN, hNx⟩ := hq.exponent
    refine ⟨N, hN, fun T x hx => ?_⟩
    apply (cancel_mono i.hom.hom).mp
    rw [MonObj.pow_comp, hNx T _ (hker T x hx), MonObj.one_comp]

end General

section Field

variable {k : Type u} [Field k]

/-- A homomorphism from a torus whose values commute with a maximal torus factors through that
maximal torus. -/
theorem IsMaximalTorus.exists_factor_of_commute {M : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth M.X.hom] [IsAffineHom M.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ M} (hj : IsMaximalTorus j)
    {B : GroupScheme (Spec (CommRingCat.of k))} (hB : IsTorus B) (b : B ⟶ M)
    (hbj : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ B.X) (y : U ⟶ T.X),
      Commute (x ≫ b.hom.hom) (y ≫ j.hom.hom)) :
    ∃ f : B ⟶ T.toGrp, f ≫ j = b := by
  obtain ⟨Z, i', π, hZ, hi', hπ⟩ := torusImageClosedTorusStatement k M (B ⊗ T.toGrp)
    (hB.tensor hj.1) (prodHom b j hbj)
  have he : (prodInr B T.toGrp ≫ π) ≫ i' = j := by
    rw [Category.assoc, hπ, prodInr_prodHom]
  have hiso : IsIso (prodInr B T.toGrp ≫ π) := hj.2.2 Z i' _ hZ hi' he
  refine ⟨(prodInl B T.toGrp ≫ π) ≫ inv (prodInr B T.toGrp ≫ π), ?_⟩
  rw [← he, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc, hπ, prodInl_prodHom]

end Field

end Langlands.GroupScheme

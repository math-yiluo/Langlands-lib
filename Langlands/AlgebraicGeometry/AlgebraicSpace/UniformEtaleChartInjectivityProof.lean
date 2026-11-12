import Langlands.AlgebraicGeometry.AlgebraicSpace.UniformEtaleChartInjectivityStatement
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top

/-!
# Uniform injectivity of affine étale charts over normed extensions

Let `a : h_U → X` be an étale map from an affine scheme `U` to a separated algebraic space
over `Spec K`. The overlap `W = U ×_X U` is a closed subscheme of `U ×_K U`, hence affine,
and the diagonal copy of `U` in `W` is open and closed. It is therefore cut out by an
idempotent global function `e` on `W`, which is the restriction of a finite sum
`∑ⱼ αⱼ ⊗ βⱼ` of products of functions on the two factors. Evaluating this sum at a pair of
points of `U` with the same image in `X` gives `1` on the diagonal, and a value close to `1`,
hence nonzero, for nearby points; a nonzero value forces the pair onto the diagonal.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest AffineCoordinateRing affineSchemePointEquiv affineCoordinatePullback
    affineCoordinatePullback_apply affineSchemePointEquiv_natural affineSchemePointEquiv_spec
    AlgPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The global sections of a fibre product of affine schemes over an affine scheme are
generated as a ring by the pullbacks of the global sections of the two factors. -/
theorem closure_range_pullback_appTop_eq_top {S X Y : Scheme.{u}} [IsAffine S] [IsAffine X]
    [IsAffine Y] (f : X ⟶ S) (g : Y ⟶ S) :
    Subring.closure (Set.range (Limits.pullback.fst f g).appTop ∪
      Set.range (Limits.pullback.snd f g).appTop) = ⊤ := by
  let a : Spec Γ(X, ⊤) ⟶ S := X.isoSpec.inv ≫ f
  let b : Spec Γ(Y, ⊤) ⟶ S := Y.isoSpec.inv ≫ g
  have h := P2MW.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top.solution
    a b
  let θ : Limits.pullback f g ⟶ Limits.pullback a b :=
    Limits.pullback.map f g a b X.isoSpec.hom Y.isoSpec.hom (𝟙 S) (by simp [a]) (by simp [b])
  let θ' : Limits.pullback a b ⟶ Limits.pullback f g :=
    Limits.pullback.map a b f g X.isoSpec.inv Y.isoSpec.inv (𝟙 S) (by simp [a]) (by simp [b])
  have hθθ' : θ ≫ θ' = 𝟙 _ := by
    simp only [θ, θ', Limits.pullback.map_comp, Iso.hom_inv_id, Category.comp_id,
      Limits.pullback.map_id]
  have hsurj : Function.Surjective θ.appTop := fun y => ⟨θ'.appTop y, by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hθθ', Scheme.Hom.id_appTop]; rfl⟩
  have h₁ : ∀ x, θ.appTop ((Limits.pullback.fst a b).appTop x) =
      (Limits.pullback.fst f g).appTop (X.isoSpec.hom.appTop x) := fun x => by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, Limits.pullback.lift_fst]
  have h₂ : ∀ x, θ.appTop ((Limits.pullback.snd a b).appTop x) =
      (Limits.pullback.snd f g).appTop (Y.isoSpec.hom.appTop x) := fun x => by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, Limits.pullback.lift_snd]
  rw [eq_top_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := hsurj y
  have hx : θ.appTop.hom x ∈ Subring.map θ.appTop.hom (Subring.closure
      (Set.range (Limits.pullback.fst a b).appTop ∪ Set.range (Limits.pullback.snd a b).appTop)) :=
    Subring.mem_map.2 ⟨x, by rw [h]; trivial, rfl⟩
  rw [RingHom.map_closure, Set.image_union] at hx
  refine Subring.closure_mono ?_ hx
  apply Set.union_subset_union
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨_, (h₁ z).symm⟩
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨_, (h₂ z).symm⟩

open TensorProduct in
/-- Every global function on the product `U ×_K U` of an affine scheme with itself is a
finite sum of products of a function pulled back along the first projection and a function
pulled back along the second. -/
theorem exists_sum_fst_mul_snd {K : Type u} [CommRing K] (U : Over (Spec (CommRingCat.of K)))
    [IsAffine U.left] [IsAffine (U ⊗ U).left] (E : AffineCoordinateRing K (U ⊗ U)) :
    ∃ (m : ℕ) (α β : Fin m → AffineCoordinateRing K U),
      E = ∑ j, affineCoordinatePullback K (fst U U) (α j) *
        affineCoordinatePullback K (snd U U) (β j) := by
  let Φ := Algebra.TensorProduct.productMap (affineCoordinatePullback K (fst U U))
    (affineCoordinatePullback K (snd U U))
  let Φr : AffineCoordinateRing K U ⊗[K] AffineCoordinateRing K U →+*
      Γ(Limits.pullback U.hom U.hom, ⊤) := Φ.toRingHom
  have hle : Subring.closure
      (Set.range (Limits.pullback.fst U.hom U.hom).appTop ∪
        Set.range (Limits.pullback.snd U.hom U.hom).appTop) ≤ Φr.range := by
    rw [Subring.closure_le]
    apply Set.union_subset
    · rintro _ ⟨z, rfl⟩
      let z' : AffineCoordinateRing K U := z
      refine ⟨z' ⊗ₜ 1, ?_⟩
      change Algebra.TensorProduct.productMap (affineCoordinatePullback K (fst U U))
        (affineCoordinatePullback K (snd U U)) (z' ⊗ₜ 1) = _
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
      rfl
    · rintro _ ⟨z, rfl⟩
      let z' : AffineCoordinateRing K U := z
      refine ⟨1 ⊗ₜ z', ?_⟩
      change Algebra.TensorProduct.productMap (affineCoordinatePullback K (fst U U))
        (affineCoordinatePullback K (snd U U)) (1 ⊗ₜ z') = _
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
      rfl
  obtain ⟨t, rfl⟩ : E ∈ Φr.range := hle (by
    rw [closure_range_pullback_appTop_eq_top]
    trivial)
  change ∃ (m : ℕ) (α β : Fin m → AffineCoordinateRing K U), Φ t = _
  induction t with
  | tmul x y =>
    refine ⟨1, fun _ => x, fun _ => y, ?_⟩
    rw [Algebra.TensorProduct.productMap_apply_tmul, Fin.sum_univ_one]
  | add s t hs ht =>
    obtain ⟨m, α, β, hs⟩ := hs
    obtain ⟨m', α', β', ht⟩ := ht
    refine ⟨m + m', Fin.append α α', Fin.append β β', ?_⟩
    rw [map_add, hs, ht, Fin.sum_univ_add]
    simp

section Overlap

variable {K : Type u} [NontriviallyNormedField K] {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {U : Over (Spec (CommRingCat.of K))} (a : (schemeYoneda _).obj U ⟶ X.presheaf)

/-- The product of an affine scheme over `Spec K` with itself is affine. -/
theorem isAffine_tensor_self [IsAffine U.left] : IsAffine (U ⊗ U).left := by
  change IsAffine (Limits.pullback U.hom U.hom)
  infer_instance

/-- If `X` is separated and `U` is affine, the overlap `U ×_X U` is affine and every global
function on it is the restriction of a global function on `U ×_K U`. -/
theorem isAffine_pairPullback_and_surjective (hX : IsSeparated X) [IsAffine U.left] :
    IsAffine (pairPullback a a).left ∧
      Function.Surjective (lift (pairPullbackFst a a) (pairPullbackSnd a a)).left.appTop := by
  have := isClosedImmersion_pairPullbackLift a a hX
  have := isAffine_tensor_self (U := U)
  exact IsClosedImmersion.isAffine_surjective_of_isAffine _

/-- Points of the overlap `U ×_X U` with values in a field are determined by their two
projections. -/
theorem pairPullback_ringPoint_ext {L : Type u} [Field L] [Algebra K L]
    {w w' : RingPoint K (pairPullback a a) L}
    (h₁ : w ≫ pairPullbackFst a a = w' ≫ pairPullbackFst a a)
    (h₂ : w ≫ pairPullbackSnd a a = w' ≫ pairPullbackSnd a a) : w = w' :=
  congrArg ULift.down (ext_app_of_isPullback (pairPullback_isPullback a a) (ringTest K L)
    (p := ULift.up w) (q := ULift.up w') (congrArg ULift.up h₁) (congrArg ULift.up h₂))

/-- **The diagonal idempotent.** For an étale map `a : h_U → X` from an affine scheme with
affine overlap `U ×_X U`, there is a global function `e` on the overlap whose value at a
field-valued point is nonzero only on the diagonal, where it equals `1`. -/
theorem exists_diagonal_idempotent (ha : IsEtale a) [IsAffine U.left]
    [IsAffine (pairPullback a a).left] :
    ∃ e : AffineCoordinateRing K (pairPullback a a),
      ∀ (L : Type u) [Field L] [Algebra K L] (w : ringTest K L ⟶ pairPullback a a),
        ((affineSchemePointEquiv K _ L w).toAlgHom e ≠ 0 →
          w ≫ pairPullbackFst a a = w ≫ pairPullbackSnd a a) ∧
        (w ≫ pairPullbackFst a a = w ≫ pairPullbackSnd a a →
          (affineSchemePointEquiv K _ L w).toAlgHom e = 1) := by
  have := etale_pairPullbackSnd a a ha
  obtain ⟨d, hd⟩ := (schemeYoneda _).map_surjective
    ((pairPullback_isPullback a a).lift (𝟙 _) (𝟙 _) rfl)
  have hd₁ : d ≫ pairPullbackFst a a = 𝟙 U :=
    (schemeYoneda _).map_injective (by
      rw [Functor.map_comp, hd, IsPullback.lift_fst]
      exact ((schemeYoneda _).map_id U).symm)
  have hd₂ : d ≫ pairPullbackSnd a a = 𝟙 U :=
    (schemeYoneda _).map_injective (by
      rw [Functor.map_comp, hd, IsPullback.lift_snd]
      exact ((schemeYoneda _).map_id U).symm)
  have : _root_.AlgebraicGeometry.IsOpenImmersion d.left :=
    isOpenImmersion_of_section (pairPullbackSnd a a).left d.left
      (by rw [← Over.comp_left, hd₂, Over.id_left])
  have : _root_.AlgebraicGeometry.IsClosedImmersion d.left := by
    have : _root_.AlgebraicGeometry.IsClosedImmersion (d.left ≫ (pairPullbackFst a a).left) := by
      rw [← Over.comp_left, hd₁, Over.id_left]
      infer_instance
    exact IsClosedImmersion.of_comp d.left (pairPullbackFst a a).left
  let W := (pairPullback a a).left
  let S : Set W := Set.range d.left
  have hS : IsClopen S :=
    ⟨d.left.isClosedEmbedding.isClosed_range, d.left.isOpenEmbedding.isOpen_range⟩
  let T : Set (PrimeSpectrum Γ(W, ⊤)) := (fun y => W.isoSpec.inv y) ⁻¹' S
  have hT : IsClopen T := hS.preimage W.isoSpec.inv.continuous
  obtain ⟨e, he, hTe⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hT
  have hT' : ∀ y : PrimeSpectrum Γ(W, ⊤), y ∈ T ↔ e ∉ y.asIdeal := fun y => by
    rw [hTe]
    exact PrimeSpectrum.mem_basicOpen _ _
  have key : ∀ (L : Type u) [Field L] [Algebra K L] (w : ringTest K L ⟶ pairPullback a a)
      (x : Spec (CommRingCat.of L)),
      w.left x ∈ S ↔ (affineSchemePointEquiv K _ L w).toAlgHom e ≠ 0 := by
    intro L _ _ w x
    have h₁ : w.left x ∈ S ↔ W.isoSpec.hom (w.left x) ∈ T := by
      change _ ↔ W.isoSpec.inv (W.isoSpec.hom (w.left x)) ∈ S
      rw [Scheme.hom_inv_apply]
    have h₂ : W.isoSpec.hom (w.left x) = Spec.map (CommRingCat.ofHom
        (affineSchemePointEquiv K _ L w).toAlgHom.toRingHom) x := by
      exact (congrArg (fun g : Spec (CommRingCat.of L) ⟶ Spec Γ(W, ⊤) => g x)
        (affineSchemePointEquiv_spec K L w)).symm
    have h₃ : ∀ (ψ : Γ(W, ⊤) →+* L) (y : PrimeSpectrum L),
        e ∉ (PrimeSpectrum.comap ψ y).asIdeal ↔ ψ e ≠ 0 := fun ψ y => by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.eq_bot_of_prime y.asIdeal,
        Ideal.mem_bot]
    refine h₁.trans ((hT' _).trans ?_)
    rw [h₂]
    exact h₃ _ x
  refine ⟨e, fun L _ _ w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · have hr : Set.range w.left ⊆ Set.range d.left := by
      rintro _ ⟨x, rfl⟩
      exact (key L w x).2 hw
    have hl := IsOpenImmersion.lift_fac d.left w.left hr
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, ← hl, Category.assoc, Category.assoc, ← Over.comp_left,
      ← Over.comp_left, hd₁, hd₂]
  · have hw' : w = (w ≫ pairPullbackFst a a) ≫ d :=
      pairPullback_ringPoint_ext a (by rw [Category.assoc, hd₁, Category.comp_id])
        (by rw [Category.assoc, hd₂, Category.comp_id, hw])
    have hne : (affineSchemePointEquiv K _ L w).toAlgHom e ≠ 0 := by
      rw [← key L w default, hw']
      exact ⟨_, rfl⟩
    have hid : (affineSchemePointEquiv K _ L w).toAlgHom e *
        (affineSchemePointEquiv K _ L w).toAlgHom e =
          (affineSchemePointEquiv K _ L w).toAlgHom e :=
      (map_mul _ e e).symm.trans (congrArg _ he.eq)
    exact mul_left_cancel₀ hne (hid.trans (mul_one _).symm)

end Overlap

/-- Evaluating a pulled-back coordinate function at a point is evaluating the original function
at the composite point. -/
theorem affineSchemePointEquiv_comp_apply {K : Type u} [CommRing K]
    {Y Z : Over (Spec (CommRingCat.of K))} [IsAffine Y.left] [IsAffine Z.left]
    {L : Type u} [CommRing L] [Algebra K L] (p : ringTest K L ⟶ Y) (f : Y ⟶ Z)
    (z : AffineCoordinateRing K Z) :
    (affineSchemePointEquiv K Z L (p ≫ f)).toAlgHom z =
      (affineSchemePointEquiv K Y L p).toAlgHom (affineCoordinatePullback K f z) := by
  exact congrArg (fun φ : AlgPoint K (AffineCoordinateRing K Z) L => φ.toAlgHom z)
    (affineSchemePointEquiv_natural K L f p)

/-- **Uniform injectivity of affine étale charts.** The coordinate functions `αⱼ, βⱼ` of a
decomposition `∑ⱼ αⱼ ⊗ βⱼ` of the diagonal idempotent separate, on each bounded coordinate
locus, sufficiently close points of the same fibre, uniformly over all normed extensions. -/
theorem uniformEtaleChartInjectivity : UniformEtaleChartInjectivityStatement.{u} := by
  intro K _ X hX U _ _ a ha
  obtain ⟨hW, hsurj⟩ := isAffine_pairPullback_and_surjective a hX
  have := isAffine_tensor_self (U := U)
  obtain ⟨e, he⟩ := exists_diagonal_idempotent a ha
  obtain ⟨E, hE⟩ := hsurj e
  obtain ⟨m, α, β, hαβ⟩ := exists_sum_fst_mul_snd U E
  let ι := lift (pairPullbackFst a a) (pairPullbackSnd a a)
  -- The value of `e` at a point `w` of the overlap, in terms of its two projections.
  have hval : ∀ (L : Type u) [Field L] [Algebra K L] (w : ringTest K L ⟶ pairPullback a a),
      (affineSchemePointEquiv K _ L w).toAlgHom e =
        ∑ j, (affineSchemePointEquiv K U L (w ≫ pairPullbackFst a a)).toAlgHom (α j) *
          (affineSchemePointEquiv K U L (w ≫ pairPullbackSnd a a)).toAlgHom (β j) := by
    intro L _ _ w
    have h₁ : (affineSchemePointEquiv K _ L w).toAlgHom e =
        (affineSchemePointEquiv K _ L (w ≫ ι)).toAlgHom E := by
      rw [← hE]
      exact (affineSchemePointEquiv_comp_apply w ι E).symm
    rw [h₁, hαβ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← affineSchemePointEquiv_comp_apply, ← affineSchemePointEquiv_comp_apply,
      Category.assoc, Category.assoc, lift_fst, lift_snd]
  refine ⟨m + m, Fin.append α β, fun R hR => ⟨1 / ((m : ℝ) * R + 1), by positivity, ?_⟩⟩
  intro L _ _ p q hp hq hpq hapq
  obtain ⟨⟨w⟩, hw₁, hw₂⟩ := exists_app_of_isPullback (pairPullback_isPullback a a)
    (ringTest K L) (ULift.up p) (ULift.up q) hapq
  obtain ⟨⟨w₀⟩, hw₀₁, hw₀₂⟩ := exists_app_of_isPullback (pairPullback_isPullback a a)
    (ringTest K L) (ULift.up p) (ULift.up p) rfl
  have hw₁' : w ≫ pairPullbackFst a a = p := congrArg ULift.down hw₁
  have hw₂' : w ≫ pairPullbackSnd a a = q := congrArg ULift.down hw₂
  have hw₀₁' : w₀ ≫ pairPullbackFst a a = p := congrArg ULift.down hw₀₁
  have hw₀₂' : w₀ ≫ pairPullbackSnd a a = p := congrArg ULift.down hw₀₂
  have hx : ∀ j, ‖(affineSchemePointEquiv K U L p).toAlgHom (α j)‖ ≤ R := fun j => by
    have := hp (Fin.castAdd m j)
    rw [Fin.append_left] at this
    exact this
  have hy : ∀ j, ‖(affineSchemePointEquiv K U L p).toAlgHom (β j) -
      (affineSchemePointEquiv K U L q).toAlgHom (β j)‖ < 1 / ((m : ℝ) * R + 1) := fun j => by
    have := hpq (Fin.natAdd m j)
    rw [Fin.append_right] at this
    exact this
  have hne : (affineSchemePointEquiv K _ L w).toAlgHom e ≠ 0 := by
    intro h0
    have h1 := (he L w₀).2 (hw₀₁'.trans hw₀₂'.symm)
    rw [hval, hw₀₁', hw₀₂'] at h1
    rw [hval, hw₁', hw₂'] at h0
    have h2 := congrArg₂ (· - ·) h1 h0
    simp only [← Finset.sum_sub_distrib, ← mul_sub, sub_zero] at h2
    have h3 : ‖(1 : L)‖ ≤ m * (R * (1 / ((m : ℝ) * R + 1))) := by
      rw [← h2]
      calc _ ≤ ∑ j, ‖(affineSchemePointEquiv K U L p).toAlgHom (α j) *
            ((affineSchemePointEquiv K U L p).toAlgHom (β j) -
              (affineSchemePointEquiv K U L q).toAlgHom (β j))‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin m, R * (1 / ((m : ℝ) * R + 1)) := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (hx j) (hy j).le (norm_nonneg _) hR.le
        _ = _ := by simp
    have h4 : (m : ℝ) * (R * (1 / ((m : ℝ) * R + 1))) < 1 := by
      rw [show (m : ℝ) * (R * (1 / ((m : ℝ) * R + 1))) = m * R / (m * R + 1) by ring,
        div_lt_one (by positivity)]
      linarith
    rw [norm_one] at h3
    linarith
  have heq := (he L w).1 hne
  rw [hw₁', hw₂'] at heq
  exact heq

end Langlands.AlgebraicGeometry.AlgebraicSpace

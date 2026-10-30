import Langlands.GroupScheme.Cartier.Characters
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Cartier characters separate rational points over an algebraically closed field

For a finite étale commutative group scheme `G` over `Spec K`, with `K` algebraically closed,
killed by an integer `n` invertible in `K`, every nontrivial `K`-point of `G` is detected by an
actual Cartier character of `G` over the identity test scheme.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier

universe u

variable {K : Type u} [Field K]

/-- Evaluation of a global function at a rational point, with values in `K`. -/
def pointValue {X : Over (Spec (CommRingCat.of K))}
    (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) : Γ(X.left, ⊤) →+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp a.left.appTop.hom

/-- Constant global functions on a scheme over `Spec K`. -/
def constants (X : Over (Spec (CommRingCat.of K))) : K →+* Γ(X.left, ⊤) :=
  X.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

lemma pointValue_constants {X : Over (Spec (CommRingCat.of K))}
    (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) (k : K) :
    pointValue a (constants X k) = k := by
  have hw : a.left ≫ X.hom = 𝟙 _ := by simp
  have hx : X.hom.appTop ≫ a.left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hw, Scheme.Hom.id_appTop]
    rfl
  have h : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop ≫ a.left.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom = 𝟙 _ := by
    rw [reassoc_of% hx, Iso.inv_hom_id]
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom k) h

/-- Rational points of an affine scheme over `Spec K` are separated by global functions. -/
lemma exists_pointValue_ne {X : Over (Spec (CommRingCat.of K))} [IsAffine X.left]
    {a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X} (hab : a ≠ b) :
    ∃ r, pointValue a r ≠ pointValue b r := by
  by_contra! h
  apply hab
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  have h' : a.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      b.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    ext r
    exact h r
  exact (cancel_mono _).1 h'

/-- A finite scheme over `Spec K` has finitely many rational points. -/
lemma finite_points (X : Over (Spec (CommRingCat.of K))) [IsFinite X.hom] :
    Finite (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) := by
  have := Langlands.AlgebraicGeometry.FiniteEtale.finite_sections_of_isFinite X.hom
  refine Finite.of_injective
    (fun a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X =>
      (⟨a.left, by simp⟩ :
        {x : Spec (CommRingCat.of K) ⟶ X.left // x ≫ X.hom = 𝟙 _})) ?_
  intro a b h
  exact Over.OverMorphism.ext (congrArg Subtype.val h)

/-- Interpolation: on an affine scheme over `Spec K` with finitely many rational points,
global functions take arbitrary prescribed values at the rational points. -/
lemma exists_section_pointValue {X : Over (Spec (CommRingCat.of K))} [IsAffine X.left]
    [Finite (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X)]
    (c : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) → K) :
    ∃ s : Γ(X.left, ⊤), ∀ a, pointValue a s = c a := by
  classical
  have := Fintype.ofFinite (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X)
  have hsep : ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X, a ≠ b →
      ∃ r, pointValue a r = 1 ∧ pointValue b r = 0 := by
    intro a b hab
    obtain ⟨r, hr⟩ := exists_pointValue_ne hab
    have hd : pointValue a r - pointValue b r ≠ 0 := sub_ne_zero.mpr hr
    refine ⟨(r - constants X (pointValue b r)) *
      constants X (pointValue a r - pointValue b r)⁻¹, ?_, ?_⟩
    · rw [map_mul, map_sub, pointValue_constants, pointValue_constants, mul_inv_cancel₀ hd]
    · rw [map_mul, map_sub, pointValue_constants, sub_self, zero_mul]
  choose! e he using hsep
  have hδ : ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X,
      pointValue b (∏ b' ∈ Finset.univ.erase a, e a b') = if b = a then 1 else 0 := by
    intro a b
    rw [map_prod]
    split_ifs with hba
    · subst hba
      exact Finset.prod_eq_one fun b' hb' => (he b b' (Finset.ne_of_mem_erase hb').symm).1
    · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩)
        (he a b (Ne.symm hba)).2
  refine ⟨∑ a, constants X (c a) * ∏ b' ∈ Finset.univ.erase a, e a b', fun b => ?_⟩
  simp only [map_sum, map_mul, pointValue_constants, hδ, mul_ite, mul_one, mul_zero]
  simp

/-- A finite étale scheme over an algebraically closed field: global functions are determined
by their values at rational points. -/
lemma section_ext_of_pointValue [IsAlgClosed K] {X : Over (Spec (CommRingCat.of K))}
    [Etale X.hom] {s t : Γ(X.left, ⊤)}
    (h : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X, pointValue a s = pointValue a t) :
    s = t := by
  have : IsReduced X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K X.left X.hom
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Scheme.exists_fac_of_etale_of_isSepClosed X.hom (𝟙 _) x
    (Subsingleton.elim _ _)
  let a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X := Over.homMk l hl
  have h0 : l.appTop (s - t) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
    have := h a
    rw [← sub_eq_zero, ← map_sub] at this
    simpa [pointValue, a] using this
  have hmem : (default : Spec (CommRingCat.of K)) ∈ l ⁻¹ᵁ X.left.basicOpen (s - t) := hx
  rw [Scheme.preimage_basicOpen] at hmem
  change (default : Spec (CommRingCat.of K)) ∈
    (Spec (CommRingCat.of K)).basicOpen (l.appTop (s - t)) at hmem
  rw [h0, Scheme.basicOpen_zero] at hmem
  exact absurd hmem (by simp)

/-- Evaluating the unit attached to a morphism to `𝔾_m` at a rational point. -/
lemma pointValue_pointsEquiv {X : Over (Spec (CommRingCat.of K))}
    (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) (f : X ⟶ (Gm _).X) :
    pointValue a (Gm.pointsEquiv _ X f).val =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
        (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (a ≫ f)).val := by
  rw [Gm.pointsEquiv_naturality]
  rfl

/-- Morphisms from a finite étale scheme over an algebraically closed field to `𝔾_m` are
determined by their values at rational points. -/
lemma gm_hom_ext [IsAlgClosed K] {X : Over (Spec (CommRingCat.of K))} [Etale X.hom]
    {f g : X ⟶ (Gm _).X}
    (h : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X, a ≫ f = a ≫ g) : f = g := by
  apply (Gm.pointsEquiv _ X).injective
  apply Units.ext
  apply section_ext_of_pointValue
  intro a
  rw [pointValue_pointsEquiv, pointValue_pointsEquiv, h a]

/-- Invertible global functions with prescribed nonzero values at rational points. -/
lemma exists_unit_pointValue [IsAlgClosed K] {X : Over (Spec (CommRingCat.of K))}
    [IsFinite X.hom] [Etale X.hom] (c : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) → Kˣ) :
    ∃ u : Γ(X.left, ⊤)ˣ, ∀ a, pointValue a (u : Γ(X.left, ⊤)) = c a := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have := finite_points X
  obtain ⟨s, hs⟩ := exists_section_pointValue (fun a => (c a : K))
  obtain ⟨t, ht⟩ := exists_section_pointValue (fun a => (((c a)⁻¹ : Kˣ) : K))
  have hst : s * t = 1 := section_ext_of_pointValue fun a => by
    rw [map_mul, hs, ht, map_one, Units.mul_inv]
  exact ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, hs⟩

/-- An abstract homomorphism on rational points is realized by an actual morphism to `𝔾_m`
which is multiplicative on all points. -/
lemma exists_gm_hom_of_points [IsAlgClosed K] (G : CommGroupScheme (Spec (CommRingCat.of K)))
    [IsFinite G.X.hom] [Etale G.X.hom]
    (φ : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) →* Kˣ) :
    ∃ f : G.X ⟶ (Gm _).X,
      (∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
          (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (a ≫ f)).val = φ a) ∧
      μ[G.X] ≫ f = (fst G.X G.X ≫ f) * (snd G.X G.X ≫ f) := by
  obtain ⟨u, hu⟩ := exists_unit_pointValue (X := G.X) (fun a => φ a)
  have hf : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of K))))
        (a ≫ (Gm.pointsEquiv _ G.X).symm u)).val = φ a := by
    intro a
    rw [← pointValue_pointsEquiv, MulEquiv.apply_symm_apply, hu]
  refine ⟨(Gm.pointsEquiv _ G.X).symm u, hf, ?_⟩
  have : IsFinite (G.X ⊗ G.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have : Etale (G.X ⊗ G.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  apply gm_hom_ext
  intro p
  rw [MonObj.comp_mul]
  apply (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of K))))).injective
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom _ =
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom _
  have hp : p ≫ μ[G.X] = (p ≫ fst G.X G.X) * (p ≫ snd G.X G.X) := by
    rw [Hom.mul_def, lift_comp_fst_snd]
  rw [map_mul, Units.val_mul, map_mul, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    hf, hf, hf, hp, map_mul, Units.val_mul]

/-- **Character separation.** Over an algebraically closed field `K`, Cartier characters of a
finite étale commutative group scheme killed by `n`, with `n` invertible in `K`, separate its
rational points from the identity. -/
theorem exists_characterEvaluation_ne_one_of_isAlgClosed [IsAlgClosed K]
    (G : CommGroupScheme (Spec (CommRingCat.of K))) [IsFinite G.X.hom] [Etale G.X.hom]
    (n : ℕ) (hn : (n : K) ≠ 0) (hG : multiplication G.toGrp (n : ℤ) = 1)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) (hx : x ≠ 1) :
    ∃ χ : (characters G).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of K))))),
      characterEvaluation χ x ≠ 1 := by
  classical
  have := finite_points G.X
  have hexp : Monoid.exponent (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) ∣ n :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun y => by
      have := points_zpow_eq_one G (n : ℤ) hG _ y
      rwa [zpow_natCast] at this
  have : NeZero ((Monoid.exponent (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) : ℕ) : K) := by
    refine ⟨fun h0 => hn ?_⟩
    obtain ⟨k, hk⟩ := hexp
    rw [hk, Nat.cast_mul, h0, zero_mul]
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) K hx
  obtain ⟨f, hf, hmul⟩ := exists_gm_hom_of_points G φ
  let ψ : G.toGrp ⟶ (Gm (Spec (CommRingCat.of K))).toGrp :=
    homOfPoints (fun T => MonoidHom.mk' (fun y => y ≫ f) fun y z => by
        change lift y z ≫ μ[G.X] ≫ f = _
        rw [hmul, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc])
      (fun a y => (Category.assoc a y f))
  refine ⟨(CommGroupScheme.baseChange (Over.mk (𝟙 (Spec (CommRingCat.of K)))).hom).map
    (Additive.ofMul ψ), ?_⟩
  change evaluation ((CommGroupScheme.baseChange _).map (Additive.ofMul ψ)) x ≠ 1
  rw [evaluation_baseChange]
  change x ≫ ψ.hom.hom ≠ 1
  rw [comp_homOfPoints]
  change x ≫ f ≠ 1
  intro h1
  apply hφ
  apply Units.ext
  rw [← hf x, h1, map_one, Units.val_one, map_one, Units.val_one]

end Langlands.GroupScheme.Cartier

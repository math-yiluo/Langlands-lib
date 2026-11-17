import Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineQuotient

/-! # Relative quotients and local orbit fibers for finite free actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.FiniteFreeSchemeAction.EffectiveQuotient

variable {G : Type u} [Group G] {X : Scheme.{u}} {A : FiniteFreeSchemeAction G X}
  (Q : A.EffectiveQuotient)

/-- Quotient fibers are action orbits locally on a Zariski cover of every test scheme. -/
theorem eq_iff_locally_act {T : Scheme.{u}} (a b : T ⟶ X) :
    a ≫ Q.map = b ≫ Q.map ↔
      ∃ (𝒰 : T.OpenCover.{u}) (g : 𝒰.I₀ → G),
        ∀ i, 𝒰.f i ≫ a = 𝒰.f i ≫ b ≫ (A.act (g i)).hom := by
  constructor
  · intro h
    let r := Q.isPullback.lift a b h
    let 𝒰 := (sigmaOpenCover (fun _ : G => X)).pullback₁ r
    refine ⟨𝒰, fun i => i, ?_⟩
    intro i
    change G at i
    change pullback.fst r (Sigma.ι (fun _ : G => X) i) ≫ a =
      pullback.fst r (Sigma.ι (fun _ : G => X) i) ≫ b ≫ (A.act i).hom
    have hr₁ : r ≫ A.target = a := Q.isPullback.lift_fst _ _ _
    have hr₂ : r ≫ A.source = b := Q.isPullback.lift_snd _ _ _
    have hc := pullback.condition (f := r) (g := Sigma.ι (fun _ : G => X) i)
    have h₁ := congrArg (fun f => f ≫ A.target) hc
    have h₂ := congrArg (fun f => f ≫ A.source) hc
    simp only [Category.assoc, hr₁, A.ι_target] at h₁
    simp only [Category.assoc, hr₂, A.ι_source, Category.comp_id] at h₂
    exact h₁.trans (by rw [← h₂, Category.assoc])
  · rintro ⟨𝒰, g, hg⟩
    apply 𝒰.hom_ext
    intro i
    simpa only [Category.assoc, Q.invariant] using
      congrArg (fun f => f ≫ Q.map) (hg i)

end Langlands.AlgebraicGeometry.FiniteFreeSchemeAction.EffectiveQuotient

namespace Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineActionOver

variable {S : Scheme.{u}} {G : Type u} [Group G] (U : Over S)
  (A : FiniteFreeSchemeAction G U.left)
  (hA : ∀ g, (A.act g).hom ≫ U.hom = U.hom) (Q : A.EffectiveQuotient)

/-- The chosen action map regarded as a morphism over the base. -/
def actOver (g : G) : U ⟶ U := Over.homMk (A.act g).hom (hA g)

/-- The effective quotient with its descended structure morphism. -/
def quotientOver : Over S := Over.mk (Q.desc U.hom hA)

/-- The finite étale quotient projection over the base. -/
def quotientMapOver : U ⟶ quotientOver U A hA Q :=
  Over.homMk Q.map (Q.map_desc U.hom hA)

@[simp] theorem quotientMapOver_left :
    (quotientMapOver U A hA Q).left = Q.map := rfl

instance : IsFinite (quotientMapOver U A hA Q).left := Q.finite
instance : Etale (quotientMapOver U A hA Q).left := Q.etale
instance : Surjective (quotientMapOver U A hA Q).left := Q.surjective

theorem quotientOver_isQuasiAffine [Finite G] [U.left.IsQuasiAffine] :
    (quotientOver U A hA Q).left.IsQuasiAffine := Q.isQuasiAffine

/-- Over an affine base, the quotient satisfies the all-affine-open version of
relative quasi-affineness used in the multiplicative-type quotient statement. -/
theorem quotientOver_quasiAffineOver [IsAffine S] [Finite G] [U.left.IsQuasiAffine]
    (V : S.affineOpens) :
    ((quotientOver U A hA Q).hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine := by
  let : (quotientOver U A hA Q).left.IsQuasiAffine := Q.isQuasiAffine
  let : IsAffineHom (V : S.Opens).ι := inferInstance
  let : IsAffineHom ((quotientOver U A hA Q).hom ⁻¹ᵁ (V : S.Opens)).ι :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_morphismRestrict (quotientOver U A hA Q).hom (V : S.Opens))
      inferInstance
  exact Scheme.IsQuasiAffine.of_isAffineHom
    ((quotientOver U A hA Q).hom ⁻¹ᵁ (V : S.Opens)).ι

/-- Every relative test has the same local orbit description as its underlying
scheme; the acting group element may vary between open pieces. -/
theorem quotientMapOver_eq_iff_locally_act {T : Over S} (a b : T ⟶ U) :
    a ≫ quotientMapOver U A hA Q = b ≫ quotientMapOver U A hA Q ↔
      ∃ (𝒰 : T.left.OpenCover.{u}) (g : 𝒰.I₀ → G),
        ∀ i, 𝒰.f i ≫ a.left = 𝒰.f i ≫ b.left ≫ (A.act (g i)).hom := by
  rw [Over.OverMorphism.ext_iff]
  exact Q.eq_iff_locally_act a.left b.left

/-- A finite free action over an affine base has a chosen effective quotient
over that base, with its quasi-affineness and finite étale projection retained. -/
def quotientModel [IsAffine S] [Finite G] [U.left.IsQuasiAffine] :
    Σ Y : Over S, {q : U ⟶ Y //
      IsFinite q.left ∧ Etale q.left ∧ Surjective q.left ∧
      (∀ V : S.affineOpens, (Y.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine) ∧
      ∀ (T : Over S) (a b : T ⟶ U),
        a ≫ q = b ≫ q ↔
          ∃ (𝒰 : T.left.OpenCover.{u}) (g : 𝒰.I₀ → G),
            ∀ i, 𝒰.f i ≫ a.left = 𝒰.f i ≫ b.left ≫ (A.act (g i)).hom} :=
  ⟨quotientOver U A hA Q, quotientMapOver U A hA Q,
    inferInstance, inferInstance, inferInstance, quotientOver_quasiAffineOver U A hA Q,
    fun _ a b => quotientMapOver_eq_iff_locally_act U A hA Q a b⟩

end Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineActionOver

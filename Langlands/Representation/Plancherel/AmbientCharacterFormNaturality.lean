import Langlands.Representation.Plancherel.AmbientCharacterForm

/-! # Symmetries of character forms induced from an ambient form -/

noncomputable section

universe u

namespace Langlands.LinearAlgebra.PositiveQuotient

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W]
  (B : LinearMap.BilinForm ℝ V) (hs : B.IsSymm)
  (hp : ∀ x : V, x ≠ 0 → 0 < B x x)
  (q : V →ₗ[ℝ] W) (hq : Function.Surjective q)

/-- The orthogonal lift is the unique lift orthogonal to the restriction kernel. -/
theorem eq_orthogonalLift_of_mem {v : V} {x : W}
    (hv : v ∈ B.orthogonal (LinearMap.ker q)) (hx : q v = x) :
    v = orthogonalLift B hs hp q hq x := by
  let e := orthogonalRestrictionEquiv B hs hp q hq
  have he : e ⟨v, hv⟩ = x := hx
  exact congrArg Subtype.val (e.injective (he.trans (e.apply_symm_apply x).symm))

/-- Commuting automorphisms preserving the ambient form commute with its lift. -/
theorem orthogonalLift_equivariant
    (a : V ≃ₗ[ℝ] V) (b : W ≃ₗ[ℝ] W)
    (hc : ∀ v, q (a v) = b (q v))
    (hB : ∀ v z, B (a v) (a z) = B v z) (x : W) :
    a (orthogonalLift B hs hp q hq x) = orthogonalLift B hs hp q hq (b x) := by
  apply eq_orthogonalLift_of_mem B hs hp q hq
  · intro z hz
    have hz' : a.symm z ∈ LinearMap.ker q := by
      change q (a.symm z) = 0
      apply b.injective
      rw [map_zero, ← hc, a.apply_symm_apply]
      exact hz
    have he := hB (a.symm z) (orthogonalLift B hs hp q hq x)
    rw [a.apply_symm_apply] at he
    exact he.trans (orthogonalLift_mem B hs hp q hq x _ hz')
  · rw [hc, map_orthogonalLift]

/-- The local quotient form inherits every compatible ambient symmetry. -/
theorem quotientForm_invariant
    (a : V ≃ₗ[ℝ] V) (b : W ≃ₗ[ℝ] W)
    (hc : ∀ v, q (a v) = b (q v))
    (hB : ∀ v z, B (a v) (a z) = B v z) (x y : W) :
    quotientForm B hs hp q hq (b x) (b y) = quotientForm B hs hp q hq x y := by
  rw [quotientForm_apply, quotientForm_apply,
    ← orthogonalLift_equivariant B hs hp q hq a b hc hB x,
    ← orthogonalLift_equivariant B hs hp q hq a b hc hB y, hB]

end Langlands.LinearAlgebra.PositiveQuotient

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme

namespace Langlands.Plancherel

open Langlands.LinearAlgebra.PositiveQuotient

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
  (f : A ⟶ T)
  (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar T)) (hs : B.IsSymm)
  (hp : ∀ x : RealTorusSpace.Vstar T, x ≠ 0 → 0 < B x x)

/-- Actual character restriction commutes with automorphisms preserving the
actual torus inclusion, with the published inverse-precomposition convention. -/
theorem restrict_characterRealAut (s : A ≅ A) (t : T ≅ T)
    (hc : f ≫ t.hom = s.hom ≫ f) (x : RealTorusSpace.Vstar T) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
      (RealTorusSpace.characterRealAut t x) =
        RealTorusSpace.characterRealAut s
          (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) x) := by
  have hi : s.inv ≫ f = f ≫ t.inv := by
    have h := congrArg (fun g : A ⟶ T => s.inv ≫ g ≫ t.inv) hc
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using h
  induction x using TensorProduct.inductionOn with
  | tmul r chi =>
    change r ⊗ₜ[ℤ] (f ≫ t.inv ≫ chi) = r ⊗ₜ[ℤ] (s.inv ≫ f ≫ chi)
    rw [← Category.assoc, ← Category.assoc, hi]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Mono (CommGroupScheme.groupHom f).hom.hom.left]

theorem characterRestrictionOrthogonalLift_equivariant (s : A ≅ A) (t : T ≅ T)
    (hc : f ≫ t.hom = s.hom ≫ f)
    (hB : ∀ x y, B (RealTorusSpace.characterRealAut t x)
      (RealTorusSpace.characterRealAut t y) = B x y) (x : RealTorusSpace.Vstar A) :
    RealTorusSpace.characterRealAut t (characterRestrictionOrthogonalLift hA hT f B hs hp x) =
      characterRestrictionOrthogonalLift hA hT f B hs hp (RealTorusSpace.characterRealAut s x) := by
  let _ := hT.finite_realCharacterSpace
  exact orthogonalLift_equivariant B hs hp _ _
    (RealTorusSpace.characterRealAut t) (RealTorusSpace.characterRealAut s)
    (restrict_characterRealAut f s t hc) hB x

theorem inducedCharacterForm_invariant (s : A ≅ A) (t : T ≅ T)
    (hc : f ≫ t.hom = s.hom ≫ f)
    (hB : ∀ x y, B (RealTorusSpace.characterRealAut t x)
      (RealTorusSpace.characterRealAut t y) = B x y) (x y : RealTorusSpace.Vstar A) :
    inducedCharacterForm hA hT f B hs hp (RealTorusSpace.characterRealAut s x)
      (RealTorusSpace.characterRealAut s y) = inducedCharacterForm hA hT f B hs hp x y := by
  let _ := hT.finite_realCharacterSpace
  exact quotientForm_invariant B hs hp _ _
    (RealTorusSpace.characterRealAut t) (RealTorusSpace.characterRealAut s)
    (restrict_characterRealAut f s t hc) hB x y

section AmbientWeyl

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]

private theorem ambientForm_symm :
    (RealTorusSpace.relativeWeylInvariantForm i hT).IsSymm :=
  ⟨RealTorusSpace.relativeWeylInvariantForm_symm i hT⟩

/-- A local form constructed using the single actual ambient relative-Weyl form. -/
def weylInducedCharacterForm : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A) :=
  inducedCharacterForm hA hT f (RealTorusSpace.relativeWeylInvariantForm i hT)
    (ambientForm_symm hT i) (fun _ hx => RealTorusSpace.relativeWeylInvariantForm_pos i hT hx)

/-- Its corresponding lift into the full ambient real character space. -/
def weylCharacterRestrictionLift :
    RealTorusSpace.Vstar A →ₗ[ℝ] RealTorusSpace.Vstar T :=
  characterRestrictionOrthogonalLift hA hT f (RealTorusSpace.relativeWeylInvariantForm i hT)
    (ambientForm_symm hT i) (fun _ hx => RealTorusSpace.relativeWeylInvariantForm_pos i hT hx)

theorem weylInducedCharacterForm_symm :
    (weylInducedCharacterForm hA hT f i).IsSymm :=
  inducedCharacterForm_symm hA hT f _ _ _

theorem weylInducedCharacterForm_pos {x : RealTorusSpace.Vstar A} (hx : x ≠ 0) :
    0 < weylInducedCharacterForm hA hT f i x x :=
  inducedCharacterForm_pos hA hT f _ _ _ hx

theorem weylInducedCharacterForm_compatible :
    CompatibleCharacterForms f (weylInducedCharacterForm hA hT f i)
      (RealTorusSpace.relativeWeylInvariantForm i hT)
      (weylCharacterRestrictionLift hA hT f i) :=
  inducedCharacterForm_compatible hA hT f _ _ _

/-- A normalizer point preserving the actual subtorus inclusion acts by
isometries of the induced local form. -/
theorem weylInducedCharacterForm_normalizer_invariant
    (n : normalizerPoints i) (s : A ≅ A)
    (hc : f ≫ (normalizingAut i n).hom = s.hom ≫ f)
    (x y : RealTorusSpace.Vstar A) :
    weylInducedCharacterForm hA hT f i (RealTorusSpace.characterRealAut s x)
      (RealTorusSpace.characterRealAut s y) = weylInducedCharacterForm hA hT f i x y := by
  apply inducedCharacterForm_invariant hA hT f _ _ _ s (normalizingAut i n) hc
  intro v z
  exact RealTorusSpace.relativeWeylInvariantForm_invariant i hT (QuotientGroup.mk n) v z

end AmbientWeyl

end Langlands.Plancherel

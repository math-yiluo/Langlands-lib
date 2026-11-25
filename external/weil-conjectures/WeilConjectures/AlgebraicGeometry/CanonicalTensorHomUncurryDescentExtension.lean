/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private def inputTransport {C : Type*} [Category* C] (H : Cᵒᵖ × C ⥤ C)
    {K K' L L' M M' : C} (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
    (f : K ⟶ H.obj (op L, M)) : K' ⟶ H.obj (op L', M') :=
  a.hom ≫ f ≫ H.map (b.hom.op, c.hom)

private def outputTransport {C : Type*} [Category* C] [MonoidalCategory C]
    {K K' L L' M M' : C} (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
    (g : K ⊗ L ⟶ M) : K' ⊗ L' ⟶ M' := (a.hom ⊗ₘ b.hom) ≫ g ≫ c.hom

private theorem inputTransport_comp {C : Type*} [Category* C] (H : Cᵒᵖ × C ⥤ C)
    {K K' K'' L L' L'' M M' M'' : C}
    (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
    (a' : K'' ≅ K') (b' : L'' ≅ L') (c' : M' ≅ M'') (f) :
    inputTransport H a' b' c' (inputTransport H a b c f) =
      inputTransport H (a' ≪≫ a) (b' ≪≫ b) (c ≪≫ c') f := by
  simp only [inputTransport, Iso.trans_hom, op_comp, Category.assoc]
  rw [← Functor.map_comp]
  rfl

private theorem outputTransport_comp {C : Type*} [Category* C] [MonoidalCategory C]
    {K K' K'' L L' L'' M M' M'' : C}
    (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
    (a' : K'' ≅ K') (b' : L'' ≅ L') (c' : M' ≅ M'') (g) :
    outputTransport a' b' c' (outputTransport a b c g) =
      outputTransport (a' ≪≫ a) (b' ≪≫ b) (c ≪≫ c') g := by
  simp only [outputTransport, Iso.trans_hom, Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]

private theorem inputTransport_refl {C : Type*} [Category* C] (H : Cᵒᵖ × C ⥤ C)
    {K L M : C} (f : K ⟶ H.obj (op L, M)) :
    inputTransport H (Iso.refl K) (Iso.refl L) (Iso.refl M) f = f := by
  change 𝟙 K ≫ f ≫ H.map (𝟙 (op L, M)) = f
  simp

private theorem inputTransport_cancel {C : Type*} [Category* C] (H : Cᵒᵖ × C ⥤ C)
    {K K' L L' M M' : C} (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M') (f) :
    inputTransport H a.symm b.symm c.symm (inputTransport H a b c f) = f := by
  rw [inputTransport_comp]
  simpa using inputTransport_refl H f

private theorem outputTransport_cancel {C : Type*} [Category* C] [MonoidalCategory C]
    {K K' L L' M M' : C} (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M') (g) :
    outputTransport a.symm b.symm c.symm (outputTransport a b c g) = g := by
  rw [outputTransport_comp]
  simp [outputTransport]

-- Extend consistent generating pairs over their isomorphism orbits.
-- The complement is invariant, so zero gives compatible values there.
private theorem orbit_extension {C : Type*} [Category* C] [MonoidalCategory C]
    [Limits.HasZeroMorphisms C] (H : Cᵒᵖ × C ⥤ C) {I : Type*} (A B N : I → C)
    (F : ∀ i, A i ⟶ H.obj (op (B i), N i)) (G : ∀ i, A i ⊗ B i ⟶ N i)
    (compare : ∀ i j (a : A i ≅ A j) (b : B i ≅ B j) (c : N j ≅ N i),
      F i = inputTransport H a b c (F j) → G i = outputTransport a b c (G j)) :
    ∃ s : ∀ K L M : C, (K ⟶ H.obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ i, s (A i) (B i) (N i) (F i) = G i) ∧
      ∀ (K K' L L' M M' : C) (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M') (f),
        s K' L' M' (inputTransport H a b c f) =
          outputTransport a b c (s K L M f) := by
  classical
  let R (K L M : C) (f : K ⟶ H.obj (op L, M)) (g : K ⊗ L ⟶ M) : Prop :=
    ∃ (i : I) (a : K ≅ A i) (b : L ≅ B i) (c : N i ≅ M),
      f = inputTransport H a b c (F i) ∧ g = outputTransport a b c (G i)
  have unique K L M f g g' (hg : R K L M f g) (hg' : R K L M f g') : g = g' := by
    obtain ⟨i, a, b, c, hf, hg⟩ := hg
    obtain ⟨j, a', b', c', hf', hg'⟩ := hg'
    have hF : F i = inputTransport H (a.symm ≪≫ a') (b.symm ≪≫ b')
        (c' ≪≫ c.symm) (F j) := by
      rw [← inputTransport_comp]
      rw [← hf', hf, inputTransport_cancel]
    have hG := compare i j _ _ _ hF
    rw [hg, hg']
    apply_fun outputTransport a.symm b.symm c.symm
    · rw [outputTransport_cancel, outputTransport_comp]
      exact hG
    · intro x y h
      have := congrArg (outputTransport a b c) h
      have hx := outputTransport_cancel a.symm b.symm c.symm x
      have hy := outputTransport_cancel a.symm b.symm c.symm y
      exact hx.symm.trans (this.trans hy)
  have transport K L M f g (hg : R K L M f g)
      K' L' M' (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M') :
      R K' L' M' (inputTransport H a b c f) (outputTransport a b c g) := by
    obtain ⟨i, ai, bi, ci, hf, hg⟩ := hg
    exact ⟨i, a ≪≫ ai, b ≪≫ bi, ci ≪≫ c,
      by rw [hf, inputTransport_comp], by rw [hg, outputTransport_comp]⟩
  -- The preceding argument proves that any witness determines the output uniquely.
  let s (K L M : C) (f : K ⟶ H.obj (op L, M)) : K ⊗ L ⟶ M :=
    if h : ∃ g, R K L M f g then Classical.choose h else 0
  have value K L M f g (hg : R K L M f g) : s K L M f = g := by
    dsimp only [s]
    rw [dite_eq_left ⟨g, hg⟩]
    exact unique _ _ _ _ _ _ (Classical.choose_spec ⟨g, hg⟩) hg
  refine ⟨s, ?_, ?_⟩
  · intro i
    apply value
    exact ⟨i, Iso.refl _, Iso.refl _, Iso.refl _,
      (inputTransport_refl H _).symm, by simp [outputTransport]⟩
  · intro K K' L L' M M' a b c f
    by_cases h : ∃ g, R K L M f g
    · obtain ⟨g, hg⟩ := h
      rw [value _ _ _ _ _ hg]
      exact value _ _ _ _ _ (transport _ _ _ _ _ hg _ _ _ a b c)
    · have h' : ¬ ∃ g, R K' L' M' (inputTransport H a b c f) g := by
        rintro ⟨g, hg⟩
        have hr := transport _ _ _ _ _ hg _ _ _ a.symm b.symm c.symm
        rw [inputTransport_cancel] at hr
        exact h ⟨_, hr⟩
      simp [s, h, h', outputTransport]

/-- Extend representative-normalized values to an isomorphism-compatible family.
The new family agrees with the given one only on the specified chain inputs;
the given family need not be compatible on arbitrary derived objects.
Source: Stacks Project, cohomology.tex, Tag 08DJ (functoriality on representatives),
and sites-cohomology.tex, Tags 0A90 and 0A96.
(blueprint: lem-pc-tensor-hom-uncurry-descent-extension).

Proof: Choose complex representatives of the three derived objects and K-flat
resolutions of the first two. Maps into Hom(Lc,I(M)) lift to chain maps modulo
homotopy because that Hom complex is K-injective. Evaluate t on these chain
inputs and transport the answer along the chosen representative isomorphisms.
The normalization hypothesis expresses every value used here as localized
componentwise evaluation, so it supplies homotopy invariance and compatibility
under changes of the chain lift. For changes of representatives, compute roofs
on common K-flat resolutions and K-injective targets. On each tensor summand,
the sheaf tensor-Hom adjunction and the Hom projections commute with pre- and
postcomposition. The coproduct universal property gives the comparison identity
for evaluation. Localize it, use the naturality of the tensor model map, Hom
resolution comparison and resolution augmentation, and cancel the invertible
quasi-isomorphisms. This proves independence of representatives and the asserted
transport identity for arbitrary derived isomorphisms. If the input already has
the form in the agreement clause, use its given K-flat P. Resolve its possibly
non-K-flat L; both P tensor - and Hom(-,I(M)) invert this resolution and evaluation
commutes with it. Cancellation and ht give precisely agreement with t on that
input. The construction does not retain arbitrary values of t elsewhere. Identity
isomorphisms, zero inputs and zero complexes satisfy the same comparison; no
boundedness or naturality of the given t outside its normalized inputs is used. -/
theorem exists_tensorHomUncurry_descent_extension (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M) :
    letI := schemeDerivedTensorMonoidal X
    ∃ s : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          s (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv)) ∧
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      s K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ s K L M f ≫ c.hom := by
  classical
  let := schemeDerivedTensorMonoidal X
  let I := Σ P : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    Σ L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    Σ M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
      {φ : P ⟶ homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M) // P.IsKFlatTensor}
  let A (i : I) := DerivedCategory.Q.obj i.1
  let B (i : I) := DerivedCategory.Q.obj i.2.1
  let N (i : I) := DerivedCategory.Q.obj i.2.2.1
  let F (i : I) := DerivedCategory.Q.map i.2.2.2.val ≫
    (schemeDerivedInternalHomResolutionIso X i.2.1 i.2.2.1).inv
  let G (i : I) := pullbackTensorModelMap X i.1 i.2.1 ≫
    DerivedCategory.Q.map (schemeTensorHomUncurry X i.1 i.2.1 i.2.2.1 i.2.2.2.val) ≫
      schemeHomResolutionInverse X i.2.2.1
  obtain ⟨s, hs, hn⟩ := orbit_extension
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf) A B N F G (by
      intro i j a b c h
      have hc := tensorHomUncurry_normalized_comparison X
        i.1 i.2.1 i.2.2.1 j.1 j.2.1 j.2.2.1 i.2.2.2.property j.2.2.2.property
        i.2.2.2.val j.2.2.2.val a b c.symm
        (by simpa only [F, A, B, N, inputTransport, Iso.symm_inv, Category.assoc] using h)
      simpa only [G, A, B, N, outputTransport, Iso.symm_inv, Category.assoc] using hc)
  refine ⟨s, ?_, hn⟩
  intro P L M hP φ
  exact (hs ⟨P, L, M, φ, hP⟩).trans (ht P L M hP φ).symm

end AlgebraicGeometry

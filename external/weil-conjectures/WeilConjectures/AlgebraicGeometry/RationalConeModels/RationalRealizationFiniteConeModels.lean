/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor

/-! # Finite integral cone models for rational realization

The finite lists below use only zero, the supplied integral quotient models, shifts,
and distinguished cones. No closure under retracts is included. Full faithfulness and
filtration models are assumptions throughout the essential-surjectivity construction.

## References

* Bhatt--Scholze, Proposition 6.8.14(2), pp. 61--62, expanded using Lemma 6.8.13 and Stacks Tags
  0145, 014A, 0152, 08J5
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject TensorProduct
namespace AlgebraicGeometry.Scheme.RationalConeModels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The existing compatible completed integral category, with unchanged morphisms. -/
abbrev Integral := PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)

/-- The existing continuous rational module category, in the coefficient universe of the site. -/
abbrev Modules := pbcModules X (rationalCoefficientSheaf l X E)

/-- The existing ambient derived category of rational module sheaves. -/
abbrev Ambient := DerivedCategory (Modules l E X)

/-- The prescribed realization on integral objects and arrows, through the raw Q. -/
abbrev realize (s : RationalModuleRealization l E X) :=
  pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙ s.J

/-- The given integer-shift comparison of J. -/
instance realizationShift (s : RationalModuleRealization l E X) : s.J.CommShift ℤ := s.shift

/-- A finite integral construction. Every entry is zero, a supplied generator up to shift
and isomorphism, or a shifted distinguished cone between strictly preceding entries. -/
def FiniteConstruction (G : Integral l E X → Prop) (K : Integral l E X) : Prop :=
  ∃ (n : ℕ) (W : Fin (n + 1) → Integral l E X), W (Fin.last n) = K ∧
    ∀ r : Fin (n + 1), IsZero (W r).obj ∨
      (∃ (L : Integral l E X) (j : ℤ), G L ∧ Nonempty ((W r).obj ≅ L.obj⟦j⟧)) ∨
      (∃ (i j : Fin (n + 1)), i < r ∧ j < r ∧
        ∃ (k : ℤ) (f : (W i).obj ⟶ (W j).obj)
          (g : (W j).obj ⟶ (W r).obj⟦k⟧)
          (h : (W r).obj⟦k⟧ ⟶ (W i).obj⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang (PbcCompletedDerived X (pbcIntegralDatum l E)))

/-- A supplied finite sheaf filtration together with its integral degree-zero quotient models. -/
structure Filtration (s : RationalModuleRealization l E X) (F : Modules l E X) where
  /-- Length, including zero. -/
  length : ℕ
  /-- Its module sheaves. -/
  H : Fin (length + 1) → Modules l E X
  /-- Inclusions into F. -/
  inclusion : ∀ k, H k ⟶ F
  /-- Consecutive inclusion maps. -/
  step : ∀ k : Fin length, H k.castSucc ⟶ H k.succ
  /-- Every term is a subobject. -/
  mono : ∀ k, Mono (inclusion k)
  /-- The initial term is zero. -/
  start : IsZero (H 0)
  /-- The final subobject is F. -/
  finish : IsIso (inclusion (Fin.last length))
  /-- The consecutive maps preserve the inclusions. -/
  commutes : ∀ k, step k ≫ inclusion k.succ = inclusion k.castSucc
  /-- Successive steps are monomorphisms. -/
  step_mono : ∀ k, Mono (step k)
  /-- The supplied integral quotient objects, including their compatible etale origins. -/
  model : Fin length → Integral l E X
  /-- Each is placed in degree zero integrally. -/
  degreeZero : ∀ k, ∃ M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)),
    Nonempty ((model k).obj ≅ (DerivedCategory.singleFunctor _ 0).obj M)
  /-- The supplied rational quotient identifications. -/
  quotient : ∀ k, (realize l E X s).obj (model k) ≅
    (DerivedCategory.singleFunctor (Modules l E X) 0).obj (cokernel (step k))

private theorem fraction_tensor {R : Type*} [CommRing R] (p : R)
    {M : Type*} [AddCommGroup M] [Module R M]
    (z : Localization.Away p ⊗[R] M) :
    ∃ (n : ℕ) (f : M),
      (algebraMap R (Localization.Away p) p ^ n) • z = 1 ⊗ₜ[R] f := by
  obtain ⟨⟨f, ⟨_, n, rfl⟩⟩, hf⟩ :=
    IsLocalizedModule.surj (Submonoid.powers p)
      (TensorProduct.mk R (Localization.Away p) M 1) z
  refine ⟨n, f, ?_⟩
  change (p ^ n) • z = _ at hf
  rw [← algebraMap_smul (Localization.Away p) (p ^ n) z, map_pow] at hf
  exact hf

private theorem fraction_category {R : Type*} [CommRing R]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] (p : R) (K L : C)
    (α : (ScalarLocalization.localization R C p).obj K ⟶
      (ScalarLocalization.localization R C p).obj L) :
    ∃ (n : ℕ) (f : K ⟶ L),
      (algebraMap R (Localization.Away p) p ^ n) • α =
        (ScalarLocalization.localization R C p).map f := by
  exact fraction_tensor p α

private theorem scalar_iso {R : Type*} [CommRing R]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] (p : R) (K : C) (n : ℕ) :
    IsIso ((ScalarLocalization.localization R C p).map (p ^ n • 𝟙 K)) := by
  let Q := ScalarLocalization.localization R C p
  have : IsScalarTower R (Localization.Away p) (Q.obj K ⟶ Q.obj K) := by
    change IsScalarTower R (Localization.Away p) (Localization.Away p ⊗[R] (K ⟶ K))
    infer_instance
  have hu := IsLocalization.map_units (Localization.Away p)
    (⟨p ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers p)
  obtain ⟨v, hv⟩ := hu
  rw [Q.map_smul, Q.map_id, ← algebraMap_smul (Localization.Away p), ← hv]
  exact ⟨⟨(↑(v⁻¹) : Localization.Away p) • 𝟙 _, by
    simp [Q, Linear.comp_smul, smul_smul], by
    simp [Q, Linear.comp_smul, smul_smul]⟩⟩

private theorem scalar_comp {R : Type*} [CommRing R]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] (p : R) (K L : C)
    (α : (ScalarLocalization.localization R C p).obj K ⟶
      (ScalarLocalization.localization R C p).obj L) (n : ℕ) (f : K ⟶ L)
    (hf : (algebraMap R (Localization.Away p) p ^ n) • α =
      (ScalarLocalization.localization R C p).map f) :
    α ≫ (ScalarLocalization.localization R C p).map (p ^ n • 𝟙 L) =
      (ScalarLocalization.localization R C p).map f := by
  have : IsScalarTower R (Localization.Away p)
      ((ScalarLocalization.localization R C p).obj K ⟶
        (ScalarLocalization.localization R C p).obj L) := by
    change IsScalarTower R (Localization.Away p) (Localization.Away p ⊗[R] (K ⟶ L))
    infer_instance
  rw [Functor.map_smul, (ScalarLocalization.localization R C p).map_id L,
    Linear.comp_smul, Category.comp_id,
    ← algebraMap_smul (Localization.Away p), map_pow]
  exact hf

private theorem coefficient_map (a : PbcIntegralRing l E) :
    pbcRationalCoefficientEquiv l E
      (algebraMap _ (Localization.Away (pbcUniformizer l E)) a) = a.down.val := by
  dsimp [pbcRationalCoefficientEquiv]
  rw [IsLocalization.ringEquivOfRingEquiv_eq]
  exact ((Padic.coefficientExtension_localization_uniformizer.{u, u} l E).2.choose
    ).commutes a.down

private theorem realize_exact (s : RationalModuleRealization l E X) :
    (realize l E X s).IsTriangulated := by
  have := s.triangulated
  have : (pbcRationalization X (pbcIntegralDatum l E)
      (pbcUniformizer l E)).IsTriangulated :=
    ((pbcRationalTriangulationData l E X Fact.out Fact.out).choose_spec.choose_spec.2
      ).choose_spec.choose_spec.2.choose_spec.2.1
  dsimp [realize]
  infer_instance

/-- The unique lifted extension arrow has an integral fraction representative. The
integral cone and its negative shift realize the middle vertex. The triangle morphism
records the rescaling square explicitly; only the lifted arrow is unique. -/
theorem extension_cone (s : RationalModuleRealization l E X)
    (_full : s.J.Full) (_faithful : s.J.Faithful)
    (K₁ K₂ : Integral l E X) (C : Ambient l E X)
    (i : (realize l E X s).obj K₁ ⟶ C)
    (p : C ⟶ (realize l E X s).obj K₂)
    (δ : (realize l E X s).obj K₂ ⟶ ((realize l E X s).obj K₁)⟦(1 : ℤ)⟧)
    (_dist : Triangle.mk i p δ ∈ distTriang (Ambient l E X)) :
    ∃! α : (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K₂ ⟶
        (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
          (K₁⟦(1 : ℤ)⟧),
      s.J.map α ≫ ((realize l E X s).commShiftIso (1 : ℤ)).hom.app K₁ = δ ∧
      ∃ (n : ℕ) (f : K₂ ⟶ K₁⟦(1 : ℤ)⟧),
        α = ((pbcRationalCoefficientEquiv l E).symm
          (((pbcUniformizer l E).down.val ^ n)⁻¹)) •
            (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f ∧
        ∃ (D K : Integral l E X) (g : K₁⟦(1 : ℤ)⟧ ⟶ D)
          (h : D ⟶ K₂⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang (Integral l E X) ∧
          Nonempty (K.obj ≅ D.obj⟦(-1 : ℤ)⟧) ∧
          Nonempty ((realize l E X s).obj K ≅ C) ∧
          ∃ (φ : (Triangle.mk i p δ).rotate.rotate ⟶
              (realize l E X s).mapTriangle.obj (Triangle.mk f g h)),
            φ.hom₁ = 𝟙 _ ∧
            φ.hom₂ =
              ((realize l E X s).commShiftIso (1 : ℤ)).inv.app K₁ ≫
                (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
                  s.J).map (pbcUniformizer l E ^ n • 𝟙 (K₁⟦(1 : ℤ)⟧)) ∧
            IsIso φ.hom₁ ∧ IsIso φ.hom₂ ∧ IsIso φ.hom₃ := by
  classical
  have := _full
  have := _faithful
  have := s.additive
  have := s.triangulated
  have := realize_exact l E X s
  let R := realize l E X s
  let Q := pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)
  let e := (R.commShiftIso (1 : ℤ)).app K₁
  let α := s.J.preimage (δ ≫ e.inv)
  have hα : s.J.map α ≫ e.hom = δ := by simp [α]
  obtain ⟨n, f, hf⟩ := fraction_category (pbcUniformizer l E) K₂ (K₁⟦(1 : ℤ)⟧) α
  have hs := scalar_comp (pbcUniformizer l E) K₂ (K₁⟦(1 : ℤ)⟧) α n f hf
  have hi := scalar_iso (pbcUniformizer l E) (K₁⟦(1 : ℤ)⟧) n
  have hrep : α = ((pbcRationalCoefficientEquiv l E).symm
      (((pbcUniformizer l E).down.val ^ n)⁻¹)) • Q.map f := by
    let c := (pbcRationalCoefficientEquiv l E).symm
      (((pbcUniformizer l E).down.val ^ n)⁻¹)
    have hz : (pbcUniformizer l E).down.val ≠ 0 := by
      have hu := (IsLocalization.map_units (Localization.Away (pbcUniformizer l E))
        (⟨pbcUniformizer l E, ⟨1, pow_one _⟩⟩ : Submonoid.powers (pbcUniformizer l E))
        ).map (pbcRationalCoefficientEquiv l E).toMonoidHom
      have hz := hu.ne_zero
      change pbcRationalCoefficientEquiv l E
        (algebraMap (PbcIntegralRing l E) (Localization.Away (pbcUniformizer l E))
          (pbcUniformizer l E)) ≠ 0 at hz
      simpa only [coefficient_map l E] using hz
    have hc : c * (algebraMap (PbcIntegralRing l E)
        (Localization.Away (pbcUniformizer l E)) (pbcUniformizer l E)) ^ n = 1 := by
      apply (pbcRationalCoefficientEquiv l E).injective
      simp [c, coefficient_map, hz]
    calc
      α = (1 : Localization.Away (pbcUniformizer l E)) • α := (one_smul _ _).symm
      _ = (c * (algebraMap (PbcIntegralRing l E)
          (Localization.Away (pbcUniformizer l E)) (pbcUniformizer l E)) ^ n) • α := by
            rw [hc]
      _ = c • Q.map f := by rw [mul_smul, hf]
  obtain ⟨D, g, h, hd⟩ := distinguished_cocone_triangle f
  let K := D⟦(-1 : ℤ)⟧
  let T := Triangle.mk i p δ
  let U := R.mapTriangle.obj (Triangle.mk f g h)
  have hu : U ∈ distTriang (Ambient l E X) := R.map_distinguished _ hd
  let b := e.inv ≫ R.map (pbcUniformizer l E ^ n • 𝟙 (K₁⟦(1 : ℤ)⟧))
  have hb : IsIso b := by
    have : IsIso (R.map (pbcUniformizer l E ^ n • 𝟙 (K₁⟦(1 : ℤ)⟧))) :=
      s.J.map_isIso _
    dsimp [b]
    infer_instance
  have hsquare : T.rotate.rotate.mor₁ ≫ b = (𝟙 _) ≫ U.mor₁ := by
    change δ ≫ (e.inv ≫ s.J.map (Q.map _)) = (𝟙 _) ≫ s.J.map (Q.map f)
    have hα' : s.J.map α = δ ≫ e.inv := by simp [α]
    rw [Category.id_comp, ← Category.assoc, ← hα', ← s.J.map_comp, hs]
  let φ := completeDistinguishedTriangleMorphism T.rotate.rotate U
    (rot_of_distTriang _ (rot_of_distTriang _ _dist)) hu (𝟙 _) b hsquare
  have hφ₁ : IsIso φ.hom₁ := by change IsIso (𝟙 _); infer_instance
  have hφ₂ : IsIso φ.hom₂ := hb
  have hφ₃ : IsIso φ.hom₃ := isIso₃_of_isIso₁₂ φ
    (rot_of_distTriang _ (rot_of_distTriang _ _dist)) hu hφ₁ hφ₂
  have eK : Nonempty (R.obj K ≅ C) := ⟨
    (R.commShiftIso (-1 : ℤ)).app D ≪≫
    (shiftFunctor (Ambient l E X) (-1 : ℤ)).mapIso (asIso φ.hom₃).symm ≪≫
    (shiftFunctorCompIsoId (Ambient l E X) (1 : ℤ) (-1 : ℤ) (by norm_num)).app C⟩
  refine ⟨α, ⟨hα, n, f, hrep, D, K, g, h, hd, ?_, eK,
    φ, rfl, rfl, hφ₁, hφ₂, hφ₃⟩, ?_⟩
  · exact ⟨((ObjectProperty.ι (PbcIsBoundedConstructibleComplete X
      (pbcIntegralDatum l E))).commShiftIso (-1 : ℤ)).app D⟩
  · intro β hβ
    apply s.J.map_injective
    apply (cancel_mono e.hom).1
    exact hβ.1.trans hα.symm

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem finite_construction_step
    (G : Integral l E X → Prop) (A B K : Integral l E X)
    (hA : FiniteConstruction l E X G A) (hB : FiniteConstruction l E X G B)
    (hK : ∃ (k : ℤ) (f : A.obj ⟶ B.obj) (g : B.obj ⟶ K.obj⟦k⟧)
      (h : K.obj⟦k⟧ ⟶ A.obj⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (PbcCompletedDerived X (pbcIntegralDatum l E))) :
    FiniteConstruction l E X G K := by
  let Leaf (L : Integral l E X) := IsZero L.obj ∨
    ∃ (M : Integral l E X) (j : ℤ), G M ∧ Nonempty (L.obj ≅ M.obj⟦j⟧)
  let Rel (L M N : Integral l E X) :=
    ∃ (k : ℤ) (f : L.obj ⟶ M.obj) (g : M.obj ⟶ N.obj⟦k⟧)
      (h : N.obj⟦k⟧ ⟶ L.obj⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (PbcCompletedDerived X (pbcIntegralDatum l E))
  obtain ⟨m, W, hw, hv⟩ := hA
  obtain ⟨n, V, hh, hu⟩ := hB
  have hv' : ∀ r, Leaf (W r) ∨ ∃ i j, i < r ∧ j < r ∧ Rel (W i) (W j) (W r) := by
    intro r; simpa only [Leaf, Rel, or_assoc] using hv r
  have hu' : ∀ r, Leaf (V r) ∨ ∃ i j, i < r ∧ j < r ∧ Rel (V i) (V j) (V r) := by
    intro r; simpa only [Leaf, Rel, or_assoc] using hu r
  have happ : ∀ r, Leaf (Fin.append W V r) ∨ ∃ i j, i < r ∧ j < r ∧
      Rel (Fin.append W V i) (Fin.append W V j) (Fin.append W V r) := by
    intro r
    refine Fin.addCases (fun r ↦ ?_) (fun r ↦ ?_) r
    · rcases hv' r with h | ⟨i, j, hi, hj, h⟩
      · exact Or.inl (by simpa using h)
      · right
        exact ⟨i.castAdd (n + 1), j.castAdd (n + 1), hi, hj, by simpa using h⟩
    · rcases hu' r with h | ⟨i, j, hi, hj, h⟩
      · exact Or.inl (by simpa using h)
      · right
        exact ⟨i.natAdd (m + 1), j.natAdd (m + 1), by simpa using hi,
          by simpa using hj, by simpa using h⟩
  refine ⟨(m + 1) + (n + 1), Fin.snoc (Fin.append W V) K, by simp, ?_⟩
  intro r
  let Z : Fin ((m + 1) + (n + 1) + 1) → Integral l E X :=
    Fin.snoc (Fin.append W V) K
  rw [← or_assoc]
  change Leaf (Z r) ∨
    ∃ (i j : Fin ((m + 1) + (n + 1) + 1)), i < r ∧ j < r ∧ Rel (Z i) (Z j) (Z r)
  dsimp only [Z]
  refine Fin.lastCases ?_ (fun r ↦ ?_) r
  · right
    refine ⟨((Fin.last m).castAdd (n + 1)).castSucc,
      ((Fin.last n).natAdd (m + 1)).castSucc,
      Fin.castSucc_lt_last _, Fin.castSucc_lt_last _, ?_⟩
    simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left,
      Fin.append_right, hw, hh] using hK
  · rcases happ r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa only [Fin.snoc_castSucc] using h)
    · exact Or.inr ⟨i.castSucc, j.castSucc, hi, hj,
        by simpa only [Fin.snoc_castSucc] using h⟩

private theorem finite_construction_zero (G : Integral l E X → Prop) :
    FiniteConstruction l E X G 0 := by
  refine ⟨0, fun _ ↦ 0, rfl, fun _ ↦ Or.inl ?_⟩
  exact (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X
    (pbcIntegralDatum l E))).map_isZero (isZero_zero (Integral l E X))

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem finite_construction_generator
    (G : Integral l E X → Prop) (K : Integral l E X) (hK : G K) :
    FiniteConstruction l E X G K := by
  refine ⟨0, fun _ ↦ K, rfl, fun _ ↦ Or.inr (Or.inl ⟨K, 0, hK, ?_⟩)⟩
  exact ⟨((shiftFunctorZero (PbcCompletedDerived X (pbcIntegralDatum l E)) ℤ).app
    K.obj).symm⟩

private theorem finite_construction_shift_one
    (G : Integral l E X → Prop) (K : Integral l E X)
    (hK : FiniteConstruction l E X G K) :
    FiniteConstruction l E X G (K⟦(1 : ℤ)⟧) := by
  let I := ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
  let z : I.obj 0 ≅ 0 := I.mapZeroObject
  let e : (K⟦(1 : ℤ)⟧).obj⟦(0 : ℤ)⟧ ≅ K.obj⟦(1 : ℤ)⟧ :=
    (shiftFunctorZero _ ℤ).app _ ≪≫ (I.commShiftIso (1 : ℤ)).app K
  apply finite_construction_step l E X G K 0 _ hK (finite_construction_zero l E X G)
  refine ⟨0, 0, 0, e.hom, ?_⟩
  apply isomorphic_distinguished _ (contractible_distinguished₂ K.obj)
  exact Triangle.isoMk _ _ (Iso.refl _) z e
    (by simp) (by simp) (by
      simp only [Triangle.mk_mor₃, Iso.refl_hom,
        (shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum l E)) (1 : ℤ)).map_id]
      exact (Category.comp_id _).trans (Category.comp_id _).symm)

private theorem finite_construction_cone
    (G : Integral l E X → Prop) (A B D K : Integral l E X)
    (hA : FiniteConstruction l E X G A) (hB : FiniteConstruction l E X G B)
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ A⟦(1 : ℤ)⟧)
    (hd : Triangle.mk f g h ∈ distTriang (Integral l E X))
    (e : K.obj ≅ D.obj⟦(-1 : ℤ)⟧) : FiniteConstruction l E X G K := by
  let I := ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
  let eD : K.obj⟦(1 : ℤ)⟧ ≅ D.obj :=
    (shiftFunctor _ (1 : ℤ)).mapIso e ≪≫
      (shiftFunctorCompIsoId _ (-1 : ℤ) (1 : ℤ) (by norm_num)).app D.obj
  let T := I.mapTriangle.obj (Triangle.mk f g h)
  apply finite_construction_step l E X G A B K hA hB
  refine ⟨1, T.mor₁, T.mor₂ ≫ eD.inv, eD.hom ≫ T.mor₃, ?_⟩
  apply isomorphic_distinguished _ (I.map_distinguished _ hd)
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) eD
    (by simp [T]) (by simp [T]) (by simp [T])

private theorem finite_path {A : Type*} (n : ℕ)
    (P : Fin (n + 1) → A → Prop) (R : Fin n → A → A → Prop)
    (h0 : ∃ a, P 0 a)
    (hs : ∀ (i : Fin n) (a : A), P i.castSucc a → ∃ b, P i.succ b ∧ R i a b) :
    ∃ W : Fin (n + 1) → A, (∀ i, P i (W i)) ∧
      ∀ i : Fin n, R i (W i.castSucc) (W i.succ) := by
  induction n with
  | zero =>
    obtain ⟨a, ha⟩ := h0
    exact ⟨fun _ ↦ a, fun i ↦ by simpa [Fin.eq_zero i] using ha, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨W, hp, hr⟩ := ih (fun i ↦ P i.castSucc) (fun i ↦ R i.castSucc)
      h0 (fun i a h ↦ hs i.castSucc a h)
    obtain ⟨b, hb, hs'⟩ := hs (Fin.last n) (W (Fin.last n)) (hp _)
    refine ⟨Fin.snoc W b, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simpa using hb
      · simpa using hp i
    · intro i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simpa using hs'
      · rw [Fin.succ_castSucc]
        simpa only [Fin.snoc_castSucc] using hr i

private theorem filtration_step (s : RationalModuleRealization l E X)
    (_full : s.J.Full) (_faithful : s.J.Faithful)
    (F : Modules l E X) (t : Filtration l E X s F) (j : Fin t.length)
    (A : Integral l E X)
    (hA : FiniteConstruction l E X (fun L ↦ ∃ k, L = t.model k) A)
    (eA : (realize l E X s).obj A ≅
      (DerivedCategory.singleFunctor (Modules l E X) 0).obj (t.H j.castSucc)) :
    ∃ B : Integral l E X,
      FiniteConstruction l E X (fun L ↦ ∃ k, L = t.model k) B ∧
      Nonempty ((realize l E X s).obj B ≅
        (DerivedCategory.singleFunctor (Modules l E X) 0).obj (t.H j.succ)) ∧
      ∃ (f : t.model j ⟶ A⟦(1 : ℤ)⟧) (D : Integral l E X)
        (g : A⟦(1 : ℤ)⟧ ⟶ D) (h : D ⟶ (t.model j)⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang (Integral l E X) ∧
        Nonempty (B.obj ≅ D.obj⟦(-1 : ℤ)⟧) := by
  have := t.step_mono j
  let S := ShortComplex.mk (t.step j) (cokernel.π (t.step j)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  let T := hS.singleTriangle
  let eQ := t.quotient j
  let T' := Triangle.mk (eA.hom ≫ T.mor₁) (T.mor₂ ≫ eQ.inv)
    (eQ.hom ≫ T.mor₃ ≫ eA.inv⟦(1 : ℤ)⟧')
  have hd : T' ∈ distTriang (Ambient l E X) := by
    apply isomorphic_distinguished _ hS.singleTriangle_distinguished
    exact Triangle.isoMk _ _ eA (Iso.refl _) eQ
      (by simp [T', T]) (by simp [T', T]) (by simp [T', T, ← Functor.map_comp])
  obtain ⟨α, hα, _⟩ := extension_cone l E X s _full _faithful A (t.model j)
    ((DerivedCategory.singleFunctor (Modules l E X) 0).obj (t.H j.succ))
    T'.mor₁ T'.mor₂ T'.mor₃ hd
  obtain ⟨_, n, f, _, D, B, g, h, hd', ⟨eB⟩, he, _⟩ := hα
  refine ⟨B, ?_, he, f, D, g, h, hd', ⟨eB⟩⟩
  exact finite_construction_cone l E X _ (t.model j) (A⟦(1 : ℤ)⟧) D B
    (finite_construction_generator l E X _ _ ⟨j, rfl⟩)
    (finite_construction_shift_one l E X _ A hA) f g h hd' eB

/-- Every supplied finite filtration is modeled by a finite integral construction using
exactly its supplied quotient models. -/
theorem filtration_model (s : RationalModuleRealization l E X)
    (_full : s.J.Full) (_faithful : s.J.Faithful)
    (F : Modules l E X) (t : Filtration l E X s F) :
    ∃ K : Integral l E X,
      FiniteConstruction l E X (fun L ↦ ∃ k, L = t.model k) K ∧
      Nonempty ((realize l E X s).obj K ≅
        (DerivedCategory.singleFunctor (Modules l E X) 0).obj F) ∧
      ∃ W : Fin (t.length + 1) → Integral l E X,
        IsZero (W 0).obj ∧
        (∀ j, Nonempty ((realize l E X s).obj (W j) ≅
          (DerivedCategory.singleFunctor (Modules l E X) 0).obj (t.H j))) ∧
        Nonempty ((W (Fin.last t.length)).obj ≅ K.obj) ∧
        (∀ j, FiniteConstruction l E X (fun L ↦ ∃ k, L = t.model k) (W j)) ∧
        ∀ j : Fin t.length,
          ∃ (f : t.model j ⟶ (W j.castSucc)⟦(1 : ℤ)⟧) (D : Integral l E X)
            (g : (W j.castSucc)⟦(1 : ℤ)⟧ ⟶ D)
            (h : D ⟶ (t.model j)⟦(1 : ℤ)⟧),
            Triangle.mk f g h ∈ distTriang (Integral l E X) ∧
            Nonempty ((W j.succ).obj ≅ D.obj⟦(-1 : ℤ)⟧) := by
  classical
  have := s.additive
  have : (realize l E X s).Additive := by dsimp [realize]; infer_instance
  have : (realize l E X s).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let G : Integral l E X → Prop := fun L ↦ ∃ k, L = t.model k
  let P (j : Fin (t.length + 1)) (K : Integral l E X) : Prop :=
    FiniteConstruction l E X G K ∧
    Nonempty ((realize l E X s).obj K ≅
      (DerivedCategory.singleFunctor (Modules l E X) 0).obj (t.H j)) ∧
    (j = 0 → IsZero K.obj)
  let R (j : Fin t.length) (A B : Integral l E X) : Prop :=
    ∃ (f : t.model j ⟶ A⟦(1 : ℤ)⟧) (D : Integral l E X)
      (g : A⟦(1 : ℤ)⟧ ⟶ D) (h : D ⟶ (t.model j)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (Integral l E X) ∧
      Nonempty (B.obj ≅ D.obj⟦(-1 : ℤ)⟧)
  have h0 : ∃ K, P 0 K := by
    refine ⟨0, finite_construction_zero l E X G, ?_, ?_⟩
    · exact ⟨((realize l E X s).map_isZero (isZero_zero _)).iso
        ((DerivedCategory.singleFunctor (Modules l E X) 0).map_isZero t.start)⟩
    · intro _
      exact (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X
        (pbcIntegralDatum l E))).map_isZero (isZero_zero (Integral l E X))
  have hs : ∀ (j : Fin t.length) A, P j.castSucc A → ∃ B, P j.succ B ∧ R j A B := by
    intro j A ⟨hA, ⟨eA⟩, _⟩
    obtain ⟨B, hB, eB, hh⟩ := filtration_step l E X s _full _faithful F t j A hA eA
    refine ⟨B, ⟨hB, eB, ?_⟩, hh⟩
    intro he
    exact False.elim (Fin.succ_ne_zero j he)
  obtain ⟨W, hp, hr⟩ := finite_path t.length P R h0 hs
  have := t.finish
  refine ⟨W (Fin.last t.length), (hp _).1, ?_, W, (hp 0).2.2 rfl,
    fun j ↦ (hp j).2.1, ⟨Iso.refl _⟩, fun j ↦ (hp j).1, hr⟩
  obtain ⟨e⟩ := (hp (Fin.last t.length)).2.1
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor (Modules l E X) 0).mapIso
    (asIso (t.inclusion (Fin.last t.length)))⟩

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem finite_construction_mono
    (G H : Integral l E X → Prop) (h : ∀ K, G K → H K) (K : Integral l E X)
    (hk : FiniteConstruction l E X G K) : FiniteConstruction l E X H K := by
  obtain ⟨n, W, hw, hv⟩ := hk
  refine ⟨n, W, hw, fun r ↦ ?_⟩
  rcases hv r with hz | ⟨L, j, hL, he⟩ | hc
  · exact Or.inl hz
  · exact Or.inr (Or.inl ⟨L, j, h L hL, he⟩)
  · exact Or.inr (Or.inr hc)

private theorem finite_construction_iso
    (G : Integral l E X → Prop) (A B : Integral l E X)
    (hA : FiniteConstruction l E X G A) (e : A.obj ≅ B.obj) :
    FiniteConstruction l E X G B := by
  let I := ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
  let z : I.obj 0 ≅ 0 := I.mapZeroObject
  let eB : B.obj⟦(0 : ℤ)⟧ ≅ A.obj := (shiftFunctorZero _ ℤ).app _ ≪≫ e.symm
  apply finite_construction_step l E X G 0 A B (finite_construction_zero l E X G) hA
  refine ⟨0, 0, eB.inv, 0, ?_⟩
  apply isomorphic_distinguished _ (contractible_distinguished₁ A.obj)
  exact Triangle.isoMk _ _ z (Iso.refl _) eB (by simp) (by simp) (by simp)

private theorem finite_construction_shift
    (G : Integral l E X → Prop) (A : Integral l E X)
    (hA : FiniteConstruction l E X G A) (j : ℤ) :
    FiniteConstruction l E X G (A⟦j⟧) := by
  obtain ⟨n, W, hw, hv⟩ := hA
  let I := ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
  have term (r : Fin (n + 1)) : FiniteConstruction l E X G ((W r)⟦j⟧) := by
    induction r using WellFoundedLT.induction with
    | ind r ih =>
      rcases hv r with hz | ⟨L, k, hL, ⟨e⟩⟩ | ⟨a, b, ha, hb, k, f, g, h, hd⟩
      · apply finite_construction_iso l E X G 0 _ (finite_construction_zero l E X G)
        have hz' := (shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum l E)) j).map_isZero hz
        have hz'' : IsZero ((W r)⟦j⟧).obj :=
          hz'.of_iso ((I.commShiftIso j).app (W r))
        exact ((I.map_isZero (isZero_zero (Integral l E X))).iso hz'')
      · refine ⟨0, fun _ ↦ (W r)⟦j⟧, rfl, fun _ ↦ Or.inr (Or.inl ?_)⟩
        refine ⟨L, k + j, hL, ⟨?_⟩⟩
        exact (I.commShiftIso j).app (W r) ≪≫
          (shiftFunctor _ j).mapIso e ≪≫ (shiftFunctorAdd _ k j).symm.app L.obj
      · let T := Triangle.mk f g h
        let T' := (Triangle.shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum l E)) j).obj T
        let ea := (I.commShiftIso j).app (W a)
        let eb := (I.commShiftIso j).app (W b)
        let ec : ((W r)⟦j⟧).obj⟦k⟧ ≅ (W r).obj⟦k⟧⟦j⟧ :=
          (shiftFunctor _ k).mapIso ((I.commShiftIso j).app (W r)) ≪≫
            (shiftFunctorComm _ j k).app (W r).obj
        apply finite_construction_step l E X G ((W a)⟦j⟧) ((W b)⟦j⟧) _
          (ih a ha) (ih b hb)
        refine ⟨k, ea.hom ≫ T'.mor₁ ≫ eb.inv,
          eb.hom ≫ T'.mor₂ ≫ ec.inv, ec.hom ≫ T'.mor₃ ≫ ea.inv⟦(1 : ℤ)⟧', ?_⟩
        apply isomorphic_distinguished _ (Triangle.shift_distinguished T hd j)
        exact Triangle.isoMk _ _ ea eb ec
          (by simp [T']) (by simp [T']) (by simp [T', ← Functor.map_comp])
  simpa only [hw] using term (Fin.last n)

omit [IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
private theorem truncation_step (C : Ambient l E X) (r : ℤ) :
    ∃ (i : (DerivedCategory.TStructure.t.truncLE (r - 1)).obj C ⟶
        (DerivedCategory.TStructure.t.truncLE r).obj C)
      (p : (DerivedCategory.TStructure.t.truncLE r).obj C ⟶
        ((DerivedCategory.singleFunctor (Modules l E X) 0).obj
          ((DerivedCategory.homologyFunctor (Modules l E X) r).obj C))⟦-r⟧)
      (δ : ((DerivedCategory.singleFunctor (Modules l E X) 0).obj
          ((DerivedCategory.homologyFunctor (Modules l E X) r).obj C))⟦-r⟧ ⟶
        ((DerivedCategory.TStructure.t.truncLE (r - 1)).obj C)⟦(1 : ℤ)⟧),
      Triangle.mk i p δ ∈ distTriang (Ambient l E X) := by
  let t := DerivedCategory.TStructure.t (C := Modules l E X)
  let M := (t.truncLE r).obj C
  let T := (t.triangleLEGE (r - 1) r (by omega)).obj M
  have hd : T ∈ distTriang (Ambient l E X) :=
    t.triangleLEGE_distinguished _ _ (by omega) M
  have h₃le : T.obj₃.IsLE r := by
    change t.IsLE ((t.truncGE r).obj M) r
    infer_instance
  have h₃ge : T.obj₃.IsGE r := by
    change t.IsGE ((t.truncGE r).obj M) r
    infer_instance
  obtain ⟨Y, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ r
  have h₁le : T.obj₁.IsLE (r - 1) := by
    change t.IsLE ((t.truncLE (r - 1)).obj M) (r - 1)
    infer_instance
  have h₀ : IsZero ((DerivedCategory.homologyFunctor (Modules l E X) r).obj T.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (r - 1) _ (by omega)
  have h₁ : IsZero ((DerivedCategory.homologyFunctor (Modules l E X) (r + 1)).obj T.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (r - 1) _ (by omega)
  have hi := DerivedCategory.isIso_homologyMap_mor₂ T hd r (r + 1) rfl h₀ h₁
  have hι : IsIso ((DerivedCategory.homologyFunctor (Modules l E X) r).map
      ((t.truncLEι r).app C)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app C (r + 1) r (by omega)
  let eH : ((DerivedCategory.homologyFunctor (Modules l E X) r).obj C) ≅ Y :=
    (asIso ((DerivedCategory.homologyFunctor (Modules l E X) r).map
      ((t.truncLEι r).app C))).symm ≪≫
    asIso ((DerivedCategory.homologyFunctor (Modules l E X) r).map T.mor₂) ≪≫
    (DerivedCategory.homologyFunctor (Modules l E X) r).mapIso eY ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules l E X) r).app Y
  let e₃ := eY ≪≫
    (((DerivedCategory.singleFunctors (Modules l E X)).shiftIso (-r) r 0 (by omega)).app Y
      ).symm ≪≫
    (shiftFunctor (Ambient l E X) (-r)).mapIso
      ((DerivedCategory.singleFunctor (Modules l E X) 0).mapIso eH.symm)
  have hi₁ := t.isIso_truncLE_map_truncLEι_app (r - 1) r (by omega) C
  let e₁ := asIso ((t.truncLE (r - 1)).map ((t.truncLEι r).app C))
  refine ⟨e₁.inv ≫ T.mor₁, T.mor₂ ≫ e₃.hom,
    e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧', ?_⟩
  apply isomorphic_distinguished _ hd
  exact Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm
    (by simp) (by simp) (by simp [← Functor.map_comp])

/-- Bounded constructible cohomology is realized by the finite standard truncation tower,
using only integral models of its finitely many filtration quotients and integral cones.
The supplied interval may contain zero cohomology groups, or even be empty. -/
theorem bounded_model (s : RationalModuleRealization l E X)
    (_full : s.J.Full) (_faithful : s.J.Faithful)
    (_models : ∀ F : Modules l E X,
      (∃ t : FiniteLocallyClosedStratification X, ∀ k : Fin t.n,
        ((proEtaleModuleInverseImage (t.immersion k)
          (rationalCoefficientSheaf l X E)).obj F).IsFiniteLocallyFree) →
        Nonempty (Filtration l E X s F))
    (C : Ambient l E X) (a b : ℤ)
    (_bounded : ∀ r : ℤ, r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor (Modules l E X) r).obj C))
    (_constructible : ∀ r : ℤ, ∃ t : FiniteLocallyClosedStratification X,
      ∀ k : Fin t.n, ((proEtaleModuleInverseImage (t.immersion k)
        (rationalCoefficientSheaf l X E)).obj
          ((DerivedCategory.homologyFunctor (Modules l E X) r).obj C)).IsFiniteLocallyFree) :
    ∃ (t : ∀ r : Set.Icc a b, Filtration l E X s
        ((DerivedCategory.homologyFunctor (Modules l E X) r.val).obj C))
      (K : Integral l E X),
      FiniteConstruction l E X (fun L ↦ ∃ (r : Set.Icc a b) (k : Fin (t r).length),
        L = (t r).model k) K ∧
      Nonempty ((realize l E X s).obj K ≅ C) ∧
      ∃ (W : Fin ((b - a + 1).toNat + 1) → Integral l E X),
        IsZero (W 0).obj ∧
        (∀ j, Nonempty ((realize l E X s).obj (W j) ≅
          (DerivedCategory.TStructure.t.truncLE (a - 1 + (j.val : ℤ))).obj C)) ∧
        Nonempty ((W (Fin.last (b - a + 1).toNat)).obj ≅ K.obj) ∧
        (∀ j, FiniteConstruction l E X (fun L ↦
          ∃ (r : Set.Icc a b) (k : Fin (t r).length), L = (t r).model k) (W j)) ∧
        ∀ j : Fin (b - a + 1).toNat,
          ∃ (L D : Integral l E X)
            (f : L ⟶ (W j.castSucc)⟦(1 : ℤ)⟧)
            (g : (W j.castSucc)⟦(1 : ℤ)⟧ ⟶ D) (h : D ⟶ L⟦(1 : ℤ)⟧),
            FiniteConstruction l E X (fun M ↦
              ∃ (r : Set.Icc a b) (k : Fin (t r).length), M = (t r).model k) L ∧
            Nonempty ((realize l E X s).obj L ≅
              ((DerivedCategory.singleFunctor (Modules l E X) 0).obj
                ((DerivedCategory.homologyFunctor (Modules l E X)
                  (a + (j.val : ℤ))).obj C))⟦-(a + (j.val : ℤ))⟧) ∧
            Triangle.mk f g h ∈ distTriang (Integral l E X) ∧
            Nonempty ((W j.succ).obj ≅ D.obj⟦(-1 : ℤ)⟧) := by
  classical
  have := s.additive
  have : (realize l E X s).Additive := by dsimp [realize]; infer_instance
  have : (realize l E X s).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have hge : C.IsGE a := (DerivedCategory.isGE_iff C a).2
    (fun r hr ↦ _bounded r (Or.inl hr))
  have hle : C.IsLE b := (DerivedCategory.isLE_iff C b).2
    (fun r hr ↦ _bounded r (Or.inr hr))
  let t : ∀ r : Set.Icc a b, Filtration l E X s
      ((DerivedCategory.homologyFunctor (Modules l E X) r.val).obj C) :=
    fun r ↦ Classical.choice (_models _ (_constructible r.val))
  let G : Integral l E X → Prop := fun L ↦
    ∃ (r : Set.Icc a b) (k : Fin (t r).length), L = (t r).model k
  let N := (b - a + 1).toNat
  let P (j : Fin (N + 1)) (K : Integral l E X) : Prop :=
    FiniteConstruction l E X G K ∧
    Nonempty ((realize l E X s).obj K ≅
      (DerivedCategory.TStructure.t.truncLE (a - 1 + (j.val : ℤ))).obj C) ∧
    (j = 0 → IsZero K.obj)
  let R (j : Fin N) (A B : Integral l E X) : Prop :=
    ∃ (L D : Integral l E X) (f : L ⟶ A⟦(1 : ℤ)⟧)
      (g : A⟦(1 : ℤ)⟧ ⟶ D) (h : D ⟶ L⟦(1 : ℤ)⟧),
      FiniteConstruction l E X G L ∧
      Nonempty ((realize l E X s).obj L ≅
        ((DerivedCategory.singleFunctor (Modules l E X) 0).obj
          ((DerivedCategory.homologyFunctor (Modules l E X) (a + (j.val : ℤ))).obj C))⟦
            -(a + (j.val : ℤ))⟧) ∧
      Triangle.mk f g h ∈ distTriang (Integral l E X) ∧
      Nonempty (B.obj ≅ D.obj⟦(-1 : ℤ)⟧)
  have h0 : ∃ K, P 0 K := by
    refine ⟨0, finite_construction_zero l E X G, ?_, ?_⟩
    · have hz := DerivedCategory.TStructure.t.isZero_truncLE_obj_of_isGE
        (a - 1) a (by omega) C
      exact ⟨((realize l E X s).map_isZero (isZero_zero _)).iso (by simpa using hz)⟩
    · intro _
      exact (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X
        (pbcIntegralDatum l E))).map_isZero (isZero_zero (Integral l E X))
  have hs : ∀ (j : Fin N) A, P j.castSucc A → ∃ B, P j.succ B ∧ R j A B := by
    intro j A ⟨hA, ⟨eA⟩, _⟩
    let r : Set.Icc a b := ⟨a + (j.val : ℤ), by
      change a ≤ a + (j.val : ℤ) ∧ a + (j.val : ℤ) ≤ b
      constructor
      · exact le_add_of_nonneg_right (Int.natCast_nonneg _)
      · have hj := j.isLt
        dsimp [N] at hj
        omega⟩
    obtain ⟨L₀, hL₀, ⟨eL₀⟩, _⟩ := filtration_model l E X s _full _faithful
      ((DerivedCategory.homologyFunctor (Modules l E X) r.val).obj C) (t r)
    have hLG : FiniteConstruction l E X G L₀ :=
      finite_construction_mono l E X _ G (fun K ⟨k, hk⟩ ↦ ⟨r, k, hk⟩) L₀ hL₀
    let L := L₀⟦-r.val⟧
    have hL : FiniteConstruction l E X G L :=
      finite_construction_shift l E X G L₀ hLG (-r.val)
    let eL := ((realize l E X s).commShiftIso (-r.val)).app L₀ ≪≫
      (shiftFunctor (Ambient l E X) (-r.val)).mapIso eL₀
    obtain ⟨i, p, δ, hd⟩ := truncation_step l E X C r.val
    have heq : r.val - 1 = a - 1 + (j.val : ℤ) := by dsimp [r]; omega
    let eA' : (realize l E X s).obj A ≅
        (DerivedCategory.TStructure.t.truncLE (r.val - 1)).obj C :=
      eA ≪≫ eqToIso (by rw [heq]; rfl)
    let T := Triangle.mk (eA'.hom ≫ i) (p ≫ eL.inv)
      (eL.hom ≫ δ ≫ eA'.inv⟦(1 : ℤ)⟧')
    have hT : T ∈ distTriang (Ambient l E X) := by
      apply isomorphic_distinguished _ hd
      exact Triangle.isoMk _ _ eA' (Iso.refl _) eL
        (by simp [T]) (by simp [T]) (by simp [T, ← Functor.map_comp])
    obtain ⟨α, hα, _⟩ := extension_cone l E X s _full _faithful A L
      ((DerivedCategory.TStructure.t.truncLE r.val).obj C) T.mor₁ T.mor₂ T.mor₃ hT
    obtain ⟨_, n, f, _, D, B, g, h, hd', ⟨eB⟩, he, _⟩ := hα
    have hB := finite_construction_cone l E X G L (A⟦(1 : ℤ)⟧) D B hL
      (finite_construction_shift_one l E X G A hA) f g h hd' eB
    refine ⟨B, ⟨hB, ?_, ?_⟩, L, D, f, g, h, hL, ⟨eL⟩, hd', ⟨eB⟩⟩
    · convert he using 2
      dsimp [r]
      congr 2
      omega
    · intro hz
      exact False.elim (Fin.succ_ne_zero j hz)
  obtain ⟨W, hp, hr⟩ := finite_path N P R h0 hs
  have hlast : b ≤ a - 1 + (N : ℤ) := by dsimp [N]; omega
  have hle' : C.IsLE (a - 1 + (N : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_of_le C b _ hlast
  have hi : IsIso ((DerivedCategory.TStructure.t.truncLEι (a - 1 + (N : ℤ))).app C) :=
    inferInstance
  refine ⟨t, W (Fin.last N), (hp _).1, ?_, W, (hp 0).2.2 rfl,
    fun j ↦ (hp j).2.1, ⟨Iso.refl _⟩, fun j ↦ (hp j).1, hr⟩
  obtain ⟨e⟩ := (hp (Fin.last N)).2.1
  exact ⟨e ≪≫ asIso ((DerivedCategory.TStructure.t.truncLEι
    (a - 1 + (N : ℤ))).app C)⟩

end AlgebraicGeometry.Scheme.RationalConeModels

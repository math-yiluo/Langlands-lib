/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Double
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-!
# Dualizable objects of `D(C)` when the unit is a finite projective generator of sections

Let `C` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, so that `D(C)` carries the derived tensor product. Suppose that the unit `𝟙` of
`C` is projective and that "global sections" `Hom(𝟙, -)` are finite in the following sense:

* a morphism from `𝟙` to a coproduct factors through a finite subcoproduct
  (`CategoryTheory.UnitFactorsThroughFiniteCoproducts`);
* a morphism from `𝟙` to a tensor product `F ⊗ G` is a finite sum of tensor products of
  morphisms `𝟙 ⟶ F` and `𝟙 ⟶ G` (`CategoryTheory.UnitTensorFinite`).

This is the situation of sheaves of modules on the pro-étale site of an affine weakly contractible
scheme. Then every dualizable object of `D(C)` is isomorphic to a bounded complex of finite
projective objects, that is, of retracts of finite direct sums `𝟙ʳ`
(`DerivedCategory.exists_iso_Q_obj_of_isDualizable`, the forward direction of Stacks 0FPV
in this setting).

## Strategy

1. (`DerivedCategory.exists_retract_of_exactPairing_of_projective_unit`) As over a ring, the
   coevaluation `𝟙 ⟶ K ⊗ N` is a cocycle of degree `0` of `M ⊗ F` for complexes `M`, `F`
   representing `K` and its dual `N` (`F` K-flat with flat terms), since `𝟙` is K-projective.
   By finiteness it is a finite sum of `sᵢ ⊗ tᵢ`, so it comes from the image `L` of a finite sum
   of disk complexes on `𝟙` mapping to `M`; hence `K` is a retract of `Q(L)`, a bounded complex
   whose terms are quotients of `𝟙ʳ`.
2. Consequently `K` is bounded, it has finite Tor amplitude, and if `M` vanishes above `b` the
   top cohomology `Hᵇ(K)` is a quotient of some `𝟙ʳ`.
3. Dualizable objects are closed under cones; one kills the top cohomology by a map
   `𝟙ʳ[-b] ⟶ K` and argues by induction on the length of the Tor amplitude. When the Tor
   amplitude is a single degree, `K = H[-b]` where `H` is a quotient of `𝟙ʳ` with
   `Hom(H, -)` exact, hence a retract of `𝟙ʳ`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Preadditive C]

/-- Morphisms from the unit to a coproduct indexed by a type of `Type` factor through finite
subcoproducts: they are finite sums of morphisms to the summands. -/
def UnitFactorsThroughFiniteCoproducts : Prop :=
  ∀ ⦃J : Type⦄ (X : J → C) [HasCoproduct X] (x : 𝟙_ C ⟶ ∐ X),
    ∃ (S : Finset J) (y : ∀ j, 𝟙_ C ⟶ X j), x = ∑ j ∈ S, y j ≫ Sigma.ι X j

/-- Morphisms from the unit to a tensor product `F ⊗ G` are finite sums of tensor products of
morphisms `𝟙 ⟶ F` and `𝟙 ⟶ G`. -/
def UnitTensorFinite : Prop :=
  ∀ (F G : C) (x : 𝟙_ C ⟶ F ⊗ G), ∃ (n : ℕ) (s : Fin n → (𝟙_ C ⟶ F)) (t : Fin n → (𝟙_ C ⟶ G)),
    x = ∑ i, (λ_ (𝟙_ C)).inv ≫ (s i ⊗ₘ t i)

/-- **An elementwise five lemma.** In a preadditive category, consider a commutative ladder
`A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄ ⟶ A₅` over `B₁ ⟶ B₂ ⟶ B₃ ⟶ B₄ ⟶ B₅` whose rows are exact at the
indicated places, in the sense of morphisms from arbitrary objects. If the outer four vertical
maps are isomorphisms, so is the middle one. -/
lemma isIso_of_five_exact {D : Type*} [Category D] [Preadditive D]
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : D}
    {a : A₁ ⟶ A₂} {b : A₂ ⟶ A₃} {c : A₃ ⟶ A₄} {d : A₄ ⟶ A₅}
    {a' : B₁ ⟶ B₂} {b' : B₂ ⟶ B₃} {c' : B₃ ⟶ B₄} {d' : B₄ ⟶ B₅}
    (γ₁ : A₁ ⟶ B₁) (γ₂ : A₂ ⟶ B₂) (γ₃ : A₃ ⟶ B₃) (γ₄ : A₄ ⟶ B₄) (γ₅ : A₅ ⟶ B₅)
    (h₁ : a ≫ γ₂ = γ₁ ≫ a') (h₂ : b ≫ γ₃ = γ₂ ≫ b') (h₃ : c ≫ γ₄ = γ₃ ≫ c')
    (h₄ : d ≫ γ₅ = γ₄ ≫ d') (hab : a ≫ b = 0) (hcd' : c' ≫ d' = 0)
    (ex₃ : ∀ ⦃W : D⦄ (u : W ⟶ A₃), u ≫ c = 0 → ∃ v, u = v ≫ b)
    (ex₄ : ∀ ⦃W : D⦄ (u : W ⟶ A₄), u ≫ d = 0 → ∃ v, u = v ≫ c)
    (ex₂' : ∀ ⦃W : D⦄ (u : W ⟶ B₂), u ≫ b' = 0 → ∃ v, u = v ≫ a')
    (ex₃' : ∀ ⦃W : D⦄ (u : W ⟶ B₃), u ≫ c' = 0 → ∃ v, u = v ≫ b')
    [IsIso γ₁] [IsIso γ₂] [IsIso γ₄] [IsIso γ₅] : IsIso γ₃ := by
  rw [isIso_iff_yoneda_map_bijective]
  intro W
  refine ⟨fun u₁ u₂ (h : u₁ ≫ γ₃ = u₂ ≫ γ₃) ↦ ?_, fun u' ↦ ?_⟩
  · rw [← sub_eq_zero]
    have hu : (u₁ - u₂) ≫ γ₃ = 0 := by rw [Preadditive.sub_comp, h, sub_self]
    have h1 : (u₁ - u₂) ≫ c = 0 := by
      rw [← cancel_mono γ₄, Category.assoc, h₃, reassoc_of% hu, zero_comp, zero_comp]
    obtain ⟨v, hv⟩ := ex₃ _ h1
    have h2 : (v ≫ γ₂) ≫ b' = 0 := by
      rw [Category.assoc, ← h₂, ← Category.assoc, ← hv, hu]
    obtain ⟨w', hw'⟩ := ex₂' _ h2
    have : v = (w' ≫ inv γ₁) ≫ a := by
      rw [← cancel_mono γ₂, hw', Category.assoc, Category.assoc, h₁, IsIso.inv_hom_id_assoc]
    rw [hv, this, Category.assoc, hab, comp_zero]
  · have hy : (u' ≫ c' ≫ inv γ₄) ≫ d = 0 := by
      rw [← cancel_mono γ₅]
      simp only [Category.assoc, h₄, IsIso.inv_hom_id_assoc, hcd', comp_zero, zero_comp]
    obtain ⟨u, hu⟩ := ex₄ _ hy
    have h3 : (u' - u ≫ γ₃) ≫ c' = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, ← h₃, ← Category.assoc, ← hu]
      simp
    obtain ⟨v', hv'⟩ := ex₃' _ h3
    refine ⟨u + (v' ≫ inv γ₂) ≫ b, ?_⟩
    change (u + (v' ≫ inv γ₂) ≫ b) ≫ γ₃ = u'
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, h₂, IsIso.inv_hom_id_assoc, ← hv']
    abel

namespace MonoidalClosed

variable {D : Type*} [Category D] [MonoidalCategory D] [MonoidalClosed D]

/-- The comparison `[X, 𝟙] ⊗ Z ⟶ [X, Z]` is natural in `X`. -/
lemma ihomUnitTensorToIhom_pre {X X' : D} (f : X ⟶ X') (Z : D) :
    ihomUnitTensorToIhom X' Z ≫ (pre f).app Z =
      (pre f).app (𝟙_ D) ▷ Z ≫ ihomUnitTensorToIhom X Z := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, id_tensor_pre_app_comp_ev,
    whiskerLeft_ihomUnitTensorToIhom_ev, whisker_exchange_assoc,
    whiskerLeft_ihomUnitTensorToIhom_ev, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, id_tensor_pre_app_comp_ev, comp_whiskerRight_assoc,
    associator_inv_naturality_left_assoc]

end MonoidalClosed

end CategoryTheory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

attribute [local instance] Abelian.hasFiniteBiproducts

omit [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C] in
/-- If morphisms from the unit are finite on coproducts and on tensor products, a morphism from
the unit to the degree `0` term of a tensor product of complexes `M ⊗ F` is a finite sum of
tensor products `sᵢ ⊗ tᵢ` of morphisms to terms `M^{pᵢ}` and `F^{qᵢ}`, `pᵢ + qᵢ = 0`. -/
lemma exists_eq_sum_ιTensorObj (hC : UnitFactorsThroughFiniteCoproducts C)
    (hT : UnitTensorFinite C) (M F : CochainComplex C ℤ) (x : 𝟙_ C ⟶ (M ⊗ F).X 0) :
    ∃ (ι : Type) (_ : Fintype ι) (p q : ι → ℤ) (h : ∀ i, p i + q i = 0)
      (s : ∀ i, 𝟙_ C ⟶ M.X (p i)) (t : ∀ i, 𝟙_ C ⟶ F.X (q i)),
      x = ∑ i, (λ_ (𝟙_ C)).inv ≫ (s i ⊗ₘ t i) ≫
        HomologicalComplex.ιTensorObj M F (p i) (q i) 0 (h i) := by
  obtain ⟨S, y, hy⟩ := hC _ (show 𝟙_ C ⟶ ∐ _ from x)
  choose n s t hst using fun j ↦ hT _ _ (y j)
  refine ⟨Σ j : S, Fin (n j), inferInstance, fun j ↦ j.1.1.1.1, fun j ↦ j.1.1.1.2,
    fun j ↦ j.1.1.2, fun j ↦ s j.1 j.2, fun j ↦ t j.1 j.2, ?_⟩
  refine hy.trans ?_
  rw [Fintype.sum_sigma, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hst j.1, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Category.assoc]
  rfl

omit [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C] in
/-- If the terms of `F` are flat, tensoring a termwise monomorphism `f : L ⟶ M` of complexes with
`F` gives a termwise monomorphism `L ⊗ F ⟶ M ⊗ F`: in each degree it is a coproduct of the
monomorphisms `Lᵖ ⊗ F^q ⟶ Mᵖ ⊗ F^q`. -/
lemma mono_whiskerRight_f {L M : CochainComplex C ℤ} (f : L ⟶ M) [Mono f]
    (F : CochainComplex C ℤ) (hF : ∀ q, ObjectProperty.flat (F.X q)) (j : ℤ) :
    Mono ((f ▷ F).f j) := by
  have (i : ℤ × ℤ) : Mono (f.f i.1 ▷ F.X i.2) := by
    have : PreservesFiniteLimits (tensorRight (F.X i.2)) := (hF i.2).tensorRight.1
    have : PreservesLimitsOfShape WalkingCospan (tensorRight (F.X i.2)) := inferInstance
    exact (tensorRight (F.X i.2)).map_mono (f.f i.1)
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := MorphismProperty.monomorphisms C) _ _ (colimit.cocone _)
    (colimit.cocone _) (colimit.isColimit _) (colimit.isColimit _)
    (Discrete.natTrans fun i ↦ f.f i.as.1.1 ▷ F.X i.as.1.2)
    (fun i ↦ by exact this i.as.1) _ (fun ⟨⟨⟨p, q⟩, h⟩⟩ ↦ by
      refine (HomologicalComplex.ι_mapBifunctorMap f (𝟙 F) _ _ p q j h).trans ?_
      simp only [curriedTensor_obj_obj, curriedTensor_map_app, HomologicalComplex.id_f,
        curriedTensor_obj_map, whiskerLeft_id, Category.id_comp,
        Functor.mapBifunctorHomologicalComplex_obj_obj_toGradedObject,
        Discrete.functor_obj_eq_as, Functor.const_obj_obj]
      rfl)

/-- **A dualizable object is a retract of a finite complex.** Suppose that the unit of `C` is
projective, with finite morphisms to coproducts and tensor products. Let `K` be an object of
`D(C)` with a right dual `N`, represented by a complex `M`. Then the isomorphism `K ≅ Q(M)`
factors through `Q(L)` for a subcomplex `L` of `M` which is bounded and whose terms are
quotients of finite direct sums `𝟙ʳ`.

The coevaluation `𝟙 ⟶ K ⊗ N ≅ Q(M ⊗ F)`, where `F` is a K-flat complex of flat objects
representing `N`, is a cocycle `x` of degree `0` of `M ⊗ F`, as `𝟙[0]` is K-projective. It is a
finite sum of `sᵢ ⊗ tᵢ` with `sᵢ : 𝟙 ⟶ M^{pᵢ}`, so it comes from `L ⊗ F` where `L` is the image of
the sum of the disk complexes `𝟙 ⟶ 𝟙` in degrees `pᵢ, pᵢ + 1` mapping to `M` by `sᵢ`; it is a
cocycle there since `L ⊗ F ⟶ M ⊗ F` is a monomorphism. So the coevaluation factors through
`Q(L) ⊗ N`, and the zigzag identity factors `K ≅ Q(M)` through `Q(L)`. -/
theorem exists_retract_of_exactPairing_of_projective_unit [Projective (𝟙_ C)]
    (hC : UnitFactorsThroughFiniteCoproducts C) (hT : UnitTensorFinite C)
    (K N : DerivedCategory C) [ExactPairing K N] (M : CochainComplex C ℤ) (e : K ≅ Q.obj M) :
    ∃ (L : CochainComplex C ℤ) (ι : L ⟶ M) (_ : Mono ι) (a b : ℤ) (_ : L.IsStrictlyGE a)
      (_ : L.IsStrictlyLE b)
      (_ : ∀ n, ∃ (r : ℕ) (π : (⨁ fun _ : Fin r ↦ 𝟙_ C) ⟶ L.X n), Epi π)
      (w : K ⟶ Q.obj L), w ≫ Q.map ι = e.hom := by
  obtain ⟨F, π, _, hFflat, hF⟩ := CochainComplex.exists_quasiIso_flat_kFlat (Q.objPreimage N)
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  let eD : Q.obj F ≅ N := asIso (Q.map π) ≪≫ Q.objObjPreimageIso N
  let T (L' : CochainComplex C ℤ) : Q.obj L' ⊗ N ≅ Q.obj (L' ⊗ F) :=
    whiskerLeftIso (Q.obj L') eD.symm ≪≫ QObjTensorQObjIsoOfKFlatRight L' F hF
  have hTn {L₁ L₂ : CochainComplex C ℤ} (f : L₁ ⟶ L₂) :
      Q.map f ▷ N ≫ (T L₂).hom = (T L₁).hom ≫ Q.map (f ▷ F) := by
    simp only [T, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc, ← whisker_exchange_assoc,
      qObjTensorQObjIsoOfKFlatRight_hom_naturality]
  let U := (HomologicalComplex.single C (.up ℤ) 0).obj (𝟙_ C)
  let eU : 𝟙_ (DerivedCategory C) ≅ Q.obj U :=
    (singleFunctorObjUnitIso C).symm ≪≫ (singleFunctorIsoCompQ C 0).app _
  obtain ⟨φ, hφ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq U (M ⊗ F)
    (eU.inv ≫ η_ K N ≫ e.hom ▷ N ≫ (T M).hom)
  let x : 𝟙_ C ⟶ (M ⊗ F).X 0 :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ≫ φ.f 0
  obtain ⟨ι, _, p, q, hpq, s, t, hx⟩ := exists_eq_sum_ιTensorObj hC hT M F x
  have hp (i : ι) : (ComplexShape.up ℤ).Rel (p i) (p i + 1) := rfl
  have hp' (i : ι) : p i ≠ p i + 1 := by omega
  let D (i : ι) : CochainComplex C ℤ := HomologicalComplex.double (𝟙 (𝟙_ C)) (hp i)
  let dm (i : ι) : D i ⟶ M := HomologicalComplex.mkHomFromDouble (hp i) (hp' i) (s i)
    (s i ≫ M.d (p i) (p i + 1)) (by simp) (fun k _ ↦ by simp)
  let g : (⨁ D) ⟶ M := biproduct.desc dm
  let L := image g
  let j : L ⟶ M := image.ι g
  let s' (i : ι) : 𝟙_ C ⟶ L.X (p i) :=
    (HomologicalComplex.doubleXIso₀ _ (hp i)).inv ≫ (biproduct.ι D i ≫ factorThruImage g).f (p i)
  have hs' (i : ι) : s' i ≫ j.f (p i) = s i := by
    have : (biproduct.ι D i ≫ factorThruImage g ≫ j) = dm i := by
      simp [j, g]
    simp only [s', Category.assoc, ← HomologicalComplex.comp_f, this, dm,
      HomologicalComplex.mkHomFromDouble_f₀, Iso.inv_hom_id_assoc]
  let x' : 𝟙_ C ⟶ (L ⊗ F).X 0 := ∑ i, (λ_ (𝟙_ C)).inv ≫ (s' i ⊗ₘ t i) ≫
    HomologicalComplex.ιTensorObj L F (p i) (q i) 0 (hpq i)
  have hx' : x' ≫ (j ▷ F).f 0 = x := by
    rw [hx, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Category.assoc]
    congr 1
    refine ((s' i ⊗ₘ t i) ≫= HomologicalComplex.ι_mapBifunctorMap j (𝟙 F) _ _
      (p i) (q i) 0 (hpq i)).trans ?_
    simp only [tensorHom_def, whiskerRight_id, Category.assoc, curriedTensor_obj_obj,
      curriedTensor_map_app, HomologicalComplex.id_f, curriedTensor_obj_map, whiskerLeft_id,
      Category.id_comp, ← hs' i, Iso.cancel_iso_hom_left]
    rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
  have hj : ∀ k, Mono ((j ▷ F).f k) := mono_whiskerRight_f j F hFflat
  have hd : x' ≫ (L ⊗ F).d 0 1 = 0 := by
    rw [← cancel_mono ((j ▷ F).f 1), Category.assoc, ← HomologicalComplex.Hom.comm,
      reassoc_of% hx', zero_comp]
    simp [x, (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (𝟙_ C) 1 (by omega)).eq_of_tgt
      (U.d 0 1) 0]
  let φ' : U ⟶ L ⊗ F := HomologicalComplex.mkHomFromSingle x' (by
    rintro k (rfl : 0 + 1 = k)
    exact hd)
  have hφ' : φ' ≫ j ▷ F = φ := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f, Category.assoc, hx']
    simp [x]
  have hu : (eU.hom ≫ Q.map φ' ≫ (T _).inv) ≫ Q.map j ▷ N = η_ K N ≫ e.hom ▷ N := by
    rw [← cancel_mono (T M).hom, Category.assoc, Category.assoc, Category.assoc, hTn j,
      Iso.inv_hom_id_assoc, ← Q.map_comp, hφ', hφ, Iso.hom_inv_id_assoc,
      Category.assoc]
  have key : (tensorRightHomEquiv _ K N _).symm (eU.hom ≫ Q.map φ' ≫ (T _).inv) ≫ Q.map j =
      (λ_ K).hom ≫ e.hom := by
    rw [← tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight (Y' := N), ← hu,
      Equiv.eq_symm_apply, tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]
  -- the terms of `L` are quotients of `𝟙ʳ`, and `L` is bounded
  have hD (i : ι) (k : ℤ) : ∃ c : 𝟙_ C ⟶ (D i).X k, Epi c := by
    by_cases h₀ : k = p i
    · subst h₀
      exact ⟨(HomologicalComplex.doubleXIso₀ _ (hp i)).inv, inferInstance⟩
    by_cases h₁ : k = p i + 1
    · subst h₁
      exact ⟨(HomologicalComplex.doubleXIso₁ _ (hp i) (hp' i)).inv, inferInstance⟩
    exact ⟨0, (HomologicalComplex.isZero_double_X _ (hp i) k h₀ h₁).epi _⟩
  choose c hc using hD
  let eX (k : ℤ) : (⨁ D).X k ≅ ⨁ fun i ↦ (D i).X k :=
    (HomologicalComplex.eval C (.up ℤ) k).mapBiproduct D
  have hL (k : ℤ) : Epi ((factorThruImage g).f k) := inferInstance
  let ε := Fintype.equivFin ι
  have hzero (k : ℤ) (hk : ∀ i, k ≠ p i ∧ k ≠ p i + 1) : IsZero (L.X k) := by
    refine IsZero.of_epi ((eX k).inv ≫ (factorThruImage g).f k) ?_
    refine (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun i ↦ ?_)
    exact (HomologicalComplex.isZero_double_X _ (hp i) k (hk i).1 (hk i).2).eq_of_src _ _
  refine ⟨L, j, inferInstance, -∑ i, |p i|, ∑ i, |p i| + 1,
    (CochainComplex.isStrictlyGE_iff L _).2 fun k hk ↦ hzero k fun i ↦ ?_,
    (CochainComplex.isStrictlyLE_iff L _).2 fun k hk ↦ hzero k fun i ↦ ?_,
    fun k ↦ ⟨Fintype.card ι, (biproduct.whiskerEquiv (f := fun _ : Fin (Fintype.card ι) ↦ 𝟙_ C)
      (g := fun _ : ι ↦ 𝟙_ C) ε.symm (fun _ ↦ Iso.refl _)).hom ≫
      biproduct.map (fun i ↦ c i k) ≫ (eX k).inv ≫ (factorThruImage g).f k, ?_⟩,
    _, by rw [Category.assoc, key, Iso.inv_hom_id_assoc]⟩
  · have := Finset.single_le_sum (f := fun i ↦ |p i|) (fun i _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    constructor <;> linarith [neg_abs_le (p i)]
  · have := Finset.single_le_sum (f := fun i ↦ |p i|) (fun i _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    constructor <;> linarith [le_abs_self (p i)]
  · infer_instance

end DerivedCategory

namespace DerivedCategory

open Pretriangulated MonoidalClosed

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

/-- A shift of a dualizable object of `D(C)` is dualizable: `X⟦n⟧ ≅ X ⊗ 𝟙⟦n⟧`, and `𝟙⟦n⟧` has
tensor inverse `𝟙⟦-n⟧`. -/
lemma isDualizable_shift {X : DerivedCategory C} (hX : IsDualizable X) (n : ℤ) :
    IsDualizable (X⟦n⟧) := by
  let U := 𝟙_ (DerivedCategory C)
  have hU : IsDualizable (U⟦n⟧) := isDualizable_of_tensorIso (Y := U⟦-n⟧)
    (shiftTensorShiftIso (X := U) (Y := U) (a := n) (b := -n) ≪≫ (shiftFunctor _ _).mapIso (λ_ U) ≪≫
      eqToIso (by rw [add_neg_cancel]) ≪≫ (shiftFunctorZero _ ℤ).app U)
    (shiftTensorShiftIso (X := U) (Y := U) (a := -n) (b := n) ≪≫ (shiftFunctor _ _).mapIso (λ_ U) ≪≫
      eqToIso (by rw [neg_add_cancel]) ≪≫ (shiftFunctorZero _ ℤ).app U)
  have hX0 : IsDualizable (X⟦(0 : ℤ)⟧) := IsDualizable.of_iso ((shiftFunctorZero _ ℤ).app X).symm hX
  exact IsDualizable.of_iso (shiftTensorShiftIso (X := X) (Y := U) (a := 0) (b := n) ≪≫
    (shiftFunctor _ _).mapIso (ρ_ X) ≪≫
    eqToIso (by rw [zero_add])) (hX0.tensorObj hU)

/-- **Dualizable objects are closed under cones.** If two vertices `T.obj₁` and `T.obj₂` of a
distinguished triangle of `D(C)` are dualizable, so is the third. For any `Z`, both
`X ↦ [X, 𝟙] ⊗ Z` and `X ↦ [X, Z]` carry distinguished triangles to distinguished triangles, and
the comparison `[X, 𝟙] ⊗ Z ⟶ [X, Z]`, natural in `X`, is an isomorphism for dualizable `X`; the
five lemma applies to the rotations of `T`. -/
theorem isDualizable_obj₃_of_distTriang (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (h₁ : IsDualizable T.obj₁) (h₂ : IsDualizable T.obj₂) :
    IsDualizable T.obj₃ := by
  obtain ⟨_⟩ := nonempty_braidedCategory C
  rw [isDualizable_iff_isIso_ihomUnitTensorToIhom]
  have hiso {X : DerivedCategory C} (hX : IsDualizable X) (Z : DerivedCategory C) :
      IsIso (ihomUnitTensorToIhom X Z) := by
    obtain ⟨_⟩ := hX
    let := BraidedCategory.exactPairing_swap X Xᘁ
    exact isIso_ihomUnitTensorToIhom Xᘁ X Z
  set Z := T.obj₃
  have hT₁ := rot_of_distTriang _ hT
  have hT₂ := rot_of_distTriang _ hT₁
  obtain ⟨k₀, hk₀⟩ := exists_distinguished_ihom_pre T hT (𝟙_ _)
  obtain ⟨k₁, hk₁⟩ := exists_distinguished_ihom_pre _ hT₁ (𝟙_ _)
  obtain ⟨k₂, hk₂⟩ := exists_distinguished_ihom_pre _ hT₂ (𝟙_ _)
  have hF₀ := (tensorRight Z).map_distinguished _ hk₀
  have hF₁ := (tensorRight Z).map_distinguished _ hk₁
  have hF₂ := (tensorRight Z).map_distinguished _ hk₂
  obtain ⟨l₀, hl₀⟩ := exists_distinguished_ihom_pre T hT Z
  obtain ⟨l₁, hl₁⟩ := exists_distinguished_ihom_pre _ hT₁ Z
  obtain ⟨l₂, hl₂⟩ := exists_distinguished_ihom_pre _ hT₂ Z
  have : IsIso (ihomUnitTensorToIhom T.rotate.rotate.obj₂ Z) := hiso (isDualizable_shift h₁ 1) Z
  have : IsIso (ihomUnitTensorToIhom T.rotate.rotate.obj₃ Z) := hiso (isDualizable_shift h₂ 1) Z
  have := hiso h₁ Z
  have := hiso h₂ Z
  exact isIso_of_five_exact (ihomUnitTensorToIhom _ Z) (ihomUnitTensorToIhom _ Z)
    (ihomUnitTensorToIhom _ Z) (ihomUnitTensorToIhom _ Z) (ihomUnitTensorToIhom _ Z)
    (ihomUnitTensorToIhom_pre _ _).symm (ihomUnitTensorToIhom_pre _ _).symm
    (ihomUnitTensorToIhom_pre _ _).symm (ihomUnitTensorToIhom_pre _ _).symm
    (comp_distTriang_mor_zero₁₂ _ hF₂) (comp_distTriang_mor_zero₁₂ _ hl₀)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hF₁ u hu)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hF₀ u hu)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hl₂ u hu)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hl₁ u hu)

end DerivedCategory

namespace CategoryTheory

open Limits

section FinProj

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C]

/-- The biproduct of copies of an object `X` indexed by a sum of finite types is the binary
biproduct of the two partial biproducts. -/
noncomputable def biprodBiproductConstIso (X : C) (ι κ : Type) [Finite ι] [Finite κ] :
    (⨁ fun _ : ι ↦ X) ⊞ (⨁ fun _ : κ ↦ X) ≅ ⨁ fun _ : ι ⊕ κ ↦ X where
  hom := biprod.desc (biproduct.desc fun i ↦ biproduct.ι (fun _ : ι ⊕ κ ↦ X) (Sum.inl i))
    (biproduct.desc fun k ↦ biproduct.ι (fun _ : ι ⊕ κ ↦ X) (Sum.inr k))
  inv := biproduct.desc fun s ↦ Sum.elim (fun i ↦ biproduct.ι (fun _ : ι ↦ X) i ≫ biprod.inl)
    (fun k ↦ biproduct.ι (fun _ : κ ↦ X) k ≫ biprod.inr) s
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> intro j <;> simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    rintro (i | k) <;> simp

/-- The biproduct of `r + s` copies of `X` is the binary biproduct of `r` and `s` copies. -/
noncomputable def biprodBiproductFinIso (X : C) (r s : ℕ) :
    (⨁ fun _ : Fin r ↦ X) ⊞ (⨁ fun _ : Fin s ↦ X) ≅ ⨁ fun _ : Fin (r + s) ↦ X :=
  biprodBiproductConstIso X (Fin r) (Fin s) ≪≫
    biproduct.whiskerEquiv (f := fun _ : Fin r ⊕ Fin s ↦ X) (g := fun _ : Fin (r + s) ↦ X)
      finSumFinEquiv (fun _ ↦ Iso.refl _)

variable [MonoidalCategory C]

variable (C) in
/-- The objects of `C` which are retracts of a finite direct sum `𝟙ʳ` of copies of the unit, the
*finite projective* objects of the blueprint. -/
def finProj : ObjectProperty C :=
  fun P ↦ ∃ r : ℕ, Nonempty (Retract P (⨁ fun _ : Fin r ↦ 𝟙_ C))

omit [HasBinaryBiproducts C] in
lemma finProj_of_iso {P P' : C} (e : P ≅ P') (hP : finProj C P) : finProj C P' := by
  obtain ⟨r, ⟨h⟩⟩ := hP
  exact ⟨r, ⟨(Retract.ofIso e.symm).trans h⟩⟩

omit [HasBinaryBiproducts C] in
lemma finProj_of_isZero {P : C} (hP : IsZero P) : finProj C P :=
  ⟨0, ⟨{ i := 0, r := 0, retract := hP.eq_of_src _ _ }⟩⟩

lemma finProj_biprod {P P' : C} (hP : finProj C P) (hP' : finProj C P') :
    finProj C (P ⊞ P') := by
  obtain ⟨r, ⟨h⟩⟩ := hP
  obtain ⟨s, ⟨h'⟩⟩ := hP'
  refine ⟨r + s, ⟨Retract.trans ?_ (Retract.ofIso (biprodBiproductFinIso _ r s))⟩⟩
  exact
    { i := biprod.map h.i h'.i
      r := biprod.map h.r h'.r
      retract := by apply biprod.hom_ext' <;> simp [h.retract_assoc, h'.retract_assoc] }

omit [MonoidalCategory C] [HasBinaryBiproducts C] in
lemma projective_biproduct_const (X : C) [Projective X] (ι : Type) [Finite ι] :
    Projective (⨁ fun _ : ι ↦ X) where
  factors f e _ := ⟨biproduct.desc fun b ↦
    Projective.factorThru (biproduct.ι (fun _ : ι ↦ X) b ≫ f) e,
    biproduct.hom_ext' _ _ fun b ↦ by simp⟩

omit [HasBinaryBiproducts C] in
lemma finProj.projective [Projective (𝟙_ C)] {P : C} (hP : finProj C P) : Projective P := by
  obtain ⟨r, ⟨h⟩⟩ := hP
  have := projective_biproduct_const (𝟙_ C) (Fin r)
  exact h.projective

lemma isDualizable_biproduct_unit [MonoidalPreadditive C] (r : ℕ) :
    IsDualizable (⨁ fun _ : Fin r ↦ 𝟙_ C) := by
  induction r with
  | zero =>
    refine CategoryTheory.IsZero.isDualizable
      ((IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ ?_))
    exact fun i ↦ i.elim0
  | succ r ih =>
    exact IsDualizable.of_iso (biprodBiproductFinIso _ r 1)
      (IsDualizable.biprod ih (IsDualizable.of_iso (biproductUniqueIso _).symm isDualizable_unit))

lemma finProj.isDualizable [MonoidalPreadditive C] [IsIdempotentComplete C] {P : C}
    (hP : finProj C P) :
    IsDualizable P := by
  obtain ⟨r, ⟨h⟩⟩ := hP
  exact IsDualizable.of_retract h (isDualizable_biproduct_unit r)

end FinProj

end CategoryTheory

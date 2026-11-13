import Langlands.Geometry.Building.QuasiSplitApartmentShifts
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.GroupScheme.Lie.RootOrbitCharacterDescent
import Langlands.GroupScheme.Torus.SplitPartCharacters
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.Geometry.Building.UnramifiedValuationDescentStatement
import Langlands.Geometry.Building.RootValueTorusFieldAxioms
import Langlands.Geometry.Building.RootValueTorusTranslation
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.GroupScheme.Rational.GenericLieWeights
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Langlands.Representation.Plancherel.LocalFieldUnits
import Mathlib.Algebra.Category.Grp.Injective

/-! # Galois-fixed translations descend to the largest split subtorus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LocalGalois Langlands.LocalGalois.Separable

namespace Langlands.GroupScheme

section IdentityBaseChange

variable {X : Scheme.{u}} {H G : GroupScheme X}

/-- Along a base map equal to the identity, a character of the base change vanishes when its
restriction along the base change of a homomorphism with injective character restriction
vanishes. -/
theorem eq_zero_of_characterRestrict_baseChange_of_eq_id (f : H ⟶ G)
    (hinj : Function.Injective (characterRestrict f)) (b : X ⟶ X) (hb : b = 𝟙 X)
    (ψ : rationalCharacters ((GroupScheme.baseChange b).obj G))
    (hψ : characterRestrict ((GroupScheme.baseChange b).map f) ψ = 0) : ψ = 0 := by
  subst hb
  have hf := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫ Functor.mapGrpIdIso).hom.naturality f
  change (GroupScheme.baseChange (𝟙 X)).map f ≫ (baseChangeIdIso G).hom =
    (baseChangeIdIso H).hom ≫ f at hf
  have hf' : f ≫ (baseChangeIdIso G).inv =
      (baseChangeIdIso H).inv ≫ (GroupScheme.baseChange (𝟙 X)).map f := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h0 : characterRestrict (baseChangeIdIso G).inv ψ = 0 := by
    apply hinj
    rw [map_zero, ← AddMonoidHom.comp_apply, ← characterRestrict_comp, hf',
      characterRestrict_comp, AddMonoidHom.comp_apply, hψ, map_zero]
  have hψ' : ψ = characterRestrict (baseChangeIdIso G).hom
      (characterRestrict (baseChangeIdIso G).inv ψ) := by
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, Iso.hom_inv_id,
      characterRestrict_id, AddMonoidHom.id_apply]
  rw [hψ', h0, map_zero]

end IdentityBaseChange

section GaloisInvariant

open Langlands.Plancherel.TorusNormKernel AffineCharacterFiniteGalois AffineCharacterTowerDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The base map of the trivial extension is the identity. -/
theorem baseMap_self_eq_id : GaloisPointComparison.baseMap k k = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- **Galois-invariant characters vanishing on the split part vanish.** Let `K/k` be a Galois
extension, not necessarily finite, `T` an affine `k`-torus of finite type and `S → T` its
largest split subtorus. A character of `T_K` fixed by `Aut(K/k)` whose restriction to `S_K` is
trivial is trivial. -/
theorem IsLargestSplitSubtorus.galoisInvariant_character_eq_zero [IsGalois k K]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    {t : S ⟶ T} (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t))
    (hT : IsTorus T.toGrp)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hχ : ∀ σ : K ≃ₐ[k] K, characterLattice.galoisRepresentation k K T σ χ = χ)
    (h0 : characterRestrict ((GroupScheme.baseChange (algebraBaseMap k K)).map
      (CommGroupScheme.groupHom t)) χ = 0) : χ = 0 := by
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : IsClosedImmersion (CommGroupScheme.groupHom t).hom.hom.left := ht.1.2
  have : IsAffine S.toGrp.X.left :=
    isAffine_of_isAffineHom (CommGroupScheme.groupHom t).hom.hom.left
  set ψ := baseChangedCharacter k K T χ with hψdef
  have hψ : ∀ σ : K ≃ₐ[k] K, tensorConj T.toGrp k K σ
      (tensorValue T.toGrp K ψ : K ⊗[k] Coord T.toGrp) = tensorValue T.toGrp K ψ := by
    intro σ
    have h := tensorConj_tensorValue_baseChangedCharacter (k := k) (L := K) T k σ χ
    rw [hχ] at h
    exact h
  have hres : characterRestrict ((GroupScheme.baseChange
      (GaloisPointComparison.baseMap k K)).map (CommGroupScheme.groupHom t)) ψ =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k K) 0 := by
    rw [map_zero]
    exact h0
  have hE := characterRestrict_fixedDescend T.toGrp k K ψ hψ (CommGroupScheme.groupHom t) 0 hres
  rw [map_zero] at hE
  have hψE : fixedDescend T.toGrp k K ψ hψ = 0 :=
    eq_zero_of_characterRestrict_baseChange_of_eq_id (CommGroupScheme.groupHom t)
      (ht.characterRestrict_injective hT) _ (baseMap_self_eq_id k) _ hE
  have hψ0 : ψ = 0 := by
    apply ext_valueE (E := K)
    intro D _ _ _ _ y
    rw [← valueE_fixedDescend T.toGrp k K ψ hψ y, hψE, valueE_apply, valueE_apply,
      rationalCharacters.comp_zero, rationalCharacters.comp_zero, map_one, map_one]
  exact hψ0

end GaloisInvariant

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

section Descent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (jT : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) jT

private instance descentExtendedAffine :
    IsAffineHom (GaloisPointComparison.baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Evaluation at a fixed real cocharacter, as an integral linear form on characters. -/
def evalAt (T' : CommGroupScheme (Spec (CommRingCat.of k))) (w : V T') :
    characterLattice T' →ₗ[ℤ] ℝ :=
  ((pair T').flip w).restrictScalars ℤ ∘ₗ TensorProduct.mk ℤ ℝ (characterLattice T') 1

omit [IsAffineHom G.X.hom] in
@[simp] theorem evalAt_apply (T' : CommGroupScheme (Spec (CommRingCat.of k))) (w : V T')
    (χ : characterLattice T') : evalAt k T' w χ = eval T' χ w := by
  rw [eval_eq_pair]
  rfl

/-- On the integral span of the roots, the Galois transport of a character depends only on
the permutation of the roots. -/
theorem galoisRepresentation_eq_of_galoisRootAction_eq {σ τ : K ≃ₐ[k] K}
    (h : galoisRootAction k K jT σ = galoisRootAction k K jT τ)
    {χ : characterLattice T_K}
    (hχ : χ ∈ Submodule.span ℤ (relativeRoots (T := T_K) j_K)) :
    characterLattice.galoisRepresentation k K T σ χ =
      characterLattice.galoisRepresentation k K T τ χ := by
  induction hχ using Submodule.span_induction with
  | mem α hα =>
    have := congrArg Subtype.val (Equiv.congr_fun h ⟨α, hα⟩)
    simpa only [galoisRootAction_val] using this
  | zero => simp only [map_zero]
  | add χ ψ _ _ hχ hψ => simp only [map_add, hχ, hψ]
  | smul n χ _ hχ => simp only [map_zsmul, hχ]

/-- On the integral span of finitely many roots, the Galois orbit is finite. -/
theorem finite_range_galoisRepresentation [Finite (relativeRoots (T := T_K) j_K)]
    {χ : characterLattice T_K}
    (hχ : χ ∈ Submodule.span ℤ (relativeRoots (T := T_K) j_K)) :
    (Set.range fun σ : K ≃ₐ[k] K => characterLattice.galoisRepresentation k K T σ χ).Finite := by
  let q := galoisRootAction k K jT
  let g : Set.range q → characterLattice T_K := fun p =>
    characterLattice.galoisRepresentation k K T p.2.choose χ
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨⟨q σ, σ, rfl⟩, ?_⟩
  exact galoisRepresentation_eq_of_galoisRootAction_eq k K jT
    (⟨q σ, σ, rfl⟩ : Set.range q).2.choose_spec hχ

/-- Characters in the integral root span annihilate the root annihilator. -/
theorem eval_eq_zero_of_mem_span {χ : characterLattice T_K}
    (hχ : χ ∈ Submodule.span ℤ (relativeRoots (T := T_K) j_K)) {a : V T_K}
    (ha : a ∈ rootAnnihilator (S := T_K) j_K) : eval T_K χ a = 0 := by
  rw [← evalAt_apply]
  induction hχ using Submodule.span_induction with
  | mem α hα =>
    rw [evalAt_apply]
    exact mem_rootAnnihilator.1 ha α hα
  | zero => simp only [map_zero]
  | add χ ψ _ _ hχ hψ => simp only [map_add, hχ, hψ, add_zero]
  | smul n χ _ hχ => simp only [map_zsmul, hχ, smul_zero]

variable {k K jT}

/-- **Vanishing on split-trivial root combinations.** Let `K/k` be Galois, `t : S → T` the
largest split subtorus of an affine `k`-torus of finite type, and `w` a real cocharacter of
`T_K` fixed by `Aut(K/k)` modulo the root annihilator. Every integral combination of roots of
`T_K` whose restriction to `S_K` vanishes vanishes at `w`. -/
theorem eval_eq_zero_of_characterRestrict_eq_zero [IsGalois k K]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [Finite (relativeRoots (T := T_K) j_K)]
    {t : S ⟶ T} (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t))
    (hT : IsTorus T.toGrp) {w : V T_K}
    (hw : ∀ σ : K ≃ₐ[k] K,
      galoisCocharacterAction k K T σ w - w ∈ rootAnnihilator (S := T_K) j_K)
    {χ : characterLattice T_K}
    (hχ : χ ∈ Submodule.span ℤ (relativeRoots (T := T_K) j_K))
    (hres : characterRestrict ((GroupScheme.baseChange b).map
      (CommGroupScheme.groupHom t)) χ = 0) :
    eval T_K χ w = 0 := by
  classical
  have hfin := finite_range_galoisRepresentation k K jT hχ
  set O := hfin.toFinset with hOdef
  have hmem : ∀ {ψ}, ψ ∈ O ↔ ∃ σ : K ≃ₐ[k] K,
      characterLattice.galoisRepresentation k K T σ χ = ψ := by
    intro ψ
    rw [hOdef, Set.Finite.mem_toFinset, Set.mem_range]
  set s := ∑ ψ ∈ O, ψ with hsdef
  have hs_fix : ∀ τ : K ≃ₐ[k] K, characterLattice.galoisRepresentation k K T τ s = s := by
    intro τ
    rw [hsdef, map_sum]
    refine Finset.sum_nbij' (fun ψ => characterLattice.galoisRepresentation k K T τ ψ)
      (fun ψ => characterLattice.galoisRepresentation k K T τ⁻¹ ψ) ?_ ?_ ?_ ?_ ?_
    · intro ψ hψ
      obtain ⟨σ, rfl⟩ := hmem.1 hψ
      exact hmem.2 ⟨τ * σ, by rw [map_mul]; rfl⟩
    · intro ψ hψ
      obtain ⟨σ, rfl⟩ := hmem.1 hψ
      exact hmem.2 ⟨τ⁻¹ * σ, by rw [map_mul]; rfl⟩
    · intro ψ _
      exact Representation.inv_self_apply _ τ ψ
    · intro ψ _
      exact Representation.self_inv_apply _ τ ψ
    · intro ψ _
      rfl
  have hs_res : characterRestrict ((GroupScheme.baseChange b).map
      (CommGroupScheme.groupHom t)) s = 0 := by
    rw [hsdef, map_sum]
    refine Finset.sum_eq_zero fun ψ hψ => ?_
    obtain ⟨σ, rfl⟩ := hmem.1 hψ
    have h := rationalCharacters.characterRestrict_galoisRepresentation k K
      (CommGroupScheme.groupHom t) σ χ
    exact h.trans (by rw [hres, map_zero])
  have hs0 : s = 0 :=
    IsLargestSplitSubtorus.galoisInvariant_character_eq_zero k K ht hT s hs_fix hs_res
  have hterm : ∀ ψ ∈ O, eval T_K ψ w = eval T_K χ w := by
    intro ψ hψ
    obtain ⟨σ, rfl⟩ := hmem.1 hψ
    have h := eval_galoisCocharacterAction_right k K T σ⁻¹ χ w
    rw [inv_inv] at h
    rw [← h]
    have hz := eval_eq_zero_of_mem_span k K jT hχ (hw σ⁻¹)
    rw [map_sub] at hz
    linarith
  have hsum : eval T_K s w = (O.card : ℝ) * eval T_K χ w := by
    rw [← evalAt_apply, hsdef, map_sum]
    simp only [evalAt_apply]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hcard : (O.card : ℝ) ≠ 0 := by
    have : χ ∈ O := hmem.2 ⟨1, by rw [map_one]; rfl⟩
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem this)
  rw [hs0] at hsum
  have h0 : eval T_K (0 : characterLattice T_K) w = 0 := by
    rw [← evalAt_apply, map_zero]
  rw [h0] at hsum
  exact (mul_eq_zero.1 hsum.symm).resolve_left hcard

/-- **Galois-fixed translations descend.** Let `K/k` be a Galois extension, not necessarily
finite, `T` an affine `k`-torus of finite type with largest split subtorus `t : S → T`, and
`jT : T → G` with finitely many roots of `T_K`. If a real cocharacter `w` of `T_K` is fixed by
`Aut(K/k)` modulo the root annihilator, then it agrees on all roots of `T_K` with the
push-forward of a real cocharacter of `S`. -/
theorem exists_descentCocharacterMap_sub_mem_of_isGalois [IsGalois k K]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [Finite (relativeRoots (T := T_K) j_K)]
    (hS : IsSplitTorus S.toGrp)
    {t : S ⟶ T} (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t))
    (hT : IsTorus T.toGrp) (w : V T_K)
    (hw : ∀ σ : K ≃ₐ[k] K,
      galoisCocharacterAction k K T σ w - w ∈ rootAnnihilator (S := T_K) j_K) :
    ∃ v : V S, w - descentCocharacterMap k K t hS v ∈ rootAnnihilator (S := T_K) j_K := by
  classical
  set R := relativeRoots (T := T_K) j_K
  let tK := (CommGroupScheme.baseChange b).map t
  let ρ := (characterRestrict ((GroupScheme.baseChange b).map
    (CommGroupScheme.groupHom t))).toIntLinearMap
  let Ψ : (R →₀ ℤ) →ₗ[ℤ] characterLattice ((CommGroupScheme.baseChange b).obj S) :=
    Finsupp.linearCombination ℤ (fun α : R => ρ α.1)
  let ℓ₀ : (R →₀ ℤ) →ₗ[ℤ] ℝ := Finsupp.linearCombination ℤ (fun α : R => eval T_K α.1 w)
  have hker : LinearMap.ker Ψ ≤ LinearMap.ker ℓ₀ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    let χ : characterLattice T_K := Finsupp.linearCombination ℤ (fun α : R => α.1) c
    have hχ : χ ∈ Submodule.span ℤ R := by
      have h : χ ∈ Submodule.span ℤ (Set.range fun α : R => (α : characterLattice T_K)) := by
        rw [← Finsupp.range_linearCombination]
        exact LinearMap.mem_range_self _ c
      have hr : (Set.range fun α : R => (α : characterLattice T_K)) = R := Subtype.range_coe
      rwa [hr] at h
    have hres : characterRestrict ((GroupScheme.baseChange b).map
        (CommGroupScheme.groupHom t)) χ = 0 := by
      have h := Finsupp.apply_linearCombination ℤ ρ (fun α : R => α.1) c
      exact h.trans hc
    have he := eval_eq_zero_of_characterRestrict_eq_zero ht hT hw hχ hres
    rw [← evalAt_apply, Finsupp.apply_linearCombination] at he
    have hf : (evalAt K T_K w ∘ fun α : R => (α : characterLattice T_K)) =
        fun α : R => eval T_K α.1 w := funext fun α => evalAt_apply K T_K w α.1
    rw [hf] at he
    exact he
  let ℓ₁ : LinearMap.range Ψ →ₗ[ℤ] ℝ :=
    (LinearMap.ker Ψ).liftQ ℓ₀ hker ∘ₗ (Ψ.quotKerEquivRange).symm.toLinearMap
  have hℓ₁ : ∀ c, ℓ₁ ⟨Ψ c, LinearMap.mem_range_self Ψ c⟩ = ℓ₀ c := by
    intro c
    simp only [ℓ₁, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  obtain ⟨ℓ, hℓ⟩ := (Module.Baer.of_divisible ℝ).extension_property
    (LinearMap.range Ψ).subtype Subtype.val_injective ℓ₁
  have hp := isPerfPair_of_isSplitTorus (T := (CommGroupScheme.baseChange b).obj S)
    (hS.baseChange b)
  obtain ⟨u, hu⟩ := (LinearMap.IsPerfPair.bijective_right (pair _)).2 (ℓ.liftBaseChange ℝ)
  refine ⟨(splitCocharacterBaseChange (K := K) S hS).symm u, ?_⟩
  have hdesc : descentCocharacterMap k K t hS
      ((splitCocharacterBaseChange (K := K) S hS).symm u) = cocharacterMapReal tK u := by
    change cocharacterMapReal tK (splitCocharacterBaseChange (K := K) S hS
      ((splitCocharacterBaseChange (K := K) S hS).symm u)) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [hdesc, mem_rootAnnihilator]
  intro α hα
  rw [map_sub, sub_eq_zero, eval_eq_pair, pair_cocharacterMapReal,
    rationalCharacterRestrictReal_tmul]
  have hpu := LinearMap.congr_fun hu (1 ⊗ₜ[ℤ] ρ α)
  rw [LinearMap.flip_apply] at hpu
  change _ = pair _ (1 ⊗ₜ[ℤ] ρ α) u
  rw [hpu, LinearMap.liftBaseChange_one_tmul]
  have h1 := LinearMap.congr_fun hℓ ⟨Ψ (Finsupp.single ⟨α, hα⟩ 1),
    LinearMap.mem_range_self Ψ _⟩
  rw [LinearMap.comp_apply, Submodule.subtype_apply, hℓ₁] at h1
  simp only [Ψ, ℓ₀, Finsupp.linearCombination_single, one_smul] at h1
  rw [← eval_eq_pair]
  exact h1.symm

end Descent

section ApartmentTorsor

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {jT : T.toGrp ⟶ G}

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) jT

private instance torsorExtendedAffine :
    IsAffineHom (GaloisPointComparison.baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance torsorExtendedSmooth [Smooth G.X.hom] :
    Smooth (GaloisPointComparison.baseChanged k K G).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) jT).hom.hom.left]

/-- **Galois-fixed apartment points differ by descended translations.** Let `K/k` be Galois,
`t : S → T` the largest split subtorus of an affine `k`-torus of finite type, and `jT : T → G`
with finitely many roots of `T_K`. Two `Aut(K/k)`-fixed points of an apartment class over `K`
differ by the push-forward of a real cocharacter of `S`. -/
theorem KPApartmentData.exists_descent_vadd_of_galoisFixed [IsGalois k K]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [Finite (relativeRoots (T := T_K) j_K)]
    (hS : IsSplitTorus S.toGrp) {t : S ⟶ T}
    (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t)) (hT : IsTorus T.toGrp)
    {ω : Kˣ → ℝ} (D : KPApartmentData (S := T_K) j_K ω) (x y : D.Apartment)
    (hx : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ x.val = x.val)
    (hy : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ y.val = y.val) :
    ∃ v : V S, y.val = descentCocharacterMap k K t hS v +ᵥ x.val := by
  obtain ⟨w, hw⟩ := D.equipollent_of_mem x.mem y.mem
  have hσ : ∀ σ : K ≃ₐ[k] K,
      galoisCocharacterAction k K T σ w - w ∈ rootAnnihilator (S := T_K) j_K := by
    intro σ
    have h := hy σ
    rw [hw, RootFunctionFamily.galoisAction_vadd, hx σ] at h
    exact x.isValuation.vadd_eq_vadd_iff.1 h
  obtain ⟨v, hv⟩ := exists_descentCocharacterMap_sub_mem_of_isGalois hS ht hT w hσ
  exact ⟨v, hw.trans (x.isValuation.vadd_eq_vadd_iff.2 hv)⟩

variable [Smooth G.X.hom]

/-- Torus-then-field restriction turns a descended translation into the original translation. -/
theorem torusFieldRestricted_eq_vadd_of_eq_descent_vadd (hS : IsSplitTorus S.toGrp)
    (hTK : IsSplitTorus (T_K).toGrp) (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K)
    {φ ψ : RootFunctionFamily T_K (GaloisPointComparison.baseChanged k K G)}
    (hφ : IsRootDatumValuation (S := T_K) j_K φ) (hψ : IsRootDatumValuation (S := T_K) j_K ψ)
    {t : S ⟶ T} (v : V S) (h : ψ = descentCocharacterMap k K t hS v +ᵥ φ) :
    torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hTK hE hψ
        ((CommGroupScheme.baseChange b).map t) =
      v +ᵥ torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hTK hE hφ
        ((CommGroupScheme.baseChange b).map t) := by
  unfold torusFieldRestrictedRootFunctionFamily
  rw [torusRestrictedRootFunctionFamily_congr (hS.baseChange b) hTK hE h hψ
    (hφ.vadd (cocharacterMapReal ((CommGroupScheme.baseChange b).map t)
      (splitCocharacterBaseChange (K := K) S hS v))) ((CommGroupScheme.baseChange b).map t),
    torusRestrictedRootFunctionFamily_vadd (hS.baseChange b) hTK hE hφ
      ((CommGroupScheme.baseChange b).map t) (splitCocharacterBaseChange (K := K) S hS v)]
  exact RootFunctionFamily.fieldRestrict_vadd hS _ v

/-- If an original translation fixes the torus-then-field restriction of a valuation upstairs,
its push-forward lies in the common annihilator of the roots upstairs. -/
theorem descentCocharacterMap_mem_rootAnnihilator_of_vadd_eq (iS : S.toGrp ⟶ G)
    (hS : IsSplitTorus S.toGrp) (hTK : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K)
    {φ : RootFunctionFamily T_K (GaloisPointComparison.baseChanged k K G)}
    (hφ : IsRootDatumValuation (S := T_K) j_K φ) {t : S ⟶ T}
    (hfactor : CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map t) ≫ j_K =
      (GroupScheme.baseChange b).map iS)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible (S := T_K) j_K (fun s => (ω s).toAdd) φ)
    (hω : ∃ s : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom s)).toAdd ≠ 0) (v : V S)
    (hv : v +ᵥ torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hTK hE hφ
        ((CommGroupScheme.baseChange b).map t) =
      torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hTK hE hφ
        ((CommGroupScheme.baseChange b).map t)) :
    descentCocharacterMap k K t hS v ∈ rootAnnihilator (S := T_K) j_K := by
  rw [mem_rootAnnihilator]
  intro α hα
  rw [eval_descentCocharacterMap]
  by_cases h0 : (CommGroupScheme.baseChange b).map t ≫ α = 0
  · rw [h0, ← evalAt_apply, map_zero]
  have hroot : (CommGroupScheme.baseChange b).map t ≫ α ∈
      relativeRoots ((GroupScheme.baseChange b).map iS) := by
    rw [← hfactor, mem_relativeRoots]
    rw [mem_relativeRoots] at hα
    refine ⟨h0, fun hbot => hα.2 ?_⟩
    exact eq_bot_iff.2 ((weightSpace_le_comp _ _ α).trans hbot.le)
  obtain ⟨a, ha⟩ := (hS.characterLattice_baseChange_bijective b S).2
    ((CommGroupScheme.baseChange b).map t ≫ α)
  have haR : a ∈ relativeRoots iS := by
    have := (mem_roots_baseChange_iff (K := K) G S hS iS a).1
    rw [ha] at this
    exact this hroot
  rw [← ha, eval_splitCocharacterBaseChange]
  have hinf := torusFieldRestrictedRootFunctionFamily_image_infinite iS hS hTK hE hφ
    ((CommGroupScheme.baseChange b).map t) hfactor ω hcompat hω haR
  obtain ⟨_, ⟨g, -, rfl⟩, hne⟩ := (Set.Infinite.nontrivial hinf).exists_ne ⊤
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  have hval := congrArg (fun ψ : RootFunctionFamily S G => ψ a g) hv
  simp only [RootFunctionFamily.vadd_apply, ← hr] at hval
  rw [← WithTop.coe_add, WithTop.coe_inj] at hval
  linarith

/-- **Injectivity on Galois-fixed points.** Under the hypotheses of
`KPApartmentData.exists_descent_vadd_of_galoisFixed`, two `Aut(K/k)`-fixed apartment points
with the same torus-then-field restriction are equal, when the order of `K` is a homomorphism
nontrivial on `k`. -/
theorem KPApartmentData.eq_of_torusFieldRestricted_eq [IsGalois k K]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [Finite (relativeRoots (T := T_K) j_K)]
    (iS : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) {t : S ⟶ T}
    (ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t)) (hT : IsTorus T.toGrp)
    (hTK : IsSplitTorus (T_K).toGrp) (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K)
    (hfactor : CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map t) ≫ j_K =
      (GroupScheme.baseChange b).map iS)
    {ω' : Kˣ → ℝ} (D : KPApartmentData (S := T_K) j_K ω') (ω : Kˣ →* Multiplicative ℝ)
    (hωω' : ∀ s, (ω s).toAdd = ω' s)
    (hω : ∃ s : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom s)).toAdd ≠ 0)
    (x y : D.Apartment)
    (hx : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ x.val = x.val)
    (hy : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ y.val = y.val)
    (hxy : torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hTK hE
        (D.isRootDatumValuation_of_mem x.mem) ((CommGroupScheme.baseChange b).map t) =
      torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hTK hE
        (D.isRootDatumValuation_of_mem y.mem) ((CommGroupScheme.baseChange b).map t)) :
    x = y := by
  obtain ⟨v, hv⟩ := D.exists_descent_vadd_of_galoisFixed hS ht hT x y hx hy
  have hcompat : IsSplitTorusCompatible (S := T_K) j_K (fun s => (ω s).toAdd) x.val := by
    have hfun : (fun s => (ω s).toAdd) = ω' := funext hωω'
    rw [hfun]
    exact x.isSplitTorusCompatible
  have hshift := torusFieldRestricted_eq_vadd_of_eq_descent_vadd hS hTK hE x.isValuation
    (D.isRootDatumValuation_of_mem y.mem) v hv
  rw [← hxy] at hshift
  have hmem := descentCocharacterMap_mem_rootAnnihilator_of_vadd_eq iS hS hTK hE
    x.isValuation hfactor ω hcompat hω v hshift.symm
  apply KPApartmentData.Apartment.ext
  rw [hv]
  exact (x.isValuation.vadd_eq_self_iff.2 hmem).symm

end ApartmentTorsor

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "𝕂" => inertiaFixedField F
local notation "bF" => algebraBaseMap F (inertiaFixedField F)

private instance unramifiedTorsorAffineHom {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] : IsAffineHom (GaloisPointComparison.baseChanged F 𝕂 G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bF)
  infer_instance

/-- **The torus `T` of KP §9.6.** If `S` is a maximal split torus of a connected reductive
`F`-group `G`, contained in `T`, and `T_K` is a maximal split torus of `G_K`, then `T` is an
affine torus of finite type and `S` is its largest split subtorus. -/
theorem unramifiedTorus_structure {G : GroupScheme (Spec (CommRingCat.of F))}
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom]
    {S T : CommGroupScheme (Spec (CommRingCat.of F))} {iS : S.toGrp ⟶ G}
    (hiS : IsMaximalSplitTorus iS) {iT : T.toGrp ⟶ G} {f : S ⟶ T}
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT)) :
    IsAffineHom T.toGrp.X.hom ∧ LocallyOfFiniteType T.toGrp.X.hom ∧ IsTorus T.toGrp ∧
      IsLargestSplitSubtorus (CommGroupScheme.groupHom f) := by
  have : Smooth G.X.hom := hG.smooth
  have hTK : IsAffineHom ((CommGroupScheme.baseChange bF).obj T).X.hom :=
    hiT.isSplitSubtorus.1.isAffineHom
  obtain ⟨h1, h2, h3⟩ := fieldExtension_fpqc F 𝕂
  have hTa : IsAffineHom T.X.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (f := T.X.hom) (g := bF) ⟨⟨h1, h2⟩, h3⟩ hTK
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Flat bF := h2
  have : Surjective bF := h1
  have hjc : IsClosedSubgroup iT :=
    IsClosedSubgroup.of_baseChange_of_isAffine bF hiT.isSplitSubtorus.2
  have : IsClosedImmersion iT.hom.hom.left := hjc
  have hlft : LocallyOfFiniteType T.X.hom := by
    rw [← Over.w iT.hom.hom]
    infer_instance
  have hT : IsTorus T.toGrp := IsTorus.of_baseChange (K := 𝕂) hiT.isSplitSubtorus.1.isTorus
  have hf' : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ iT) := hf ▸ hiS
  exact ⟨hTa, hlft, hT, (hf'.of_comp hjc).isLargestSplitSubtorus⟩

/-- **Torsor statement of KP §9.6.** Two `Aut(𝕂/F)`-fixed points of an apartment class of
`(G_K, T_K)` differ by the push-forward of a real cocharacter of the maximal split torus `S`. -/
theorem unramified_exists_descent_vadd_of_galoisFixed
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom]
    {S T : CommGroupScheme (Spec (CommRingCat.of F))} {iS : S.toGrp ⟶ G}
    (hiS : IsMaximalSplitTorus iS) {iT : T.toGrp ⟶ G} {f : S ⟶ T}
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT))
    [Mono ((GroupScheme.baseChange bF).map iT).hom.hom.left]
    {ω : 𝕂ˣ → ℝ} (D : KPApartmentData (S := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT) ω) (x y : D.Apartment)
    (hx : ∀ σ : 𝕂 ≃ₐ[F] 𝕂, RootFunctionFamily.galoisAction F 𝕂 T G σ x.val = x.val)
    (hy : ∀ σ : 𝕂 ≃ₐ[F] 𝕂, RootFunctionFamily.galoisAction F 𝕂 T G σ y.val = y.val) :
    ∃ v : V S, y.val = descentCocharacterMap F 𝕂 f hiS.isSplitSubtorus.1 v +ᵥ x.val := by
  obtain ⟨h1, h2, hT, ht⟩ := unramifiedTorus_structure hG hiS hf hiT
  have : Smooth G.X.hom := hG.smooth
  have : LocallyOfFiniteType (GaloisPointComparison.baseChanged F 𝕂 G).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom bF)
    infer_instance
  have : Finite (relativeRoots (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT)) :=
    (hiT.isSplitSubtorus.1.finite_relativeRoots _).to_subtype
  exact D.exists_descent_vadd_of_galoisFixed hiS.isSplitSubtorus.1 ht hT x y hx hy

/-- **Clause 3 of `UnramifiedValuationDescentStatement`.** The torus-then-field restriction is
injective on the `Aut(𝕂/F)`-fixed points of an apartment class for the order of `𝕂`. -/
theorem unramified_eq_of_torusFieldRestricted_eq
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {S T : CommGroupScheme (Spec (CommRingCat.of F))} {iS : S.toGrp ⟶ G}
    (hiS : IsMaximalSplitTorus iS) {iT : T.toGrp ⟶ G} {f : S ⟶ T}
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT))
    [Mono ((GroupScheme.baseChange bF).map iT).hom.hom.left]
    (hE : RelativeRoot.HasOppositeFactorPairs (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT))
    (D : KPApartmentData (S := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F))) (x y : D.Apartment)
    (hx : ∀ σ : 𝕂 ≃ₐ[F] 𝕂, RootFunctionFamily.galoisAction F 𝕂 T G σ x.val = x.val)
    (hy : ∀ σ : 𝕂 ≃ₐ[F] 𝕂, RootFunctionFamily.galoisAction F 𝕂 T G σ y.val = y.val)
    (hxy : torusFieldRestrictedRootFunctionFamily (k := F) (K := 𝕂)
        hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
        ((CommGroupScheme.baseChange bF).map f) =
      torusFieldRestrictedRootFunctionFamily (k := F) (K := 𝕂)
        hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem y.mem)
        ((CommGroupScheme.baseChange bF).map f)) :
    x = y := by
  obtain ⟨h1, h2, hT, ht⟩ := unramifiedTorus_structure hG hiS hf hiT
  have : LocallyOfFiniteType (GaloisPointComparison.baseChanged F 𝕂 G).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom bF)
    infer_instance
  have : Finite (relativeRoots (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT)) :=
    (hiT.isSplitSubtorus.1.finite_relativeRoots _).to_subtype
  have hfactor : CommGroupScheme.groupHom ((CommGroupScheme.baseChange bF).map f) ≫
      (GroupScheme.baseChange bF).map iT = (GroupScheme.baseChange bF).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  let ω : 𝕂ˣ →* Multiplicative ℝ :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom ℝ)).comp
      (IntegerValuation.orderUnits (MaximalUnramified.valuation F))
  have hω : ∃ s : Fˣ, (ω (Units.map (algebraMap F 𝕂).toMonoidHom s)).toAdd ≠ 0 := by
    obtain ⟨a, ha⟩ := Plancherel.fieldOrderUnits_surjective F (Multiplicative.ofAdd 1)
    refine ⟨a, ?_⟩
    change (((IntegerValuation.orderUnits (MaximalUnramified.valuation F)
      (Units.map (algebraMap F 𝕂).toMonoidHom a)).toAdd : ℤ) : ℝ) ≠ 0
    rw [MaximalUnramified.orderUnits_base_eq_fieldOrderUnits, ha]
    norm_num
  exact D.eq_of_torusFieldRestricted_eq iS hiS.isSplitSubtorus.1 ht hT hiT.isSplitSubtorus.1 hE
    hfactor ω (fun _ => rfl) hω x y hx hy hxy

end Unramified


end Langlands.Geometry.Building

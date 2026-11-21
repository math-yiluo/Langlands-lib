import Langlands.Global.AdelicIntertwiningRepresentativeStatement
import Langlands.Global.AdelicIntertwiningRightLeviRepresentative
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.Representation.Exponents.LeviNormalizerQuotientProof
import Langlands.Representation.Plancherel.SplitComponentNormRigidity

/-! # The intertwining operator depends only on the element of `W(P, Q)`

Proof of `IntertwiningRepresentativeIndependenceStatement`. Two presentations `(w₁, c₁)`,
`(w₂, c₂)` with the same parameter map give the automorphism `θ = c₂⁻¹ ∘ c₁` of `M`, which is
conjugation by `w₁⁻¹ w₂` on `M` and acts trivially on the characters of the split component
`A_M`. Hence `θ` is the identity on `A_M`, so `w₁⁻¹ w₂` centralizes `A_M` and is a rational
point of `M`. Right multiplication of the representative by a rational point of `P` does not
change the intertwining integral. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.GroupScheme

open CocharacterUniformizer

variable {k : Type u} [Field k]

/-- On a split torus `A`, a morphism `r : A → H` detects characters of `H` up to tensoring with
`ℂ`: if `1 ⊗ x = 1 ⊗ y` in `ℂ ⊗ X^*(H)`, then `x` and `y` restrict to the same character
of `A`. -/
theorem characterRestrict_eq_of_one_tmul_eq {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (hA : IsSplitTorus A.toGrp) {H : GroupScheme (Spec (CommRingCat.of k))}
    (r : A.toGrp ⟶ H) {x y : rationalCharacters H}
    (h : (1 : ℂ) ⊗ₜ[ℤ] x = (1 : ℂ) ⊗ₜ[ℤ] y) :
    characterRestrict r x = characterRestrict r y := by
  let := latticePairing_isPerfPair k A hA
  apply (rationalCharacters.equivCharacterLattice A).injective
  apply (LinearMap.IsPerfPair.bijective_left (latticePairing A)).injective
  apply LinearMap.ext
  intro ν
  let f : rationalCharacters H →ₗ[ℤ] ℤ :=
    (latticePairing A).flip ν ∘ₗ
      ((rationalCharacters.equivCharacterLattice A).toAddMonoidHom.comp
        (characterRestrict r)).toIntLinearMap
  have hf := congrArg (fun t => TensorProduct.rid ℤ ℂ (LinearMap.lTensor ℂ f t)) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, zsmul_eq_mul, mul_one] at hf
  exact Int.cast_injective hf

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {M : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom M.X.hom] {a : A.toGrp ⟶ M}

/-- An automorphism of a connected reductive group which fixes every rational character after
restriction to a split component induces the identity on that split component. -/
theorem IsSplitComponent.automorphismRestriction_eq_id_of_characters
    (hM : IsConnectedReductive M) (ha : IsSplitComponent a) (φ : M ≅ M)
    (hχ : ∀ χ : rationalCharacters M,
      characterRestrict (a ≫ φ.hom) χ = characterRestrict a χ) :
    ha.automorphismRestriction φ = 𝟙 A.toGrp := by
  let f := ha.automorphismRestriction φ
  have hf : f ≫ a = a ≫ φ.hom := ha.automorphismRestriction_comp φ
  have hres (χ : rationalCharacters M) :
      characterRestrict f (characterRestrict a χ) = characterRestrict a χ := by
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, hf]
    exact hχ χ
  let S := (characterRestrict a).range
  let : S.FiniteIndex := ha.finiteIndex_range_characterRestrict hM
  have hfix (ψ : rationalCharacters A.toGrp) : characterRestrict f ψ = ψ := by
    obtain ⟨χ, hχ⟩ := S.nsmul_index_mem ψ
    have he : S.index • characterRestrict f ψ = S.index • ψ := by
      rw [← map_nsmul, ← hχ]
      exact hres χ
    let := latticePairing_isPerfPair k A ha.1.1.1
    apply (rationalCharacters.equivCharacterLattice A).injective
    apply (LinearMap.IsPerfPair.bijective_left (latticePairing A)).injective
    apply LinearMap.ext
    intro c
    have hp := congrArg (fun ξ : rationalCharacters A.toGrp =>
      latticePairing A (rationalCharacters.equivCharacterLattice A ξ) c) he
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hp
    exact mul_left_cancel₀
      (Int.natCast_ne_zero.mpr (AddSubgroup.FiniteIndex.index_ne_zero (H := S))) hp
  have hfc : Additive.ofMul f = (𝟙 A : A ⟶ A) := by
    apply ha.1.1.1.hom_ext_characters
    intro χ
    have hc : (Additive.ofMul f : A ⟶ A) ≫ χ = χ :=
      congrArg (rationalCharacters.equivCharacterLattice A)
        (hfix ((rationalCharacters.equivCharacterLattice A).symm χ))
    rw [Category.id_comp]
    exact hc
  exact congrArg CommGroupScheme.groupHom hfc

/-- Character preservation fixes the inclusion of the split component. -/
theorem IsSplitComponent.comp_automorphism_eq_of_characters
    (hM : IsConnectedReductive M) (ha : IsSplitComponent a) (φ : M ≅ M)
    (hχ : ∀ χ : rationalCharacters M,
      characterRestrict (a ≫ φ.hom) χ = characterRestrict a χ) :
    a ≫ φ.hom = a := by
  rw [← ha.automorphismRestriction_comp φ,
    ha.automorphismRestriction_eq_id_of_characters hM φ hχ, Category.id_comp]

end Langlands.GroupScheme

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

section Coset

variable {F : Type u} [Field F]
  {G P M Q M' : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G} {l' : M' ⟶ Q} {π' : Q ⟶ M'}
  {w₁ w₂ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c₁ c₂ : M' ⟶ M}

/-- Two presentations of Weyl elements with the same parameter map differ by a rational point
of the source Levi: `w₂ = w₁ · y` with `y ∈ M(F)`. -/
theorem IsWeylConjugation.exists_levi_of_weylParameter_eq
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hπ' : l' ≫ π' = 𝟙 M')
    (hw₁ : IsWeylConjugation p l q l' w₁ c₁) (hw₂ : IsWeylConjugation p l q l' w₂ c₂)
    (hpar : weylParameter (F := F) l c₁ π' = weylParameter l c₂ π') :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ M.X,
      w₂ = w₁ * (y ≫ (l ≫ p).hom.hom) := by
  have := hw₁.isIso
  have := hw₂.isIso
  let : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  let θ : M ≅ M := (asIso c₂).symm ≪≫ asIso c₁
  have hθhom : θ.hom = inv c₂ ≫ c₁ := rfl
  -- `θ` is conjugation by `w₁⁻¹ w₂` on `M`.
  have hθ : θ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (w₁⁻¹ * w₂)).hom := by
    rw [hθhom, innerIso_mul_hom, innerIso_inv_hom, ← cancel_epi c₂]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [hw₁.comp_eq, reassoc_of% hw₂.comp_eq, Iso.inv_hom_id_assoc]
  obtain ⟨A, a, ha⟩ := (splitComponentStatement F M hl.isConnectedReductive).1
  obtain ⟨χ, hP⟩ := Aubert.General.RepresentedParabolic.exists_dynamicParabolic_isRepresentedBy hG hp
  obtain ⟨-, -, -, hZ⟩ := hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP ha
  -- `θ` fixes the characters of `M` restricted to `A`.
  have hchar : ∀ ψ : rationalCharacters M,
      characterRestrict (a ≫ θ.hom) ψ = characterRestrict a ψ := by
    intro ψ
    obtain ⟨χP, rfl⟩ := hl.characterRestrict_bijective.2 ψ
    have h1 : (1 : ℂ) ⊗ₜ[ℤ] characterRestrict (π' ≫ c₁ ≫ l) χP =
        (1 : ℂ) ⊗ₜ[ℤ] characterRestrict (π' ≫ c₂ ≫ l) χP := by
      simpa only [weylParameter_tmul] using LinearMap.congr_fun hpar ((1 : ℂ) ⊗ₜ[ℤ] χP)
    have key := characterRestrict_eq_of_one_tmul_eq ha.1.1.1 (a ≫ inv c₂ ≫ l') h1
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, ← AddMonoidHom.comp_apply,
      ← characterRestrict_comp] at key
    have e₁ : (a ≫ inv c₂ ≫ l') ≫ π' ≫ c₁ ≫ l = (a ≫ θ.hom) ≫ l := by
      rw [hθhom]
      simp only [Category.assoc, reassoc_of% hπ']
    have e₂ : (a ≫ inv c₂ ≫ l') ≫ π' ≫ c₂ ≫ l = a ≫ l := by
      simp only [Category.assoc, reassoc_of% hπ', IsIso.inv_hom_id_assoc]
    rw [e₁, e₂] at key
    simpa only [characterRestrict_comp, AddMonoidHom.comp_apply] using key
  have hfix : a ≫ θ.hom = a :=
    ha.comp_automorphism_eq_of_characters hl.isConnectedReductive θ hchar
  have hmem : w₁⁻¹ * w₂ ∈ (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) := by
    rw [← hZ, mem_torusCentralizer_base_iff]
    simp only [Category.assoc]
    rw [← hθ, ← Category.assoc, hfix]
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hmem
  exact ⟨y, by rw [hy, mul_inv_cancel_left]⟩

end Coset

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- **Mœglin–Waldspurger II.1.6 (i); Bernstein–Lapid §2.1–§2.2.** The intertwining operator
`M(w, λ)` depends only on the element of `W(P, Q)` presented by `(w, c)`. -/
theorem intertwiningRepresentativeIndependence :
    IntertwiningRepresentativeIndependenceStatement := by
  intro F _ _ G P M U Q M' V _ _ _ _ _ _ p _ iU l q _ iV l' _ π' w₁ w₂ c₁ c₂ hG hp hU hl _ _
    _ _ _ hπ' hw₁ hw₂ hpar K hK hK' N d rho hsmooth hcalc φ _ _ hφ lam g
  obtain ⟨y, hy⟩ := hw₁.exists_levi_of_weylParameter_eq hG hp hl hπ' hw₂ hpar
  unfold IsIwasawaCompact.intertwiningOperator
  rw [hpar]
  congr 1
  rw [hy]
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    (hK.intertwiningIntegral_mul_rational_parabolic (iV ≫ q) w₁ (y ≫ l.hom.hom) hl hU hφ.1
      lam g).symm

end Langlands.Global

import Langlands.GaloisCohomology.Global.Abelianization.SIdeleClassGroup
import Langlands.Galois.RestrictedRamification.ClosureChange
import Langlands.ClassFieldTheory.Global.Artin.ArtinMap
import Langlands.ClassFieldTheory.Global.Artin.ClassField
import Langlands.ClassFieldTheory.Global.Artin.FiniteArtinUnramified

/-!
# Characters of `G_S` and the `S`-idèle class group

For a number field `K`, a separable closure `Ω` of `K`, a finite set `S` of finite places of `K`
and `n ≠ 0`, this file proves that the continuous characters of `G_S = Gal(K_S / K)` with values in
`ℤ/n` are the homomorphisms from the narrow `S`-idèle class group `I_K / K^× U^S_+` to `ℤ/n`
(`continuousCharEquivNarrowSIdeleClass`), with no condition on `n` or on the real places; and, if
`n` is odd or `K` is totally complex, the homomorphisms from the `S`-idèle class group
`I_K / K^× U^S` (`continuousCharEquivSIdeleClass`). The groups are those of the module
`Langlands.GaloisCohomology.Global.Abelianization.SIdeleClassGroup`.

The isomorphism is built with the Library's global Artin map
`Langlands.ClassFieldTheory.Global.Artin.geometricArtinMap K : IdeleClasses K →ₜ*
Field.absoluteGaloisGroupAbelianization K`, which is in the **geometric** normalization: the
character of the idèles attached to `χ` is `x ↦ χ(σ|_{K_S})` for any `σ` whose image in the
abelianized absolute Galois group is `geometricArtinMap K x`
(`continuousCharEquivNarrowSIdeleClass_mk`).
The statements themselves involve only kernels and images, and do not depend on the normalization.

**Outline.** First for `Ω = AlgebraicClosure K`. A continuous character `χ` of `G_S`, read on the
absolute Galois group (`absoluteCharacter`), factors through the abelianization; composed with the
Artin map and the quotient map from the idèles it is a continuous character `ideleCharacter χ`
of the idèles. Its field `characterField χ` (the fixed field of its kernel) is a finite abelian
extension contained in `K_S`, hence unramified outside `S`; by the unit criterion
`arithmeticFiniteArtin_finiteClassInclusion_units_eq_one_iff` the Artin map of that field kills
the integral local units outside `S`, so `ideleCharacter χ` does
(`ideleCharacter_finiteIdeleInclusion`);
by `positiveUnitIdelesOutside_le_ker` it kills `U^S_+`, and it descends to the narrow `S`-idèle
class group (`narrowSIdeleClassCharacter`). The map `χ ↦ narrowSIdeleClassCharacter χ` is injective
because the Artin map is surjective. It is surjective for finite `S`: a homomorphism `ψ` to `ℤ/n`
kills `n`-th powers, so its kernel in the idèle class group is open
(`isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le`); the class field `E` of that kernel
(`classField`, the existence theorem) is unramified outside `S` by the unit criterion again, so
`E ⊆ K_S`, and `ψ` is `σ ↦ θ(σ|_E)⁻¹` with `θ ∘ arithmeticFiniteArtin K E = ψ` on idèle classes.
For a general separable closure `Ω` the characters are transported along an isomorphism
`AlgebraicClosure K ≃ₐ[K] Ω` (`galoisGroupUnramifiedOutsideCongr`, `continuousCharCongr`); the value
lemma holds for every isomorphism, because conjugation does not change images in the
abelianization (`absoluteAbelianizationProjection_autCongr_eq`).

## Main declarations

* `characterField χ`, finite abelian Galois and unramified outside `S` (`characterField_le`).
* `ideleCharacter χ`, `narrowSIdeleClassCharacter χ`, `narrowSIdeleClassCharacterHom`, with
  `narrowSIdeleClassCharacterHom_injective` and `narrowSIdeleClassCharacterHom_surjective`.
* `continuousCharEquivNarrowSIdeleClass`, `continuousCharEquivSIdeleClass` and their value lemmas
  `continuousCharEquivNarrowSIdeleClass_mk`, `continuousCharEquivSIdeleClass_mk`.

## References

Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter VIII, §3, p. 454 (the `S`-idèle
class group) and Theorem (8.3.13), p. 459 (`0 → D_S → C_S → G_S^ab → 0`); Neukirch, *Algebraic
Number Theory*, Chapter VI, Theorem (5.5) and Proposition (5.6), p. 391, Theorem (6.1), p. 395;
Chapter V, Proposition (1.7), p. 323.
-/

noncomputable section

universe u v

namespace Langlands.GaloisCohomology

open Langlands.Global Langlands.Galois Langlands.ClassFieldTheory.Global.Artin IsDedekindDomain
open scoped NumberField

section AlgebraicClosure

variable {K : Type u} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

/-- A continuous character of `G_S`, read on the absolute Galois group. -/
def absoluteCharacter
    (χ : GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) :
    Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod n) :=
  χ.comp (GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S)

/-- The value of `absoluteCharacter χ`. -/
theorem absoluteCharacter_apply
    (χ : GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))
    (σ : Gal(AlgebraicClosure K/K)) :
    absoluteCharacter χ σ =
      χ (GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S σ) :=
  rfl

variable (χ : GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n))

/-- The kernel of `absoluteCharacter χ` is open. -/
theorem isOpen_ker_absoluteCharacter :
    IsOpen ((absoluteCharacter χ : Gal(AlgebraicClosure K/K) →* Multiplicative (ZMod n)).ker :
      Set Gal(AlgebraicClosure K/K)) := by
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete {1}).preimage (absoluteCharacter χ).continuous

/-- The kernel of `absoluteCharacter χ` is closed. -/
theorem isClosed_ker_absoluteCharacter :
    IsClosed ((absoluteCharacter χ : Gal(AlgebraicClosure K/K) →* Multiplicative (ZMod n)).ker :
      Set Gal(AlgebraicClosure K/K)) := by
  rw [MonoidHom.coe_ker]
  exact (isClosed_discrete {1}).preimage (absoluteCharacter χ).continuous

/-- The finite abelian extension of `K` cut out by a continuous character `χ` of `G_S`: the fixed
field in `AlgebraicClosure K` of the kernel of `χ` read on the absolute Galois group. -/
def characterField : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField
    (absoluteCharacter χ : Gal(AlgebraicClosure K/K) →* Multiplicative (ZMod n)).ker

/-- The fixing subgroup of the field of `χ` is the kernel of `absoluteCharacter χ`. -/
theorem fixingSubgroup_characterField :
    (characterField χ).fixingSubgroup =
      (absoluteCharacter χ : Gal(AlgebraicClosure K/K) →* Multiplicative (ZMod n)).ker :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨_, isClosed_ker_absoluteCharacter χ⟩

/-- The field of `χ` is finite over `K`. -/
instance finiteDimensional_characterField : FiniteDimensional K (characterField χ) :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by
    rw [fixingSubgroup_characterField]
    exact isOpen_ker_absoluteCharacter χ)

/-- The field of `χ` is Galois over `K`. -/
instance isGalois_characterField : IsGalois K (characterField χ) :=
  IsGalois.of_fixedField_normal_subgroup _

/-- `χ σ` depends only on the restriction of `σ` to the field of `χ`. -/
theorem absoluteCharacter_eq_one_iff (σ : Gal(AlgebraicClosure K/K)) :
    absoluteCharacter χ σ = 1 ↔
      AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure K) (characterField χ) σ = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, fixingSubgroup_characterField]
  rfl

/-- The field of `χ` is abelian over `K`. -/
instance isAbelianGalois_characterField : IsAbelianGalois K (characterField χ) := by
  have : IsMulCommutative (characterField χ ≃ₐ[K] characterField χ) := ⟨⟨fun τ₁ τ₂ => by
    obtain ⟨g₁, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := AlgebraicClosure K) τ₁
    obtain ⟨g₂, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := AlgebraicClosure K) τ₂
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      ← absoluteCharacter_eq_one_iff χ (g₁ * g₂ * (g₂ * g₁)⁻¹), map_mul, map_inv, map_mul,
      map_mul]
    exact mul_inv_eq_one.2 (mul_comm _ _)⟩⟩
  exact ⟨⟩

/-- The field of a character of `G_S` lies in the maximal extension unramified outside `S`. -/
theorem characterField_le :
    characterField χ ≤ maximalUnramifiedOutside K (AlgebraicClosure K) S := by
  intro x hx
  rw [← InfiniteGalois.fixedField_fixingSubgroup
    (maximalUnramifiedOutside K (AlgebraicClosure K) S), IntermediateField.mem_fixedField_iff]
  intro g hg
  have h1 : GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S g = 1 := by
    change AlgEquiv.restrictNormalHom (maximalUnramifiedOutside K (AlgebraicClosure K) S) g = 1
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hg
  have h2 : absoluteCharacter χ g = 1 := by rw [absoluteCharacter_apply, h1, map_one]
  exact (IntermediateField.mem_fixedField_iff _ _).1 hx g h2

/-- The field of a character of `G_S` is unramified outside `S`. -/
theorem isUnramifiedOutside_characterField : IsUnramifiedOutside S (characterField χ) :=
  (isUnramifiedOutside_iff_le S).2 (characterField_le χ)

/-- The character of the idèles attached to a continuous character `χ` of `G_S`: `χ` of the
restriction to `K_S` of any element of the absolute Galois group whose image in the abelianization
is the image of the idèle under the global Artin map `geometricArtinMap K`
(`ideleCharacter_apply`). -/
def ideleCharacter : Ideles K →ₜ* Multiplicative (ZMod n) :=
  ((LocalClassField.abelianizationLift
    (show Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod n) from absoluteCharacter χ)).comp
      (geometricArtinMap K)).comp (ideleClassMap K)

/-- The value of `ideleCharacter χ` at an idèle `x`: `χ` of the restriction to `K_S` of any `σ`
lifting `geometricArtinMap K x`. -/
theorem ideleCharacter_apply (x : Ideles K) (σ : Gal(AlgebraicClosure K/K))
    (hσ : LocalClassField.absoluteAbelianizationProjection K σ =
      geometricArtinMap K (ideleClassMap K x)) :
    ideleCharacter χ x =
      χ (GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S σ) := by
  change LocalClassField.abelianizationLift
    (show Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod n) from absoluteCharacter χ)
      (geometricArtinMap K (ideleClassMap K x)) = _
  rw [← hσ]
  rfl

/-- Every value of the Artin map lifts to the absolute Galois group. -/
theorem exists_absoluteAbelianizationProjection_eq (x : IdeleClasses K) :
    ∃ σ : Gal(AlgebraicClosure K/K),
      LocalClassField.absoluteAbelianizationProjection K σ = geometricArtinMap K x :=
  QuotientGroup.mk'_surjective _ (geometricArtinMap K x)

/-- The idèle character of a character of `G_S` kills the integral local units at every finite
place outside `S`: the field of the character is unramified there. -/
theorem ideleCharacter_finiteIdeleInclusion {v : FinitePlace K} (hv : v ∉ S)
    {a : (FiniteCompletion K v)ˣ}
    (ha : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    ideleCharacter χ (finiteIdeleInclusion K v a) = 1 := by
  obtain ⟨σ, hσ⟩ := exists_absoluteAbelianizationProjection_eq (finiteClassInclusion K v a)
  rw [ideleCharacter_apply χ (finiteIdeleInclusion K v a) σ hσ, ← absoluteCharacter_apply,
    absoluteCharacter_eq_one_iff]
  let := NumberField.of_module_finite K (characterField χ)
  have hres := restrictNormalHom_eq_inv_arithmeticFiniteArtin (characterField χ)
    (finiteClassInclusion K v a) σ hσ
  have h1 : arithmeticFiniteArtin K (characterField χ) (finiteClassInclusion K v a) = 1 :=
    (arithmeticFiniteArtin_finiteClassInclusion_units_eq_one_iff v).2
      (fun w hw => isUnramifiedOutside_characterField χ v hv w.asIdeal w.isPrime hw) a ha
  rw [hres, h1, inv_one]

variable [NeZero n]

/-- `ideleCharacter χ` kills `K^× U^S_+`. -/
theorem narrowSIdeleClassSubgroup_le_ker_ideleCharacter :
    narrowSIdeleClassSubgroup S ≤ (ideleCharacter χ : Ideles K →* Multiplicative (ZMod n)).ker := by
  refine sup_le ?_ ?_
  · rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    change LocalClassField.abelianizationLift
      (show Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod n) from absoluteCharacter χ)
        (geometricArtinMap K (ideleClassMap K (diagonalUnits K a))) = 1
    rw [ideleClassMap_diagonalUnits, map_one, map_one]
  · exact positiveUnitIdelesOutside_le_ker (ideleCharacter χ) (NeZero.ne n) zmod_pow_eq_one
      fun v hv a ha => ideleCharacter_finiteIdeleInclusion χ hv ha

/-- The character of the narrow `S`-idèle class group attached to a continuous character `χ` of
`G_S` (for `Ω = AlgebraicClosure K`). -/
def narrowSIdeleClassCharacter : NarrowSIdeleClassGroup S →* Multiplicative (ZMod n) :=
  QuotientGroup.lift _ (ideleCharacter χ : Ideles K →* Multiplicative (ZMod n))
    (narrowSIdeleClassSubgroup_le_ker_ideleCharacter χ)

/-- The value of `narrowSIdeleClassCharacter χ` on the class of an idèle `x`. -/
theorem narrowSIdeleClassCharacter_mk (x : Ideles K) (σ : Gal(AlgebraicClosure K/K))
    (hσ : LocalClassField.absoluteAbelianizationProjection K σ =
      geometricArtinMap K (ideleClassMap K x)) :
    narrowSIdeleClassCharacter χ (NarrowSIdeleClassGroup.mk S x) =
      χ (GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S σ) :=
  ideleCharacter_apply χ x σ hσ

variable (K S n) in
/-- `χ ↦ narrowSIdeleClassCharacter χ`, as a homomorphism of groups. -/
def narrowSIdeleClassCharacterHom :
    (GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →ₜ* Multiplicative (ZMod n)) →*
      (NarrowSIdeleClassGroup S →* Multiplicative (ZMod n)) where
  toFun χ := narrowSIdeleClassCharacter χ
  map_one' := NarrowSIdeleClassGroup.hom_ext S fun x => by
    obtain ⟨σ, hσ⟩ := exists_absoluteAbelianizationProjection_eq (ideleClassMap K x)
    rw [narrowSIdeleClassCharacter_mk _ x σ hσ]
    rfl
  map_mul' χ₁ χ₂ := NarrowSIdeleClassGroup.hom_ext S fun x => by
    obtain ⟨σ, hσ⟩ := exists_absoluteAbelianizationProjection_eq (ideleClassMap K x)
    rw [MonoidHom.mul_apply, narrowSIdeleClassCharacter_mk _ x σ hσ,
      narrowSIdeleClassCharacter_mk _ x σ hσ, narrowSIdeleClassCharacter_mk _ x σ hσ]
    rfl

/-- The value of `narrowSIdeleClassCharacterHom`. -/
theorem narrowSIdeleClassCharacterHom_apply :
    narrowSIdeleClassCharacterHom K S n χ = narrowSIdeleClassCharacter χ :=
  rfl

/-- `narrowSIdeleClassCharacterHom` is injective: the Artin map is surjective. -/
theorem narrowSIdeleClassCharacterHom_injective :
    Function.Injective (narrowSIdeleClassCharacterHom K S n) := by
  rw [injective_iff_map_eq_one]
  intro χ hχ
  refine ContinuousMonoidHom.ext fun τ => ?_
  obtain ⟨σ, rfl⟩ := GaloisGroupUnramifiedOutside.quotientMap_surjective K (AlgebraicClosure K) S τ
  obtain ⟨c, hc⟩ := geometricArtinMap_surjective K
    (LocalClassField.absoluteAbelianizationProjection K σ)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (principalIdeles K) c
  rw [← narrowSIdeleClassCharacter_mk χ x σ hc.symm]
  exact DFunLike.congr_fun hχ (NarrowSIdeleClassGroup.mk S x)

/-- For finite `S`, every homomorphism from the narrow `S`-idèle class group to `ℤ/n` comes from
a continuous character of `G_S`. Its kernel in the idèle class group is open (it contains the
`n`-th powers and the image of `positiveUnitIdelesOutside S`), so it is the kernel of the Artin map
of its class field `E` (`classField`); `E` is unramified outside `S` because the integral local
units outside `S` lie in that kernel, hence `E ⊆ K_S`; the character is `σ ↦ θ(σ|_E)⁻¹`, where
`θ ∘ arithmeticFiniteArtin K E` is the given homomorphism on idèle classes. -/
theorem narrowSIdeleClassCharacterHom_surjective (hS : S.Finite) :
    Function.Surjective (narrowSIdeleClassCharacterHom K S n) := by
  intro ψ
  have hn : n ≠ 0 := NeZero.ne n
  set Ψ : IdeleClasses K →* Multiplicative (ZMod n) :=
    ψ.comp (NarrowSIdeleClassGroup.ofIdeleClasses S) with hΨ
  have hN : IsOpen ((ψ.comp (NarrowSIdeleClassGroup.mk S)).ker : Set (Ideles K)) :=
    isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le hS hn _
      (fun x => by rw [MonoidHom.mem_ker, map_pow]; exact zmod_pow_eq_one _)
      (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, NarrowSIdeleClassGroup.mk_eq_one_of_mem hx,
          map_one])
  have hH : IsOpen (Ψ.ker : Set (IdeleClasses K)) := by
    rw [← (QuotientGroup.isQuotientMap_mk (principalIdeles K)).isOpen_preimage]
    exact hN
  let H : OpenSubgroup (IdeleClasses K) := ⟨Ψ.ker, hH⟩
  let E : IntermediateField K (AlgebraicClosure K) := classField K H
  let := NumberField.of_module_finite K E
  have hker : (arithmeticFiniteArtin K E).ker = Ψ.ker := arithmeticFiniteArtin_classField_ker K H
  have hEu : IsUnramifiedOutside S E := by
    intro v hv P hP hPv
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    refine (arithmeticFiniteArtin_finiteClassInclusion_units_eq_one_iff (L := E) v).1
      (fun a ha => ?_) ⟨P, hP, hP0⟩ hPv
    rw [← MonoidHom.mem_ker, hker, MonoidHom.mem_ker]
    change ψ (NarrowSIdeleClassGroup.mk S (finiteIdeleInclusion K v a)) = 1
    rw [NarrowSIdeleClassGroup.mk_eq_one_of_mem
      (finiteIdeleInclusion_mem_positiveUnitIdelesOutside hv ha), map_one]
  have hES : E ≤ maximalUnramifiedOutside K (AlgebraicClosure K) S :=
    (isUnramifiedOutside_iff_le S).1 hEu
  have hA := arithmeticFiniteArtin_surjective K E
  let θ : (E ≃ₐ[K] E) →* Multiplicative (ZMod n) :=
    (arithmeticFiniteArtin K E).liftOfRightInverse (Function.surjInv hA)
      (Function.rightInverse_surjInv hA) ⟨Ψ, hker.le⟩
  have hθ : ∀ c, θ (arithmeticFiniteArtin K E c) = Ψ c := fun c =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
  let χ' : Gal(AlgebraicClosure K/K) →* Multiplicative (ZMod n) :=
    (θ.comp (AlgEquiv.restrictNormalHom E))⁻¹
  have hχ'c : Continuous χ' := by
    change Continuous fun σ => (θ (AlgEquiv.restrictNormalHom E σ))⁻¹
    exact continuous_inv.comp ((continuous_of_discreteTopology (f := ⇑θ)).comp
      (InfiniteGalois.restrictNormalHom_continuous E))
  have hkerq : (GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S :
      Gal(AlgebraicClosure K/K) →* GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S).ker ≤
        χ'.ker := by
    intro g hg
    have hg' : g ∈ (maximalUnramifiedOutside K (AlgebraicClosure K) S).fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hg
    have h1 : AlgEquiv.restrictNormalHom E g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
      exact IntermediateField.fixingSubgroup_antitone hES hg'
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, MonoidHom.comp_apply, h1, map_one, inv_one]
  let χS : GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S →* Multiplicative (ZMod n) :=
    (GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S :
      Gal(AlgebraicClosure K/K) →* GaloisGroupUnramifiedOutside K (AlgebraicClosure K) S
      ).liftOfRightInverse GaloisGroupUnramifiedOutside.lift
        GaloisGroupUnramifiedOutside.quotientMap_lift ⟨χ', hkerq⟩
  have hχS : ∀ g, χS (GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S g) = χ' g :=
    fun g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hcont : Continuous χS := by
    rw [(GaloisGroupUnramifiedOutside.isQuotientMap_quotientMap K (AlgebraicClosure K)
      S).continuous_iff]
    have : (⇑χS ∘ ⇑(GaloisGroupUnramifiedOutside.quotientMap K (AlgebraicClosure K) S)) = ⇑χ' :=
      funext hχS
    rw [this]
    exact hχ'c
  refine ⟨⟨χS, hcont⟩, NarrowSIdeleClassGroup.hom_ext S fun x => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_absoluteAbelianizationProjection_eq (ideleClassMap K x)
  rw [narrowSIdeleClassCharacterHom_apply, narrowSIdeleClassCharacter_mk _ x σ hσ]
  change χS _ = _
  rw [hχS, MonoidHom.inv_apply, MonoidHom.comp_apply,
    restrictNormalHom_eq_inv_arithmeticFiniteArtin E (ideleClassMap K x) σ hσ, map_inv, inv_inv,
    hθ]
  rfl

end AlgebraicClosure

section Precomposition

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- Precomposition with an isomorphism of topological groups, on continuous characters with
values in `ℤ/n`. -/
def continuousCharCongr (f : G ≃ₜ* H) (n : ℕ) :
    ContinuousMonoidHom H (Multiplicative (ZMod n)) ≃*
      ContinuousMonoidHom G (Multiplicative (ZMod n)) where
  toFun χ := χ.comp ⟨f.toMulEquiv.toMonoidHom, f.continuous⟩
  invFun χ := χ.comp ⟨f.symm.toMulEquiv.toMonoidHom, f.symm.continuous⟩
  left_inv χ := ContinuousMonoidHom.ext fun x => congrArg χ (f.apply_symm_apply x)
  right_inv χ := ContinuousMonoidHom.ext fun x => congrArg χ (f.symm_apply_apply x)
  map_mul' _ _ := rfl

/-- The value of `continuousCharCongr f n χ`. -/
theorem continuousCharCongr_apply (f : G ≃ₜ* H) (n : ℕ)
    (χ : ContinuousMonoidHom H (Multiplicative (ZMod n))) (x : G) :
    continuousCharCongr f n χ x = χ (f x) :=
  rfl

end Precomposition

section SeparableClosure

variable {K : Type u} [Field K] [NumberField K] (Ω : Type v) [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **Characters of `G_S` by narrow `S`-idèle classes.** For a number field `K`, a separable
closure `Ω` of `K`, a finite set `S` of finite places of `K` and `n ≠ 0`, the continuous
characters of `G_S = Gal(K_S / K)` with values in `ℤ/n` correspond to the homomorphisms from the
narrow `S`-idèle class group `I_K / K^× U^S_+` to `ℤ/n`: a character `χ` goes to
`x ↦ χ(σ|_{K_S})` for `σ` with image `geometricArtinMap K x` in the abelianized absolute Galois
group (`continuousCharEquivNarrowSIdeleClass_mk`). No condition on `n` or on the real places. -/
def continuousCharEquivNarrowSIdeleClass (hS : S.Finite) (n : ℕ) [NeZero n] :
    ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) ≃*
      (NarrowSIdeleClassGroup S →* Multiplicative (ZMod n)) :=
  (continuousCharCongr
      (galoisGroupUnramifiedOutsideCongr S (IsSepClosure.equiv K (AlgebraicClosure K) Ω)) n).trans
    (MulEquiv.ofBijective (narrowSIdeleClassCharacterHom K S n)
      ⟨narrowSIdeleClassCharacterHom_injective, narrowSIdeleClassCharacterHom_surjective hS⟩)

omit [NumberField K] in
/-- Conjugation by an isomorphism of algebraic closures does not change the image of an element of
the absolute Galois group in the abelianization. -/
theorem absoluteAbelianizationProjection_autCongr_eq {Ω : Type v} [Field Ω] [Algebra K Ω]
    (e e' : Ω ≃ₐ[K] AlgebraicClosure K) (σ : Gal(Ω/K)) :
    LocalClassField.absoluteAbelianizationProjection K (e.autCongr σ) =
      LocalClassField.absoluteAbelianizationProjection K (e'.autCongr σ) := by
  have h : (e.autCongr σ : Gal(AlgebraicClosure K/K)) =
      (e'.symm.trans e) * e'.autCongr σ * (e'.symm.trans e)⁻¹ := by
    ext x
    simp [AlgEquiv.autCongr_apply, AlgEquiv.mul_apply]
  let π : Gal(AlgebraicClosure K/K) →* Field.absoluteGaloisGroupAbelianization K :=
    (LocalClassField.absoluteAbelianizationProjection K).toMonoidHom
  change π (e.autCongr σ) = π (e'.autCongr σ)
  rw [h, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/-- The value of `continuousCharEquivNarrowSIdeleClass` on the class of an idèle `x`: `χ` of the
restriction to `K_S` of any `σ ∈ Gal(Ω / K)` whose conjugate into `AlgebraicClosure K`, by any
isomorphism `e`, maps to `geometricArtinMap K x` in the abelianization. -/
theorem continuousCharEquivNarrowSIdeleClass_mk (hS : S.Finite) (n : ℕ) [NeZero n]
    (χ : ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (x : Ideles K) (e : Ω ≃ₐ[K] AlgebraicClosure K) (σ : Gal(Ω/K))
    (hσ : LocalClassField.absoluteAbelianizationProjection K (e.autCongr σ) =
      geometricArtinMap K (ideleClassMap K x)) :
    continuousCharEquivNarrowSIdeleClass Ω hS n χ (NarrowSIdeleClassGroup.mk S x) =
      χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S σ) := by
  have hσ₀ : LocalClassField.absoluteAbelianizationProjection K
      ((IsSepClosure.equiv K (AlgebraicClosure K) Ω).symm.autCongr σ) =
        geometricArtinMap K (ideleClassMap K x) := by
    rw [absoluteAbelianizationProjection_autCongr_eq _ e σ, hσ]
  change narrowSIdeleClassCharacter (continuousCharCongr _ n χ) (NarrowSIdeleClassGroup.mk S x) = _
  rw [narrowSIdeleClassCharacter_mk _ x _ hσ₀, continuousCharCongr_apply,
    galoisGroupUnramifiedOutsideCongr_quotientMap]
  congr 2
  ext y
  simp [AlgEquiv.autCongr_apply]

/-- **Characters of `G_S` by `S`-idèle classes.** For a number field `K`, a separable closure `Ω`
of `K`, a finite set `S` of finite places of `K` and `n ≠ 0` with `n` odd or `K` totally complex,
the continuous characters of `G_S = Gal(K_S / K)` with values in `ℤ/n` correspond to the
homomorphisms from the `S`-idèle class group `I_K / K^× U^S` to `ℤ/n`
(`continuousCharEquivSIdeleClass_mk`). -/
def continuousCharEquivSIdeleClass (hS : S.Finite) {n : ℕ} [NeZero n]
    (h : Odd n ∨ NumberField.IsTotallyComplex K) :
    ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) ≃*
      (SIdeleClassGroup S →* Multiplicative (ZMod n)) :=
  (continuousCharEquivNarrowSIdeleClass Ω hS n).trans
    (NarrowSIdeleClassGroup.precompToSIdeleClassGroupEquiv S n h).symm

/-- Read on the narrow group, `continuousCharEquivSIdeleClass` is
`continuousCharEquivNarrowSIdeleClass`. -/
theorem precompToSIdeleClassGroup_continuousCharEquivSIdeleClass (hS : S.Finite) {n : ℕ}
    [NeZero n] (h : Odd n ∨ NumberField.IsTotallyComplex K)
    (χ : ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n))) :
    NarrowSIdeleClassGroup.precompToSIdeleClassGroup S n (continuousCharEquivSIdeleClass Ω hS h χ) =
      continuousCharEquivNarrowSIdeleClass Ω hS n χ :=
  (NarrowSIdeleClassGroup.precompToSIdeleClassGroupEquiv S n h).apply_symm_apply _

/-- The value of `continuousCharEquivSIdeleClass` on the class of an idèle `x`: `χ` of the
restriction to `K_S` of any `σ ∈ Gal(Ω / K)` whose conjugate into `AlgebraicClosure K` maps to
`geometricArtinMap K x` in the abelianization. -/
theorem continuousCharEquivSIdeleClass_mk (hS : S.Finite) {n : ℕ} [NeZero n]
    (h : Odd n ∨ NumberField.IsTotallyComplex K)
    (χ : ContinuousMonoidHom (GaloisGroupUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (x : Ideles K) (e : Ω ≃ₐ[K] AlgebraicClosure K) (σ : Gal(Ω/K))
    (hσ : LocalClassField.absoluteAbelianizationProjection K (e.autCongr σ) =
      geometricArtinMap K (ideleClassMap K x)) :
    continuousCharEquivSIdeleClass Ω hS h χ (SIdeleClassGroup.mk S x) =
      χ (GaloisGroupUnramifiedOutside.quotientMap K Ω S σ) := by
  rw [← NarrowSIdeleClassGroup.precompToSIdeleClassGroup_apply_mk,
    precompToSIdeleClassGroup_continuousCharEquivSIdeleClass,
    continuousCharEquivNarrowSIdeleClass_mk Ω hS n χ x e σ hσ]

end SeparableClosure

end Langlands.GaloisCohomology

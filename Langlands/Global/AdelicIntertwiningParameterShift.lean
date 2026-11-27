import Langlands.Global.AdelicIntertwiningRightLeviRepresentative
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Global.AdelicWeylParameterEquivalence

/-! # Intertwining operators are invariant under parameters of an ambient parabolic

Let `P` and `Q` be closed subgroups of `G` contained in a closed subgroup `L`, through
`eP : P → L` and `eQ : Q → L`, and let `(w, c)` present a Weyl conjugation from `P` to `Q` with
`w` a rational point of `L`. For a parameter `ν ∈ X^*(L) ⊗ ℂ`, restricted to `P` along `eP`,
the intertwining operator satisfies `M(w, λ + ν|_P) = M(w, λ)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]

section Heights

variable {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {K : Subgroup (AdelicGroupPoints F G)}

variable {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- Height powers are multiplicative in the parameter. -/
theorem IsIwasawaCompact.heightPower_add' (hK : IsIwasawaCompact p K)
    (s t : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.heightPower (s + t) g = hK.heightPower s g * hK.heightPower t g := by
  simp only [IsIwasawaCompact.heightPower, map_add, LinearMap.add_apply, Complex.exp_add]

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The height powers of opposite parameters are inverse to each other. -/
theorem IsIwasawaCompact.heightPower_neg_mul_self (hK : IsIwasawaCompact p K)
    (s : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.heightPower (-s) g * hK.heightPower s g = 1 := by
  rw [← hK.heightPower_add', neg_add_cancel]
  simp [IsIwasawaCompact.heightPower]

end Heights

section Parameter

variable {G P Q L M M' : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {q : Q ⟶ G} {pL : L ⟶ G} {l : M ⟶ P} {l' : M' ⟶ Q}

omit [NumberField F] in
/-- If `(w, c)` presents a Weyl conjugation from `P` to `Q`, both contained in `L`, with `w` a
rational point of `L`, then the transported parameter of a restricted parameter of `L` is its
restriction to `Q`. -/
theorem weylParameter_parameterRestrict (hpL : Mono pL)
    (eP : P ⟶ L) (heP : eP ≫ pL = p) (eQ : Q ⟶ L) (heQ : eQ ≫ pL = q)
    (hl' : IsRationalLeviSubgroup l') {π' : Q ⟶ M'} (hπ' : l' ≫ π' = 𝟙 M')
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (hw : IsWeylConjugation p l q l' w c)
    (y : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ L.X) (hy : w = y ≫ pL.hom.hom)
    (ν : ComplexCharacterParameter F L) :
    weylParameter (F := F) l c π' (parameterRestrict eP ν) = parameterRestrict eQ ν := by
  -- `c ≫ l ≫ eP = l' ≫ eQ ≫ Int(y)⁻¹` in `L`.
  have hcomp : c ≫ l ≫ eP = l' ≫ eQ ≫ (L.innerIso y).inv := by
    rw [← cancel_mono pL]
    simp only [Category.assoc, heP, hw.comp_eq]
    rw [hy, ← innerIso_inv_hom, ← innerIso_inv_hom, innerIso_hom_comp pL y⁻¹, reassoc_of% heQ]
    simp only [GrpObj.inv_comp]
  -- characters of `L` are invariant under inner automorphisms
  have hchar : ∀ χ : rationalCharacters L,
      characterRestrict (π' ≫ c ≫ l) (characterRestrict eP χ) = characterRestrict eQ χ := by
    intro χ
    -- both sides restrict to the same character of `M'`
    apply hl'.characterRestrict_bijective.1
    simp only [← AddMonoidHom.comp_apply, ← characterRestrict_comp]
    rw [show l' ≫ (π' ≫ c ≫ l) ≫ eP = c ≫ l ≫ eP by
      simp only [Category.assoc, reassoc_of% hπ'], hcomp]
    apply Additive.toMul.injective
    simp only [characterRestrict_apply, Category.assoc]
    rw [← innerIso_inv_hom, DominantMultiple.innerIso_hom_comp_character]
  have hmap : (weylParameter (F := F) l c π').comp (parameterRestrict eP) =
      parameterRestrict eQ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s χ
    simp only [LinearMap.comp_apply, parameterRestrict, AlgebraTensorModule.map_tmul,
      LinearMap.id_apply, AddMonoidHom.coe_toIntLinearMap, weylParameter_tmul]
    rw [hchar]
  exact LinearMap.congr_fun hmap ν

end Parameter

section Operator

variable {G P Q L U V M M' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine L.X.left]
  [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {pL : L ⟶ G} [IsClosedImmersion pL.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}

omit [LocallyOfFiniteType G.X.hom] in
/-- Restricting a parameter of `L` to a closed subgroup `P ⊆ L` does not change the height
power, for a compact Iwasawa for both. -/
theorem IsIwasawaCompact.heightPower_parameterRestrict (hL : IsIwasawaCompact pL K)
    (e : P ⟶ L) (he : e ≫ pL = p) (hK : IsIwasawaCompact p K)
    (ν : ComplexCharacterParameter F L) (g : AdelicGroupPoints F G) :
    hK.heightPower (parameterRestrict e ν) g = hL.heightPower ν g := by
  subst he
  exact hL.heightPower_restrict e hK ν g

omit [IsAffine G.X.left] [IsClosedImmersion pL.hom.hom.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine L.X.left] in
/-- The adelic point of a rational point of `L`, sent to `G`. -/
theorem innerAdelicPoint_comp (y : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ L.X) :
    innerAdelicPoint F G (y ≫ pL.hom.hom) =
      map F L G pL (rational F L
        (L.constantPoint y ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))))) := by
  rw [innerAdelicPoint_eq_rational, ← constantPoint_comp pL y]
  exact DFunLike.congr_fun (rational_naturality F L pL) _

variable {iU : U ⟶ P} {l : M ⟶ P} {iV : V ⟶ Q} [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {l' : M' ⟶ Q}

/-- **Invariance under ambient parameters.** Let `P` and `Q` lie in a closed subgroup `L`, let
`(w, c)` present a Weyl conjugation from `P` to `Q` with `w` a rational point of `L`, and let
the unipotent radical `V` of `Q` be unipotent. Then the intertwining operator does not change
when its parameter is translated by the restriction to `P` of a parameter of `L`. -/
theorem IsIwasawaCompact.intertwiningOperator_add_parameterRestrict
    (hK : IsIwasawaCompact p K) (hQ : IsIwasawaCompact q K) (hL : IsIwasawaCompact pL K)
    (eP : P ⟶ L) (heP : eP ≫ pL = p) (eQ : Q ⟶ L) (heQ : eQ ≫ pL = q)
    (hl' : IsRationalLeviSubgroup l') {π' : Q ⟶ M'} (hπ' : l' ≫ π' = 𝟙 M')
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (hw : IsWeylConjugation p l q l' w c)
    (y : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ L.X) (hy : w = y ≫ pL.hom.hom)
    (hV : IsUnipotent V) (ψ : AdelicGroupPoints F G → ℂ)
    (mu : ComplexCharacterParameter F P) (ν : ComplexCharacterParameter F L)
    (g : AdelicGroupPoints F G) :
    hK.intertwiningOperator hQ iU l iV c π' w ψ (mu + parameterRestrict eP ν) g =
      hK.intertwiningOperator hQ iU l iV c π' w ψ mu g := by
  have hpOver : Mono pL.hom.hom := Over.mono_of_mono_left _
  have hmono : Mono pL := (Grp.forget _).mono_of_mono_map (f := pL) hpOver
  have hpar := weylParameter_parameterRestrict hmono eP heP eQ heQ hl' hπ' hw y hy ν
  -- the integrand acquires the factor `m_L(g)^ν`
  have hint : hK.intertwiningIntegral iU (iV ≫ q) w ψ (mu + parameterRestrict eP ν) g =
      hL.heightPower ν g * hK.intertwiningIntegral iU (iV ≫ q) w ψ mu g := by
    unfold IsIwasawaCompact.intertwiningIntegral
    rw [← integral_const_mul]
    congr 1
    funext x
    unfold IsIwasawaCompact.intertwiningIntegrand IsIwasawaCompact.parameterTwist
    rw [hK.heightPower_add', hL.heightPower_parameterRestrict eP heP hK]
    obtain ⟨u₀, hu⟩ := (Quotient.out x :
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))).property
    let u : AdelicGroupPoints F V := u₀
    have hv : ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) =
        map F V G ((iV ≫ eQ) ≫ pL) u := by
      rw [← hu]
      subst heQ
      simp only [Category.assoc]
      rfl
    have hshift : hL.heightPower ν ((innerAdelicPoint F G w)⁻¹ *
        ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * g) =
        hL.heightPower ν g := by
      rw [hv, hy, innerAdelicPoint_comp, ← map_inv, ← map_inv, mul_assoc,
        hL.heightPower_rational_mul, hL.heightPower_unipotent_mul hV]
    rw [hshift]
    ring
  unfold IsIwasawaCompact.intertwiningOperator
  rw [hint, map_add, hpar, neg_add, hQ.heightPower_add',
    show -(parameterRestrict eQ ν) = parameterRestrict eQ (-ν) from (map_neg _ _).symm,
    hL.heightPower_parameterRestrict eQ heQ hQ]
  have h1 := hL.heightPower_neg_mul_self ν g
  linear_combination (hQ.heightPower (-(weylParameter l c π') mu) g *
    hK.intertwiningIntegral iU (iV ≫ q) w ψ mu g) * h1

end Operator

end Langlands.Global.AdelicGroupPoints

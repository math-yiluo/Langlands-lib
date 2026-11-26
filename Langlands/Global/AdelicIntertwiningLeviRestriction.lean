import Langlands.Global.AdelicIntertwiningStabilizerModulusStatement
import Langlands.Global.AdelicIntertwiningNormalizedLevi
import Langlands.Global.AdelicWeylPositiveTransport
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Global.InfiniteAdelicModularCharacter
import Langlands.Global.AdelicGroupPolish
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure

/-! # Restriction of the intertwining operator to the target Levi subgroup

For a point `m` of the target Levi `M'(𝔸)`, the closed-quotient change of variables moves `m`
from the external argument of `M(w, λ)φ` into the integrand. With the Haar factor of
`IntertwiningStabilizerModulusStatement` and the Weyl transport of parameters, the normalized
value `δ_Q(m)^{-1/2} M(w, λ)φ(m g)` becomes
`δ_P(w⁻¹ m w)^{-1/2} m_Q(g)^{-wλ} ∫ φ(w⁻¹ m w · w⁻¹ v g) m_P(w⁻¹ v g)^λ dv`
(Bernstein–Lapid (6.5)). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]

theorem parameterPower_neg {H : GroupScheme (Spec (CommRingCat.of F))}
    (lam : ComplexCharacterParameter F H) (x : AdelicGroupPoints F H) :
    parameterPower F H (-lam) x = (parameterPower F H lam x)⁻¹ := by
  simp [parameterPower, Complex.exp_neg]

theorem parameterPower_ne_zero {H : GroupScheme (Spec (CommRingCat.of F))}
    (lam : ComplexCharacterParameter F H) (x : AdelicGroupPoints F H) :
    parameterPower F H lam x ≠ 0 :=
  Complex.exp_ne_zero _

theorem continuous_parameterPower_univ {H : GroupScheme (Spec (CommRingCat.of F))}
    (lam : ComplexCharacterParameter F H) : Continuous (parameterPower F H lam) := by
  have hpair : Continuous (complexParameterPairing F H lam) := by
    induction lam using TensorProduct.inductionOn with
    | tmul t χ =>
      have h : ⇑(complexParameterPairing F H (t ⊗ₜ[ℤ] χ)) = fun D => t * (D χ : ℂ) :=
        funext fun D => complexParameterPairing_tmul F H t χ D
      rw [h]
      exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_dualEval F H χ))
    | add x y hx hy => rw [map_add, LinearMap.coe_add]; exact hx.add hy
  exact Complex.continuous_exp.comp (hpair.comp (continuous_characterLog F H))

theorem map_comp_eq_map_map {A B C : GroupScheme (Spec (CommRingCat.of F))} (f : A ⟶ B) (h : B ⟶ C)
    (x : AdelicGroupPoints F A) : map F A C (f ≫ h) x = map F B C h (map F A B f x) := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]

variable {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {iU : U ⟶ P} {l : M ⟶ P} {iV : V ⟶ Q} {l' : M' ⟶ Q}
  [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M} {π' : Q ⟶ M'}
  {K : Subgroup (AdelicGroupPoints F G)}

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))

/-- Bernstein–Lapid (6.5) for the Library's operator: for a target Levi point `x`, the value
`δ_Q(x)^{-1/2} M(w, λ)φ(x g)` is `δ_P(c(x))^{-1/2} m_Q(g)^{-wλ}` times the integral of
`φ(c(x) · w⁻¹ v g) m_P(w⁻¹ v g)^λ` over `(V(F) ∩ w U(𝔸) w⁻¹) \ V(𝔸)`. -/
theorem IsIwasawaCompact.intertwiningOperator_levi_mul (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact q K) (hC : IntertwiningStabilizerModulusStatement.{u})
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hl : IsRationalLeviSubgroup l)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl' : IsRationalLeviSubgroup l') (hw : IsWeylConjugation p l q l' w c)
    (hπ : l' ≫ π' = 𝟙 M') {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
    (hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (lam : ComplexCharacterParameter F P) (x : AdelicGroupPoints F M')
    (g : AdelicGroupPoints F G) :
    parameterPower F Q (-halfModulusParameter F Q) (map F M' Q l' x) *
        hK.intertwiningOperator hK' iU l iV c π' w φ lam (map F Q G q (map F M' Q l' x) * g) =
      parameterPower F P (-halfModulusParameter F P) (map F M' P (c ≫ l) x) *
        hK'.heightPower (-weylParameter l c π' lam) g *
        ∫ r, φ (map F P G p (map F M' P (c ≫ l) x) *
            ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)) *
          hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)
          ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w) := by
  have hUrad : IsUnipotentRadical iU := hU.1
  have hVrad : IsUnipotentRadical iV := hV.1
  have hi : IsClosedSubgroup (iU ≫ p) :=
    IsClosedSubgroup.comp (i := iU) (j := p) hUrad.isClosedSubgroup
      (inferInstanceAs (IsClosedImmersion p.hom.hom.left))
  have hfactor := hC F G P M U Q M' V p iU l q iV l' w c hG hp hU hl hq hV hl' hw hi
    hVrad.isUnipotent hUrad.isNormal hVrad.isNormal x
  have hcP : map F M' P (c ≫ l) x = map F M P l (map F M' M c x) := map_comp_eq_map_map c l x
  have hHaar : intertwiningLeviHaarFactor iU iV hw hUrad.isNormal hVrad.isNormal hi
      hVrad.isUnipotent x * parameterPower F P (halfModulusParameter F P) (map F M P l (map F M' M c x)) =
      parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' x) := by
    unfold intertwiningLeviHaarFactor
    rw [hfactor, hcP, mul_assoc, parameterPower_neg,
      inv_mul_cancel₀ (parameterPower_ne_zero _ _), mul_one]
  rw [IsIwasawaCompact.intertwiningOperator_normalized_levi (iU := iU) (iV := iV) (hw := hw)
    (hU := hUrad.isNormal) (hV := hVrad.isNormal) (hi := hi) (hVu := hVrad.isUnipotent) (hK := hK)
    (hK' := hK') (hπ' := hπ) (hVs := hVrad.smooth) (hVc := hVrad.connectedSpace)
    (hUu := hUrad.isUnipotent) (hφc := hφc) (hφ := hφU) (m := x) (lam := lam) (g := g)
    (hHaar := hHaar), hcP]
  simp_rw [mul_assoc, integral_const_mul]
  ring

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType P.X.hom] [IsAffine Q.X.left]
  [LocallyOfFiniteType Q.X.hom] [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  [IsClosedImmersion q.hom.hom.left] [IsClosedImmersion (iV ≫ q).hom.hom.left] in
/-- The restricted integrand can be evaluated at any representative of a class. -/
theorem IsIwasawaCompact.leviIntegrand_mk (hK : IsIwasawaCompact p K)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) {φ : AdelicGroupPoints F G → ℂ}
    (hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (lam : ComplexCharacterParameter F P) (x : AdelicGroupPoints F M') (g : AdelicGroupPoints F G)
    (v : Vₐ) :
    φ (map F P G p (map F M' P (c ≫ l) x) * ((innerAdelicPoint F G w)⁻¹ *
        (Quotient.out (LeftCosetSpace.mk (intertwiningRationalSubgroup F p iU (iV ≫ q)
          (innerAdelicPoint F G w)) v) : Vₐ).val * g)) *
      hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ *
        (Quotient.out (LeftCosetSpace.mk (intertwiningRationalSubgroup F p iU (iV ≫ q)
          (innerAdelicPoint F G w)) v) : Vₐ).val * g) =
    φ (map F P G p (map F M' P (c ≫ l) x) * ((innerAdelicPoint F G w)⁻¹ * v.val * g)) *
      hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * v.val * g) := by
  have hUrad : IsUnipotentRadical iU := hU.1
  let wA := innerAdelicPoint F G w
  let Γ := intertwiningRationalSubgroup F p iU (iV ≫ q) wA
  let y := (LeftCosetSpace.mk Γ v).out
  have hs : y * v⁻¹ ∈ Γ :=
    (LeftCosetSpace.mk_eq_mk_iff Γ v y).mp (LeftCosetSpace.mk_out Γ _).symm
  obtain ⟨u₀, hu₀⟩ := ((mem_intertwiningRationalSubgroup_iff F p iU (iV ≫ q) wA _).mp hs).2
  change map F U G (iU ≫ p) u₀ =
    wA⁻¹ * ((y : AdelicGroupPoints F G) * (v : AdelicGroupPoints F G)⁻¹) * wA at hu₀
  have hrearr : wA⁻¹ * (y : AdelicGroupPoints F G) * g =
      map F U G (iU ≫ p) u₀ * (wA⁻¹ * (v : AdelicGroupPoints F G) * g) := by
    rw [hu₀]
    group
  change φ (map F P G p (map F M' P (c ≫ l) x) * (wA⁻¹ * (y : AdelicGroupPoints F G) * g)) *
      hK.heightPower lam (wA⁻¹ * (y : AdelicGroupPoints F G) * g) = _
  rw [hrearr, hK.heightPower_unipotent_mul hUrad.isUnipotent]
  congr 1
  have hmem : map F U G (iU ≫ p) u₀ ∈ parabolicUnipotentImage F p iU := ⟨u₀, rfl⟩
  have hconj := conj_mem_adelicPoints_range p iU hUrad.isNormal (map F M' P (c ≫ l) x) hmem
  rw [show map F P G p (map F M' P (c ≫ l) x) * (map F U G (iU ≫ p) u₀ *
      (wA⁻¹ * (v : AdelicGroupPoints F G) * g)) =
      (map F P G p (map F M' P (c ≫ l) x) * map F U G (iU ≫ p) u₀ *
        (map F P G p (map F M' P (c ≫ l) x))⁻¹) *
      (map F P G p (map F M' P (c ≫ l) x) * (wA⁻¹ * (v : AdelicGroupPoints F G) * g)) by group]
  exact hφU _ hconj _

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType P.X.hom] [IsAffine Q.X.left]
  [LocallyOfFiniteType Q.X.hom] [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  [IsClosedImmersion q.hom.hom.left] [IsClosedImmersion (iV ≫ q).hom.hom.left] in
/-- The restricted integrand is jointly continuous in the Levi point and the quotient point, for
Levi points depending continuously on a parameter. -/
theorem IsIwasawaCompact.continuous_leviIntegrand (hK : IsIwasawaCompact p K)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) {φ : AdelicGroupPoints F G → ℂ}
    (hφc : Continuous φ) (hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
    {X : Type*} [TopologicalSpace X] {κ : X → AdelicGroupPoints F M'} (hκ : Continuous κ) :
    Continuous (fun z : X × LeftCosetSpace (intertwiningRationalSubgroup F p iU
        (iV ≫ q) (innerAdelicPoint F G w)) =>
      φ (map F P G p (map F M' P (c ≫ l) (κ z.1)) * ((innerAdelicPoint F G w)⁻¹ *
          (Quotient.out z.2 : Vₐ).val * g)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out z.2 : Vₐ).val * g)) := by
  let Γ := intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)
  have hq : IsQuotientMap (Prod.map (id : X → X) (LeftCosetSpace.mk Γ)) :=
    (IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)).isQuotientMap
  rw [hq.continuous_iff]
  have heq : (fun z : X × LeftCosetSpace Γ =>
      φ (map F P G p (map F M' P (c ≫ l) (κ z.1)) * ((innerAdelicPoint F G w)⁻¹ *
          (Quotient.out z.2 : Vₐ).val * g)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out z.2 : Vₐ).val * g)) ∘
      Prod.map id (LeftCosetSpace.mk Γ) =
      fun z : X × Vₐ =>
        φ (map F P G p (map F M' P (c ≫ l) (κ z.1)) * ((innerAdelicPoint F G w)⁻¹ * z.2.val * g)) *
          hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * z.2.val * g) := by
    funext z
    exact hK.leviIntegrand_mk hU hφU lam (κ z.1) g z.2
  rw [heq]
  have hB : Continuous (fun z : X × Vₐ => map F P G p (map F M' P (c ≫ l) (κ z.1))) :=
    (map F P G p).continuous.comp ((map F M' P (c ≫ l)).continuous.comp (hκ.comp continuous_fst))
  have hh : Continuous (fun z : X × Vₐ => (innerAdelicPoint F G w)⁻¹ * z.2.val * g) :=
    (continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_const
  exact (hφc.comp (hB.mul hh)).mul ((hK.continuous_heightPower lam).comp hh)

omit [IsClosedImmersion q.hom.hom.left] in
/-- The `L¹`-mass of the restricted integrand at a Levi point is the mass of the intertwining
integrand at the translated point, times the Haar factor and the parameter power. -/
theorem IsIwasawaCompact.lintegral_leviIntegrand (hK : IsIwasawaCompact p K)
    (hC : IntertwiningStabilizerModulusStatement.{u})
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hl : IsRationalLeviSubgroup l)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl' : IsRationalLeviSubgroup l') (hw : IsWeylConjugation p l q l' w c)
    {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
    (hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (lam : ComplexCharacterParameter F P) (x : AdelicGroupPoints F M')
    (g : AdelicGroupPoints F G) :
    (∫⁻ r, ‖φ (map F P G p (map F M' P (c ≫ l) x) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)‖ₑ
        ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) =
      ‖(parameterPower F P lam (map F M' P (c ≫ l) x) *
          (parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' x) *
            parameterPower F P (-halfModulusParameter F P) (map F M' P (c ≫ l) x)))⁻¹‖ₑ *
        ∫⁻ r, ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ lam
          (map F Q G q (map F M' Q l' x) * g) r‖ₑ
          ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w) := by
  have hUrad : IsUnipotentRadical iU := hU.1
  have hVrad : IsUnipotentRadical iV := hV.1
  have hUn := hUrad.isNormal
  have hVn := hVrad.isNormal
  have hi : IsClosedSubgroup (iU ≫ p) :=
    IsClosedSubgroup.comp (i := iU) (j := p) hUrad.isClosedSubgroup
      (inferInstanceAs (IsClosedImmersion p.hom.hom.left))
  have hα := conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hUn hVn x
  have hconj := intertwiningIntegralConjugation p iU (iV ≫ q) w hi hVrad.smooth
    hVrad.connectedSpace hVrad.isUnipotent (map F Q G q (map F M' Q l' x))
    (EisensteinConstantTerm.conjAdelic q iV hVn (map F M' Q l' x)) hα (fun _ => rfl) K hK φ hφc
    hφU hUrad.isUnipotent lam g
  have hfactor := hC F G P M U Q M' V p iU l q iV l' w c hG hp hU hl hq hV hl' hw hi
    hVrad.isUnipotent hUn hVn x
  obtain ⟨-, -, hL⟩ := hconj
  dsimp only at hL
  have hB : map F P G p (map F M' P (c ≫ l) x) =
      (innerAdelicPoint F G w)⁻¹ * map F Q G q (map F M' Q l' x) * innerAdelicPoint F G w := by
    rw [map_comp_eq_map_map c l]
    exact hw.adelic_comp_eq x
  have hmoved : ∀ r : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
      (innerAdelicPoint F G w)),
      hK.parameterTwist φ lam ((innerAdelicPoint F G w)⁻¹ * map F Q G q (map F M' Q l' x) *
          (Quotient.out r : Vₐ).val * g) =
        parameterPower F P lam (map F M' P (c ≫ l) x) *
          (φ (map F P G p (map F M' P (c ≫ l) x) *
              ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)) *
            hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)) := by
    intro r
    have harg : (innerAdelicPoint F G w)⁻¹ * map F Q G q (map F M' Q l' x) *
          (Quotient.out r : Vₐ).val * g =
        map F P G p (map F M' P (c ≫ l) x) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g) := by
      rw [hB]
      group
    unfold IsIwasawaCompact.parameterTwist
    rw [harg, hK.heightPower_map_mul]
    ring
  simp_rw [hmoved, enorm_mul] at hL
  rw [lintegral_const_mul' _ _ enorm_ne_top] at hL
  have : LocallyCompactSpace Vₐ :=
    (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)).locallyCompactSpace
  have : LocallyCompactSpace (intertwiningAdelicStabilizer p iU (iV ≫ q) w) :=
    (intertwiningStabilizer p iU (iV ≫ q) w
      (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) hi
      hVrad.isUnipotent).1.locallyCompactSpace
  set t : ℝ≥0 := mulEquivHaarChar (EisensteinConstantTerm.conjAdelic q iV hVn (map F M' Q l' x)) /
    mulEquivHaarChar (subgroupAutomorphism (intertwiningAdelicStabilizer p iU (iV ≫ q) w)
      (EisensteinConstantTerm.conjAdelic q iV hVn (map F M' Q l' x)) hα) with ht
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos (mulEquivHaarChar_pos _) (mulEquivHaarChar_pos _)
  have hinv : (mulEquivHaarChar (subgroupAutomorphism (intertwiningAdelicStabilizer p iU (iV ≫ q) w)
      (EisensteinConstantTerm.conjAdelic q iV hVn (map F M' Q l' x)) hα) /
      mulEquivHaarChar (EisensteinConstantTerm.conjAdelic q iV hVn (map F M' Q l' x)) : ℝ≥0) =
      t⁻¹ := by
    rw [ht, inv_div]
  rw [hinv] at hL
  have hpp := parameterPower_ne_zero lam (map F M' P (c ≫ l) x)
  have hfac : ((t : ℝ) : ℂ) = parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' x) *
      parameterPower F P (-halfModulusParameter F P) (map F M' P (c ≫ l) x) := by
    rw [← hfactor]
  have hte : ‖((t : ℝ) : ℂ)‖ₑ = ((t : ℝ≥0) : ℝ≥0∞) := by
    rw [enorm_eq_nnnorm]
    congr 1
    ext
    simp
  have hpe0 : ‖parameterPower F P lam (map F M' P (c ≫ l) x)‖ₑ ≠ 0 := enorm_ne_zero.mpr hpp
  have hpet : ‖parameterPower F P lam (map F M' P (c ≫ l) x)‖ₑ ≠ ⊤ := enorm_ne_top
  have ht0 : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
  rw [← hfac, enorm_inv (mul_ne_zero hpp ht0), enorm_mul,
    ENNReal.mul_inv (Or.inl hpe0) (Or.inl hpet), hte, ← ENNReal.coe_inv htpos.ne', mul_assoc, ← hL,
    ← mul_assoc, ENNReal.inv_mul_cancel hpe0 hpet, one_mul]
  simp_rw [enorm_mul]


omit [IsClosedImmersion q.hom.hom.left] in
/-- Against a continuous compactly supported weight on `M'(F_∞)`, the restricted integrand is
integrable on `M'(F_∞) × (V(F) ∩ w U(𝔸) w⁻¹) \ V(𝔸)`, when the intertwining integrand is
dominated by one integrable function at the translated points of the support. -/
theorem IsIwasawaCompact.integrable_leviIntegrand_prod (hK : IsIwasawaCompact p K)
    (hC : IntertwiningStabilizerModulusStatement.{u})
    (hG : IsConnectedReductive G) (hp : IsParabolicSubgroup p)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hl : IsRationalLeviSubgroup l)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl' : IsRationalLeviSubgroup l') (hw : IsWeylConjugation p l q l' w c)
    [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
    (hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
    (ν : Measure (InfiniteAdelicGroupPoints F M')) [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    {ϑ : InfiniteAdelicGroupPoints F M' → ℂ} (hϑ : Continuous ϑ) (hϑc : HasCompactSupport ϑ)
    {b : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)) → ℝ}
    (hb : Integrable b (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)))
    (hbound : ∀ m ∈ tsupport ϑ, ∀ r, ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ lam
      (map F Q G q (map F M' Q l' (ofInfinite F M' m)) * g) r‖ ≤ b r) :
    Integrable (fun z : InfiniteAdelicGroupPoints F M' ×
        LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)) =>
      ϑ z.1 * (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' z.1)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out z.2 : Vₐ).val * g)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out z.2 : Vₐ).val * g)))
      (ν.prod (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w))) := by
  let Γ := intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)
  have hΓ := isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)
  have hclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)
  have : LocallyCompactSpace Vₐ := hclosed.locallyCompactSpace
  have : PolishSpace Vₐ := hclosed.polishSpace
  have : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ hΓ
  have : SFinite (AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))) := by
    unfold AdelicSubgroupPoints.normalizedHaarMeasure
    infer_instance
  have : SFinite (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) := by
    unfold intertwiningMeasure LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
    infer_instance
  have hf : Continuous (fun z : InfiniteAdelicGroupPoints F M' × LeftCosetSpace Γ =>
      ϑ z.1 * (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' z.1)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out z.2 : Vₐ).val * g)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out z.2 : Vₐ).val * g))) :=
    (hϑ.comp continuous_fst).mul
      (hK.continuous_leviIntegrand hU hφc hφU lam g (ofInfinite F M').continuous)
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  let h₁ : InfiniteAdelicGroupPoints F M' → ℂ := fun m =>
    (parameterPower F P lam (map F M' P (c ≫ l) (ofInfinite F M' m)) *
      (parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' (ofInfinite F M' m)) *
        parameterPower F P (-halfModulusParameter F P)
          (map F M' P (c ≫ l) (ofInfinite F M' m))))⁻¹
  have hh₁ : Continuous h₁ := by
    have hP (ε : ComplexCharacterParameter F P) : Continuous (fun m =>
        parameterPower F P ε (map F M' P (c ≫ l) (ofInfinite F M' m))) :=
      (continuous_parameterPower_univ ε).comp
        ((map F M' P (c ≫ l)).continuous.comp (ofInfinite F M').continuous)
    have hQ : Continuous (fun m =>
        parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' (ofInfinite F M' m))) :=
      (continuous_parameterPower_univ _).comp
        ((map F M' Q l').continuous.comp (ofInfinite F M').continuous)
    exact ((hP lam).mul (hQ.mul (hP _))).inv₀ fun m =>
      mul_ne_zero (parameterPower_ne_zero _ _)
        (mul_ne_zero (parameterPower_ne_zero _ _) (parameterPower_ne_zero _ _))
  have hk : Integrable (fun m => ϑ m * h₁ m) ν :=
    (hϑ.mul hh₁).integrable_of_hasCompactSupport hϑc.mul_right
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hf.enorm.aemeasurable]
  have hinner : ∀ m, (∫⁻ r : LeftCosetSpace Γ, ‖ϑ m * (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g))‖ₑ
      ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) ≤
      ‖ϑ m * h₁ m‖ₑ * ∫⁻ r, ‖b r‖ₑ
        ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w) := by
    intro m
    have hsplit : (fun r : LeftCosetSpace Γ => ‖ϑ m * (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g))‖ₑ) = fun r : LeftCosetSpace Γ => ‖ϑ m‖ₑ * ‖φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)‖ₑ :=
      funext fun r => enorm_mul _ _
    rw [hsplit, lintegral_const_mul' _ _ enorm_ne_top]
    by_cases hm : m ∈ tsupport ϑ
    · rw [hK.lintegral_leviIntegrand hC hG hp hU hl hq hV hl' hw hφc hφU lam
        (ofInfinite F M' m) g, enorm_mul, mul_assoc]
      gcongr with r
      exact enorm_le_iff_norm_le.mpr (by
        rw [Real.norm_eq_abs]
        exact (hbound m hm r).trans (le_abs_self _))
    · rw [image_eq_zero_of_notMem_tsupport hm]
      simp
  calc (∫⁻ m, ∫⁻ r : LeftCosetSpace Γ, ‖ϑ m * (φ (map F P G p (map F M' P (c ≫ l) (ofInfinite F M' m)) *
          ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g)) *
        hK.heightPower lam ((innerAdelicPoint F G w)⁻¹ * (Quotient.out r : Vₐ).val * g))‖ₑ
          ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w) ∂ν)
      ≤ ∫⁻ m, ‖ϑ m * h₁ m‖ₑ * ∫⁻ r, ‖b r‖ₑ
          ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w) ∂ν :=
        lintegral_mono hinner
    _ = (∫⁻ m, ‖ϑ m * h₁ m‖ₑ ∂ν) * ∫⁻ r, ‖b r‖ₑ
          ∂intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w) :=
        lintegral_mul_const' _ _ hb.hasFiniteIntegral.ne
    _ < ⊤ := ENNReal.mul_lt_top hk.hasFiniteIntegral hb.hasFiniteIntegral


end Langlands.Global.AdelicGroupPoints

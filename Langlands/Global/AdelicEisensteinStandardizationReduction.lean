import Langlands.Global.AdelicHarishChandraCompactConjugation
import Langlands.Global.AdelicEisensteinStandardizationStatement
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicEisensteinRegularityParabolicTransport
import Langlands.Global.AdelicStandardLeviCompactAssembly
import Langlands.Global.InfinitePlaceStandardLeviCompact
import Langlands.Global.FinitePlaceStandardLeviCompact
import Langlands.Global.InfiniteAdelicMaximalCompactConjugacy
import Langlands.Global.AdelicEisensteinConjugateCompactProof
import Langlands.Global.AdelicEisensteinFiniteCompactOperatorComparison
import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicEisensteinRootHyperplaneCompactReduction
import Langlands.Automorphic.GroupSchemeAutomorphicRightTranslation
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Absolute.ParabolicTransport

/-! # Standardization of Eisenstein series from available Bruhat–Tits data

`EisensteinStandardizationStatement` follows from `BruhatTitsAvailabilityStatement`
(`eisensteinStandardization_of_bruhatTitsAvailability`). Given `P = MU` with a root presentation,
a maximal compact `K` with `P(𝔸)K = G(𝔸)` and an automorphic `φ`, the proof

* builds the standard family of the presentation's maximal split torus and generic cocharacter,
  in which the presentation's index `I` gives a parabolic with the image of `P`;
* assembles a maximal compact `K'` in good position for that family from local compacts at all
  places (the finite ones from available Bruhat–Tits data);
* conjugates the archimedean factor of `K` onto that of `K'` by `t ∈ G(F_∞)` and compares `K`
  with `C = t⁻¹K't`, which has the same archimedean factor, by a finite change of heights;
* passes from `C` to `K'` by right translation by `t`, and from `P` to `P_I` by restriction of
  parameters.

The first part of the file contains auxiliary facts: functoriality of the restriction of
complex parameters, the pairing with a fixed real dual element as a linear form, the
archimedean factor of a conjugate of an adelic subgroup, and the image of the unipotent radical
for two presentations of one parabolic. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The unipotent radicals of two presentations of one subgroup have the same image in the
ambient group. -/
theorem IsUnipotentRadical.range_comp_eq_of_iso
    {U U' P P' G : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {p' : P' ⟶ G} (e : P' ≅ P) (he : e.hom ≫ p = p')
    {i : U ⟶ P} {i' : U' ⟶ P'} (hi : IsUnipotentRadical i) (hi' : IsUnipotentRadical i') :
    SubgroupFunctor.range (i ≫ p) = SubgroupFunctor.range (i' ≫ p') := by
  have h := hi.range_eq (hi'.comp_iso e)
  rw [← he, ← Category.assoc]
  exact le_antisymm (SubgroupFunctor.range_comp_mono h.le p)
    (SubgroupFunctor.range_comp_mono h.ge p)

end Langlands.GroupScheme

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F]

/-- Restriction of complex parameters along the identity is the identity. -/
theorem parameterRestrict_id (H : GroupScheme (Spec (CommRingCat.of F))) :
    parameterRestrict (F := F) (𝟙 H) = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s χ
  change s ⊗ₜ[ℤ] characterRestrict (𝟙 H) χ = s ⊗ₜ[ℤ] χ
  rw [characterRestrict_id]
  rfl

/-- Restriction of complex parameters along a composite is the composite of the
restrictions, in reverse order. -/
theorem parameterRestrict_comp {H H' H'' : GroupScheme (Spec (CommRingCat.of F))}
    (g : H'' ⟶ H') (f : H' ⟶ H) :
    parameterRestrict (F := F) (g ≫ f) = (parameterRestrict g).comp (parameterRestrict f) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s χ
  change s ⊗ₜ[ℤ] characterRestrict (g ≫ f) χ =
    s ⊗ₜ[ℤ] characterRestrict g (characterRestrict f χ)
  rw [characterRestrict_comp]
  rfl

/-- Restriction of complex parameters along an isomorphism is a linear isomorphism. -/
def parameterRestrictEquiv {H H' : GroupScheme (Spec (CommRingCat.of F))} (e : H' ≅ H) :
    ComplexCharacterParameter F H ≃ₗ[ℂ] ComplexCharacterParameter F H' :=
  LinearEquiv.ofLinearMap (parameterRestrict e.hom) (parameterRestrict e.inv)
    (by rw [← parameterRestrict_comp, e.hom_inv_id, parameterRestrict_id])
    (by rw [← parameterRestrict_comp, e.inv_hom_id, parameterRestrict_id])

/-- The linear isomorphism `parameterRestrictEquiv e` is restriction along `e.hom`. -/
theorem parameterRestrictEquiv_apply {H H' : GroupScheme (Spec (CommRingCat.of F))} (e : H' ≅ H)
    (lam : ComplexCharacterParameter F H) :
    parameterRestrictEquiv e lam = parameterRestrict e.hom lam :=
  rfl

/-- The pairing of a complex parameter with a fixed real dual element, as a complex linear
form in the parameter. -/
def complexParameterPairingAt (G : GroupScheme (Spec (CommRingCat.of F)))
    (H : RealCharacterDual F G) : ComplexCharacterParameter F G →ₗ[ℂ] ℂ where
  toFun lam := complexParameterPairing F G lam H
  map_add' x y := by rw [map_add, LinearMap.add_apply]
  map_smul' c x := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- Evaluation of `complexParameterPairingAt`. -/
theorem complexParameterPairingAt_apply (G : GroupScheme (Spec (CommRingCat.of F)))
    (H : RealCharacterDual F G) (lam : ComplexCharacterParameter F G) :
    complexParameterPairingAt G H lam = complexParameterPairing F G lam H :=
  rfl

section Conjugation

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

variable [NumberField F]

end Conjugation

/-- Conjugating a subgroup by `t` and then by `t⁻¹` gives back the subgroup. -/
theorem subgroup_map_conj_map_conj_inv {X : Type*} [Group X] (H : Subgroup X) (t : X) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id H
  apply MonoidHom.ext
  intro x
  change t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x
  group

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Available corrected Bruhat–Tits data (`BruhatTitsAvailabilityStatement`) give the passage
of Eisenstein series to a standard family with a maximal compact subgroup in good position
(`EisensteinStandardizationStatement`). -/
theorem eisensteinStandardization_of_bruhatTitsAvailability
    (hBT : Geometry.Building.BruhatTitsAvailabilityStatement.{u}) :
    EisensteinStandardizationStatement.{u} := by
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ instW₀ _ hA hT hG hU K hK N d rho hsmooth hcalc φ
    hrho hmax hφ
  -- The standard family of the presentation and the index of `p`.
  let fam : StandardParabolicFamily F G :=
    StandardParabolicFamily.ofMaximalSplitTorus hG r.data.i r.isCompatible.maximalSplit
      r.data.ν r.isCompatible.generic
  let I : StandardIndex F G fam.i fam.ν := ⟨r.data.J, r.isCompatible.subset_simpleRoots⟩
  have hrange : SubgroupFunctor.range (fam.p I) = SubgroupFunctor.range p :=
    (fam.isCompatible I).parabolic_eq.trans r.isCompatible.parabolic_eq.symm
  have hpI : IsClosedSubgroup (fam.p I) := (fam.isCompatible I).parabolic.isClosedSubgroup
  have hp : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
  let e : fam.P I ≅ P := hpI.sourceIsoOfRangeEq hp hrange
  have he : e.hom ≫ p = fam.p I := hpI.sourceIsoOfRangeEq_hom_comp hp hrange
  have hUrange : SubgroupFunctor.range (fam.iU I ≫ fam.p I) = SubgroupFunctor.range (iU ≫ p) :=
    (IsUnipotentRadical.range_comp_eq_of_iso e he hU.1 (fam.isUnipotentRadical I).1).symm
  have hLrange : SubgroupFunctor.range (fam.l I ≫ fam.p I) = SubgroupFunctor.range (l ≫ p) :=
    (fam.isCompatible I).levi_eq.trans r.isCompatible.levi_eq.symm
  have hΓ : parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I) =
      parabolicQuotientSubgroup F p iU l :=
    parabolicQuotientSubgroup_eq_of_range_eq hUrange hLrange
  -- A maximal compact subgroup in good position.
  have hlocal : ∀ v, ∃ L, fam.IsStandardLeviCompact v L := by
    rintro (w | w)
    · exact InfinitePlaceGroupPoints.infinitePlaceStandardLeviCompact F G fam w
    · exact FinitePlaceGroupPoints.finitePlaceStandardLeviCompactReduction hBT F G fam w
  obtain ⟨K', hK'par, hK'levi⟩ := fam.standardLeviCompactAssembly hlocal
  have hK'max : IsMaximalCompactSubgroup F G K' := hK'par.1
  have hle : SubgroupFunctor.range (fam.p fam.minimalIndex) ≤ SubgroupFunctor.range (fam.p I) :=
    (fam.le_iff_range_le _ _).mp (Set.empty_subset _)
  have hp₀ : IsClosedSubgroup (fam.p fam.minimalIndex) :=
    (fam.isCompatible fam.minimalIndex).parabolic.isClosedSubgroup
  let : IsClosedImmersion (fam.p fam.minimalIndex).hom.hom.left := hp₀
  let : IsClosedImmersion (fam.p I).hom.hom.left := hpI
  let : Mono (fam.p fam.minimalIndex).hom.hom := Over.mono_of_mono_left _
  let : Mono (fam.p I).hom.hom := Over.mono_of_mono_left _
  obtain ⟨f₀, hf₀⟩ := SubgroupFunctor.exists_factor_of_range_le hle
  have hK'I : IsIwasawaCompact (fam.p I) K' := by
    refine (IsParabolicIwasawaCompact.of_comp f₀ (fam.p I) ?_).isIwasawaCompact
    rw [hf₀]
    exact hK'par
  have hK'p : IsIwasawaCompact p K' := hK'I.of_range_eq hrange
  -- The archimedean conjugation.
  obtain ⟨t, ht⟩ := InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy F G
    (K.comap (ofInfinite F G).toMonoidHom) (K'.comap (ofInfinite F G).toMonoidHom) hG
    hmax.isMaximalCompact_comap_ofInfinite hK'max.isMaximalCompact_comap_ofInfinite
  let T := ofInfinite F G t
  let C := K'.map (MulAut.conj T⁻¹).toMonoidHom
  have hC : IsIwasawaCompact p C := hK'p.conjInv T
  have hCmax : IsMaximalCompactSubgroup F G C := hK'max.map_conj T⁻¹
  have hArch : C.comap (ofInfinite F G).toMonoidHom = K.comap (ofInfinite F G).toMonoidHom := by
    rw [comap_ofInfinite_conjugate, ← ht, subgroup_map_conj_map_conj_inv]
  have hinf : K.map (infinite F G).toMonoidHom = C.map (infinite F G).toMonoidHom := by
    rw [← hmax.comap_ofInfinite_eq_map_infinite, ← hCmax.comap_ofInfinite_eq_map_infinite, hArch]
  -- The finite change of compact from `K` to `C`.
  obtain ⟨S, cut, hcut, htwist⟩ :=
    hφ.exists_parameterTwist_of_infinite_eq iU l hK hC hmax hCmax hinf
  have hconv (v : S) : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      ∀ g, Summable (hC.eisensteinTerm (cut v) lam g) := by
    have hv := hcut v v.2
    rw [← hArch] at hv
    exact eisensteinAbsoluteConvergence.exists_summable_eisensteinTerm r hA hT hG hU hC rho
      hsmooth hcalc hCmax hrho hv
  choose R hR using hconv
  let B : ℝ := ∑ v : S, max (R v) 0
  have hB (v : S) : R v ≤ B :=
    (le_max_left (R v) 0).trans
      (Finset.single_le_sum (f := fun x => max (R x) 0)
        (fun x _ => le_max_right (R x) 0) (Finset.mem_univ v))
  -- The new inducing data.
  let ε : S ≃ Fin S.card := S.equivFin
  let φ' : Fin S.card → AdelicGroupPoints F G → ℂ := fun i x => cut (ε.symm i) (x * T)
  let ℓ : Fin S.card → ComplexCharacterParameter F P →ₗ[ℂ] ℂ := fun i =>
    complexParameterPairingAt P ((ε.symm i : RealCharacterDual F P) + hC.height T)
  refine ⟨fam, I, K', hK'I, t, parameterRestrictEquiv e, S.card, φ', ℓ, hrange,
    ⟨e.hom, he, fun lam => rfl⟩, hK'max, hK'par.isIwasawaCompact, hK'levi, ?_, ?_, ?_⟩
  · intro i
    have h := IsAutomorphicFunctionOn.infiniteRightTranslate hcalc (hcut _ (ε.symm i).2) t
    rw [ht] at h
    change IsAutomorphicFunctionOn F G hsmooth _
      (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) _ rho _
    rw [hΓ]
    exact h
  · intro f hf
    have h := IsAutomorphicFunctionOn.infiniteRightTranslate hcalc hf t
    rwa [ht] at h
  · intro instW _ instF
    have hW : instW = instW₀ := Subsingleton.elim _ _
    subst instW
    have : Mono (@CommGroupScheme.groupHom _ (fam.A I) r.data.T (fam.f I)).hom.hom.left := instF
    refine ⟨fun R' => ⟨R', fun lam hlam => ?_⟩, ⟨B, fun lam hlam g => ?_⟩⟩
    · exact (eisensteinRegularityParabolicTransport F G P M (fam.P I) (fam.M I) r.data.T A
        (fam.A I) r.data.i r.data.ν r.data.J r.data.f (fam.f I) p l a (fam.p I) (fam.l I)
        (fam.a I) r.isCompatible (fam.isCompatible I) hA
        (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1 hT hG e.hom he R'
        lam).mpr hlam
    · have hregular (v : S) : r.IsRegularParameter hA hT (R v) lam :=
        fun α hα => (hB v).trans_lt (hlam α hα)
      rw [hK.eisensteinSeries_eq_finset_sum_of_twist hC S
        (fun v => Complex.exp (complexParameterPairing F P lam v)) φ cut lam (htwist lam) (g * T)
        (fun v hv => hR ⟨v, hv⟩ lam (hregular ⟨v, hv⟩) (g * T))]
      have hterm (v : RealCharacterDual F P) :
          hC.eisensteinSeries (cut v) lam (g * T) =
            hC.heightPower lam T *
              hK'I.eisensteinSeries (fun x => cut v (x * T)) (parameterRestrict e.hom lam) g := by
        rw [hK'p.eisensteinSeries_mul_conjInv T hC,
          hK'p.eisensteinSeries_eq_of_range_eq hK'I e.hom he hrange.symm]
      simp_rw [hterm]
      rw [← Finset.sum_coe_sort S]
      refine Fintype.sum_equiv ε _ _ (fun v => ?_)
      simp only [φ', ℓ, ε, Equiv.symm_apply_apply, complexParameterPairingAt_apply, map_add,
        IsIwasawaCompact.heightPower, Complex.exp_add, parameterRestrictEquiv_apply]
      ring

end Langlands.Global

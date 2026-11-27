import Langlands.Global.AdelicInducedRightTranslate
import Langlands.Global.AdelicIntertwiningElementaryChainStatement
import Langlands.Global.AdelicEisensteinFiniteCompactOperatorComparison
import Langlands.Global.AdelicIntertwiningConjugateTarget
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicEisensteinRegularityParabolicTransport
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicIwasawaWithInfiniteCompact
import Langlands.Global.AdelicEisensteinAmbientParametersProof
import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Global.AdelicEisensteinRootHyperplaneCompactReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.GroupScheme.Rational.RationalLeviConjugacyProof
import Langlands.GroupScheme.Rational.LeviAmbientTransport
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Standardization of intertwining operators

The proof of `IntertwiningStandardizationStatement` (`intertwiningStandardization`). For a
parabolic `P = MU` with a root presentation, a target parabolic `Q = M'V`, an element `(w, c)`
of `W(P, Q)` and a maximal compact `K` with `P(𝔸)K = Q(𝔸)K = G(𝔸)`:

* the standard family of the presentation's maximal split torus and generic cocharacter has a
  standard parabolic `P_I` with the image of `P`;
* a rational point `s` conjugates `Q` and its Levi onto a standard parabolic `P_{I'}` and its
  standard Levi (`StandardParabolicFamily.exists_standardConjugate`), and conjugating the
  target by `s` multiplies the operator by a target height power at `s` and translates the
  argument by `s`;
* a maximal compact `K₀` with the archimedean factor of `K` and with `P_J(𝔸)K₀ = G(𝔸)` for every
  standard `J` replaces `K`; the finite change of compact writes the operator for `K` as a
  finite combination of operators for `K₀`, and the ratio of the target height powers for `K₀`
  and `K` is a finite combination of indicator functions with exponential coefficients;
* the operators for `P` and the conjugated target equal the operators for `P_I` and `P_{I'}`
  at the restricted parameter (`IsIwasawaCompact.intertwiningOperator_eq_of_transport`), and
  root forms correspond under restriction (`rootFunctional_parameterRestrict_eq_of_comp_eq`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

namespace AdelicGroupPoints

section Transport

variable {F : Type u} [Field F] [NumberField F]
  {G P P₁ Q Q₁ : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine P₁.X.left]
  [IsAffine Q.X.left] [IsAffine Q₁.X.left]
  {K : Subgroup (AdelicGroupPoints F G)}

/-- Restriction of the parameter along a map over the two parabolic inclusions identifies the
height powers. -/
theorem IsIwasawaCompact.heightPower_restrict_of_comp_eq {p : P ⟶ G} {p₁ : P₁ ⟶ G}
    [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion p₁.hom.hom.left]
    (hK : IsIwasawaCompact p K) (hK₁ : IsIwasawaCompact p₁ K) (f : P₁ ⟶ P) (hf : f ≫ p = p₁)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK₁.heightPower (parameterRestrict f lam) g = hK.heightPower lam g := by
  subst hf
  exact hK.heightPower_restrict f hK₁ lam g

omit [IsAffine G.X.left] [IsAffine P.X.left] in
/-- The height powers at opposite parameters are inverse, in the other order. -/
theorem IsIwasawaCompact.heightPower_mul_neg {p : P ⟶ G} (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.heightPower lam g * hK.heightPower (-lam) g = 1 := by
  rw [mul_comm, hK.heightPower_neg_mul]

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine P₁.X.left]
  [IsAffine Q.X.left] [IsAffine Q₁.X.left] in
/-- Weyl parameters correspond under restriction along maps that are compatible with the
composites of the Levi projections, the Weyl isomorphisms and the Levi inclusions. -/
theorem weylParameter_parameterRestrict_eq {M M₁ M' M'₁ : GroupScheme (Spec (CommRingCat.of F))}
    (l : M ⟶ P) (c : M' ⟶ M) (π : Q ⟶ M') (l₁ : M₁ ⟶ P₁) (c₁ : M'₁ ⟶ M₁) (π₁ : Q₁ ⟶ M'₁)
    (jP : P₁ ⟶ P) (jQ : Q₁ ⟶ Q) (h : π₁ ≫ c₁ ≫ l₁ ≫ jP = jQ ≫ π ≫ c ≫ l)
    (lam : ComplexCharacterParameter F P) :
    weylParameter l₁ c₁ π₁ (parameterRestrict jP lam) =
      parameterRestrict jQ (weylParameter l c π lam) := by
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    change s ⊗ₜ[ℤ] characterRestrict (π₁ ≫ c₁ ≫ l₁) (characterRestrict jP χ) =
      s ⊗ₜ[ℤ] characterRestrict jQ (characterRestrict (π ≫ c ≫ l) χ)
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, ← AddMonoidHom.comp_apply,
      ← characterRestrict_comp]
    simp only [Category.assoc, h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The intertwining operator is unchanged when the source and target parabolics are replaced by
parabolics with the same images, compatibly with the Levi data, and the parameter is restricted
along the identification of the sources. -/
theorem IsIwasawaCompact.intertwiningOperator_eq_of_transport [LocallyOfFiniteType G.X.hom]
    {U U₁ V V₁ M M₁ M' M'₁ : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine V.X.left] [IsAffine V₁.X.left]
    {p : P ⟶ G} {p₁ : P₁ ⟶ G} {q : Q ⟶ G} {q₁ : Q₁ ⟶ G}
    [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion p₁.hom.hom.left]
    [IsClosedImmersion q.hom.hom.left] [IsClosedImmersion q₁.hom.hom.left]
    (hK : IsIwasawaCompact p K) (hQ : IsIwasawaCompact q K)
    (hK₁ : IsIwasawaCompact p₁ K) (hQ₁ : IsIwasawaCompact q₁ K)
    (iU : U ⟶ P) (l : M ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (c : M' ⟶ M) (π : Q ⟶ M')
    (iU₁ : U₁ ⟶ P₁) (l₁ : M₁ ⟶ P₁) (iV₁ : V₁ ⟶ Q₁)
    [IsClosedImmersion (iV₁ ≫ q₁).hom.hom.left] (c₁ : M'₁ ⟶ M₁) (π₁ : Q₁ ⟶ M'₁)
    (jP : P₁ ⟶ P) (hjP : jP ≫ p = p₁) (jQ : Q₁ ⟶ Q) (hjQ : jQ ≫ q = q₁)
    (hU : SubgroupFunctor.range (iU ≫ p) = SubgroupFunctor.range (iU₁ ≫ p₁))
    (hV : SubgroupFunctor.range (iV ≫ q) = SubgroupFunctor.range (iV₁ ≫ q₁))
    (hW : π₁ ≫ c₁ ≫ l₁ ≫ jP = jQ ≫ π ≫ c ≫ l)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (φ : AdelicGroupPoints F G → ℂ)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.intertwiningOperator hQ iU l iV c π w φ lam g =
      hK₁.intertwiningOperator hQ₁ iU₁ l₁ iV₁ c₁ π₁ w φ (parameterRestrict jP lam) g := by
  unfold IsIwasawaCompact.intertwiningOperator
  rw [weylParameter_parameterRestrict_eq l c π l₁ c₁ π₁ jP jQ hW,
    ← map_neg (parameterRestrict jQ), hQ.heightPower_restrict_of_comp_eq hQ₁ jQ hjQ,
    hK.intertwiningIntegral_eq_of_range_eq_of_twist hK₁ iU iU₁ (iV ≫ q) (iV₁ ≫ q₁) hU hV w φ lam
      (parameterRestrict jP lam) (hK.parameterTwist_restrict_of_comp_eq hK₁ jP hjP φ lam) g]

end Transport

section ParameterIso

variable {F : Type u} [Field F]

/-- Restriction of complex parameters along an isomorphism `e : H' ≅ H`, as a linear
isomorphism `X^*(H) ⊗ ℂ ≃ X^*(H') ⊗ ℂ` whose inverse is restriction along `e.inv`. -/
def parameterRestrictIsoEquiv {H H' : GroupScheme (Spec (CommRingCat.of F))} (e : H' ≅ H) :
    ComplexCharacterParameter F H ≃ₗ[ℂ] ComplexCharacterParameter F H' :=
  LinearEquiv.ofLinearMap (parameterRestrict e.hom) (parameterRestrict e.inv)
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro s χ
      change s ⊗ₜ[ℤ] characterRestrict e.hom (characterRestrict e.inv χ) = s ⊗ₜ[ℤ] χ
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, e.hom_inv_id,
        characterRestrict_id]
      rfl)
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro s χ
      change s ⊗ₜ[ℤ] characterRestrict e.inv (characterRestrict e.hom χ) = s ⊗ₜ[ℤ] χ
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, e.inv_hom_id,
        characterRestrict_id]
      rfl)

/-- The linear isomorphism `parameterRestrictIsoEquiv e` is restriction along `e.hom`. -/
theorem parameterRestrictIsoEquiv_apply {H H' : GroupScheme (Spec (CommRingCat.of F))} (e : H' ≅ H)
    (lam : ComplexCharacterParameter F H) :
    parameterRestrictIsoEquiv e lam = parameterRestrict e.hom lam :=
  rfl

end ParameterIso

end AdelicGroupPoints

section RootForms

variable {F : Type u} [Field F] [NumberField F]
  {G P M P' M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T A A' : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)] {nu : cocharacterLattice T}
  {J : Set (characterLattice T)} {f : A ⟶ T} {f' : A' ⟶ T}
  [Mono (CommGroupScheme.groupHom f).hom.hom.left]
  [Mono (CommGroupScheme.groupHom f').hom.hom.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {p' : P' ⟶ G} {l' : M' ⟶ P'} {a' : A'.toGrp ⟶ M'}

/-- For two presentations with the same maximal split torus, generic cocharacter and set of
simple roots, the root form of the restriction `f' ≫ β` to the second split component, at the
restriction of a parameter along a map over the parabolic inclusions, equals the root form of
the restriction `f ≫ β` to the first split component at the parameter itself. Both equal
`B_T(λ|_T, β)` for the Weyl-invariant form of the common torus. -/
theorem rootFunctional_parameterRestrict_eq_of_comp_eq
    (hp : ParabolicRootPresentationData.IsCompatible ⟨T, i, nu, J, f⟩ p l a)
    (hp' : ParabolicRootPresentationData.IsCompatible ⟨T, i, nu, J, f'⟩ p' l' a')
    (hA : IsSplitTorus A.toGrp) (hA' : IsSplitTorus A'.toGrp) (hT : IsSplitTorus T.toGrp)
    (hG : IsConnectedReductive G) (j : P' ⟶ P) (hj : j ≫ p = p')
    (β : characterLattice T) (lam : ComplexCharacterParameter F P) :
    (ParabolicRootPresentation.mk ⟨T, i, nu, J, f'⟩ hp').rootFunctional hA' hT (f' ≫ β)
        (parameterRestrict j lam) =
      (ParabolicRootPresentation.mk ⟨T, i, nu, J, f⟩ hp).rootFunctional hA hT (f ≫ β) lam := by
  let r : ParabolicRootPresentation p l a := ⟨⟨T, i, nu, J, f⟩, hp⟩
  let r' : ParabolicRootPresentation p' l' a' := ⟨⟨T, i, nu, J, f'⟩, hp'⟩
  obtain ⟨t, _, ht⟩ := r.exists_leviTorusLift
  obtain ⟨t', _, ht'⟩ := r'.exists_leviTorusLift
  let : Mono p.hom.hom.left := hp.parabolic.isClosedSubgroup.mono
  have hpOver : Mono p.hom.hom := Over.mono_of_mono_left _
  let : Mono p := (Grp.forget _).mono_of_mono_map (f := p) hpOver
  have htcomp : (t' ≫ l') ≫ j = t ≫ l := by
    apply (cancel_mono p).mp
    simpa only [Category.assoc, hj, r, r'] using ht'.trans ht.symm
  have hform (x : RealCharacterParameter F P) :
      r.realRootFunctional hA hT (f ≫ β) x =
        RealTorusSpace.relativeWeylInvariantForm i hT
          (realParameterRestriction (t ≫ l) x) ((1 : ℝ) ⊗ₜ[ℤ] β) := by
    rw [eisensteinAmbientParameterLift F G P M A p l a r hA hT t hG ht x,
      (Langlands.Plancherel.weylInducedCharacterForm_compatible hA hT f i).2,
      rationalCharacterRestrictReal_tmul]
    rfl
  have hform' (x : RealCharacterParameter F P') :
      r'.realRootFunctional hA' hT (f' ≫ β) x =
        RealTorusSpace.relativeWeylInvariantForm i hT
          (realParameterRestriction (t' ≫ l') x) ((1 : ℝ) ⊗ₜ[ℤ] β) := by
    rw [eisensteinAmbientParameterLift F G P' M' A' p' l' a' r' hA' hT t' hG ht' x,
      (Langlands.Plancherel.weylInducedCharacterForm_compatible hA' hT f' i).2,
      rationalCharacterRestrictReal_tmul]
    rfl
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    change s * (r'.realRootFunctional hA' hT (f' ≫ β)
        ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict j χ) : ℂ) =
      s * (r.realRootFunctional hA hT (f ≫ β) ((1 : ℝ) ⊗ₜ[ℤ] χ) : ℂ)
    have hres : realParameterRestriction (t' ≫ l') ((1 : ℝ) ⊗ₜ[ℤ] characterRestrict j χ) =
        realParameterRestriction (t ≫ l) ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
      change (1 : ℝ) ⊗ₜ[ℤ] characterRestrict (t' ≫ l') (characterRestrict j χ) =
        (1 : ℝ) ⊗ₜ[ℤ] characterRestrict (t ≫ l) χ
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, htcomp]
    rw [hform, hform', hres]
  | add x y hx hy => simp only [map_add, hx, hy]

end RootForms

section Radicals

variable {k : Type u} [Field k]

/-- Unipotent radicals of two parabolics identified by an isomorphism over the ambient group
have the same image in the ambient group. -/
theorem range_comp_unipotentRadical_eq_of_iso
    {U U' P P' G : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {p' : P' ⟶ G} (e : P' ≅ P) (he : e.hom ≫ p = p')
    {iU : U ⟶ P} {iU' : U' ⟶ P'} (hU : IsUnipotentRadical iU)
    (hU' : IsUnipotentRadical iU') :
    SubgroupFunctor.range (iU ≫ p) = SubgroupFunctor.range (iU' ≫ p') := by
  have h := hU.range_eq (hU'.comp_iso e)
  rw [← he, ← Category.assoc]
  exact le_antisymm (SubgroupFunctor.range_comp_mono h.le p)
    (SubgroupFunctor.range_comp_mono h.ge p)

end Radicals

section StandardConjugate

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- A rational parabolic `q : Q → G` with a rational Levi `l' : M' → Q` is conjugate by a
rational point `s` to a standard parabolic `P_{I'}` of a standard family, compatibly with the
Levis: there are an isomorphism `eQ : P_{I'} ≅ Q` over the conjugated embedding
`q ≫ int(s)` and an isomorphism `κ : M_{I'} ≅ M'` with `κ ≫ l' = l_{I'} ≫ eQ`. The unipotent
radicals then have the same image. -/
theorem StandardParabolicFamily.exists_standardConjugate (fam : StandardParabolicFamily F G)
    {Q M' V : GroupScheme (Spec (CommRingCat.of F))} (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl' : IsRationalLeviSubgroup l') :
    ∃ (I' : StandardIndex F G fam.i fam.ν) (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
      (eQ : fam.P I' ≅ Q) (κ : fam.M I' ≅ M'),
      eQ.hom ≫ q ≫ (G.innerIso s).hom = fam.p I' ∧ κ.hom ≫ l' = fam.l I' ≫ eQ.hom ∧
      SubgroupFunctor.range (iV ≫ q ≫ (G.innerIso s).hom) =
        SubgroupFunctor.range (fam.iU I' ≫ fam.p I') := by
  have hG := fam.connectedReductive
  obtain ⟨χ, hχ⟩ := (parabolicDynamic F G hG Q q hq.isClosedSubgroup).mp hq
  obtain ⟨B, ⟨g, hg⟩, -⟩ := (standardParabolicClassification F G hG fam.T fam.i
    fam.maximalSplit fam.ν fam.generic).2 χ
  let I' : StandardIndex F G fam.i fam.ν := B
  have hpI' : IsClosedSubgroup (fam.p I') := (fam.isCompatible I').parabolic.isClosedSubgroup
  have hq₁ : IsClosedSubgroup (q ≫ (G.innerIso g).hom) := hq.isClosedSubgroup.comp_iso _
  have hrange₁ : SubgroupFunctor.range (fam.p I') =
      SubgroupFunctor.range (q ≫ (G.innerIso g).hom) := by
    rw [SubgroupFunctor.range_comp_iso, hχ, (fam.isCompatible I').parabolic_eq]
    exact ((SubgroupFunctor.eq_comap_iso_iff (G.innerIso g)).mp hg).symm
  let eQ₁ : fam.P I' ≅ Q := hpI'.sourceIsoOfRangeEq hq₁ hrange₁
  have heQ₁ : eQ₁.hom ≫ q ≫ (G.innerIso g).hom = fam.p I' :=
    hpI'.sourceIsoOfRangeEq_hom_comp hq₁ hrange₁
  have hl₁ : IsRationalLeviSubgroup (fam.l I' ≫ eQ₁.hom) :=
    (fam.isCompatible I').levi.comp_iso eQ₁
  obtain ⟨u, ⟨e', he'⟩, -⟩ := rationalLeviConjugacy F G hG Q q hq M' (fam.M I') l'
    (fam.l I' ≫ eQ₁.hom) hl' hl₁ V iV hV
  let x : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Q.X := u ≫ iV.hom.hom
  have hnat : (Q.innerIso x).hom ≫ q = q ≫ (G.innerIso (x ≫ q.hom.hom)).hom :=
    innerIso_hom_comp q x
  let s := g * (x ≫ q.hom.hom)
  have hs : q ≫ (G.innerIso s).hom = (Q.innerIso x).hom ≫ q ≫ (G.innerIso g).hom := by
    rw [G.innerIso_mul_hom, ← Category.assoc, ← hnat, Category.assoc]
  let eQ : fam.P I' ≅ Q := eQ₁ ≪≫ (Q.innerIso x).symm
  have heQ : eQ.hom ≫ q ≫ (G.innerIso s).hom = fam.p I' := by
    rw [hs]
    simp only [eQ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    exact heQ₁
  have hκ : e'.symm.hom ≫ l' = fam.l I' ≫ eQ.hom := by
    rw [← cancel_mono (Q.innerIso x).hom]
    simp only [eQ, Iso.symm_hom, Iso.trans_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he', Iso.inv_hom_id_assoc]
  exact ⟨I', s, eQ, e'.symm, heQ, hκ,
    range_comp_unipotentRadical_eq_of_iso eQ heQ hV.1 (fam.isUnipotentRadical I').1⟩

end StandardConjugate

section Main

/-- **Standardization of intertwining operators.** The proof of
`IntertwiningStandardizationStatement`: conjugate the target to a standard parabolic of the
family of the presentation, change the compact to one with the same archimedean factor that
serves every standard parabolic, and identify the parabolics with standard ones. -/
theorem intertwiningStandardization : IntertwiningStandardizationStatement.{u} := by
  classical
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ instW₀ _ hA hT q _ iV l' _ π' w c
    hG hU hq hV hl' hmul hπ' hw K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  -- The standard family of the presentation and the index of `p`.
  let fam : StandardParabolicFamily F G :=
    StandardParabolicFamily.ofMaximalSplitTorus hG r.data.i r.isCompatible.maximalSplit
      r.data.ν r.isCompatible.generic
  let I : StandardIndex F G fam.i fam.ν := ⟨r.data.J, r.isCompatible.subset_simpleRoots⟩
  have hpI : IsClosedSubgroup (fam.p I) := (fam.isCompatible I).parabolic.isClosedSubgroup
  have hp : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
  have hrange : SubgroupFunctor.range (fam.p I) = SubgroupFunctor.range p :=
    (fam.isCompatible I).parabolic_eq.trans r.isCompatible.parabolic_eq.symm
  let e : fam.P I ≅ P := hpI.sourceIsoOfRangeEq hp hrange
  have he : e.hom ≫ p = fam.p I := hpI.sourceIsoOfRangeEq_hom_comp hp hrange
  have hUrange : SubgroupFunctor.range (iU ≫ p) = SubgroupFunctor.range (fam.iU I ≫ fam.p I) :=
    range_comp_unipotentRadical_eq_of_iso e he hU.1 (fam.isUnipotentRadical I).1
  have hLrange : SubgroupFunctor.range (fam.l I ≫ fam.p I) = SubgroupFunctor.range (l ≫ p) :=
    (fam.isCompatible I).levi_eq.trans r.isCompatible.levi_eq.symm
  have hΓ : parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I) =
      parabolicQuotientSubgroup F p iU l :=
    parabolicQuotientSubgroup_eq_of_range_eq hUrange.symm hLrange
  -- The Levi of `P_I` and the Levi of `P` correspond under `e`.
  have hMI : IsClosedSubgroup (fam.l I ≫ fam.p I) :=
    (fam.isCompatible I).levi.isClosedSubgroup.comp hpI
  have hM : IsClosedSubgroup (l ≫ p) := r.isCompatible.levi.isClosedSubgroup.comp hp
  let δ : fam.M I ≅ M := hMI.sourceIsoOfRangeEq hM hLrange
  have hδ : δ.hom ≫ l = fam.l I ≫ e.hom := by
    let : Mono p.hom.hom.left := hp.mono
    have hpOver : Mono p.hom.hom := Over.mono_of_mono_left _
    let : Mono p := (Grp.forget _).mono_of_mono_map (f := p) hpOver
    apply (cancel_mono p).mp
    rw [Category.assoc, Category.assoc, he]
    exact hMI.sourceIsoOfRangeEq_hom_comp hM hLrange
  -- The target is conjugate to a standard parabolic, compatibly with the Levis.
  obtain ⟨I', s, eQ, κ, heQ, hκ, hVrange⟩ := fam.exists_standardConjugate q iV l' hq hV hl'
  let sA := innerAdelicPoint F G s
  have hq'closed : IsClosedSubgroup (q ≫ (G.innerIso s).hom) :=
    hq.isClosedSubgroup.comp_iso _
  have : IsClosedImmersion (q ≫ (G.innerIso s).hom).hom.hom.left := hq'closed
  have : IsClosedImmersion (iV ≫ q ≫ (G.innerIso s).hom).hom.hom.left := by
    have h : IsClosedSubgroup ((iV ≫ q) ≫ (G.innerIso s).hom) :=
      IsClosedSubgroup.comp_iso (i := iV ≫ q)
        (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) _
    rw [Category.assoc] at h
    exact h
  have hq' : IsParabolicSubgroup (q ≫ (G.innerIso s).hom) := hq.comp_iso (G.innerIso s)
  have hrange' : SubgroupFunctor.range (fam.p I') =
      SubgroupFunctor.range (q ≫ (G.innerIso s).hom) :=
    le_antisymm (SubgroupFunctor.range_le_of_factor eQ.hom heQ)
      (SubgroupFunctor.range_le_of_factor eQ.inv (by rw [← heQ, Iso.inv_hom_id_assoc]))
  have hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hφ.1 x (Subgroup.mem_sup_left hx) g
  obtain ⟨hw', hQ', hconj⟩ := intertwiningConjugateTarget F G P M U Q M' V p iU l q iV l' π' w s
    c hw hU.1.isUnipotent K hK hK' φ hφU
  -- A maximal compact subgroup with the archimedean factor of `K`, Iwasawa for every standard
  -- parabolic.
  let I₀ : StandardIndex F G fam.i fam.ν := ⟨∅, Set.empty_subset _⟩
  have hp₀ : IsParabolicSubgroup (fam.p I₀) := (fam.isCompatible _).parabolic
  obtain ⟨K₀, hK₀par, hK₀arch⟩ := iwasawaWithInfiniteCompact F G (fam.P I₀)
    (fam.p I₀) hG hp₀ (K.comap (ofInfinite F G).toMonoidHom)
    hmax.isMaximalCompact_comap_ofInfinite
  have hK₀max : IsMaximalCompactSubgroup F G K₀ := hK₀par.1
  have hK₀ : ∀ J, IsIwasawaCompact (fam.p J) K₀ := by
    intro J
    have hle : SubgroupFunctor.range (fam.p I₀) ≤ SubgroupFunctor.range (fam.p J) :=
      (fam.le_iff_range_le _ _).mp (Set.empty_subset _)
    let : IsClosedImmersion (fam.p I₀).hom.hom.left := hp₀.isClosedSubgroup
    let : IsClosedImmersion (fam.p J).hom.hom.left :=
      (fam.isCompatible J).parabolic.isClosedSubgroup
    let : Mono (fam.p I₀).hom.hom := Over.mono_of_mono_left _
    let : Mono (fam.p J).hom.hom := Over.mono_of_mono_left _
    obtain ⟨f₀, hf₀⟩ := SubgroupFunctor.exists_factor_of_range_le hle
    refine (IsParabolicIwasawaCompact.of_comp f₀ (fam.p J) ?_).isIwasawaCompact
    rw [hf₀]
    exact hK₀par
  have hinf : K.map (infinite F G).toMonoidHom = K₀.map (infinite F G).toMonoidHom := by
    rw [← hmax.comap_ofInfinite_eq_map_infinite, ← hK₀max.comap_ofInfinite_eq_map_infinite,
      hK₀arch]
  have hK₀p : IsIwasawaCompact p K₀ := (hK₀ I).of_range_eq hrange
  have hK₀q' : IsIwasawaCompact (q ≫ (G.innerIso s).hom) K₀ := (hK₀ I').of_range_eq hrange'
  -- The finite change of compact from `K` to `K₀` for the conjugated target.
  obtain ⟨S, cut, hcut, R, hR⟩ := eisensteinFiniteCompactOperatorComparison F G P M U Q M' V A
    p iU l a r hA hT (q ≫ (G.innerIso s).hom) iV l' (s * w) c π' hG hU hq' hV hl' hmul hw'
    K K₀ hK hK₀p hQ' hK₀q' hmax hK₀max hinf rho hsmooth hcalc φ hrho hφ
  -- The difference of the target heights takes finitely many values.
  have hopen := IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq F G K₀ K hmax
    hinf.symm
  have hfin := hK₀q'.finite_range_height_sub hQ' hopen
  let D := hfin.toFinset
  let Δ : AdelicGroupPoints F G → RealCharacterDual F Q := fun y => hK₀q'.height y - hQ'.height y
  have hΔD (y : AdelicGroupPoints F G) : Δ y ∈ D := hfin.mem_toFinset.mpr ⟨y, rfl⟩
  -- The standard data.
  let c₀ : fam.M I' ⟶ fam.M I := κ.hom ≫ c ≫ δ.inv
  let π₀ : fam.P I' ⟶ fam.M I' := eQ.hom ≫ π' ≫ κ.inv
  let iota : ComplexCharacterParameter F P ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P I) :=
    parameterRestrictIsoEquiv e
  have := hw.isIso
  have hW₀ : IsWeylConjugation (fam.p I) (fam.l I) (fam.p I') (fam.l I') (s * w) c₀ := by
    refine ⟨inferInstance, ?_⟩
    have h1 : δ.inv ≫ fam.l I ≫ fam.p I = l ≫ p := by
      rw [← he, ← Category.assoc (fam.l I), ← hδ, Category.assoc, Iso.inv_hom_id_assoc]
    simp only [c₀, Category.assoc, h1, hw'.comp_eq]
    rw [← Category.assoc κ.hom, hκ, Category.assoc, reassoc_of% heQ]
  have hπ₀ : fam.l I' ≫ π₀ = 𝟙 (fam.M I') := by
    simp only [π₀, ← Category.assoc, ← hκ]
    simp only [Category.assoc, reassoc_of% hπ', Iso.hom_inv_id]
  have hW : π₀ ≫ c₀ ≫ fam.l I ≫ e.hom = eQ.hom ≫ π' ≫ c ≫ l := by
    simp only [π₀, c₀, Category.assoc, Iso.inv_hom_id_assoc, ← hδ]
  -- The terms of the sum.
  let T := S ×ˢ D
  let ε : T ≃ Fin T.card := T.equivFin
  let pr (j : Fin T.card) : RealCharacterDual F P × RealCharacterDual F Q := (ε.symm j).val
  let form (x : RealCharacterDual F P × RealCharacterDual F Q) :
      ComplexCharacterParameter F P →ₗ[ℂ] ℂ :=
    (complexParameterPairing F P).flip x.1 +
      ((complexParameterPairing F Q).flip (x.2 + hQ'.height sA)).comp (weylParameter l c π')
  let E : Fin T.card → ComplexCharacterParameter F P → ℂ := fun j lam =>
    Complex.exp (form (pr j) lam)
  let h : Fin T.card → AdelicGroupPoints F G → ℂ := fun j g =>
    if Δ (sA * g) = (pr j).2 then 1 else 0
  let τ : Fin T.card → AdelicGroupPoints F G → AdelicGroupPoints F G := fun _ g => sA * g
  let φ₀ : Fin T.card → AdelicGroupPoints F G → ℂ := fun j => cut (pr j).1
  have hpr (j : Fin T.card) : (pr j).1 ∈ S := (Finset.mem_product.mp (ε.symm j).2).1
  have hmonoF : ∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left := by
    intro J
    let := (fam.isCompatible J).splitComponent.1.isSplitSubtorus.mono
    let := (fam.isCompatible J).levi.isClosedSubgroup.mono
    let := (fam.isCompatible J).parabolic.isClosedSubgroup.mono
    have : Mono (fam.a J ≫ fam.l J ≫ fam.p J).hom.hom.left := by
      change Mono ((fam.a J).hom.hom.left ≫ (fam.l J).hom.hom.left ≫ (fam.p J).hom.hom.left)
      infer_instance
    exact mono_of_mono_fac
      (congrArg (fun z => z.hom.hom.left) (fam.isCompatible J).factor_comp)
  have := hmonoF I
  have instCI : ∀ J, IsClosedImmersion (fam.p J).hom.hom.left :=
    fun J => (fam.isCompatible J).parabolic.isClosedSubgroup
  refine ⟨fam, I, I', K₀, hK₀, s * w, c₀, π₀, iota, T.card, E, h, τ, φ₀, hK₀max, hW₀, hπ₀,
    fun j => ?_, fun j n e' => ?_, instW₀, instCI, hmonoF, fun R' => ⟨R', fun lam hlam => ?_⟩,
    ?_, R, fun lam hlam g => ?_⟩
  · -- automorphy of the new inducing data
    change IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) _ rho (cut (pr j).1)
    rw [hΓ]
    exact hcut _ (hpr j)
  · -- the coefficients are entire
    exact ((form (pr j)).comp e'.toLinearMap).toContinuousLinearMap.differentiable.cexp
  · -- regularity transport
    exact (eisensteinRegularityParabolicTransport F G P M (fam.P I) (fam.M I) r.data.T A
      (fam.A I) r.data.i r.data.ν r.data.J r.data.f (fam.f I) p l a (fam.p I) (fam.l I)
      (fam.a I) r.isCompatible (fam.isCompatible I) hA
      (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1 hT hG e.hom he R' lam).mpr hlam
  · -- root-form kernels
    rintro β₀ ⟨hβ₀, χ, hχ, rfl⟩
    refine ⟨r.data.f ≫ χ, ⟨fun h0 => hβ₀ ?_, χ, hχ, rfl⟩, fun ν hν => ?_⟩
    · exact ((fam.rootPresentation I).restrict_positiveRoot_eq_zero_iff hχ).mpr
        ((r.restrict_positiveRoot_eq_zero_iff hχ).mp h0)
    · rw [parameterRestrictIsoEquiv_apply]
      exact (rootFunctional_parameterRestrict_eq_of_comp_eq r.isCompatible (fam.isCompatible I) hA
        (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1 hT hG e.hom he χ ν).trans hν
  · -- the comparison of operators
    have hreg := (hR lam hlam (sA * g)).2
    simp only [IsIwasawaCompact.parameterTwist] at hreg
    -- conjugation of the target by `s`
    have h1 : hK.intertwiningOperator hK' iU l iV c π' w φ lam g =
        hQ'.heightPower (weylParameter l c π' lam) sA *
          hK.intertwiningOperator hQ' iU l iV c π' (s * w) φ lam (sA * g) := by
      rw [hconj lam g, ← mul_assoc, hQ'.heightPower_mul_neg, one_mul]
    -- the finite change of compact, solved for the operator
    have h2 : hK.intertwiningOperator hQ' iU l iV c π' (s * w) φ lam (sA * g) =
        ∑ v ∈ S, Complex.exp (complexParameterPairing F P lam v) *
          hK₀p.intertwiningOperator hK₀q' iU l iV c π' (s * w) (cut v) lam (sA * g) *
            (hK₀q'.heightPower (weylParameter l c π' lam) (sA * g) *
              hQ'.heightPower (-weylParameter l c π' lam) (sA * g)) := by
      calc
        _ = hK.intertwiningOperator hQ' iU l iV c π' (s * w) φ lam (sA * g) *
              hQ'.heightPower (weylParameter l c π' lam) (sA * g) *
                hQ'.heightPower (-weylParameter l c π' lam) (sA * g) := by
          rw [mul_assoc, hQ'.heightPower_mul_neg, mul_one]
        _ = _ := by
          rw [hreg, Finset.sum_mul]
          exact Finset.sum_congr rfl fun v _ => by ring
    -- passage to the standard parabolics
    have h3 (v : RealCharacterDual F P) :
        hK₀p.intertwiningOperator hK₀q' iU l iV c π' (s * w) (cut v) lam (sA * g) =
          (hK₀ I).intertwiningOperator (hK₀ I') (fam.iU I) (fam.l I) (fam.iU I') c₀ π₀ (s * w)
            (cut v) (iota lam) (sA * g) :=
      hK₀p.intertwiningOperator_eq_of_transport hK₀q' (hK₀ I) (hK₀ I') iU l iV c π' (fam.iU I)
        (fam.l I) (fam.iU I') c₀ π₀ e.hom he eQ.hom heQ hUrange hVrange hW (s * w) (cut v) lam
        (sA * g)
    -- the ratio of the target height powers
    have h4 (y : AdelicGroupPoints F G) :
        hK₀q'.heightPower (weylParameter l c π' lam) y *
            hQ'.heightPower (-weylParameter l c π' lam) y =
          ∑ x ∈ D, (if Δ y = x then 1 else 0) *
            Complex.exp (complexParameterPairing F Q (weylParameter l c π' lam) x) := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq D (Δ y), ite_eq_left (hΔD y)]
      simp only [IsIwasawaCompact.heightPower, ← Complex.exp_add, Δ, map_sub, map_neg,
        LinearMap.neg_apply, ← sub_eq_add_neg]
    have hsum : ∑ j : Fin T.card, E j lam * h j g *
        (hK₀ I).intertwiningOperator (hK₀ I') (fam.iU I) (fam.l I) (fam.iU I') c₀ π₀ (s * w)
          (φ₀ j) (iota lam) (τ j g) =
        ∑ x ∈ T, Complex.exp (form x lam) * (if Δ (sA * g) = x.2 then 1 else 0) *
          (hK₀ I).intertwiningOperator (hK₀ I') (fam.iU I) (fam.l I) (fam.iU I') c₀ π₀ (s * w)
            (cut x.1) (iota lam) (sA * g) := by
      have hprε (x : T) : pr (ε x) = x.val := by
        simp only [pr, Equiv.symm_apply_apply]
      rw [← Finset.sum_coe_sort T]
      exact (Fintype.sum_equiv ε _ _ (fun x => by
        dsimp only [E, h, τ, φ₀]
        rw [hprε x])).symm
    rw [hsum, Finset.sum_product, h1, h2]
    simp_rw [h3, h4]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [form, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.flip_apply, map_add,
      Complex.exp_add, IsIwasawaCompact.heightPower]
    ring

end Main

end Langlands.Global

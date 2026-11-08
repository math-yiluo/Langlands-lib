import Langlands.Geometry.Building.OmegaCompatibleApartmentRigidity
import Langlands.Geometry.Building.IntegerCentralizer

/-! # Rigidity of centralizer-compatible apartment classes over any field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

private theorem eval_sub_zsmul_char' {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (a b : characterLattice S) (z : ℤ) (w : V S) :
    eval S (a - z • b) w = eval S a w - (z : ℝ) * eval S b w := by
  rw [eval_eq_pair, eval_eq_pair, eval_eq_pair, TensorProduct.tmul_sub,
    TensorProduct.tmul_smul, map_sub, map_zsmul, LinearMap.sub_apply,
    LinearMap.smul_apply, zsmul_eq_mul]

section Coroot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (hS : IsSplitTorus S.toGrp)
    {α : relativeRoots i} {u : rationalPoints G}
    (hu : u ∈ rootGroupPoints i α) (h1 : u ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i (α : characterLattice S) u p)

/-- The class in the apartment translation space of the integral coroot of an
actual opposite factor pair. -/
def oppositeFactorPairCorootClass : TranslationSpace i :=
  Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] hp.coroot i hS α.property.1 hu h1)

/-- The root takes value two on the actual pair coroot class. -/
theorem rootForm_oppositeFactorPairCorootClass :
    rootForm i α (oppositeFactorPairCorootClass hS hu h1 hp) = 2 := by
  simp only [oppositeFactorPairCorootClass, rootForm_mk, eval_tmul, one_mul]
  exact_mod_cast (hp.coroot_spec i hS α.property.1 hu h1).1

/-- The linear action of the actual product of an opposite factor pair is the
reflection along its coroot class. -/
theorem translationAction_oppositeFactorPair (w : TranslationSpace i) :
    translationAction i ⟨p.1 * u * p.2, hp.2.2⟩ w =
      w - rootForm i α w • oppositeFactorPairCorootClass hS hu h1 hp := by
  let ν := hp.coroot i hS α.property.1 hu h1
  obtain ⟨hν, hr⟩ := hp.coroot_spec i hS α.property.1 hu h1
  let m : normalizerPoints i := ⟨p.1 * u * p.2, hp.2.2⟩
  have hr' : ∀ χ, weylAction i m χ = χ - latticePairing S χ ν • α.val := hr
  have h2 : ∀ χ, weylAction i m (weylAction i m χ) = χ := by
    intro χ
    rw [hr', hr', map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hν,
      smul_eq_mul]
    module
  have hinv : ∀ χ, weylAction i m⁻¹ χ = χ - latticePairing S χ ν • α.val := by
    intro χ
    calc
      weylAction i m⁻¹ χ = weylAction i m⁻¹ (weylAction i m (weylAction i m χ)) := by
        rw [h2]
      _ = weylAction i m χ := by
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          LinearEquiv.coe_one, id]
      _ = _ := hr' χ
  refine Submodule.Quotient.induction_on _ w fun v => ?_
  rw [translationAction_mk]
  change (Submodule.Quotient.mk (m • v) : TranslationSpace i) =
    Submodule.Quotient.mk v - eval S α.val v •
      Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν)
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
  refine mem_rootAnnihilator.2 fun b _ => ?_
  rw [map_sub, map_sub, eval_normalizer_smul, hinv, eval_sub_zsmul_char',
    map_smul, eval_tmul, one_mul]
  ring

end Coroot

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ}

section Reflection

variable (D : KPApartmentData i ω)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

include hG hi in
/-- AS 1 over any field: the actual product of an opposite factor pair fixes
every apartment point at which the root value of the middle point vanishes. -/
theorem oppositeFactorPair_smul_eq_self {α : relativeRoots i} {u : rationalPoints G}
    (hu : u ∈ rootGroupPoints i α) (h1 : u ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i (α : characterLattice S) u p)
    (x : D.Apartment) (hx : x.val α u = 0) :
    (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • x = x := by
  have := hG.smooth
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hfin := hS.finite_relativeRoots i
  obtain ⟨a, ha⟩ := α
  have ha0 : a ≠ 0 := ha.1
  set m : normalizerPoints i := ⟨p.1 * u * p.2, hp.2.2⟩ with hm_def
  have hmG : (m : rationalPoints G) = p.1 * u * p.2 := rfl
  have hφ := x.isValuation
  obtain ⟨v, hv⟩ := D.equipollent_of_mem x.mem (m • x).mem
  rw [KPApartmentData.val_smul] at hv
  obtain ⟨hν, hr⟩ := hp.coroot_spec i hS ha0 hu h1
  set ν := hp.coroot i hS ha0 hu h1 with hν_def
  have hr' : ∀ χ, weylAction i m χ = χ - latticePairing S χ ν • a := hr
  have h2 : ∀ χ, weylAction i m (weylAction i m χ) = χ := by
    intro χ
    rw [hr', hr', map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hν,
      smul_eq_mul]
    module
  have hinv : ∀ χ, weylAction i m⁻¹ χ = χ - latticePairing S χ ν • a := by
    intro χ
    calc weylAction i m⁻¹ χ = weylAction i m⁻¹ (weylAction i m (weylAction i m χ)) := by
          rw [h2]
      _ = weylAction i m χ := by
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one,
            id]
      _ = _ := hr' χ
  have hma : weylAction i m a = -a := by
    rw [hr', hν, show a - (2 : ℤ) • a = -a by module]
  have hmna : weylAction i m⁻¹ (-a) = a := by
    rw [hinv, map_neg, LinearMap.neg_apply, hν, show -a - (-2 : ℤ) • a = a by module]
  have hna : -a ∈ relativeRoots i := hma ▸ weylAction_mapsTo_relativeRoots i m ha
  have hu0 : x.val a u = 0 := hx
  have hp1 : x.val (-a) p.1 = 0 := by
    have := hφ.opposite a ha u hu h1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    rwa [hu0, add_zero] at this
  have hminv : p.2⁻¹ * u⁻¹ * p.1⁻¹ ∈ normalizerPoints i := by
    have : p.2⁻¹ * u⁻¹ * p.1⁻¹ = (m : rationalPoints G)⁻¹ := by
      rw [hmG]
      group
    rw [this]
    exact inv_mem m.2
  have hp2 : x.val (-a) p.2 = 0 := by
    have := hφ.opposite a ha u⁻¹ (inv_mem hu) (inv_ne_one.2 h1) p.2⁻¹ (inv_mem hp.2.1)
      p.1⁻¹ (inv_mem hp.1) hminv
    rwa [RootReflectionProof.apply_inv hφ, RootReflectionProof.apply_inv hφ, hu0,
      add_zero] at this
  have hmc : (m : rationalPoints G) ∈
      Subgroup.closure (rootFiltration i x.val a 0 ∪ rootFiltration i x.val (-a) 0) := by
    rw [hmG]
    refine mul_mem (mul_mem (Subgroup.subset_closure (Or.inr ⟨hp.1, ?_⟩))
      (Subgroup.subset_closure (Or.inl ⟨hu, ?_⟩)))
      (Subgroup.subset_closure (Or.inr ⟨hp.2.1, ?_⟩))
    · rw [hp1, WithTop.coe_zero]
    · rw [hu0, WithTop.coe_zero]
    · rw [hp2, WithTop.coe_zero]
  obtain ⟨y, hy_def⟩ : ∃ y, y = (m : rationalPoints G)⁻¹ * p.1 * m := ⟨_, rfl⟩
  have hy : y ∈ rootGroupPoints i a := by
    have := conj_mem_rootGroupPoints m⁻¹ (a := -a) hp.1
    rwa [hmna, InvMemClass.coe_inv, inv_inv, ← hy_def] at this
  have hminv' : y⁻¹ * p.2⁻¹ * u⁻¹ ∈ normalizerPoints i := by
    have : y⁻¹ * p.2⁻¹ * u⁻¹ = (m : rationalPoints G)⁻¹ := by
      rw [hy_def, hmG]
      group
    rw [this]
    exact inv_mem m.2
  have hp2ne := (hp.factors_ne_one i hS ha0 hu h1).2
  have hy0 : x.val a y = 0 := by
    have := hφ.opposite (-a) hna p.2⁻¹ (inv_mem hp.2.1) (inv_ne_one.2 hp2ne) y⁻¹
      (by rw [neg_neg]; exact inv_mem hy) u⁻¹ (by rw [neg_neg]; exact inv_mem hu) hminv'
    rwa [neg_neg, RootReflectionProof.apply_inv hφ, RootReflectionProof.apply_inv hφ, hp2,
      add_zero] at this
  have hav : eval S a v = 0 := by
    have hval := congrArg (fun ψ : RootFunctionFamily S G => ψ (-a) p.1) hv
    simp only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply, hmna, ← hy_def,
      hy0, hp1, zero_add, eval_neg_char] at hval
    have := (WithTop.coe_eq_zero.1 hval.symm)
    linarith
  have hall : ∀ d ∈ relativeRoots i, eval S d v = 0 := by
    intro d hd
    rcases lt_trichotomy (eval S d v) 0 with hlt | heq | hgt
    · exact (RootReflectionProof.not_eval_neg hS hφ hfin ha hν hinv hmc hv hav hd hlt).elim
    · exact heq
    · exfalso
      have hv' : m⁻¹ • x.val = (-(m⁻¹ • v)) +ᵥ x.val := by
        have h := congrArg (m⁻¹ • ·) hv
        simp only [inv_smul_smul, RootFunctionFamily.smul_vadd] at h
        calc m⁻¹ • x.val = -(m⁻¹ • v) +ᵥ ((m⁻¹ • v) +ᵥ m⁻¹ • x.val) := by
              rw [neg_vadd_vadd]
          _ = _ := by rw [← h]
      refine RootReflectionProof.not_eval_neg (n := m⁻¹) hS hφ hfin ha hν
        (fun χ => by rw [inv_inv]; exact hr' χ) ?_ hv' ?_
        (weylAction_mapsTo_relativeRoots i m hd) ?_
      · rw [InvMemClass.coe_inv]
        exact inv_mem hmc
      · rw [map_neg, eval_normalizer_smul, inv_inv, hma, eval_neg_char, hav, neg_zero, neg_zero]
      · rw [map_neg, eval_normalizer_smul, inv_inv, h2]
        linarith
  refine KPApartmentData.Apartment.ext ?_
  rw [KPApartmentData.val_smul, hv]
  exact hφ.vadd_eq_self_iff.2 (mem_rootAnnihilator.2 hall)

include hG hi in
/-- Applying the root to the displacement of an actual opposite-pair product
recovers twice the negative root value. -/
theorem rootForm_oppositeFactorPair_vsub {α : relativeRoots i} {u : rationalPoints G}
    (hu : u ∈ rootGroupPoints i α) (h1 : u ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i (α : characterLattice S) u p)
    (x : D.Apartment) {t : ℝ} (ht : x.val α u = t) :
    rootForm i α ((⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • x -ᵥ x) = -2 * t := by
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hc := rootForm_oppositeFactorPairCorootClass hS hu h1 hp
  obtain ⟨d, hd⟩ : ∃ d : TranslationSpace i,
      d = (-(t / 2)) • oppositeFactorPairCorootClass hS hu h1 hp := ⟨_, rfl⟩
  have hdα : rootForm i α d = -t := by
    rw [hd, map_smul, hc, smul_eq_mul]
    ring
  obtain ⟨x0, hx0⟩ : ∃ x0 : D.Apartment, x0 = d +ᵥ x := ⟨_, rfl⟩
  have hx0α : x0.val α u = 0 := by
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ d
    rw [hx0, val_mk_vadd, RootFunctionFamily.vadd_apply, ht]
    rw [rootForm_mk] at hdα
    rw [hdα, ← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero]
  have hfix := D.oppositeFactorPair_smul_eq_self hG hi hu h1 hp x0 hx0α
  have hx : x = (-d) +ᵥ x0 := by
    rw [hx0, neg_vadd_vadd]
  have hmx : (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • x =
      translationAction i ⟨p.1 * u * p.2, hp.2.2⟩ (-d) +ᵥ x0 := by
    calc
      _ = (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • ((-d) +ᵥ x0) :=
        congrArg (fun y : D.Apartment => (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • y) hx
      _ = _ := by rw [smul_vadd, hfix]
  have hdisp : (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • x -ᵥ x =
      translationAction i ⟨p.1 * u * p.2, hp.2.2⟩ (-d) - (-d) := by
    calc
      _ = (translationAction i ⟨p.1 * u * p.2, hp.2.2⟩ (-d) +ᵥ x0) -ᵥ ((-d) +ᵥ x0) := by
        rw [← hmx, ← hx]
      _ = _ := vadd_vsub_vadd_cancel_right _ _ _
  rw [hdisp, map_sub, translationAction_oppositeFactorPair hS hu h1 hp, map_sub, map_smul,
    hc, smul_eq_mul, map_neg, hdα]
  ring

include hG hi in
/-- An equivariant affine comparison with identity derivative preserves the
root value of every nonidentity root point admitting an actual opposite pair. -/
theorem val_eq_of_equivariant_of_oppositeFactorPair (E : KPApartmentData i ω)
    (f : D.Apartment ≃ᵃ[ℝ] E.Apartment)
    (hlinear : f.linear = LinearEquiv.refl ℝ (TranslationSpace i))
    (hequiv : ∀ (n : normalizerPoints i) (x : D.Apartment), f (n • x) = n • f x)
    {α : relativeRoots i} {u : rationalPoints G}
    (hu : u ∈ rootGroupPoints i α) (h1 : u ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i (α : characterLattice S) u p)
    (x : D.Apartment) :
    (f x).val α u = x.val α u := by
  have hdisp : (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • f x -ᵥ f x =
      (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • x -ᵥ x := by
    rw [← hequiv]
    have hf := f.toAffineMap.linearMap_vsub
      ((⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • x) x
    change f.linear _ = _ at hf
    rw [hlinear, LinearEquiv.refl_apply] at hf
    exact hf.symm
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
    (fun h => h1 ((x.isValuation.eq_top_iff α α.property u hu).1 h))
  obtain ⟨t', ht'⟩ := WithTop.ne_top_iff_exists.1
    (fun h => h1 (((f x).isValuation.eq_top_iff α α.property u hu).1 h))
  have hD := D.rootForm_oppositeFactorPair_vsub hG hi hu h1 hp x ht.symm
  have hE := E.rootForm_oppositeFactorPair_vsub hG hi hu h1 hp (f x) ht'.symm
  rw [hdisp, hD] at hE
  rw [← ht, ← ht']
  exact_mod_cast (by linarith : t' = t)

include hG hi in
/-- Under actual opposite-pair existence, an equivariant affine comparison with
identity derivative identifies the two full apartment classes. -/
theorem eq_of_equivariant_of_hasOppositeFactorPairs (E : KPApartmentData i ω)
    (hpair : RelativeRoot.HasOppositeFactorPairs i)
    (f : D.Apartment ≃ᵃ[ℝ] E.Apartment)
    (hlinear : f.linear = LinearEquiv.refl ℝ (TranslationSpace i))
    (hequiv : ∀ (n : normalizerPoints i) (x : D.Apartment), f (n • x) = n • f x) :
    D = E := by
  obtain ⟨x⟩ := (inferInstance : Nonempty D.Apartment)
  apply eq_of_common_mem x.mem
  have hval : (f x).val = x.val := by
    apply (f x).isValuation.eq_of_eq_on_nonidentity_root_points x.isValuation
    intro α g hg hg1
    obtain ⟨p, hp⟩ := hpair α α.property g hg hg1
    exact D.val_eq_of_equivariant_of_oppositeFactorPair hG hi E f hlinear hequiv hg hg1 hp x
  rw [← hval]
  exact (f x).mem

end Reflection

section Averaging

variable (D E : KPApartmentData i ω)

/-- The actual centralizer points displace the points of both classes by the
same translations. -/
def HasCommonCentralizerDisplacements : Prop :=
  ∀ n : normalizerPoints i, (n : rationalPoints G) ∈ centralizerPoints i →
    ∀ (x : D.Apartment) (y : E.Apartment), n • y -ᵥ y = n • x -ᵥ x

theorem normalizerDisplacement_mul (x : D.Apartment) (n m : normalizerPoints i) :
    (n * m) • x -ᵥ x =
      translationAction i n (m • x -ᵥ x) + (n • x -ᵥ x) := by
  rw [mul_smul]
  have h := ((D.normalizerAffineEquiv n).toAffineMap.linearMap_vsub (m • x) x).symm
  change n • (m • x) -ᵥ n • x = translationAction i n (m • x -ᵥ x) at h
  rw [← h, vsub_add_vsub_cancel]

/-- The difference of the two displacement cocycles at chosen points. -/
def centralizerComparisonDefect (x : D.Apartment) (y : E.Apartment)
    (n : normalizerPoints i) : TranslationSpace i :=
  (n • y -ᵥ y) - (n • x -ᵥ x)

theorem centralizerComparisonDefect_mul (x : D.Apartment) (y : E.Apartment)
    (n m : normalizerPoints i) :
    centralizerComparisonDefect D E x y (n * m) =
      centralizerComparisonDefect D E x y n +
        translationAction i n (centralizerComparisonDefect D E x y m) := by
  simp only [centralizerComparisonDefect, normalizerDisplacement_mul, map_sub]
  abel

variable {D E}

theorem centralizerComparisonDefect_eq_zero
    (hC : D.HasCommonCentralizerDisplacements E)
    (x : D.Apartment) (y : E.Apartment) (n : normalizerPoints i)
    (hn : (n : rationalPoints G) ∈ centralizerPoints i) :
    centralizerComparisonDefect D E x y n = 0 := by
  rw [centralizerComparisonDefect, hC n hn x y, sub_self]

theorem centralizerComparisonDefect_eq_of_weylClass_eq
    (hC : D.HasCommonCentralizerDisplacements E)
    (x : D.Apartment) (y : E.Apartment) (n m : normalizerPoints i)
    (hnm : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk m) :
    centralizerComparisonDefect D E x y n = centralizerComparisonDefect D E x y m := by
  have hz : (m⁻¹ * n : normalizerPoints i) ∈
      (centralizerPoints i).subgroupOf (normalizerPoints i) :=
    QuotientGroup.eq.mp hnm.symm
  have hc := centralizerComparisonDefect_eq_zero hC x y (m⁻¹ * n) hz
  have hn : n = m * (m⁻¹ * n) := by group
  conv_lhs => rw [hn]
  rw [centralizerComparisonDefect_mul, hc, map_zero, add_zero]

variable (D E)

/-- The averaging correction over the actual finite relative Weyl quotient. -/
def centralizerComparisonCorrection [Fintype (relativeWeylGroup i)]
    (x : D.Apartment) (y : E.Apartment) : TranslationSpace i :=
  FiniteQuotientAffineComparison.average
    (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
    (QuotientGroup.mk'_surjective _) (centralizerComparisonDefect D E x y)

variable {D E}

theorem centralizerComparisonCorrection_spec [Fintype (relativeWeylGroup i)]
    (hC : D.HasCommonCentralizerDisplacements E)
    (x : D.Apartment) (y : E.Apartment) (n : normalizerPoints i) :
    centralizerComparisonDefect D E x y n +
        translationAction i n (centralizerComparisonCorrection D E x y) =
      centralizerComparisonCorrection D E x y :=
  FiniteQuotientAffineComparison.average_spec _ _ _ _
    (centralizerComparisonDefect_mul D E x y)
    (centralizerComparisonDefect_eq_of_weylClass_eq hC x y) n

variable (D E)

/-- The affine comparison with identity derivative obtained by averaging the
displacement defect over the actual finite relative Weyl quotient. -/
def centralizerComparisonAffineEquiv
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    D.Apartment ≃ᵃ[ℝ] E.Apartment := by
  let := hG.finite_relativeWeylGroup i hi
  let := Fintype.ofFinite (relativeWeylGroup i)
  let x : D.Apartment := Classical.arbitrary _
  let y : E.Apartment := Classical.arbitrary _
  exact (AffineEquiv.vaddConst ℝ x).symm.trans
    (AffineEquiv.vaddConst ℝ (centralizerComparisonCorrection D E x y +ᵥ y))

@[simp]
theorem centralizerComparisonAffineEquiv_linear
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    (centralizerComparisonAffineEquiv D E hG hi).linear =
      LinearEquiv.refl ℝ (TranslationSpace i) := by
  rfl

variable {D E}

theorem centralizerComparisonAffineEquiv_smul
    (hC : D.HasCommonCentralizerDisplacements E)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (n : normalizerPoints i) (z : D.Apartment) :
    centralizerComparisonAffineEquiv D E hG hi (n • z) =
      n • centralizerComparisonAffineEquiv D E hG hi z := by
  let := hG.finite_relativeWeylGroup i hi
  let := Fintype.ofFinite (relativeWeylGroup i)
  let x : D.Apartment := Classical.arbitrary _
  let y : E.Apartment := Classical.arbitrary _
  let b := centralizerComparisonCorrection D E x y
  change (n • z -ᵥ x) +ᵥ (b +ᵥ y) =
    n • ((z -ᵥ x) +ᵥ (b +ᵥ y))
  have h := centralizerComparisonCorrection_spec hC x y n
  change (n • y -ᵥ y) - (n • x -ᵥ x) + translationAction i n b = b at h
  have h' : (n • x -ᵥ x) + b =
      translationAction i n b + (n • y -ᵥ y) := by
    calc
      _ = (n • x -ᵥ x) +
          ((n • y -ᵥ y) - (n • x -ᵥ x) + translationAction i n b) :=
        congrArg ((n • x -ᵥ x) + ·) h.symm
      _ = _ := by abel
  have hz := ((D.normalizerAffineEquiv n).toAffineMap.linearMap_vsub z x).symm
  change n • z -ᵥ n • x = translationAction i n (z -ᵥ x) at hz
  rw [smul_vadd, smul_vadd, vadd_vadd, vadd_vadd,
    ← vsub_add_vsub_cancel (n • z) (n • x) x, hz, add_assoc, h',
    ← add_assoc, ← vadd_vadd, vsub_vadd]

/-- Classes with common centralizer displacements coincide under actual
opposite-pair existence. -/
theorem eq_of_hasCommonCentralizerDisplacements_of_hasOppositeFactorPairs
    (hC : D.HasCommonCentralizerDisplacements E)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hpair : RelativeRoot.HasOppositeFactorPairs i) :
    D = E :=
  D.eq_of_equivariant_of_hasOppositeFactorPairs hG hi E hpair
    (centralizerComparisonAffineEquiv D E hG hi)
    (centralizerComparisonAffineEquiv_linear D E hG hi)
    (centralizerComparisonAffineEquiv_smul hC hG hi)

end Averaging

end KPApartmentData

namespace IntegerValuation

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {D E : KPApartmentData i (order v)} {C : CentralizerDatum i}

/-- Two classes satisfying integer-valued V 6 on the same actual centralizer
have common centralizer displacements. -/
theorem IsOmegaCompatible.hasCommonCentralizerDisplacements
    (hD : IsOmegaCompatible v D C) (hE : IsOmegaCompatible v E C) :
    D.HasCommonCentralizerDisplacements E := by
  intro n hn x y
  rw [← torusCentralizer_carrier_base, ← C.isRepresentedBy.2] at hn
  change ∃ z : rationalPoints C.Z, rationalPoints.map C.j z = (n : rationalPoints G) at hn
  obtain ⟨z, hz⟩ := hn
  have hnz : C.toNormalizer z = n := Subtype.ext hz
  rw [← hnz, hD.smul_eq_vadd, hE.smul_eq_vadd, vadd_vsub, vadd_vsub]

/-- Integer-valued omega-compatible classes coincide under actual opposite-pair
existence, over an arbitrary field. -/
theorem IsOmegaCompatible.eq_of_hasOppositeFactorPairs
    (hD : IsOmegaCompatible v D C) (hE : IsOmegaCompatible v E C)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hpair : RelativeRoot.HasOppositeFactorPairs i) :
    D = E :=
  KPApartmentData.eq_of_hasCommonCentralizerDisplacements_of_hasOppositeFactorPairs
    (hD.hasCommonCentralizerDisplacements hE) hG hi hpair

end IntegerValuation

/-- The class-rigidity step of KP Proposition 6.2.6 for an integer-valued
valuation on an arbitrary field. Actual opposite-factor-pair existence is
retained as a premise. -/
def IntegerOmegaCompatibleApartmentRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G)
      [Mono i.hom.hom.left],
      IsMaximalSplitTorus i →
      RelativeRoot.HasOppositeFactorPairs i →
      ∀ (C : CentralizerDatum i)
        (D E : KPApartmentData i (IntegerValuation.order v)),
        IntegerValuation.IsOmegaCompatible v D C →
        IntegerValuation.IsOmegaCompatible v E C → D = E

/-- Integer-valued omega-compatible classes coincide under actual opposite-pair
existence, in every universe. -/
theorem integerOmegaCompatibleApartmentRigidity :
    IntegerOmegaCompatibleApartmentRigidityStatement.{u} := by
  intro k _ v G _ hG S i _ hi hpair C D E hD hE
  exact hD.eq_of_hasOppositeFactorPairs hE hG hi hpair

end Langlands.Geometry.Building

import Langlands.Representation.Jacquet.StandardCasselmanConstantTerm
import Langlands.Representation.Jacquet.DynamicCasselmanConstantTerm
import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # The standard and the dynamic constant terms of Proposition I.6.2 agree

The Library has two actual forms of Waldspurger's Proposition I.6.2. The standard form
(`standardConstantTerm`) uses the source's cones `|α(a)|_F < ε`, `α ∈ Δ(P_J)`, of a compatible
split component `A` of `M_J`. The dynamic form (`dynamicConstantTerm`) uses the tails
`{χ(t)^r ; r ≥ r₀}` of a cocharacter `χ` and a unit `t` with `t^n → 0`. For a standard
cocharacter `ζ` of `J` the actual parabolic `P_J` is the dynamic parabolic of `χ = ζ ∘ i`; this
module proves that the two constant terms then agree for every `t` with `t^n → 0`. In particular
the dynamic constant term along a standard cocharacter does not depend on `t` or on `ζ`.
-/

noncomputable section

universe u v w uV

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.DynamicUnipotentContainment
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Jacquet

section Abstract

/-- The Haar modulus of conjugation on a closed subgroup depends only on the subgroup and on the
conjugating element. -/
theorem closedRestrictCharacter_congr {H : Type u} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [IsTopologicalGroup H] {U U' : Subgroup H} (hUU : U = U')
    (hU : IsClosed (U : Set H)) (hU' : IsClosed (U' : Set H)) {M M' : Subgroup H}
    (hM : M ≤ Subgroup.normalizer (U : Set H)) (hM' : M' ≤ Subgroup.normalizer (U' : Set H))
    {m : M} {m' : M'} (hm : (m : H) = m') :
    HaarModulus.closedRestrictCharacter U hU M hM m =
      HaarModulus.closedRestrictCharacter U' hU' M' hM' m' := by
  subst hUU
  simp only [HaarModulus.closedRestrictCharacter, MonoidHom.comp_apply]
  congr 1
  exact Subtype.ext hm

/-- Right finiteness is preserved by composition with a group homomorphism `e : M' → M` that maps
`Z'` into `Z`. -/
theorem isRightFinite_comp {M : Type v} {M' : Type w} [Group M] [Group M'] {Z : Subgroup M}
    {Z' : Subgroup M'} (e : M' →* M) (hZ : ∀ x ∈ Z', e x ∈ Z) {φ : M → ℂ}
    (h : HarishChandraSchwartz.IsRightFinite Z φ) :
    HarishChandraSchwartz.IsRightFinite Z' (φ ∘ e) := by
  obtain ⟨V, hV, hφ, hVZ⟩ := h
  let L : (M → ℂ) →ₗ[ℂ] (M' → ℂ) := LinearMap.funLeft ℂ ℂ e
  have := hV
  refine ⟨V.map L, inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
  rintro x hx _ ⟨ψ, hψ, rfl⟩
  refine ⟨fun m => ψ (m * e x), hVZ (e x) (hZ x hx) ψ hψ, ?_⟩
  funext m
  simp [L, LinearMap.funLeft_apply, map_mul]

end Abstract

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- **`M_J(F) = Z(χ)(F)`**: when the standard Levi of `J` is the dynamic centralizer of `χ`, the
identification of the two groups of actual points. -/
def standardLeviDynamicEquiv (hM : standardLevi i ν J = Dynamic.centralizer χ) :
    dynamicLeviPoints χ ≃* standardLeviPoints i ν J :=
  MulEquiv.subgroupCongr
    (congrArg (fun P : SubgroupFunctor G => P.carrier (Over.mk (𝟙 _))) hM).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
@[simp] theorem coe_standardLeviDynamicEquiv (hM : standardLevi i ν J = Dynamic.centralizer χ)
    (m : dynamicLeviPoints χ) :
    ((standardLeviDynamicEquiv χ hM m : standardLeviPoints i ν J) : rationalPoints G) =
      (m : RationalPoint F G.X) :=
  rfl

/-- **`δ_{U(χ)} = δ_{U_J}`** on `M_J(F) = Z(χ)(F)`, when moreover `U_J = U(χ)`. -/
theorem dynamicHalfModulus_eq_standardHalfModulus
    (hM : standardLevi i ν J = Dynamic.centralizer χ)
    (hU : standardUnipotent i ν J = Dynamic.unipotent χ) (m : dynamicLeviPoints χ) :
    dynamicHalfModulus χ m = standardHalfModulus i ν J (standardLeviDynamicEquiv χ hM m) := by
  have key := closedRestrictCharacter_congr (H := rationalPoints G)
    (congrArg (fun P : SubgroupFunctor G => P.carrier (Over.mk (𝟙 _))) hU.symm)
    (isClosed_unipotentPoints χ) (isClosed_standardUnipotentPoints i ν J)
    (dynamicLeviPoints_le_normalizer_radical χ)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
    (m := m) (m' := standardLeviDynamicEquiv χ hM m) rfl
  unfold dynamicHalfModulus standardHalfModulus dynamicParabolicModulus standardRadicalModulus
  rw [key]

/-- **The source's cone condition implies the tail condition.** Suppose `M_J = Z(χ)` and
`U_J = U(χ)`, `Δ(P_J)` is finite, and `χ(t)` is the image of a point `y ∈ A(F)` with
`|α(y)|_F < 1` for every `α ∈ Δ(P_J)`. Then every constant term `f_P` of `f` in the sense of the
cones of `A(F)` is, transported to `Z(χ)(F)`, a constant term of `f` along the powers of `χ(t)`. -/
theorem IsStandardConstantTerm.isDynamicConstantTerm
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hM : standardLevi i ν J = Dynamic.centralizer χ)
    (hU : standardUnipotent i ν J = Dynamic.unipotent χ)
    (hfin : (standardParabolicComponentCharacters i ν J q).Finite) (t : Fˣ)
    {y : rationalPoints A.toGrp}
    (hy : ∀ α ∈ standardParabolicComponentCharacters i ν J q,
      CocharacterUniformizer.characterNorm F A α y < 1)
    (hty : cocharPoint χ t = rationalPoints.map (q ≫ i) y)
    {f : rationalPoints G → ℂ} {fP : standardLeviPoints i ν J → ℂ}
    (h : IsStandardConstantTerm hA f fP) :
    IsDynamicConstantTerm χ t f (fun m => fP (standardLeviDynamicEquiv χ hM m)) := by
  intro m
  obtain ⟨ε, hε, e⟩ := h (standardLeviDynamicEquiv χ hM m)
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp (eventually_pow_mem_standardCone hfin hy hε)
  refine ⟨r₀, fun r hr => ?_⟩
  have hE : standardLeviDynamicEquiv χ hM (m * dynamicCocharPoint χ t ^ r) =
      standardLeviDynamicEquiv χ hM m * standardComponentHom hA (y ^ r) := by
    apply Subtype.ext
    rw [coe_standardLeviDynamicEquiv, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_standardLeviDynamicEquiv, coe_standardComponentHom, coe_dynamicCocharPoint_pow, hty,
      map_pow]
  have hcoe : ((m * dynamicCocharPoint χ t ^ r : dynamicLeviPoints χ) : RationalPoint F G.X) =
      ((standardLeviDynamicEquiv χ hM m * standardComponentHom hA (y ^ r) :
        standardLeviPoints i ν J) : rationalPoints G) :=
    congrArg Subtype.val hE
  beta_reduce
  rw [dynamicHalfModulus_eq_standardHalfModulus χ hM hU, hE, hcoe]
  exact e (y ^ r) (hr₀ r hr)

/-- **Comparison of the two constant terms.** Under the hypotheses of
`IsStandardConstantTerm.isDynamicConstantTerm`, if `f` has a right-finite standard constant term,
then `f` has a right-finite constant term along the powers of `χ(t)`, and
`dynamicConstantTerm χ t f` is `standardConstantTerm hA f` transported to `Z(χ)(F)`. -/
theorem HasStandardConstantTerm.dynamicConstantTerm_eq
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hM : standardLevi i ν J = Dynamic.centralizer χ)
    (hU : standardUnipotent i ν J = Dynamic.unipotent χ)
    (hfin : (standardParabolicComponentCharacters i ν J q).Finite) (t : Fˣ)
    {y : rationalPoints A.toGrp}
    (hy : ∀ α ∈ standardParabolicComponentCharacters i ν J q,
      CocharacterUniformizer.characterNorm F A α y < 1)
    (hty : cocharPoint χ t = rationalPoints.map (q ≫ i) y)
    {f : rationalPoints G → ℂ} (h : HasStandardConstantTerm hA f) :
    HasDynamicConstantTerm χ t f ∧
      dynamicConstantTerm χ t f =
        fun m => standardConstantTerm hA f (standardLeviDynamicEquiv χ hM m) := by
  have hR := HasStandardConstantTerm.isRightFinite hA h
  have hC := HasStandardConstantTerm.isStandardConstantTerm hA h
  have hD := IsStandardConstantTerm.isDynamicConstantTerm χ hA hM hU hfin t hy hty hC
  have hc : standardLeviDynamicEquiv χ hM (dynamicCocharPoint χ t) = standardComponentHom hA y :=
    Subtype.ext hty
  have hR' : HarishChandraSchwartz.IsRightFinite (dynamicCocharSubgroup χ t)
      (fun m => standardConstantTerm hA f (standardLeviDynamicEquiv χ hM m)) := by
    refine isRightFinite_comp (standardLeviDynamicEquiv χ hM).toMonoidHom ?_ hR
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [MulEquiv.coe_toMonoidHom, map_zpow, hc]
    exact ⟨y ^ k, map_zpow _ _ _⟩
  exact ⟨⟨_, hR', hD⟩, Langlands.Jacquet.dynamicConstantTerm_eq χ t hR' hD⟩

end Rational

section Standard

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}

omit [LocallyOfFiniteType G.X.hom] in
/-- If `t^n → 0` in `F`, then `|t|_F < 1`. -/
theorem residueNormalizedAbsoluteValue_lt_one_of_tendsto_pow {t : F}
    (ht : Tendsto (fun n : ℕ => t ^ n) atTop (𝓝 0)) :
    LocalField.residueNormalizedAbsoluteValue F t < 1 := by
  by_contra h'
  have h := not_lt.mp h'
  have hlim : Tendsto (fun n : ℕ => LocalField.residueNormalizedAbsoluteValue F (t ^ n)) atTop
      (𝓝 (LocalField.residueNormalizedAbsoluteValue F 0)) :=
    ((Plancherel.continuous_residueNormalizedAbsoluteValue F).tendsto 0).comp ht
  rw [map_zero] at hlim
  have hge : ∀ n : ℕ, 1 ≤ LocalField.residueNormalizedAbsoluteValue F (t ^ n) := by
    intro n
    rw [map_pow]
    exact one_le_pow₀ h
  have := ge_of_tendsto' hlim hge
  linarith

omit [LocallyOfFiniteType G.X.hom] in
/-- `|α(c(t))|_F = |t|_F^{⟨α, c⟩}` for an actual character `α` and cocharacter `c` of `A`. -/
theorem characterNorm_cocharacterPoints (α : characterLattice A) (c : cocharacterLattice A)
    (t : Fˣ) :
    CocharacterUniformizer.characterNorm F A α (CocharacterUniformizer.cocharacterPoints F A c t) =
      LocalField.residueNormalizedAbsoluteValue F (t : F) ^ latticePairing A α c := by
  unfold CocharacterUniformizer.characterNorm
  rw [Plancherel.rationalNormCharacters_apply,
    CocharacterUniformizer.rationalCharacterEval_cocharacterPoints, map_zpow]
  simp [Plancherel.fieldNormUnits_val]

omit [LocallyOfFiniteType G.X.hom] in
/-- **The tail of a standard cocharacter lies in the cones.** For a standard cocharacter `ζ` of `J`
and a unit `t` with `t^n → 0`, `ζ(t)` is the image of a point `y ∈ A(F)` with `|α(y)|_F < 1` for
every `α ∈ Δ(P_J)`. -/
theorem exists_componentPoint_of_isStandardCocharacter
    (hA : IsCompatibleStandardSplitComponent i ν J A q) (hi : IsMaximalSplitTorus i)
    {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν J ζ) (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)) :
    ∃ y : rationalPoints A.toGrp,
      (∀ α ∈ standardParabolicComponentCharacters i ν J q,
        CocharacterUniformizer.characterNorm F A α y < 1) ∧
      cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t = rationalPoints.map (q ≫ i) y := by
  obtain ⟨c, hc⟩ := hA.exists_cocharacter_lift i ν hi hζ
  refine ⟨CocharacterUniformizer.cocharacterPoints F A c t, ?_, ?_⟩
  · rintro α ⟨β, hβ, rfl⟩
    have hpair : latticePairing A (componentCharacterRestriction q β) c =
        latticePairing S β ζ := by
      change gmEndEquiv F (c ≫ (Additive.ofMul q ≫ β)) = _
      rw [← Category.assoc]
      have hc' : c ≫ Additive.ofMul q = ζ := congrArg Additive.ofMul hc
      rw [hc']
      rfl
    rw [characterNorm_cocharacterPoints, hpair]
    have hpos : 0 < latticePairing S β ζ := hζ.2.2 β hβ.1 hβ.2
    have h1 := residueNormalizedAbsoluteValue_lt_one_of_tendsto_pow ht
    have h0 : 0 < LocalField.residueNormalizedAbsoluteValue F (t : F) :=
      (LocalField.residueNormalizedAbsoluteValue F).pos t.ne_zero
    exact zpow_lt_one₀ h0 h1 hpos
  · rw [cocharPoint_eq]
    change (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t ≫
        (CommGroupScheme.groupHom ζ ≫ i).hom.hom =
      ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t ≫
        (CommGroupScheme.groupHom c).hom.hom) ≫ (q ≫ i).hom.hom
    rw [← hc]
    simp only [Grp.comp_hom_hom, Category.assoc]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- **`M_J = Z(ζ ∘ i)` and `U_J = U(ζ ∘ i)`.** For connected reductive `G`, a maximal split torus
`i` and a generic `ν`, the standard Levi and unipotent subgroup functors of `J` are the dynamic
centralizer and unipotent subgroup functors of `ζ ∘ i`, for every standard cocharacter `ζ` of `J`
(the Library's `standardCocharacter`). -/
theorem standardLevi_eq_dynamic (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) :
    standardLevi i ν J = Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) ∧
      standardUnipotent i ν J = Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i) :=
  ((standardCocharacter F G hG S i hi ν hν J hζ.1).2 ζ hζ).2

/-- **The two forms of Proposition I.6.2 agree.** Let `ζ` be a standard cocharacter of `J`, `A` a
compatible split component of `M_J`, and `t ∈ F^×` with `t^n → 0`. If `f` has a right-finite
standard constant term, then `f` has a right-finite constant term along the powers of
`ζ(t)`, and `dynamicConstantTerm (ζ ∘ i) t f` is `standardConstantTerm hA f` transported along
`Z(ζ ∘ i)(F) ≃* M_J(F)`. In particular, for such `f`, the dynamic constant term along `ζ ∘ i`
depends neither on `t` nor on `ζ`. -/
theorem HasStandardConstantTerm.dynamicConstantTerm_eq_of_isStandardCocharacter
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν J ζ)
    (hA : IsCompatibleStandardSplitComponent i ν J A q) (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    {f : rationalPoints G → ℂ} (h : HasStandardConstantTerm hA f) :
    HasDynamicConstantTerm (CommGroupScheme.groupHom ζ ≫ i) t f ∧
      dynamicConstantTerm (CommGroupScheme.groupHom ζ ≫ i) t f =
        fun m => standardConstantTerm hA f
          (standardLeviDynamicEquiv _ (standardLevi_eq_dynamic hG hi hν hζ).1 m) := by
  obtain ⟨y, hy, hty⟩ := exists_componentPoint_of_isStandardCocharacter hA hi hζ t ht
  exact HasStandardConstantTerm.dynamicConstantTerm_eq _ hA
    (standardLevi_eq_dynamic hG hi hν hζ).1 (standardLevi_eq_dynamic hG hi hν hζ).2
    (exists_strictly_contracting_point hi hζ hA).1 t hy hty h

/-- **Independence of `t` and of `ζ`.** For `f` with a right-finite standard constant term, standard
cocharacters `ζ, ζ'` of `J` and units `t, t'` with `t^n → 0` and `t'^n → 0`, the dynamic constant
terms of `f` along `ζ(t)` and along `ζ'(t')` agree at every point of `M_J(F) = Z(ζ ∘ i)(F) =
Z(ζ' ∘ i)(F)`. -/
theorem HasStandardConstantTerm.dynamicConstantTerm_independent
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {ζ ζ' : cocharacterLattice S} (hζ : IsStandardCocharacter i ν J ζ)
    (hζ' : IsStandardCocharacter i ν J ζ')
    (hA : IsCompatibleStandardSplitComponent i ν J A q) {t t' : Fˣ}
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (ht' : Tendsto (fun n : ℕ => (t' : F) ^ n) atTop (𝓝 0))
    {f : rationalPoints G → ℂ} (h : HasStandardConstantTerm hA f)
    (m : dynamicLeviPoints (CommGroupScheme.groupHom ζ ≫ i))
    (m' : dynamicLeviPoints (CommGroupScheme.groupHom ζ' ≫ i))
    (hm : (m : RationalPoint F G.X) = m') :
    dynamicConstantTerm (CommGroupScheme.groupHom ζ ≫ i) t f m =
      dynamicConstantTerm (CommGroupScheme.groupHom ζ' ≫ i) t' f m' := by
  rw [(HasStandardConstantTerm.dynamicConstantTerm_eq_of_isStandardCocharacter hG hi hν hζ hA t
      ht h).2,
    (HasStandardConstantTerm.dynamicConstantTerm_eq_of_isStandardCocharacter hG hi hν hζ' hA t'
      ht' h).2]
  exact congrArg (standardConstantTerm hA f) (Subtype.ext hm)

/-- **The constant terms of `f ∈ A(ρ)`.** With Renard's simultaneous standard basis (`hB`,
`hmem`), for an admissible `ρ` and `f ∈ A(ρ)`, every `t ∈ F^×` with `t^n → 0` and every standard
cocharacter `ζ` of `J`, `f` has a right-finite constant term along the powers of `ζ(t)`, equal
to `standardConstantTerm hA f` transported along `Z(ζ ∘ i)(F) ≃* M_J(F)`. -/
theorem dynamicConstantTerm_eq_standardConstantTerm (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) {K0 : Subgroup (rationalPoints G)}
    {B : Set (Subgroup (rationalPoints G))} (hB : CompactOpenNormalBasis K0 B)
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (rationalPoints G) V)
    (hρ : IsAdmissible ρ) {f : rationalPoints G → ℂ}
    (hf : f ∈ HarishChandraSchwartz.coefficientFunctionSpace (SmoothRep.of ρ hρ.1)) (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0)) :
    HasDynamicConstantTerm (CommGroupScheme.groupHom ζ ≫ i) t f ∧
      dynamicConstantTerm (CommGroupScheme.groupHom ζ ≫ i) t f =
        fun m => standardConstantTerm hA f
          (standardLeviDynamicEquiv _ (standardLevi_eq_dynamic hG hi hν hζ).1 m) :=
  HasStandardConstantTerm.dynamicConstantTerm_eq_of_isStandardCocharacter hG hi hν hζ hA t ht
    (standardConstantTerm_spec hG hi hν hζ hB hA hmem ρ hρ hf).1

end Standard

end Langlands.Jacquet

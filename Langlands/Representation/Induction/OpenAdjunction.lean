import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Cohomology.SupercuspidalExt.Statement
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Compact induction from an open subgroup is left adjoint to restriction

Let `H` be an open subgroup of a topological group `G` and `R` a commutative ring. Compact
induction `c-Ind_H^G` (the published `compactInductionFunctor`: functions `f : G → V` with
`f (h x) = σ h (f x)`, smooth under right translation, with compact support in `H \ G`) is left
adjoint to restriction of smooth representations (Vignéras 1996, I.5.7 (ii)).

Since `H` is open, `H \ G` is discrete and every compactly induced function has finite support
modulo `H`. The unit sends `v` to the function `unitFunction` supported on `H` with value `σ h v`
at `h`. The inverse of `T ↦ T ∘ unit` sends an `H`-equivariant `φ` to
`cosetSum φ : f ↦ ∑ᶠ_{H x ∈ H \ G} τ(x⁻¹) φ(f x)`. The two key identities are
`cosetSum_unitMap` (each `f` is the finite sum of the translates `τ(x⁻¹) unit(f x)`) and
`cosetSum_comp_unitMap`.

## Main definitions

* `smoothRestriction R H`: restriction `SmoothRep R G ⥤ SmoothRep R H`.
* `smoothCompactInduction R H`: compact induction on smooth representations.
* `compactInductionHomEquiv H hH A B`: Frobenius reciprocity
  `(c-Ind A ⟶ B) ≃ (A ⟶ B|_H)`.
* `compactInductionAdjunction H hH : smoothCompactInduction R H ⊣ smoothRestriction R H`.
* `Langlands.Cohomology.SupercuspidalExt.compactInductionAdjunction R G H hH`: the same adjunction
  for the one-universe functors `compactInduction R G H` and `restriction R G H` of
  `Langlands.Cohomology.SupercuspidalExt.Statement`.

Consequences: restriction preserves epimorphisms and monomorphisms; compact induction preserves
monomorphisms, and for open `H` epimorphisms and projective objects; restriction to an open
subgroup preserves injective objects (Vignéras 1996, I.5.9 d)).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Induction

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]

section Quotient

variable (H : Subgroup G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Two points of `G` have the same right coset `H x` exactly when their quotient lies in `H`. -/
theorem quotientMap_eq_iff (x y : G) :
    quotientMap H x = quotientMap H y ↔ y * x⁻¹ ∈ H :=
  Quotient.eq.trans QuotientGroup.rightRel_apply

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem quotientRight_quotientMap (g x : G) :
    quotientRight H g (quotientMap H x) = quotientMap H (x * g) :=
  rfl

/-- Right translation on `H \ G`, as an equivalence. -/
def quotientRightEquiv (g : G) : LeftQuotient H ≃ LeftQuotient H where
  toFun := quotientRight H g
  invFun := quotientRight H g⁻¹
  left_inv q := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change quotientMap H (x * g * g⁻¹) = quotientMap H x
    rw [mul_inv_cancel_right]
  right_inv q := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change quotientMap H (x * g⁻¹ * g) = quotientMap H x
    rw [inv_mul_cancel_right]

/-- For an open subgroup `H`, the coset space `H \ G` is discrete. -/
theorem discreteTopology_leftQuotient (hH : IsOpen (H : Set G)) :
    DiscreteTopology (LeftQuotient H) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel H)).isCoinducing.isOpen_preimage.mp
  convert hH.preimage (continuous_mul_const x⁻¹) using 1
  ext y
  change quotientMap H y = quotientMap H x ↔ y * x⁻¹ ∈ H
  rw [eq_comm, quotientMap_eq_iff]

/-- An open subgroup of an open subgroup `H` is an open subgroup of `G`. -/
def openSubgroupMap (hH : IsOpen (H : Set G)) (K : OpenSubgroup H) : OpenSubgroup G where
  toSubgroup := K.toSubgroup.map H.subtype
  isOpen' := by
    change IsOpen (H.subtype '' (K : Set H))
    exact hH.isOpenMap_subtype_val _ K.isOpen

end Quotient

section Functions

variable (H : Subgroup G) (σ : Representation R H V)

/-- Compactly induced functions are determined by their values. -/
theorem compactFunctions_ext {f f' : CompactFunctions H σ}
    (h : ∀ x, eval H σ f.1 x = eval H σ f'.1 x) : f = f' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

/-- The value at a point of `G`, as an additive map on compactly induced functions. -/
def evalAddHom (y : G) : CompactFunctions H σ →+ V where
  toFun f := eval H σ f.1 y
  map_zero' := rfl
  map_add' _ _ := rfl

theorem eval_compactInduced (g : G) (f : CompactFunctions H σ) (x : G) :
    eval H σ (compactInduced H σ g f).1 x = eval H σ f.1 (x * g) :=
  rfl

theorem eval_compactInducedMap {τ : Representation R H W} (T : σ.IntertwiningMap τ)
    (f : CompactFunctions H σ) (x : G) :
    eval H τ (compactInducedMap H T f).1 x = T (eval H σ f.1 x) :=
  rfl

/-- For an open subgroup, the projected support of a compactly induced function is finite. -/
theorem quotientSupport_finite (hH : IsOpen (H : Set G)) (f : CompactFunctions H σ) :
    (quotientSupport H (eval H σ f.1)).Finite :=
  haveI := discreteTopology_leftQuotient H hH
  IsCompact.finite_of_discrete f.2

end Functions

section Unit

variable (H : Subgroup G) (hH : IsOpen (H : Set G)) (σ : Representation R H V) (hσ : IsSmooth σ)

open Classical in
/-- The function supported on `H` with value `σ h v` at `h ∈ H`. -/
def unitFunction (v : V) : CompactFunctions H σ :=
  compactFunctionOf H σ (fun x => if hx : x ∈ H then σ ⟨x, hx⟩ v else 0)
    (by
      intro p x
      by_cases hx : x ∈ H
      · have hpx : (p : G) * x ∈ H := H.mul_mem p.2 hx
        simp only [hx, hpx, ↓reduceDIte]
        rw [← Module.End.mul_apply, ← map_mul]
        rfl
      · have hpx : (p : G) * x ∉ H := fun h => hx ((H.mul_mem_cancel_left p.2).mp h)
        simp only [hx, hpx, ↓reduceDIte, map_zero])
    (openSubgroupMap H hH (Classical.choose (hσ v)))
    (by
      intro k x
      obtain ⟨k₀, hk₀, hk⟩ := Subgroup.mem_map.mp k.2
      have hfix : σ k₀ v = v := Classical.choose_spec (hσ v) ⟨k₀, hk₀⟩
      have hkH : (k : G) ∈ H := hk ▸ k₀.2
      by_cases hx : x ∈ H
      · have hxk : x * (k : G) ∈ H := H.mul_mem hx hkH
        simp only [hx, hxk, ↓reduceDIte]
        have hk' : (⟨x * (k : G), hxk⟩ : H) = ⟨x, hx⟩ * k₀ := Subtype.ext (congrArg (x * ·) hk.symm)
        rw [hk', map_mul, Module.End.mul_apply, hfix]
      · have hxk : x * (k : G) ∉ H := fun h => hx ((H.mul_mem_cancel_right hkH).mp h)
        simp only [hx, hxk, ↓reduceDIte])
    (by
      apply ((Set.finite_singleton (quotientMap H 1)).subset _).isCompact
      rintro _ ⟨x, hx, rfl⟩
      by_cases hxH : x ∈ H
      · exact (quotientMap_eq_iff H x 1).mpr (by simpa using H.inv_mem hxH)
      · exact absurd (by simp only [hxH, ↓reduceDIte]) hx)

open Classical in
theorem eval_unitFunction (v : V) (x : G) :
    eval H σ (unitFunction H hH σ hσ v).1 x = if hx : x ∈ H then σ ⟨x, hx⟩ v else 0 :=
  rfl

theorem eval_unitFunction_one (v : V) :
    eval H σ (unitFunction H hH σ hσ v).1 1 = v := by
  rw [eval_unitFunction]
  simp only [H.one_mem, ↓reduceDIte]
  exact congrArg (fun T : Module.End R V => T v) (map_one σ)

open Classical in
/-- The unit `σ → c-Ind_H^G σ` of the adjunction, an `H`-equivariant map. -/
def unitMap : σ.IntertwiningMap ((compactInduced H σ).comp H.subtype) where
  toFun := unitFunction H hH σ hσ
  map_add' v w := compactFunctions_ext H σ fun x => by
    change (if hx : x ∈ H then σ ⟨x, hx⟩ (v + w) else 0) =
      (if hx : x ∈ H then σ ⟨x, hx⟩ v else 0) + (if hx : x ∈ H then σ ⟨x, hx⟩ w else 0)
    by_cases hx : x ∈ H
    · simp only [hx, ↓reduceDIte, map_add]
    · simp only [hx, ↓reduceDIte, add_zero]
  map_smul' c v := compactFunctions_ext H σ fun x => by
    change (if hx : x ∈ H then σ ⟨x, hx⟩ (c • v) else 0) =
      c • (if hx : x ∈ H then σ ⟨x, hx⟩ v else 0)
    by_cases hx : x ∈ H
    · simp only [hx, ↓reduceDIte, map_smul]
    · simp only [hx, ↓reduceDIte, smul_zero]
  isIntertwining' h := LinearMap.ext fun v => compactFunctions_ext H σ fun x => by
    change (if hx : x ∈ H then σ ⟨x, hx⟩ (σ h v) else 0) =
      (if hx : x * (h : G) ∈ H then σ ⟨x * (h : G), hx⟩ v else 0)
    by_cases hx : x ∈ H
    · have hxh : x * (h : G) ∈ H := H.mul_mem hx h.2
      simp only [hx, hxh, ↓reduceDIte]
      rw [← Module.End.mul_apply, ← map_mul]
      rfl
    · have hxh : x * (h : G) ∉ H := fun hh => hx ((H.mul_mem_cancel_right h.2).mp hh)
      simp only [hx, hxh, ↓reduceDIte]

theorem unitMap_apply (v : V) : unitMap H hH σ hσ v = unitFunction H hH σ hσ v :=
  rfl

end Unit

section CosetSum

variable (H : Subgroup G) (hH : IsOpen (H : Set G)) (τ : Representation R G W)
  (σ : Representation R H V)

/-- An equivariant map of `G`-representations, viewed as a map of their restrictions to `H`. -/
def resIntertwining {τ' : Representation R G U} (T : τ'.IntertwiningMap τ) :
    Representation.IntertwiningMap (τ'.comp H.subtype) (τ.comp H.subtype) where
  toLinearMap := T.toLinearMap
  isIntertwining' h := T.isIntertwining' h

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem resIntertwining_apply {τ' : Representation R G U} (T : τ'.IntertwiningMap τ) (u : U) :
    resIntertwining H τ T u = T u :=
  rfl

/-- The term of the coset `H x` in the inverse reciprocity map: `τ(x⁻¹) φ(f x)`. It does not
depend on the representative `x`. -/
def cosetTerm (φ : σ.IntertwiningMap (τ.comp H.subtype)) (f : CompactFunctions H σ)
    (q : LeftQuotient H) : W :=
  Quotient.liftOn q (fun x => τ x⁻¹ (φ (eval H σ f.1 x))) (by
    intro a b hab
    have hba : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hab
    have hcov : eval H σ f.1 b = σ ⟨b * a⁻¹, hba⟩ (eval H σ f.1 a) := by
      have h := f.1.1.2 ⟨b * a⁻¹, hba⟩ a
      rw [Subgroup.coe_subtype, inv_mul_cancel_right] at h
      exact h
    change τ a⁻¹ (φ (eval H σ f.1 a)) = τ b⁻¹ (φ (eval H σ f.1 b))
    rw [hcov, φ.isIntertwining]
    change τ a⁻¹ (φ (eval H σ f.1 a)) = τ b⁻¹ (τ (b * a⁻¹) (φ (eval H σ f.1 a)))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left])

theorem cosetTerm_quotientMap (φ : σ.IntertwiningMap (τ.comp H.subtype))
    (f : CompactFunctions H σ) (x : G) :
    cosetTerm H τ σ φ f (quotientMap H x) = τ x⁻¹ (φ (eval H σ f.1 x)) :=
  rfl

theorem support_cosetTerm_subset (φ : σ.IntertwiningMap (τ.comp H.subtype))
    (f : CompactFunctions H σ) :
    Function.support (cosetTerm H τ σ φ f) ⊆ quotientSupport H (eval H σ f.1) := by
  intro q hq
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  refine ⟨x, fun hx => hq ?_, rfl⟩
  change τ x⁻¹ (φ (eval H σ f.1 x)) = 0
  rw [hx, map_zero, map_zero]

include hH in
theorem hasFiniteSupport_cosetTerm (φ : σ.IntertwiningMap (τ.comp H.subtype))
    (f : CompactFunctions H σ) : Function.HasFiniteSupport (cosetTerm H τ σ φ f) :=
  (quotientSupport_finite H σ hH f).subset (support_cosetTerm_subset H τ σ φ f)

include hH in
/-- The inverse reciprocity map `f ↦ ∑ᶠ_{H x} τ(x⁻¹) φ(f x)`, a finite sum since `H` is open. -/
def cosetSum (φ : σ.IntertwiningMap (τ.comp H.subtype)) :
    (compactInduced H σ).IntertwiningMap τ where
  toFun f := ∑ᶠ q, cosetTerm H τ σ φ f q
  map_add' f f' := by
    rw [← finsum_add_distrib (hasFiniteSupport_cosetTerm H hH τ σ φ f)
      (hasFiniteSupport_cosetTerm H hH τ σ φ f')]
    refine finsum_congr fun q => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change τ x⁻¹ (φ (eval H σ f.1 x + eval H σ f'.1 x)) =
      τ x⁻¹ (φ (eval H σ f.1 x)) + τ x⁻¹ (φ (eval H σ f'.1 x))
    rw [map_add, map_add]
  map_smul' c f := by
    rw [RingHom.id_apply, smul_finsum' c (hasFiniteSupport_cosetTerm H hH τ σ φ f)]
    refine finsum_congr fun q => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change τ x⁻¹ (φ (c • eval H σ f.1 x)) = c • τ x⁻¹ (φ (eval H σ f.1 x))
    rw [map_smul, map_smul]
  isIntertwining' g := LinearMap.ext fun f => by
    change ∑ᶠ q, cosetTerm H τ σ φ (compactInduced H σ g f) q =
      τ g (∑ᶠ q, cosetTerm H τ σ φ f q)
    rw [map_finsum (τ g) (hasFiniteSupport_cosetTerm H hH τ σ φ f)]
    refine Eq.trans ?_ (finsum_comp_equiv (quotientRightEquiv H g)
      (f := fun q => τ g (cosetTerm H τ σ φ f q)))
    refine finsum_congr fun q => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change τ x⁻¹ (φ (eval H σ f.1 (x * g))) = τ g (τ (x * g)⁻¹ (φ (eval H σ f.1 (x * g))))
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, mul_inv_cancel_left]

theorem cosetSum_apply (φ : σ.IntertwiningMap (τ.comp H.subtype)) (f : CompactFunctions H σ) :
    cosetSum H hH τ σ φ f = ∑ᶠ q, cosetTerm H τ σ φ f q :=
  rfl

theorem cosetTerm_resIntertwining_comp {τ' : Representation R G U} (T : τ'.IntertwiningMap τ)
    (φ : σ.IntertwiningMap (τ'.comp H.subtype)) (f : CompactFunctions H σ) (q : LeftQuotient H) :
    cosetTerm H τ σ ((resIntertwining H τ T).comp φ) f q = T (cosetTerm H τ' σ φ f q) := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact (T.isIntertwining _ _ x⁻¹ _).symm

theorem cosetSum_resIntertwining_comp {τ' : Representation R G U} (T : τ'.IntertwiningMap τ)
    (φ : σ.IntertwiningMap (τ'.comp H.subtype)) (f : CompactFunctions H σ) :
    cosetSum H hH τ σ ((resIntertwining H τ T).comp φ) f = T (cosetSum H hH τ' σ φ f) := by
  rw [cosetSum_apply, cosetSum_apply, map_finsum T (hasFiniteSupport_cosetTerm H hH τ' σ φ f)]
  exact finsum_congr fun q => cosetTerm_resIntertwining_comp H τ σ T φ f q

theorem cosetTerm_comp_compactInducedMap {σ' : Representation R H U}
    (φ : σ.IntertwiningMap (τ.comp H.subtype)) (ψ : σ'.IntertwiningMap σ)
    (f : CompactFunctions H σ') (q : LeftQuotient H) :
    cosetTerm H τ σ' (φ.comp ψ) f q = cosetTerm H τ σ φ (compactInducedMap H ψ f) q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rfl

theorem cosetSum_comp_compactInducedMap {σ' : Representation R H U}
    (φ : σ.IntertwiningMap (τ.comp H.subtype)) (ψ : σ'.IntertwiningMap σ)
    (f : CompactFunctions H σ') :
    cosetSum H hH τ σ' (φ.comp ψ) f = cosetSum H hH τ σ φ (compactInducedMap H ψ f) :=
  finsum_congr fun q => cosetTerm_comp_compactInducedMap H τ σ φ ψ f q

variable (hσ : IsSmooth σ)

open Classical in
/-- Every compactly induced function is the finite sum over the cosets `H x` meeting its
support of the translates by `x⁻¹` of the unit functions of its values `f x`. -/
theorem cosetSum_unitMap (f : CompactFunctions H σ) :
    cosetSum H hH (compactInduced H σ) σ (unitMap H hH σ hσ) f = f := by
  refine compactFunctions_ext H σ fun y => ?_
  rw [cosetSum_apply]
  change evalAddHom H σ y (∑ᶠ q, cosetTerm H (compactInduced H σ) σ (unitMap H hH σ hσ) f q) = _
  rw [map_finsum (evalAddHom H σ y)
    (hasFiniteSupport_cosetTerm H hH (compactInduced H σ) σ (unitMap H hH σ hσ) f)]
  rw [finsum_eq_single _ (quotientMap H y)]
  · change (if hx : y * y⁻¹ ∈ H then σ ⟨y * y⁻¹, hx⟩ (eval H σ f.1 y) else 0) = eval H σ f.1 y
    have h1 : y * y⁻¹ ∈ H := by rw [mul_inv_cancel]; exact H.one_mem
    have he : (⟨y * y⁻¹, h1⟩ : H) = 1 := Subtype.ext (mul_inv_cancel y)
    simp only [h1, ↓reduceDIte, he, map_one, Module.End.one_apply]
  · intro q hq
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change (if hx : y * x⁻¹ ∈ H then σ ⟨y * x⁻¹, hx⟩ (eval H σ f.1 x) else 0) = 0
    have hyx : y * x⁻¹ ∉ H := fun h => hq ((quotientMap_eq_iff H x y).mpr h)
    simp only [hyx, ↓reduceDIte]

open Classical in
/-- Restriction along the unit recovers an equivariant map on the inducing subgroup. -/
theorem cosetSum_comp_unitMap (φ : σ.IntertwiningMap (τ.comp H.subtype)) (v : V) :
    cosetSum H hH τ σ φ (unitMap H hH σ hσ v) = φ v := by
  rw [cosetSum_apply, finsum_eq_single _ (quotientMap H 1)]
  · change τ 1⁻¹ (φ (eval H σ (unitFunction H hH σ hσ v).1 1)) = φ v
    rw [eval_unitFunction_one, inv_one, map_one, Module.End.one_apply]
  · intro q hq
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change τ x⁻¹ (φ (eval H σ (unitFunction H hH σ hσ v).1 x)) = 0
    have hx : x ∉ H := fun h => hq ((quotientMap_eq_iff H x 1).mpr (by simpa using H.inv_mem h))
    rw [eval_unitFunction]
    simp only [hx, ↓reduceDIte, map_zero]

end CosetSum

section Adjunction

variable (R)

/-- Restriction of smooth representations to a subgroup, with the subspace topology. -/
def smoothRestriction (H : Subgroup G) :
    Langlands.SmoothRep.{uR, uG, uV} R G ⥤ Langlands.SmoothRep.{uR, uG, uV} R H :=
  (smoothRepProperty R H).lift (SmoothRep.toRep ⋙ Rep.resFunctor H.subtype)
    (fun A => isSmooth_comp H.subtype continuous_subtype_val A.isSmooth)

/-- Compact induction on smooth representations of a subgroup. -/
abbrev smoothCompactInduction (H : Subgroup G) :
    Langlands.SmoothRep.{uR, uG, max uG uV} R H ⥤ Langlands.SmoothRep.{uR, uG, max uG uV} R G :=
  SmoothRep.toRep ⋙ compactInductionFunctor H

variable {R}

omit [IsTopologicalGroup G] in
theorem smoothRestriction_hom_apply (H : Subgroup G) {A B : Langlands.SmoothRep.{uR, uG, uV} R G}
    (f : A ⟶ B) (a : A) : SmoothRep.hom ((smoothRestriction R H).map f) a = SmoothRep.hom f a :=
  rfl

variable (H : Subgroup G) (hH : IsOpen (H : Set G))

/-- Frobenius reciprocity for compact induction from an open subgroup. -/
def compactInductionHomEquiv (A : Langlands.SmoothRep.{uR, uG, max uG uV} R H)
    (B : Langlands.SmoothRep.{uR, uG, max uG uV} R G) :
    ((smoothCompactInduction R H).obj A ⟶ B) ≃ (A ⟶ (smoothRestriction R H).obj B) where
  toFun T := SmoothRep.ofHom
    ((resIntertwining H B.representation (SmoothRep.hom T)).comp
      (unitMap H hH A.representation A.isSmooth))
  invFun φ := SmoothRep.ofHom (cosetSum H hH B.representation A.representation (SmoothRep.hom φ))
  left_inv T := by
    refine (congrArg SmoothRep.ofHom ?_).trans (SmoothRep.ofHom_hom T)
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_)
    exact (cosetSum_resIntertwining_comp H hH B.representation A.representation
      (SmoothRep.hom T) (unitMap H hH A.representation A.isSmooth) f).trans
      (congrArg (SmoothRep.hom T) (cosetSum_unitMap H hH A.representation A.isSmooth f))
  right_inv φ := by
    refine (congrArg SmoothRep.ofHom ?_).trans (SmoothRep.ofHom_hom φ)
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
    exact cosetSum_comp_unitMap H hH B.representation A.representation A.isSmooth
      (SmoothRep.hom φ) v

/-- Compact induction from an open subgroup is left adjoint to restriction. -/
def compactInductionAdjunction :
    smoothCompactInduction.{uR, uG, uV} R H ⊣ smoothRestriction.{uR, uG, max uG uV} R H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := compactInductionHomEquiv.{uR, uG, uV} H hH
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        ext F
        exact cosetSum_comp_compactInducedMap H hH Y.representation X.representation
          (SmoothRep.hom g) (SmoothRep.hom f) F
      homEquiv_naturality_right := fun _ _ => by
        ext v
        rfl }

theorem compactInductionAdjunction_homEquiv (A : Langlands.SmoothRep.{uR, uG, max uG uV} R H)
    (B : Langlands.SmoothRep.{uR, uG, max uG uV} R G) :
    (compactInductionAdjunction.{uR, uG, uV} H hH).homEquiv A B =
      compactInductionHomEquiv.{uR, uG, uV} H hH A B :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) A) B

/-- The unit at `A` sends `v` to the function supported on `H` with value `A(h) v` at `h`. -/
theorem compactInductionAdjunction_unit_app_apply
    (A : Langlands.SmoothRep.{uR, uG, max uG uV} R H) (v : A) :
    SmoothRep.hom ((compactInductionAdjunction.{uR, uG, uV} H hH).unit.app A) v =
      unitFunction H hH A.representation A.isSmooth v :=
  rfl

/-- The counit at `B` sends `f` to `∑ᶠ_{H x} B(x⁻¹) f(x)`. -/
theorem compactInductionAdjunction_counit_app_apply
    (B : Langlands.SmoothRep.{uR, uG, max uG uV} R G)
    (f : CompactFunctions H ((smoothRestriction.{uR, uG, max uG uV} R H).obj B).representation) :
    SmoothRep.hom ((compactInductionAdjunction.{uR, uG, uV} H hH).counit.app B) f =
      ∑ᶠ q, cosetTerm H B.representation _
        (SmoothRep.hom (𝟙 ((smoothRestriction.{uR, uG, max uG uV} R H).obj B))) f q :=
  rfl

end Adjunction

section Exactness

variable (R) (H : Subgroup G)

/-- Restriction preserves epimorphisms: these are the surjective intertwiners. -/
instance smoothRestriction_preservesEpimorphisms :
    (smoothRestriction.{uR, uG, uV} R H).PreservesEpimorphisms where
  preserves f _ :=
    (SmoothRep.epi_iff_surjective _).mpr ((SmoothRep.epi_iff_surjective f).mp inferInstance)

/-- Restriction preserves monomorphisms: these are the injective intertwiners. -/
instance smoothRestriction_preservesMonomorphisms :
    (smoothRestriction.{uR, uG, uV} R H).PreservesMonomorphisms where
  preserves f _ :=
    (SmoothRep.mono_iff_injective _).mpr ((SmoothRep.mono_iff_injective f).mp inferInstance)

/-- Compact induction preserves monomorphisms, since it acts by composition on values. -/
instance smoothCompactInduction_preservesMonomorphisms :
    (smoothCompactInduction.{uR, uG, uV} R H).PreservesMonomorphisms where
  preserves {A B} f _ := by
    rw [SmoothRep.mono_iff_injective]
    intro F F' h
    have hf := (SmoothRep.mono_iff_injective f).mp inferInstance
    exact compactFunctions_ext H A.representation fun x =>
      hf (congrArg (fun F'' : CompactFunctions H B.representation => eval H B.representation F''.1 x) h)

variable {R} (hH : IsOpen (H : Set G))

include hH in
/-- Compact induction from an open subgroup preserves epimorphisms, being a left adjoint. -/
theorem smoothCompactInduction_preservesEpimorphisms :
    (smoothCompactInduction.{uR, uG, uV} R H).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_adjunction (compactInductionAdjunction.{uR, uG, uV} H hH)

include hH in
/-- Compact induction from an open subgroup sends projective objects to projective objects. -/
theorem projective_smoothCompactInduction (P : Langlands.SmoothRep.{uR, uG, max uG uV} R H)
    (hP : Projective P) : Projective ((smoothCompactInduction.{uR, uG, uV} R H).obj P) :=
  (compactInductionAdjunction.{uR, uG, uV} H hH).map_projective P hP

include hH in
/-- Restriction to an open subgroup sends injective objects to injective objects. -/
theorem injective_smoothRestriction (I : Langlands.SmoothRep.{uR, uG, max uG uV} R G)
    (hI : Injective I) : Injective ((smoothRestriction.{uR, uG, max uG uV} R H).obj I) :=
  (compactInductionAdjunction.{uR, uG, uV} H hH).map_injective I hI

end Exactness

end Langlands.Induction

namespace Langlands.Cohomology.SupercuspidalExt

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- For an open subgroup `H`, the compact induction functor `compactInduction R G H` is left
adjoint to `restriction R G H`; this is `Induction.compactInductionAdjunction` in one universe. -/
def compactInductionAdjunction (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    compactInduction R G H ⊣ restriction R G H :=
  Induction.compactInductionAdjunction.{u, u, u} H hH

end Langlands.Cohomology.SupercuspidalExt

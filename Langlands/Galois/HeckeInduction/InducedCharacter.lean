import Langlands.Galois.HeckeInduction.MonomialDeterminant
import Langlands.Weil.Representation.Induction
import Langlands.Weil.Representation.Twist
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Finite-index induction of a character: coset matrices and continuity

For a subgroup `S` of finite index of a group `G` and a character `χ : S →* Lˣ`, `induced S χ`
is the published equivariant-function induction `FiniteRepresentation.induce` of the rank-one
representation `twist χ (of 1)`. In the basis `cosetBasis χ` given by values on the chosen
right-coset representatives, an element `g` acts by a weighted permutation matrix
(`toMatrix_cosetBasis`): the row of the coset `q` has the entry `χ (factor S (q.out * g))` in
the column of the coset of `q.out * g`. Combined with
`Langlands.MonomialDeterminant.det_one_sub_X_smul_monomial`, this gives `det (1 - X g)` from the
cycles of right multiplication by `g` on the cosets (`det_one_sub_X_smul_induced`). The file also
proves a criterion for an element to act trivially (`induced_eq_one`), the rank formula
(`rank_induced`) and continuity for an open subgroup and a continuous character
(`continuous_induced`).
-/

noncomputable section

universe uL uG

open Polynomial
open scoped Classical

namespace Langlands.FiniteRepresentation.InducedCharacter

open Induction

variable {L : Type uL} {G : Type uG} [Field L] [Group G]
section General

variable {S : Subgroup G}

/-- The right coset of `x * g` depends only on the right coset of `x`. -/
theorem coset_out_mul (x g : G) :
    coset S ((coset S x).out * g) = coset S (x * g) := by
  apply Quotient.sound
  have h : x * (coset S x).out⁻¹ ∈ S :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact (coset S x).out_eq)
  apply QuotientGroup.rightRel_apply.mpr
  simpa [mul_assoc] using h

theorem coset_eq_iff (x y : G) : coset S x = coset S y ↔ y * x⁻¹ ∈ S := by
  constructor
  · intro h
    exact QuotientGroup.rightRel_apply.mp (Quotient.exact h)
  · intro h
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr h)

/-- Right multiplication of right cosets. -/
def cosetMul (g : G) (q : Cosets S) : Cosets S := coset S (q.out * g)

theorem cosetMul_iterate (g x : G) (k : ℕ) :
    (cosetMul (S := S) g)^[k] (coset S x) = coset S (x * g ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, cosetMul, coset_out_mul, pow_succ, mul_assoc]

end General

variable (S : Subgroup G) [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The rank-one representation of `S` on `L` given by a unit-valued character. -/
abbrev characterRep (χ : S →* Lˣ) : FiniteRepresentation.{uL, uG, uL} L S :=
  twist χ (of (1 : Representation L S L))

/-- Finite-index induction of a character, on the published equivariant-function model. -/
abbrev induced (χ : S →* Lˣ) : FiniteRepresentation.{uL, uG, max uG uL} L G :=
  induce S (characterRep S χ)

variable {S}

omit [S.FiniteIndex] in
theorem characterRep_apply (χ : S →* Lˣ) (s : S) (a : L) :
    (characterRep S χ).representation s a = (χ s : L) * a := rfl


/-- The value of an element of the induced space, an equivariant function `G → L`. -/
def ev (χ : S →* Lˣ) (f : induced S χ) (x : G) : L :=
  (f : Representation.coindV S.subtype (characterRep S χ).representation).val x

theorem ev_mul (χ : S →* Lˣ) (f : induced S χ) (s : S) (x : G) :
    ev χ f ((s : G) * x) = (χ s : L) * ev χ f x :=
  f.property s x

theorem ev_add (χ : S →* Lˣ) (f f' : induced S χ) (x : G) :
    ev χ (f + f') x = ev χ f x + ev χ f' x := rfl

theorem ev_injective (χ : S →* Lˣ) {f f' : induced S χ} (h : ∀ x, ev χ f x = ev χ f' x) :
    f = f' := by
  apply Subtype.ext
  funext x
  exact h x

/-- The group acts on the induced space by right translation. -/
theorem ev_representation (χ : S →* Lˣ) (g : G) (f : induced S χ) (x : G) :
    ev χ ((induced S χ).representation g f) x = ev χ f (x * g) := rfl

/-- The coordinates of an equivariant function: its values on the chosen right-coset
representatives. -/
def cosetCoords (χ : S →* Lˣ) : induced S χ ≃ₗ[L] (Cosets S → L) :=
  coordinates S (characterRep S χ)

theorem cosetCoords_apply (χ : S →* Lˣ) (f : induced S χ) (q : Cosets S) :
    cosetCoords χ f q = ev χ f q.out := rfl

theorem ev_cosetCoords_symm (χ : S →* Lˣ) (a : Cosets S → L) (x : G) :
    ev χ ((cosetCoords χ).symm a) x = (χ (factor S x) : L) * a (coset S x) := rfl

/-- The basis of the induced space given by the coset coordinates. -/
def cosetBasis (χ : S →* Lˣ) : Module.Basis (Cosets S) L (induced S χ) :=
  Module.Basis.ofEquivFun (cosetCoords χ)

theorem cosetBasis_repr (χ : S →* Lˣ) (f : induced S χ) (q : Cosets S) :
    (cosetBasis χ).repr f q = cosetCoords χ f q := by
  rw [cosetBasis, Module.Basis.ofEquivFun_repr_apply]

theorem cosetBasis_eq (χ : S →* Lˣ) (q : Cosets S) :
    cosetBasis χ q = (cosetCoords χ).symm (Pi.single q 1) := by
  rw [cosetBasis, Module.Basis.coe_ofEquivFun]

/-- The matrix of an element `g` in the coset basis is monomial: the row of `q` has the
single entry `χ (factor S (q.out * g))`, in the column of the coset of `q.out * g`. -/
theorem toMatrix_cosetBasis (χ : S →* Lˣ) (g : G) (q q' : Cosets S) :
    LinearMap.toMatrix (cosetBasis χ) (cosetBasis χ) ((induced S χ).representation g) q q' =
      if cosetMul g q = q' then (χ (factor S (q.out * g)) : L) else 0 := by
  rw [LinearMap.toMatrix_apply, cosetBasis_repr, cosetCoords_apply, ev_representation,
    cosetBasis_eq, ev_cosetCoords_symm, cosetMul]
  by_cases h : coset S (q.out * g) = q'
  · rw [ite_eq_left h, h, Pi.single_eq_same, mul_one]
  · rw [ite_eq_right h, Pi.single_eq_of_ne h, mul_zero]

omit [S.FiniteIndex] in
theorem mem_of_coset_eq {a b : G} (h : coset S a = coset S b) : b * a⁻¹ ∈ S :=
  (coset_eq_iff a b).mp h

omit [S.FiniteIndex] in
/-- The subgroup factor of `q.out * g` is `q.out * g * (cosetMul g q).out⁻¹`. -/
theorem coe_factor_out_mul (g : G) (q : Cosets S) :
    (factor S (q.out * g) : G) = q.out * g * (cosetMul g q).out⁻¹ := rfl

omit [S.FiniteIndex] in
/-- Telescoping the subgroup factors along `n` steps of right multiplication. -/
theorem prod_range_factor (χ : S →* Lˣ) (g : G) (q : Cosets S) (n : ℕ) :
    ∏ k ∈ Finset.range n, (χ (factor S (((cosetMul g)^[k] q).out * g)) : L) =
      (χ ⟨q.out * g ^ n * ((cosetMul g)^[n] q).out⁻¹, by
        apply mem_of_coset_eq
        rw [← cosetMul_iterate, coset_out, coset_out]⟩ : L) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, pow_zero, mul_one, Function.iterate_zero,
      id_eq]
    have h1 : (⟨q.out * q.out⁻¹, by simp⟩ : S) = 1 := Subtype.ext (mul_inv_cancel _)
    rw [h1, map_one, Units.val_one]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, ← Units.val_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_factor_out_mul]
    show q.out * g ^ n * ((cosetMul g)^[n] q).out⁻¹ *
        (((cosetMul g)^[n] q).out * g * (cosetMul g ((cosetMul g)^[n] q)).out⁻¹) =
      q.out * g ^ (n + 1) * ((cosetMul g)^[n + 1] q).out⁻¹
    rw [Function.iterate_succ_apply', pow_succ]
    group

omit [S.FiniteIndex] in
/-- Along a closed cycle the product of the subgroup factors is the character of the
return element `x * g ^ m * x⁻¹`, for any representative `x` of the starting coset. -/
theorem prod_fin_factor_cycle (χ : S →* Lˣ) (g x : G) (m : ℕ)
    (hm : x * g ^ m * x⁻¹ ∈ S) :
    ∏ k : Fin m, (χ (factor S (((cosetMul g)^[k] (coset S x)).out * g)) : L) =
      (χ ⟨x * g ^ m * x⁻¹, hm⟩ : L) := by
  rw [Fin.prod_univ_eq_prod_range (fun k => (χ (factor S (((cosetMul g)^[k] (coset S x)).out *
    g)) : L)) m, prod_range_factor]
  have hcyc : (cosetMul g)^[m] (coset S x) = coset S x := by
    rw [cosetMul_iterate, coset_eq_iff]
    have : x * (x * g ^ m)⁻¹ = (x * g ^ m * x⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hm
  -- conjugate by the subgroup element relating `x` and the chosen representative
  set t := factor S x with ht
  have hx : (t : G) * (coset S x).out = x := factor_mul_out S x
  have heq : (⟨(coset S x).out * g ^ m * ((cosetMul g)^[m] (coset S x)).out⁻¹, by
        apply mem_of_coset_eq
        rw [← cosetMul_iterate, coset_out, coset_out]⟩ : S) =
      t⁻¹ * ⟨x * g ^ m * x⁻¹, hm⟩ * t := by
    apply Subtype.ext
    simp only [hcyc, Subgroup.coe_mul, Subgroup.coe_inv]
    conv_rhs => rw [← hx]
    group
  rw [heq, map_mul, map_mul, map_inv]
  simp only [Units.val_mul]
  rw [mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- **Reciprocal characteristic polynomial of an induced character.** Suppose the orbits of
right multiplication by `g` on the right cosets of `S` are the cycles through the cosets of
`x w`, of lengths `len w`, listed without repetition. Then `det (1 - X g)` on the induced space
is the product over the cycles of `1 - χ (x w * g ^ len w * (x w)⁻¹) X ^ len w`. -/
theorem det_one_sub_X_smul_induced (χ : S →* Lˣ) (g : G) {W : Type*} [Fintype W]
    (x : W → G) (len : W → ℕ) (hlen : ∀ w, 0 < len w)
    (hmem : ∀ w, x w * g ^ len w * (x w)⁻¹ ∈ S)
    (hbij : Function.Bijective
      (fun i : Σ w, Fin (len w) => coset S (x i.1 * g ^ (i.2 : ℕ)))) :
    Matrix.det (1 - (X : L[X]) • (LinearMap.toMatrix (cosetBasis χ) (cosetBasis χ)
        ((induced S χ).representation g)).map C) =
      ∏ w, (1 - C (χ ⟨x w * g ^ len w * (x w)⁻¹, hmem w⟩ : L) * X ^ len w) := by
  have hM : LinearMap.toMatrix (cosetBasis χ) (cosetBasis χ) ((induced S χ).representation g) =
      Matrix.of fun q q' => if cosetMul g q = q' then (χ (factor S (q.out * g)) : L) else 0 := by
    ext q q'
    rw [toMatrix_cosetBasis, Matrix.of_apply]
  have hcycle (w : W) : (cosetMul g)^[len w] (coset S (x w)) = coset S (x w) := by
    rw [cosetMul_iterate, coset_eq_iff]
    have : x w * (x w * g ^ len w)⁻¹ = (x w * g ^ len w * (x w)⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem (hmem w)
  have hbij' : Function.Bijective
      (fun i : Σ w, Fin (len w) => (cosetMul g)^[i.2] (coset S (x i.1))) := by
    convert hbij using 2 with i
    exact cosetMul_iterate g _ _
  rw [hM, Langlands.MonomialDeterminant.det_one_sub_X_smul_monomial (cosetMul g)
    (fun q => (χ (factor S (q.out * g)) : L)) (fun w => coset S (x w)) len hlen hcycle hbij']
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [prod_fin_factor_cycle χ g (x w) (len w) (hmem w)]

/-- An element acts trivially on the induced space when all its conjugates lie in `S` and
are killed by `χ`. -/
theorem induced_eq_one (χ : S →* Lˣ) (g : G)
    (h : ∀ y : G, ∃ hy : y * g * y⁻¹ ∈ S, χ ⟨y * g * y⁻¹, hy⟩ = 1) :
    (induced S χ).representation g = 1 := by
  apply LinearMap.ext
  intro f
  apply ev_injective
  intro y
  obtain ⟨hy, hχ⟩ := h y
  rw [ev_representation]
  have : y * g = ((⟨y * g * y⁻¹, hy⟩ : S) : G) * y := by simp
  rw [this, ev_mul, hχ, Units.val_one, one_mul]
  rfl

omit [S.FiniteIndex] in
theorem rank_characterRep (χ : S →* Lˣ) : (characterRep S χ).rank = 1 :=
  Module.finrank_self L

/-- The induced space has dimension the index of `S`. -/
theorem rank_induced (χ : S →* Lˣ) : (induced S χ).rank = S.index := by
  rw [rank_induce, rank_characterRep, mul_one]

/-- An element conjugated into `S` by every chosen coset representative acts diagonally in
the coset basis. -/
theorem induced_cosetBasis_of_conj_mem (χ : S →* Lˣ) (u : G)
    (hu : ∀ q : Cosets S, q.out * u * q.out⁻¹ ∈ S) (q' : Cosets S) :
    (induced S χ).representation u (cosetBasis χ q') =
      (χ ⟨q'.out * u * q'.out⁻¹, hu q'⟩ : L) • cosetBasis χ q' := by
  apply (cosetCoords χ).injective
  funext q
  have hq : coset S (q.out * u) = q := by
    have h : coset S q.out = coset S (q.out * u) := (coset_eq_iff _ _).mpr (hu q)
    rw [← h, coset_out]
  have hfac : factor S (q.out * u) = ⟨q.out * u * q.out⁻¹, hu q⟩ := by
    apply Subtype.ext
    simp only [factor, hq]
  rw [cosetCoords_apply, ev_representation, cosetBasis_eq, ev_cosetCoords_symm, map_smul,
    LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, hq, hfac]
  by_cases h : q = q'
  · subst h
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

/-- **Continuity.** If `S` is an open subgroup of finite index of a topological group and `χ`
is continuous, the induced representation is continuous for the module topology on the
endomorphisms of the induced space. -/
theorem continuous_induced [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace L]
    [IsTopologicalRing L] (hS : IsOpen (S : Set G)) (χ : S →* Lˣ)
    (hχ : Continuous fun s : S => (χ s : L)) :
    letI : TopologicalSpace (Module.End L (induced S χ)) :=
      moduleTopology L (Module.End L (induced S χ))
    Continuous (induced S χ).representation := by
  let : TopologicalSpace (Module.End L (induced S χ)) :=
    moduleTopology L (Module.End L (induced S χ))
  have : IsModuleTopology L (Module.End L (induced S χ)) := ⟨rfl⟩
  have : IsTopologicalRing (Module.End L (induced S χ)) := IsModuleTopology.isTopologicalRing L _
  apply continuous_of_continuousAt_one
  let U : Set G := {u | ∀ q : Cosets S, q.out * u * q.out⁻¹ ∈ S}
  have hU : IsOpen U := by
    have : U = ⋂ q : Cosets S, (fun u => q.out * u * q.out⁻¹) ⁻¹' (S : Set G) := by
      ext u
      simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun q => hS.preimage (by fun_prop)
  have h1 : (1 : G) ∈ U := fun q => by simp
  let P : Cosets S → Module.End L (induced S χ) := fun q =>
    LinearMap.smulRight ((cosetBasis χ).coord q) (cosetBasis χ q)
  have hsum : ∀ u : U, (induced S χ).representation u =
      ∑ q, (χ ⟨q.out * u * q.out⁻¹, u.2 q⟩ : L) • P q := by
    intro u
    apply (cosetBasis χ).ext
    intro q'
    rw [induced_cosetBasis_of_conj_mem χ u u.2 q', LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, P, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, smul_smul]
    rw [Finset.sum_eq_single q']
    · rw [Finsupp.single_eq_same, mul_one]
    · intro q _ hq
      rw [Finsupp.single_eq_of_ne hq, mul_zero, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ q') h
  have hcont : ContinuousOn (induced S χ).representation U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : U.domRestrict (induced S χ).representation =
        fun u : U => ∑ q, (χ ⟨q.out * u * q.out⁻¹, u.2 q⟩ : L) • P q := by
      funext u
      exact hsum u
    rw [this]
    have := IsModuleTopology.toContinuousAdd L (Module.End L (induced S χ))
    refine continuous_finsetSum _ fun q _ => ?_
    have hc : Continuous fun u : U => (χ ⟨q.out * u * q.out⁻¹, u.2 q⟩ : L) :=
      hχ.comp (Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _)
    exact hc.smul continuous_const
  exact hcont.continuousAt (hU.mem_nhds h1)

end Langlands.FiniteRepresentation.InducedCharacter

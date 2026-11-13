import Langlands.BruhatTits.Cartan.CentralizerTorusValuation
import Langlands.BruhatTits.Cartan.RelativeWeylChamber
import Langlands.GroupScheme.Rational.RestrictedSimpleRootCones
import Langlands.Geometry.Building.CocharacterUniformizer

/-!
# Renard V.3.21–V.3.22: the sets `M^+`, `M^{++}`, `A^+_M`, `A^{++}_M` and `A^+(ε)`

The chambers `^G_P[𝔞]^+` and their nonstrict versions in `𝔞_M = V(A)` are cut out by the
published restricted simple roots `Δ(P)`. The sets `M^+` and `M^{++}` are their inverse
images under the published positive centralizer valuation `H_M`. The cones `A^+_M`,
`A^{++}_M` and `A^+(ε)` in the split component are cut out by normalized character norms.
For a split component, `A_M ∩ M^+ = A^+_M` and `A_M ∩ M^{++} = A^{++}_M` are proved.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct NNReal CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.BruhatTits.Cartan.RenardLeviCones

/-! ### The chambers in `𝔞_M` -/

section Chambers

variable {F : Type u} [Field F]
  {A T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (J : Set (characterLattice T)) (f : A ⟶ T)

/-- Renard V.3.15, `^G_P[𝔞]^+` in `𝔞_M = V(A)`: the real cocharacters on which every
restricted simple root in `Δ(P)` is strictly positive. -/
def chamber : Set (V A) :=
  {x | ∀ β ∈ restrictedSimpleRoots i ν J f, 0 < pair A β x}

/-- The nonstrict chamber, the source's closure of `^G_P[𝔞]^+`: every restricted simple
root in `Δ(P)` is nonnegative. -/
def closedChamber : Set (V A) :=
  {x | ∀ β ∈ restrictedSimpleRoots i ν J f, 0 ≤ pair A β x}

theorem chamber_subset_closedChamber : chamber i ν J f ⊆ closedChamber i ν J f :=
  fun _ hx β hβ => (hx β hβ).le

/-- The nonstrict chamber, through the integral restricted simple characters. -/
theorem mem_closedChamber_iff_eval {x : V A} :
    x ∈ closedChamber i ν J f ↔
      ∀ α ∈ restrictedSimpleCharacters i ν J f, 0 ≤ eval A α x := by
  rw [closedChamber, Set.mem_ofPred_eq,
    restrictedSimpleRoots_eq_image_restrictedSimpleCharacters, Set.forall_mem_image]
  simp only [eval_eq_pair]

/-- The open chamber, through the integral restricted simple characters. -/
theorem mem_chamber_iff_eval {x : V A} :
    x ∈ chamber i ν J f ↔
      ∀ α ∈ restrictedSimpleCharacters i ν J f, 0 < eval A α x := by
  rw [chamber, Set.mem_ofPred_eq,
    restrictedSimpleRoots_eq_image_restrictedSimpleCharacters, Set.forall_mem_image]
  simp only [eval_eq_pair]

theorem zero_mem_closedChamber : (0 : V A) ∈ closedChamber i ν J f :=
  fun β _ => by rw [map_zero]

theorem add_mem_closedChamber {x y : V A} (hx : x ∈ closedChamber i ν J f)
    (hy : y ∈ closedChamber i ν J f) : x + y ∈ closedChamber i ν J f :=
  fun β hβ => by rw [map_add]; exact add_nonneg (hx β hβ) (hy β hβ)

theorem add_mem_chamber {x y : V A} (hx : x ∈ closedChamber i ν J f)
    (hy : y ∈ chamber i ν J f) : x + y ∈ chamber i ν J f :=
  fun β hβ => by rw [map_add]; exact add_pos_of_nonneg_of_pos (hx β hβ) (hy β hβ)

end Chambers

/-! ### Norms and valuations of characters of the split component -/

section Norms

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (A : CommGroupScheme (Spec (CommRingCat.of F)))

/-- The integer valuation `v_F(α(a))` of the value of an integral character `α` of `A`. -/
def characterOrder (α : characterLattice A) (a : rationalPoints A.toGrp) : ℤ :=
  (rationalCharacterValuation A.toGrp a).toAdd
    ((rationalCharacters.equivCharacterLattice A).symm α)

/-- `characterOrder` is the published order `ord_F` of the character value in `F`. -/
theorem ord_rationalCharacterEval (α : characterLattice A) (a : rationalPoints A.toGrp) :
    FML.ord F (rationalCharacterEval ((rationalCharacters.equivCharacterLattice A).symm α) a : F) =
      (characterOrder A α a : WithTop ℤ) :=
  rationalCharacterValuation_ord A.toGrp a _

/-- `|α(a)|_F = q^{-v_F(α(a))}`, with `q` the residue cardinality. -/
theorem characterNorm_eq_rpow (α : characterLattice A) (a : rationalPoints A.toGrp) :
    CocharacterUniformizer.characterNorm F A α a =
      (LocalField.residueCardinality F : ℝ) ^ (-(characterOrder A α a : ℝ)) := by
  rw [characterOrder, ← rationalNormLogarithm_eq_intValuation, rationalNormLogarithm_spec]
  rfl

private theorem one_lt_residueCardinality :
    (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
  exact_mod_cast LocalField.residueCardinality_gt_one F

theorem characterNorm_le_one_iff (α : characterLattice A) (a : rationalPoints A.toGrp) :
    CocharacterUniformizer.characterNorm F A α a ≤ 1 ↔ 0 ≤ characterOrder A α a := by
  rw [characterNorm_eq_rpow, ← Real.rpow_zero (LocalField.residueCardinality F : ℝ),
    Real.rpow_le_rpow_left_iff one_lt_residueCardinality, neg_nonpos, Int.cast_nonneg_iff]

theorem characterNorm_lt_one_iff (α : characterLattice A) (a : rationalPoints A.toGrp) :
    CocharacterUniformizer.characterNorm F A α a < 1 ↔ 0 < characterOrder A α a := by
  rw [characterNorm_eq_rpow, ← Real.rpow_zero (LocalField.residueCardinality F : ℝ),
    Real.rpow_lt_rpow_left_iff one_lt_residueCardinality, neg_lt_zero, Int.cast_pos]

theorem characterOrder_mul (α : characterLattice A) (a b : rationalPoints A.toGrp) :
    characterOrder A α (a * b) = characterOrder A α a + characterOrder A α b := by
  simp only [characterOrder, map_mul, toAdd_mul, AddMonoidHom.add_apply]

theorem characterOrder_one (α : characterLattice A) :
    characterOrder A α 1 = 0 := by
  simp only [characterOrder, map_one, toAdd_one, AddMonoidHom.zero_apply]

end Norms

/-! ### The cones `A^+_M`, `A^{++}_M` and `A^+(ε)` -/

section Component

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (J : Set (characterLattice T)) (f : A ⟶ T)

variable (F) in
/-- Renard V.3.21, `A^+_M`: the points `a` of the split component with `|α(a)|_F ≤ 1` for
every `α ∈ Δ(P)`. -/
def componentPlus : Set (rationalPoints A.toGrp) :=
  {a | ∀ α ∈ restrictedSimpleCharacters i ν J f,
    CocharacterUniformizer.characterNorm F A α a ≤ 1}

variable (F) in
/-- Renard V.3.21, `A^{++}_M`: the points `a` with `|α(a)|_F < 1` for every `α ∈ Δ(P)`. -/
def componentStrict : Set (rationalPoints A.toGrp) :=
  {a | ∀ α ∈ restrictedSimpleCharacters i ν J f,
    CocharacterUniformizer.characterNorm F A α a < 1}

variable (F) in
/-- Renard (V.3.22.1), `A^+(ε)`: the points `a` with `|α(a)|_F < ε` for every `α ∈ Δ(P)`.
The source takes `ε > 0`; the definition is stated for every real `ε`. -/
def componentEpsilon (ε : ℝ) : Set (rationalPoints A.toGrp) :=
  {a | ∀ α ∈ restrictedSimpleCharacters i ν J f,
    CocharacterUniformizer.characterNorm F A α a < ε}

/-- `A^+_M = {a | v_F(α(a)) ≥ 0, α ∈ Δ(P)}`. -/
theorem mem_componentPlus_iff_order {a : rationalPoints A.toGrp} :
    a ∈ componentPlus F i ν J f ↔
      ∀ α ∈ restrictedSimpleCharacters i ν J f, 0 ≤ characterOrder A α a := by
  simp only [componentPlus, Set.mem_ofPred_eq, characterNorm_le_one_iff]

/-- `A^{++}_M = {a | v_F(α(a)) > 0, α ∈ Δ(P)}`. -/
theorem mem_componentStrict_iff_order {a : rationalPoints A.toGrp} :
    a ∈ componentStrict F i ν J f ↔
      ∀ α ∈ restrictedSimpleCharacters i ν J f, 0 < characterOrder A α a := by
  simp only [componentStrict, Set.mem_ofPred_eq, characterNorm_lt_one_iff]

theorem componentStrict_subset_componentPlus :
    componentStrict F i ν J f ⊆ componentPlus F i ν J f :=
  fun _ ha α hα => (ha α hα).le

theorem componentEpsilon_one : componentEpsilon F i ν J f 1 = componentStrict F i ν J f := rfl

theorem componentEpsilon_mono {ε ε' : ℝ} (h : ε ≤ ε') :
    componentEpsilon F i ν J f ε ⊆ componentEpsilon F i ν J f ε' :=
  fun _ ha α hα => (ha α hα).trans_le h

theorem componentEpsilon_subset_componentStrict {ε : ℝ} (hε : ε ≤ 1) :
    componentEpsilon F i ν J f ε ⊆ componentStrict F i ν J f :=
  componentEpsilon_mono i ν J f hε

/-- For `ε ≤ 0` and nonempty `Δ(P)`, `A^+(ε)` is empty, since norms are nonnegative. -/
theorem componentEpsilon_eq_empty {ε : ℝ} (hε : ε ≤ 0) {α : characterLattice A}
    (hα : α ∈ restrictedSimpleCharacters i ν J f) :
    componentEpsilon F i ν J f ε = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun a ha => ?_
  have h0 : 0 ≤ CocharacterUniformizer.characterNorm F A α a := NNReal.coe_nonneg _
  exact absurd ((ha α hα).trans_le hε) (not_lt.mpr h0)

theorem one_mem_componentPlus : (1 : rationalPoints A.toGrp) ∈ componentPlus F i ν J f := by
  rw [mem_componentPlus_iff_order]
  intro α _
  rw [characterOrder_one]

theorem mul_mem_componentPlus {a b : rationalPoints A.toGrp}
    (ha : a ∈ componentPlus F i ν J f) (hb : b ∈ componentPlus F i ν J f) :
    a * b ∈ componentPlus F i ν J f := by
  rw [mem_componentPlus_iff_order] at ha hb ⊢
  intro α hα
  rw [characterOrder_mul]
  exact add_nonneg (ha α hα) (hb α hα)

theorem mul_mem_componentStrict {a b : rationalPoints A.toGrp}
    (ha : a ∈ componentPlus F i ν J f) (hb : b ∈ componentStrict F i ν J f) :
    a * b ∈ componentStrict F i ν J f := by
  rw [mem_componentPlus_iff_order] at ha
  rw [mem_componentStrict_iff_order] at hb ⊢
  intro α hα
  rw [characterOrder_mul]
  exact add_pos_of_nonneg_of_pos (ha α hα) (hb α hα)

/-- Renard V.3.23's `C_A^+` is the lattice cut `C_A ∩ A^+_M`. -/
theorem CAplus_eq_inter :
    CocharacterUniformizer.CAplus F A (restrictedSimpleCharacters i ν J f) =
      (CocharacterUniformizer.CA F A : Set (rationalPoints A.toGrp)) ∩
        componentPlus F i ν J f := rfl

/-- The strict lattice cut `C_A^{++} = C_A ∩ A^{++}_M`. -/
theorem CAstrict_eq_inter :
    CocharacterUniformizer.CAstrict F A (restrictedSimpleCharacters i ν J f) =
      (CocharacterUniformizer.CA F A : Set (rationalPoints A.toGrp)) ∩
        componentStrict F i ν J f := rfl

/-- Renard V.3.23's `C_A^+(ε) = C_A ∩ A^+(ε)`. -/
theorem CAepsilon_eq_inter (ε : ℝ) :
    CocharacterUniformizer.CAepsilon F A (restrictedSimpleCharacters i ν J f) ε =
      (CocharacterUniformizer.CA F A : Set (rationalPoints A.toGrp)) ∩
        componentEpsilon F i ν J f ε := rfl

end Component

/-! ### The sets `M^+` and `M^{++}` -/

section Levi

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (J : Set (characterLattice T)) (f : A ⟶ T)
  (s : A.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))

/-- Renard V.3.21, `M^+`: the inverse image under `H_M` of the nonstrict chamber. -/
def leviPlus : Set (rationalPoints Z) :=
  {m | (centralizerValuation s h m).toAdd ∈ closedChamber i ν J f}

/-- Renard V.3.21, `M^{++}`: the inverse image under `H_M` of the open chamber. -/
def leviStrict : Set (rationalPoints Z) :=
  {m | (centralizerValuation s h m).toAdd ∈ chamber i ν J f}

theorem leviStrict_subset_leviPlus : leviStrict i ν J f s h ⊆ leviPlus i ν J f s h :=
  fun _ hm => chamber_subset_closedChamber i ν J f hm

theorem one_mem_leviPlus : (1 : rationalPoints Z) ∈ leviPlus i ν J f s h := by
  change (centralizerValuation s h 1).toAdd ∈ closedChamber i ν J f
  rw [map_one, toAdd_one]
  exact zero_mem_closedChamber i ν J f

theorem mul_mem_leviPlus {m m' : rationalPoints Z} (hm : m ∈ leviPlus i ν J f s h)
    (hm' : m' ∈ leviPlus i ν J f s h) : m * m' ∈ leviPlus i ν J f s h := by
  change (centralizerValuation s h (m * m')).toAdd ∈ closedChamber i ν J f
  rw [map_mul, toAdd_mul]
  exact add_mem_closedChamber i ν J f hm hm'

theorem mul_mem_leviStrict {m m' : rationalPoints Z} (hm : m ∈ leviPlus i ν J f s h)
    (hm' : m' ∈ leviStrict i ν J f s h) : m * m' ∈ leviStrict i ν J f s h := by
  change (centralizerValuation s h (m * m')).toAdd ∈ chamber i ν J f
  rw [map_mul, toAdd_mul]
  exact add_mem_chamber i ν J f hm hm'

/-- `M^+` contains the common norm kernel `⁰M`. -/
theorem rationalCommonNormKernel_subset_leviPlus :
    (rationalCommonNormKernel Z : Set (rationalPoints Z)) ⊆ leviPlus i ν J f s h := by
  intro m hm
  rw [SetLike.mem_coe, ← centralizerValuation_ker s h, MonoidHom.mem_ker] at hm
  change (centralizerValuation s h m).toAdd ∈ closedChamber i ν J f
  rw [hm, toAdd_one]
  exact zero_mem_closedChamber i ν J f

/-- On a split component, `H_M(s(a))` evaluates every integral character `α` of `A` to the
integer valuation `v_F(α(a))`. -/
theorem eval_centralizerValuation_map (hA : IsSplitTorus A.toGrp) (α : characterLattice A)
    (a : rationalPoints A.toGrp) :
    eval A α (centralizerValuation s h (rationalPoints.map s a)).toAdd =
      (characterOrder A α a : ℝ) := by
  have hid := restrictionEvaluation_id_bijective hA
  have h1 : centralizerValuation s h (rationalPoints.map s a) =
      centralizerValuation (𝟙 A.toGrp) hid a := by
    rw [← torusValuationRestriction_eq_id s h hid]
    rfl
  rw [h1]
  have h2 := centralizerValuation_spec (𝟙 A.toGrp) hid a
    ((rationalCharacters.equivCharacterLattice A).symm α)
  simpa [characterRestriction, characterRestrict_id, characterOrder] using h2

/-- Renard V.3.21, `A^+_M = A_M ∩ M^+`: on a split component, `s(a) ∈ M^+` exactly when
`|α(a)|_F ≤ 1` for every `α ∈ Δ(P)`. -/
theorem map_mem_leviPlus_iff (hA : IsSplitTorus A.toGrp) (a : rationalPoints A.toGrp) :
    rationalPoints.map s a ∈ leviPlus i ν J f s h ↔ a ∈ componentPlus F i ν J f := by
  change _ ∈ closedChamber i ν J f ↔ _
  rw [mem_closedChamber_iff_eval, mem_componentPlus_iff_order]
  refine forall₂_congr fun α _ => ?_
  rw [eval_centralizerValuation_map s h hA, Int.cast_nonneg_iff]

/-- Renard V.3.21, `A^{++}_M = A_M ∩ M^{++}`. -/
theorem map_mem_leviStrict_iff (hA : IsSplitTorus A.toGrp) (a : rationalPoints A.toGrp) :
    rationalPoints.map s a ∈ leviStrict i ν J f s h ↔ a ∈ componentStrict F i ν J f := by
  change _ ∈ chamber i ν J f ↔ _
  rw [mem_chamber_iff_eval, mem_componentStrict_iff_order]
  refine forall₂_congr fun α _ => ?_
  rw [eval_centralizerValuation_map s h hA, Int.cast_pos]

theorem preimage_leviPlus (hA : IsSplitTorus A.toGrp) :
    rationalPoints.map s ⁻¹' leviPlus i ν J f s h = componentPlus F i ν J f :=
  Set.ext fun a => map_mem_leviPlus_iff i ν J f s h hA a

theorem preimage_leviStrict (hA : IsSplitTorus A.toGrp) :
    rationalPoints.map s ⁻¹' leviStrict i ν J f s h = componentStrict F i ν J f :=
  Set.ext fun a => map_mem_leviStrict_iff i ν J f s h hA a

/-- Renard V.3.23, `C_A^+ = C_A ∩ M^+`, read on the split component through `s`. -/
theorem CAplus_eq_preimage_leviPlus (hA : IsSplitTorus A.toGrp) :
    CocharacterUniformizer.CAplus F A (restrictedSimpleCharacters i ν J f) =
      (CocharacterUniformizer.CA F A : Set (rationalPoints A.toGrp)) ∩
        rationalPoints.map s ⁻¹' leviPlus i ν J f s h := by
  rw [preimage_leviPlus i ν J f s h hA]
  rfl

/-- `C_A^{++} = C_A ∩ M^{++}`, read on the split component through `s`. -/
theorem CAstrict_eq_preimage_leviStrict (hA : IsSplitTorus A.toGrp) :
    CocharacterUniformizer.CAstrict F A (restrictedSimpleCharacters i ν J f) =
      (CocharacterUniformizer.CA F A : Set (rationalPoints A.toGrp)) ∩
        rationalPoints.map s ⁻¹' leviStrict i ν J f s h := by
  rw [preimage_leviStrict i ν J f s h hA]
  rfl

end Levi

/-! ### The minimal Levi subgroup -/

section Minimal

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
  (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- With `J = ∅` and `f = 𝟙`, the restricted simple characters are the simple roots. -/
theorem restrictedSimpleCharacters_minimal :
    restrictedSimpleCharacters i ν ∅ (𝟙 S) = simpleRelativeRoots i ν := by
  rw [restrictedSimpleCharacters, Set.sdiff_empty]
  simp only [Category.id_comp, Set.image_id']

/-- For the minimal parabolic (`J = ∅`, `A = A_∅`), `M_∅^+` is the published dominant
centralizer set: nonnegativity on the simple roots is nonnegativity on all positive roots. -/
theorem leviPlus_minimal :
    leviPlus i ν ∅ (𝟙 S) s h = dominantCentralizer i ν s h := by
  ext z
  change _ ∈ closedChamber i ν ∅ (𝟙 S) ↔ _
  rw [mem_closedChamber_iff_eval, restrictedSimpleCharacters_minimal]
  constructor
  · intro hz
    exact isDominantVector_of_simple i ν hz
  · intro hz α hα
    exact hz α (simpleRelativeRoots_subset_positive i ν hα)

end Minimal

end Langlands.BruhatTits.Cartan.RenardLeviCones

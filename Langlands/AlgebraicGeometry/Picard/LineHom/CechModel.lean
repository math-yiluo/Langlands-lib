import Langlands.AlgebraicGeometry.Picard.LineHom.GaugeComplex
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules

/-! # A Čech model of the gauge complex

For two unit cocycles `α` and `β` on an ordered affine cover `𝒰` of `Y`, with `p : Y ⟶ Spec R`
proper and flat and `R` Noetherian, the gauge differential `gaugeD p α β` has an `R`-level model:
a two-term complex `G` of finite free `R`-modules mapping to the gauge complex such that the
induced map on kernels is bijective after every base change `R → A`.

The proof glues the line bundle `E` of the cocycle `γ i j = (α i j)⁻¹ * β i j`, applies the
two-term complex theorem for its Čech complex on `𝒰`, and identifies the first two Čech groups
of `E` with the gauge groups through the coordinates against the local generators of `E`. Under
these identifications the Čech differential becomes the gauge differential.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.LineHom

open CocycleGluing

namespace CechModel

section Transfer

variable {R : Type u} [CommRing R] {K0 K1 C0 C1 D0 D1 : Type u}
  [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [AddCommGroup D0] [Module R D0] [AddCommGroup D1] [Module R D1]

/-- Bijectivity of the base-changed kernel map transfers along isomorphisms of the target
complexes. -/
lemma kerMapBaseChange_bijective_of_linearEquiv (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1)
    (d' : D0 →ₗ[R] D1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK)
    (e0 : C0 ≃ₗ[R] D0) (e1 : C1 ≃ₗ[R] D1) (sq : d' ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ d)
    (comm' : d' ∘ₗ (e0.toLinearMap ∘ₗ ι0) = (e1.toLinearMap ∘ₗ ι1) ∘ₗ dK)
    (A : Type u) [CommRing A] [Algebra R A]
    (h : Function.Bijective (TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm A)) :
    Function.Bijective
      (TwoChartCech.kerMapBaseChange dK d' (e0.toLinearMap ∘ₗ ι0) (e1.toLinearMap ∘ₗ ι1)
        comm' A) := by
  have hsqA : d'.baseChange A ∘ₗ e0.toLinearMap.baseChange A =
      e1.toLinearMap.baseChange A ∘ₗ d.baseChange A := by
    rw [← LinearMap.baseChange_comp, sq, LinearMap.baseChange_comp]
  have he0 := (e0.baseChange R A C0 D0).bijective
  have he1 := (e1.baseChange R A C1 D1).injective
  rw [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange] at he0 he1
  have key : ∀ x, (TwoChartCech.kerMapBaseChange dK d' (e0.toLinearMap ∘ₗ ι0)
      (e1.toLinearMap ∘ₗ ι1) comm' A x : A ⊗[R] D0) =
        e0.toLinearMap.baseChange A (TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm A x) := by
    intro x
    change (e0.toLinearMap ∘ₗ ι0).baseChange A x = e0.toLinearMap.baseChange A (ι0.baseChange A x)
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  constructor
  · intro x y hxy
    apply h.1
    apply Subtype.ext
    apply he0.1
    rw [← key, ← key, hxy]
  · intro z
    obtain ⟨w, hw⟩ := he0.2 z
    have hwk : w ∈ LinearMap.ker (d.baseChange A) := by
      rw [LinearMap.mem_ker]
      apply he1
      rw [map_zero, ← LinearMap.comp_apply, ← hsqA, LinearMap.comp_apply, hw]
      exact z.2
    obtain ⟨x, hx⟩ := h.2 ⟨w, hwk⟩
    refine ⟨x, Subtype.ext ?_⟩
    rw [key, hx]
    exact hw

end Transfer

section Coord

variable {X : Scheme.{u}} {ι : Type u} {T : ι → X.Opens} (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)

/-- The coordinate of a section of the glued line bundle over `W ≤ T i` against the local
generator at `i`. -/
noncomputable def coord (i : ι) {W : X.Opens} (hW : W ≤ T i) (m : Γ(glued g, W)) : Γ(X, W) :=
  X.presheaf.map (homOfLE (le_inf le_rfl hW : W ≤ W ⊓ T i)).op (comp g m i)

variable (hg : IsCocycle g)

lemma coord_smul_genSec_eq (i : ι) {W : X.Opens} (hW : W ≤ T i) (m : Γ(glued g, W)) :
    coord g i hW m • genSec g hg i hW = m :=
  (eq_comp_smul_genSec g hg i hW m).symm

include hg in
lemma coord_eq {i : ι} {W : X.Opens} (hW : W ≤ T i) {m : Γ(glued g, W)} {r : Γ(X, W)}
    (h : r • genSec g hg i hW = m) : coord g i hW m = r :=
  (smul_genSec_bijective g hg i hW).1 ((coord_smul_genSec_eq g hg i hW m).trans h.symm)

lemma coord_smul_genSec (i : ι) {W : X.Opens} (hW : W ≤ T i) (r : Γ(X, W)) :
    coord g i hW (r • genSec g hg i hW) = r :=
  coord_eq g hg hW rfl

include hg in
lemma coord_add (i : ι) {W : X.Opens} (hW : W ≤ T i) (m m' : Γ(glued g, W)) :
    coord g i hW (m + m') = coord g i hW m + coord g i hW m' :=
  coord_eq g hg hW (by
    rw [add_smul, coord_smul_genSec_eq, coord_smul_genSec_eq])

include hg in
lemma coord_neg (i : ι) {W : X.Opens} (hW : W ≤ T i) (m : Γ(glued g, W)) :
    coord g i hW (-m) = -coord g i hW m :=
  coord_eq g hg hW (by rw [neg_smul, coord_smul_genSec_eq])

include hg in
lemma coord_smul (i : ι) {W : X.Opens} (hW : W ≤ T i) (a : Γ(X, W)) (m : Γ(glued g, W)) :
    coord g i hW (a • m) = a * coord g i hW m :=
  coord_eq g hg hW (by rw [mul_smul, coord_smul_genSec_eq])

include hg in
lemma coord_res (i : ι) {W W' : X.Opens} (h : W' ≤ W) (hW : W ≤ T i) (m : Γ(glued g, W)) :
    coord g i (h.trans hW) ((glued g).presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (coord g i hW m) :=
  coord_eq g hg _ (by
    rw [← map_genSec g hg i h hW, ← Scheme.Modules.map_smul, coord_smul_genSec_eq])

end Coord

lemma neg_units_inv_mul_neg_mul {S : Type*} [CommRing S] (a : Sˣ) (z : S) :
    -((a⁻¹ : Sˣ) : S) * (-(a : S) * z) = z := by
  rw [← mul_assoc, neg_mul_neg, Units.inv_mul, one_mul]

lemma neg_units_mul_neg_inv_mul {S : Type*} [CommRing S] (a : Sˣ) (z : S) :
    -(a : S) * (-((a⁻¹ : Sˣ) : S) * z) = z := by
  rw [← mul_assoc, neg_mul_neg, Units.mul_inv, one_mul]

section Cover

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
  {𝒰 : Y.OrderedAffineCover}

/-- The cocycle `γ i j = (α i j)⁻¹ * β i j`. -/
def gaugeCocycle (α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ) (i j : 𝒰.ι) :
    (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ :=
  (α i j)⁻¹ * β i j

lemma isCocycle_gaugeCocycle {α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ}
    (hα : IsCocycle α) (hβ : IsCocycle β) : IsCocycle (gaugeCocycle α β) := by
  intro i j k
  have hinv : ∀ {U V : Y.Opens} (h : V ≤ U) (w : (Γ(Y, U))ˣ),
      Y.presheaf.map (homOfLE h).op ((w⁻¹ : (Γ(Y, U))ˣ) : Γ(Y, U)) *
        Y.presheaf.map (homOfLE h).op (w : Γ(Y, U)) = 1 := fun h w ↦ by
    rw [← map_mul, Units.inv_mul, map_one]
  simp only [gaugeCocycle, Units.val_mul, map_mul]
  have e1 := hinv (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i ⊓ 𝒰.U j) (α i j)
  have e2 := hinv (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U j ⊓ 𝒰.U k) (α j k)
  have e3 := hinv (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k ≤ 𝒰.U i ⊓ 𝒰.U k) (α i k)
  have ha := hα i j k
  have hb := hβ i j k
  generalize Y.presheaf.map _ ((α i j : Γ(Y, 𝒰.U i ⊓ 𝒰.U j))) = a1 at *
  generalize Y.presheaf.map _ ((α j k : Γ(Y, 𝒰.U j ⊓ 𝒰.U k))) = a2 at *
  generalize Y.presheaf.map _ ((α i k : Γ(Y, 𝒰.U i ⊓ 𝒰.U k))) = a3 at *
  generalize Y.presheaf.map _ (((α i j)⁻¹ : (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ) : Γ(Y, 𝒰.U i ⊓ 𝒰.U j))
    = a1' at *
  generalize Y.presheaf.map _ (((α j k)⁻¹ : (Γ(Y, 𝒰.U j ⊓ 𝒰.U k))ˣ) : Γ(Y, 𝒰.U j ⊓ 𝒰.U k))
    = a2' at *
  generalize Y.presheaf.map _ (((α i k)⁻¹ : (Γ(Y, 𝒰.U i ⊓ 𝒰.U k))ˣ) : Γ(Y, 𝒰.U i ⊓ 𝒰.U k))
    = a3' at *
  rw [← hb]
  have h3 : a3' = a1' * a2' := by
    calc a3' = a3' * ((a1' * a1) * (a2' * a2)) := by rw [e1, e2]; ring
      _ = (a3' * (a1 * a2)) * (a1' * a2') := by ring
      _ = a1' * a2' := by rw [ha, e3, one_mul]
  rw [h3]
  ring

/-- The singleton index `[i]` of the ordered cover. -/
def idx0 (i : 𝒰.ι) : 𝒰.Idx 0 :=
  ⟨fun _ ↦ i, fun a b hab ↦
    absurd hab (by rw [Subsingleton.elim (α := Fin 1) a b]; exact lt_irrefl b)⟩

lemma le_inter_idx0 (i : 𝒰.ι) : 𝒰.U i ≤ 𝒰.inter (idx0 i) := le_iInf fun _ ↦ le_rfl

lemma inter_idx0_le (i : 𝒰.ι) : 𝒰.inter (idx0 i) ≤ 𝒰.U i := 𝒰.inter_le (idx0 i) 0

lemma exists_eq_idx0 (s : 𝒰.Idx 0) : ∃ i, s = idx0 i :=
  ⟨s.1 0, Subtype.ext (funext fun j ↦ by fin_cases j; rfl)⟩

/-- The intersection of an increasing pair is the meet of its two opens. -/
lemma pair_le_inter (t : 𝒰.Idx 1) : 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) ≤ 𝒰.inter t :=
  le_iInf fun j ↦ by fin_cases j; exacts [inf_le_left, inf_le_right]

lemma inter_le_pair (t : 𝒰.Idx 1) : 𝒰.inter t ≤ 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) :=
  le_inf (𝒰.inter_le t 0) (𝒰.inter_le t 1)

variable (γ : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ) (hγ : IsCocycle γ)

/-- The degree-zero comparison map: the coordinates against the local generators. -/
noncomputable def toGauge0 (c : (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 0) :
    GaugeC0 p 𝒰 := fun i ↦
  Y.presheaf.map (homOfLE (le_inter_idx0 i)).op
    (coord γ i (inter_idx0_le i) (c (idx0 i)))

/-- The inverse of the degree-zero comparison map. -/
noncomputable def ofGauge0 (b : GaugeC0 p 𝒰) :
    (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 0 := fun s ↦
  Y.presheaf.map (homOfLE (𝒰.inter_le s 0)).op (b (s.1 0)) • genSec γ hγ (s.1 0) (𝒰.inter_le s 0)

/-- The degree-zero Čech group of the glued line bundle is the degree-zero gauge group. -/
noncomputable def cochain0Equiv :
    (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 0 ≃ₗ[R] GaugeC0 p 𝒰 where
  toFun := toGauge0 p γ
  map_add' c c' := by
    funext i
    simp only [toGauge0, Pi.add_apply]
    erw [coord_add γ hγ, map_add]
    rfl
  map_smul' r c := by
    funext i
    simp only [toGauge0, Pi.smul_apply, RingHom.id_apply]
    erw [coord_smul γ hγ, map_mul]
    erw [GaugeC0.smul_apply]
    congr 1
    exact res_scalarOn p _ r
  invFun := ofGauge0 p γ hγ
  left_inv c := by
    funext s
    obtain ⟨i, rfl⟩ := exists_eq_idx0 s
    simp only [ofGauge0, toGauge0]
    erw [res_res, res_self]
    exact coord_smul_genSec_eq γ hγ i _ _
  right_inv b := by
    funext i
    simp only [ofGauge0, toGauge0]
    erw [coord_smul_genSec γ hγ i, res_res, res_self]
    rfl

lemma cochain0Equiv_apply (c : (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 0) (i : 𝒰.ι) :
    cochain0Equiv p γ hγ c i = Y.presheaf.map (homOfLE (le_inter_idx0 i)).op
      (coord γ i (inter_idx0_le i) (c (idx0 i))) := rfl

lemma res_idx0_eq_smul_genSec (c : (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 0)
    (j : 𝒰.ι) {W : Y.Opens} (h : W ≤ 𝒰.inter (idx0 j)) (hW : W ≤ 𝒰.U j) :
    (OModulePresheaf.ofModules p (glued γ)).res h (c (idx0 j)) =
      Y.presheaf.map (homOfLE hW).op (cochain0Equiv p γ hγ c j) • genSec γ hγ j hW := by
  rw [cochain0Equiv_apply, res_res]
  change (glued γ).presheaf.map (homOfLE h).op (c (idx0 j)) = _
  conv_lhs => rw [← coord_smul_genSec_eq γ hγ j (inter_idx0_le j) (c (idx0 j))]
  rw [Scheme.Modules.map_smul, map_genSec γ hγ j h (inter_idx0_le j)]

/-- A degree-zero cochain restricted to an open `W ≤ U i` is its gauge coordinate at `i` times
the local generator. -/
lemma res_eq_smul_genSec (c : (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 0)
    (s : 𝒰.Idx 0) (i : 𝒰.ι) (hs : s.1 0 = i) {W : Y.Opens} (h : W ≤ 𝒰.inter s)
    (hW : W ≤ 𝒰.U i) :
    (OModulePresheaf.ofModules p (glued γ)).res h (c s) =
      Y.presheaf.map (homOfLE hW).op (cochain0Equiv p γ hγ c i) • genSec γ hγ i hW := by
  subst hs
  obtain ⟨j, rfl⟩ := exists_eq_idx0 s
  exact res_idx0_eq_smul_genSec p γ hγ c j h hW

variable (α : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ)

/-- The degree-one comparison map: the coordinate against the local generator at `t 0`,
multiplied by `-α (t 0) (t 1)`. -/
noncomputable def toGauge1 (x : (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 1) :
    GaugeC1 p 𝒰 := fun t ↦
  -(α (t.1 0) (t.1 1) : Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) *
    Y.presheaf.map (homOfLE (pair_le_inter t)).op (coord γ (t.1 0) (𝒰.inter_le t 0) (x t))

/-- The inverse of the degree-one comparison map. -/
noncomputable def ofGauge1 (y : GaugeC1 p 𝒰) :
    (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 1 := fun t ↦
  Y.presheaf.map (homOfLE (inter_le_pair t)).op
      (-(((α (t.1 0) (t.1 1))⁻¹ : (Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1)))ˣ) :
        Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) * y t) •
    genSec γ hγ (t.1 0) (𝒰.inter_le t 0)

/-- The degree-one Čech group of the glued line bundle is the degree-one gauge group. -/
noncomputable def cochain1Equiv :
    (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 1 ≃ₗ[R] GaugeC1 p 𝒰 where
  toFun := toGauge1 p γ α
  map_add' x x' := by
    funext t
    simp only [toGauge1, Pi.add_apply]
    erw [coord_add γ hγ, map_add, mul_add]
    rfl
  map_smul' r x := by
    funext t
    change toGauge1 p γ α (r • x) t = scalarOn p r * toGauge1 p γ α x t
    have e : (r • x) t = (scalarOn p r : Γ(Y, 𝒰.inter t)) • x t := rfl
    simp only [toGauge1]
    rw [e]
    erw [coord_smul γ hγ, map_mul, res_scalarOn]
    ring
  invFun := ofGauge1 p γ hγ α
  left_inv x := by
    funext t
    simp only [ofGauge1, toGauge1]
    rw [neg_units_inv_mul_neg_mul]
    erw [res_res, res_self]
    exact coord_smul_genSec_eq γ hγ _ _ _
  right_inv y := by
    funext t
    simp only [ofGauge1, toGauge1]
    erw [coord_smul_genSec γ hγ, res_res, res_self]
    exact neg_units_mul_neg_inv_mul _ _

lemma cochain1Equiv_apply (x : (OModulePresheaf.ofModules p (glued γ)).cochain 𝒰 1)
    (t : 𝒰.Idx 1) :
    cochain1Equiv p γ hγ α x t =
      -(α (t.1 0) (t.1 1) : Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) *
        Y.presheaf.map (homOfLE (pair_le_inter t)).op
          (coord γ (t.1 0) (𝒰.inter_le t 0) (x t)) := rfl

end Cover

section Square

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
  {𝒰 : Y.OrderedAffineCover} {α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ}
  (hγ : IsCocycle (gaugeCocycle α β))

/-- Under the comparison maps, the Čech differential of the glued line bundle is the gauge
differential. -/
lemma gaugeD_comp_cochain0Equiv :
    gaugeD p α β ∘ₗ (cochain0Equiv p (gaugeCocycle α β) hγ).toLinearMap =
      (cochain1Equiv p (gaugeCocycle α β) hγ α).toLinearMap ∘ₗ
        (OModulePresheaf.ofModules p (glued (gaugeCocycle α β))).d 𝒰 0 := by
  refine LinearMap.ext fun c ↦ ?_
  funext t
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cochain1Equiv_apply, gaugeD_apply]
  have h0 := res_eq_smul_genSec p (gaugeCocycle α β) hγ c (𝒰.face t 1) (t.1 0) rfl
    (𝒰.inter_le_inter_face t 1) (𝒰.inter_le t 0)
  have h1 := res_eq_smul_genSec p (gaugeCocycle α β) hγ c (𝒰.face t 0) (t.1 1) rfl
    (𝒰.inter_le_inter_face t 0) (𝒰.inter_le t 1)
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [h0, h1, genSec_eq_smul_genSec hγ (𝒰.inter_le t 0) (𝒰.inter_le t 1), smul_smul,
    ← sub_eq_add_neg, ← sub_smul, coord_smul_genSec, map_sub, map_mul, res_res, res_res,
    res_res, res_self]
  simp only [gaugeCocycle, Units.val_mul]
  have hinv := Units.mul_inv (α (t.1 0) (t.1 1))
  linear_combination
    ((β (t.1 0) (t.1 1) : Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) *
      Y.presheaf.map (homOfLE (inf_le_right : 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) ≤ 𝒰.U (t.1 1))).op
        (cochain0Equiv p (gaugeCocycle α β) hγ c (t.1 1))) * hinv

end Square

end CechModel

open CechModel in
/-- **Čech model of the gauge complex.** For a proper flat `p : Y ⟶ Spec R` with `R`
Noetherian, an ordered affine cover `𝒰` and two unit cocycles `α`, `β`, there is a two-term
complex of finite free `R`-modules with a map to the gauge complex inducing a bijection on
kernels after every base change. -/
theorem exists_gauge_model {R : Type u} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of R)) [IsProper p] [Flat p] (𝒰 : Y.OrderedAffineCover)
    (α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ)
    (hα : CocycleGluing.IsCocycle α) (hβ : CocycleGluing.IsCocycle β) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ψ0 : G.C0 →ₗ[R] GaugeC0 p 𝒰)
      (ψ1 : G.C1 →ₗ[R] GaugeC1 p 𝒰) (comm : gaugeD p α β ∘ₗ ψ0 = ψ1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d (gaugeD p α β) ψ0 ψ1 comm A) := by
  have hγ := isCocycle_gaugeCocycle hα hβ
  have htriv : ∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (glued (gaugeCocycle α β)) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := isLocallyFreeRankOne_glued (gaugeCocycle α β) 𝒰.iSup_eq_top hγ x
    exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm ≪≫ e⟩⟩
  obtain ⟨G, ι0, ι1, comm, hbij⟩ :=
    OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules p
      (glued (gaugeCocycle α β)) htriv 𝒰
  have sq := gaugeD_comp_cochain0Equiv p hγ
  have comm' : gaugeD p α β ∘ₗ ((cochain0Equiv p _ hγ).toLinearMap ∘ₗ ι0) =
      ((cochain1Equiv p _ hγ α).toLinearMap ∘ₗ ι1) ∘ₗ G.d := by
    rw [← LinearMap.comp_assoc, sq, LinearMap.comp_assoc, comm, LinearMap.comp_assoc]
  exact ⟨G, _, _, comm', fun A _ _ ↦ kerMapBaseChange_bijective_of_linearEquiv G.d _ _ ι0 ι1
    comm _ _ sq comm' A (hbij A)⟩

end Langlands.AlgebraicGeometry.Picard.LineHom

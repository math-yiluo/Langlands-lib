import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqPullback
import Langlands.AlgebraicGeometry.Modules.CechResolution.Naturality
import Langlands.AlgebraicGeometry.CechPullback

/-!
# Cohomology classes and the cup product of ordered Čech cocycles

For the ordered Čech cochain complex over all tuples (`AllSeq.cochainComplex`), this module
describes cohomology classes of cocycles (`classMap`), and for the structure sheaf it defines the
product `H¹ × H¹ ⟶ H²` from the Alexander–Whitney product `Langlands.Cohomology.Cech.cup₁`. It
transports this product to the actual cohomology `(relativeCohomology π n).obj 𝒪_X`
(`cupCanonical`), proves graded anticommutativity in degree one, and proves that the canonical
structure-sheaf pullback (`relativeCohomologyPullback` followed by the unit comparison
`h^* 𝒪_X ≅ 𝒪_Y`) is a ring map in degrees `1, 1 → 2` (`pull_cupCanonical`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology

section Classes

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) {ι : Type u} [Fintype ι]
  (U : ι → X.Opens) (M : X.Modules)

lemma subtype_comp_d (n : ℕ) :
    ModuleCat.ofHom (LinearMap.ker (dCochain π U M (n + 1))).subtype ≫
      (cochainComplex π U M).d (n + 1) (n + 2) = 0 := by
  rw [cochainComplex_d]
  ext z
  exact z.2

/-- An ordered Čech cocycle as an element of the cycles of the cochain complex. -/
def cyclesOfKer (n : ℕ) :
    ModuleCat.of R (LinearMap.ker (dCochain π U M (n + 1))) ⟶
      (cochainComplex π U M).cycles (n + 1) :=
  (cochainComplex π U M).liftCycles
    (ModuleCat.ofHom (LinearMap.ker (dCochain π U M (n + 1))).subtype) (n + 2) (by simp)
    (subtype_comp_d π U M n)

lemma cyclesOfKer_i (n : ℕ) (z : LinearMap.ker (dCochain π U M (n + 1))) :
    (cochainComplex π U M).iCycles (n + 1) (cyclesOfKer π U M n z) = (z : cochain π U M (n + 1)) := by
  rw [← ConcreteCategory.comp_apply, cyclesOfKer, HomologicalComplex.liftCycles_i]
  rfl

/-- The cohomology class of an ordered Čech cocycle. -/
def classMap (n : ℕ) :
    LinearMap.ker (dCochain π U M (n + 1)) →ₗ[R] (cochainComplex π U M).homology (n + 1) :=
  (cyclesOfKer π U M n ≫ (cochainComplex π U M).homologyπ (n + 1)).hom

lemma classMap_apply (n : ℕ) (z : LinearMap.ker (dCochain π U M (n + 1))) :
    classMap π U M n z = (cochainComplex π U M).homologyπ (n + 1) (cyclesOfKer π U M n z) := rfl

lemma iCycles_mem_ker (n : ℕ) (c : (cochainComplex π U M).cycles (n + 1)) :
    (cochainComplex π U M).iCycles (n + 1) c ∈ LinearMap.ker (dCochain π U M (n + 1)) := by
  rw [LinearMap.mem_ker]
  have h := congrArg (fun f => f c) ((cochainComplex π U M).iCycles_d (n + 1) (n + 2))
  rw [cochainComplex_d] at h
  exact h

lemma cyclesOfKer_iCycles (n : ℕ) (c : (cochainComplex π U M).cycles (n + 1)) :
    cyclesOfKer π U M n ⟨_, iCycles_mem_ker π U M n c⟩ = c := by
  apply (ModuleCat.mono_iff_injective ((cochainComplex π U M).iCycles (n + 1))).1 inferInstance
  rw [cyclesOfKer_i]

lemma classMap_surjective (n : ℕ) : Function.Surjective (classMap π U M n) := by
  intro x
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainComplex π U M).homologyπ (n + 1))).1 inferInstance x
  exact ⟨⟨_, iCycles_mem_ker π U M n c⟩, by rw [classMap_apply, cyclesOfKer_iCycles]⟩

lemma classMap_eq_zero_iff (n : ℕ) (z : LinearMap.ker (dCochain π U M (n + 1))) :
    classMap π U M n z = 0 ↔ ∃ y, dCochain π U M n y = z := by
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := exists_toCycles_eq_of_homologyπ_eq_zero (cochainComplex π U M) n _ hz
    refine ⟨y, ?_⟩
    have h := congrArg ((cochainComplex π U M).iCycles (n + 1)) hy
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i, cochainComplex_d] at h
    exact h.trans (cyclesOfKer_i π U M n z)
  · rintro ⟨y, hy⟩
    have hc : cyclesOfKer π U M n z = (cochainComplex π U M).toCycles n (n + 1) y := by
      apply (ModuleCat.mono_iff_injective ((cochainComplex π U M).iCycles (n + 1))).1
        inferInstance
      rw [cyclesOfKer_i, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i,
        cochainComplex_d]
      exact hy.symm
    rw [classMap_apply, hc, ← ConcreteCategory.comp_apply,
      HomologicalComplex.toCycles_comp_homologyπ]
    rfl

variable {π U M} in
lemma homologyMap_classMap {Y : Scheme.{u}} {π'' : Y ⟶ Spec R}
    {κ : Type u} [Fintype κ] {V : κ → Y.Opens} {N : Y.Modules}
    (φ : cochainComplex π U M ⟶ cochainComplex π'' V N) (n : ℕ)
    (z : LinearMap.ker (dCochain π U M (n + 1)))
    (hz : φ.f (n + 1) (z : cochain π U M (n + 1)) ∈ LinearMap.ker (dCochain π'' V N (n + 1))) :
    HomologicalComplex.homologyMap φ (n + 1) (classMap π U M n z) =
      classMap π'' V N n ⟨_, hz⟩ := by
  rw [classMap_apply, classMap_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective ((cochainComplex π'' V N).iCycles (n + 1))).1 inferInstance
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    cyclesOfKer_i, cyclesOfKer_i]

end Classes

section ChainLevel

open Cech

variable {T : TopCat.{u}} (P : TopCat.Presheaf CommRingCat.{u} T) {ι : Type u}
  {U : ι → TopologicalSpace.Opens T}

/-- Pointwise product of two `1`-cochains of a presheaf of rings. -/
def mulPt (z w : C (ab P) U 1) : C (ab P) U 1 := fun σ => z σ * w σ

lemma face_mulPt (z w : C (ab P) U 1) {n : ℕ} (τ : Fin n → ι) (θ : Fin 2 → Fin n) :
    face (mulPt P z w) τ θ = face z τ θ * face w τ θ :=
  res_mul _ _ _

/-- Graded anticommutativity of the product of two `1`-cocycles, on cochains:
`z ∪ w + w ∪ z = d (-(z · w))`. -/
lemma cup₁_add_cup₁_swap {z w : C (ab P) U 1} (hz : Cech.d (ab P) U 1 z = 0)
    (hw : Cech.d (ab P) U 1 w = 0) :
    cup₁ P U z w + cup₁ P U w z = Cech.d (ab P) U 1 (-mulPt P z w) := by
  funext τ
  have e0 : (Fin.succAbove (0 : Fin 3)) = ![1, 2] := by funext a; fin_cases a <;> rfl
  have e1 : (Fin.succAbove (1 : Fin 3)) = ![0, 2] := by funext a; fin_cases a <;> rfl
  have e2 : (Fin.succAbove (2 : Fin 3)) = ![0, 1] := by funext a; fin_cases a <;> rfl
  have es : (Fin.succ : Fin 2 → Fin 3) = ![1, 2] := by funext a; fin_cases a <;> rfl
  have ed : (edge (0 : Fin 2)) = ![0, 1] := by funext a; fin_cases a <;> rfl
  have hz' := congrFun hz τ
  have hw' := congrFun hw τ
  rw [d_apply_face, Fin.sum_univ_three, e0, e1, e2] at hz' hw'
  simp only [Pi.zero_apply, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    neg_one_sq, one_smul, neg_smul] at hz' hw'
  rw [Pi.add_apply, cup₁_apply, cup₁_apply, d_apply_face, Fin.sum_univ_three, e0, e1, e2, ed]
  simp only [face_neg, face_mulPt, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    neg_one_sq, one_smul, neg_smul]
  rw [es]
  linear_combination face w τ ![0, 2] * hz' + (face z τ ![0, 1] + face z τ ![1, 2]) * hw'

end ChainLevel

section Cup

open Cech

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) {ι : Type u} [Fintype ι]
  (U : ι → X.Opens)

/-- The structure sheaf as a module over itself. -/
abbrev unitModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

omit [Fintype ι] in
lemma dCochain_unit (p : ℕ) (c : cochain π U (unitModule X) p) :
    (dCochain π U (unitModule X) p c : C (ab X.presheaf) U (p + 1)) =
      Cech.d (ab X.presheaf) U p (c : C (ab X.presheaf) U p) := by
  funext τ
  refine (dCochain_apply π U _ p c τ).trans ?_
  exact (d_apply _ _ p _ τ).symm

/-- The product of an ordered Čech `1`-cochain and a `q`-cochain of the structure sheaf. -/
def cup {q : ℕ} (z : cochain π U (unitModule X) 1) (b : cochain π U (unitModule X) q) :
    cochain π U (unitModule X) (q + 1) :=
  cup₁ X.presheaf U (z : C (ab X.presheaf) U 1) (b : C (ab X.presheaf) U q)

/-- The image of `r : R` in the sections of the structure sheaf over `W`. -/
abbrev algC (W : X.Opens) (r : R) : (ab X.presheaf).obj (op W) :=
  (π.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso R).inv.hom r)

omit [Fintype ι] in
lemma smul_apply {p : ℕ} (r : R) (c : cochain π U (unitModule X) p) (σ : Fin (p + 1) → ι) :
    (show (ab X.presheaf).obj (op (inter U σ)) from (r • c) σ) =
      algC π (inter U σ) r * (show (ab X.presheaf).obj (op (inter U σ)) from c σ) :=
  rfl

omit [Fintype ι] in
lemma res_appLE {W W' : X.Opens} (h : W' ≤ W) (x : Γ(Spec R, ⊤)) :
    Cech.res (P := ab X.presheaf) h ((π.appLE ⊤ W le_top).hom x) =
      (π.appLE ⊤ W' le_top).hom x := by
  change (π.appLE ⊤ W le_top ≫ X.presheaf.map (homOfLE h).op).hom x = _
  rw [Scheme.Hom.appLE_map]

omit [Fintype ι] in
lemma face_smul {m n : ℕ} (r : R) (c : cochain π U (unitModule X) m) (τ : Fin (n + 1) → ι)
    (θ : Fin (m + 1) → Fin (n + 1)) :
    face (P := ab X.presheaf) (U := U) ((r • c : cochain π U (unitModule X) m) :
        C (ab X.presheaf) U m) τ θ =
      algC π (inter U τ) r * face (P := ab X.presheaf) (U := U) (c : C (ab X.presheaf) U m) τ θ := by
  change Cech.res _ (algC π (inter U (τ ∘ θ)) r *
    (show (ab X.presheaf).obj (op (inter U (τ ∘ θ))) from c (τ ∘ θ))) = _
  rw [res_mul, res_appLE]
  rfl

omit [Fintype ι] in
lemma cup_add_left {q : ℕ} (z z' : cochain π U (unitModule X) 1)
    (b : cochain π U (unitModule X) q) : cup π U (z + z') b = cup π U z b + cup π U z' b :=
  cup₁_add_left (R := X.presheaf) (U := U) z z' b

omit [Fintype ι] in
lemma cup_add_right {q : ℕ} (z : cochain π U (unitModule X) 1)
    (b b' : cochain π U (unitModule X) q) : cup π U z (b + b') = cup π U z b + cup π U z b' :=
  cup₁_add_right (R := X.presheaf) (U := U) z b b'

omit [Fintype ι] in
lemma cup_smul_left {q : ℕ} (r : R) (z : cochain π U (unitModule X) 1)
    (b : cochain π U (unitModule X) q) : cup π U (r • z) b = r • cup π U z b := by
  funext τ
  change face (P := ab X.presheaf) (U := U) ((r • z : cochain π U (unitModule X) 1) :
      C (ab X.presheaf) U 1) τ (edge 0) * face (P := ab X.presheaf) (U := U)
      (b : C (ab X.presheaf) U q) τ Fin.succ =
    algC π (inter U τ) r *
      (face (P := ab X.presheaf) (U := U) (z : C (ab X.presheaf) U 1) τ (edge 0) *
        face (P := ab X.presheaf) (U := U) (b : C (ab X.presheaf) U q) τ Fin.succ)
  rw [face_smul, mul_assoc]

omit [Fintype ι] in
lemma cup_smul_right {q : ℕ} (r : R) (z : cochain π U (unitModule X) 1)
    (b : cochain π U (unitModule X) q) : cup π U z (r • b) = r • cup π U z b := by
  funext τ
  change face (P := ab X.presheaf) (U := U) (z : C (ab X.presheaf) U 1) τ (edge 0) *
      face (P := ab X.presheaf) (U := U) ((r • b : cochain π U (unitModule X) q) :
        C (ab X.presheaf) U q) τ Fin.succ =
    algC π (inter U τ) r *
      (face (P := ab X.presheaf) (U := U) (z : C (ab X.presheaf) U 1) τ (edge 0) *
        face (P := ab X.presheaf) (U := U) (b : C (ab X.presheaf) U q) τ Fin.succ)
  rw [face_smul, mul_left_comm]

/-- The product with a `1`-cochain, as an `R`-bilinear map. -/
def cupL (q : ℕ) :
    cochain π U (unitModule X) 1 →ₗ[R] cochain π U (unitModule X) q →ₗ[R]
      cochain π U (unitModule X) (q + 1) :=
  LinearMap.mk₂ R (cup π U) (cup_add_left π U) (cup_smul_left π U) (cup_add_right π U)
    (cup_smul_right π U)

omit [Fintype ι] in
/-- Leibniz rule for the product with a `1`-cocycle. -/
lemma dCochain_cup {q : ℕ} {z : cochain π U (unitModule X) 1}
    (hz : dCochain π U (unitModule X) 1 z = 0) (b : cochain π U (unitModule X) q) :
    dCochain π U (unitModule X) (q + 1) (cup π U z b) =
      -cup π U z (dCochain π U (unitModule X) q b) := by
  have hz' : Cech.d (ab X.presheaf) U 1 (z : C (ab X.presheaf) U 1) = 0 := by
    rw [← dCochain_unit]; exact hz
  rw [dCochain_unit]
  exact (d_cup₁_of_cocycle (R := X.presheaf) hz' b).trans
    (congrArg (fun x => -cup₁ X.presheaf U (z : C (ab X.presheaf) U 1) x)
      (dCochain_unit π U q b).symm)

omit [Fintype ι] in
/-- The product of a coboundary with a cocycle is a coboundary. -/
lemma cup_dCochain_zero {q : ℕ} (y : cochain π U (unitModule X) 0)
    {b : cochain π U (unitModule X) q} (hb : dCochain π U (unitModule X) q b = 0) :
    ∃ c, cup π U (dCochain π U (unitModule X) 0 y) b = dCochain π U (unitModule X) q c := by
  have hb' : Cech.d (ab X.presheaf) U q (b : C (ab X.presheaf) U q) = 0 := by
    rw [← dCochain_unit]; exact hb
  refine ⟨cup₀ X.presheaf U (y : C (ab X.presheaf) U 0) (b : C (ab X.presheaf) U q), ?_⟩
  have h := d_cup₀ (R := X.presheaf) (U := U) q (y : C (ab X.presheaf) U 0) b
  rw [hb', cup₀_zero_right, add_zero] at h
  exact (congrArg (fun x => cup₁ X.presheaf U x (b : C (ab X.presheaf) U q))
    (dCochain_unit π U 0 y)).trans (h.symm.trans (dCochain_unit π U q _).symm)

omit [Fintype ι] in
lemma cup_mem_ker {z w : cochain π U (unitModule X) 1}
    (hz : z ∈ LinearMap.ker (dCochain π U (unitModule X) 1))
    (hw : w ∈ LinearMap.ker (dCochain π U (unitModule X) 1)) :
    cup π U z w ∈ LinearMap.ker (dCochain π U (unitModule X) 2) := by
  rw [LinearMap.mem_ker] at hz hw ⊢
  rw [dCochain_cup π U hz, hw]
  exact neg_eq_zero.mpr (cup₁_zero_right (R := X.presheaf) (U := U) _)

/-- The product of two ordered Čech `1`-cocycles of the structure sheaf. -/
def cupZ :
    LinearMap.ker (dCochain π U (unitModule X) 1) →ₗ[R]
      LinearMap.ker (dCochain π U (unitModule X) 1) →ₗ[R]
        LinearMap.ker (dCochain π U (unitModule X) 2) :=
  LinearMap.mk₂ R (fun z w => ⟨cup π U z w, cup_mem_ker π U z.2 w.2⟩)
    (fun z z' w => Subtype.ext (cup_add_left π U (z : cochain π U (unitModule X) 1) z'
      (w : cochain π U (unitModule X) 1)))
    (fun r z w => Subtype.ext (cup_smul_left π U r (z : cochain π U (unitModule X) 1)
      (w : cochain π U (unitModule X) 1)))
    (fun z w w' => Subtype.ext (cup_add_right π U (z : cochain π U (unitModule X) 1)
      (w : cochain π U (unitModule X) 1) w'))
    (fun r z w => Subtype.ext (cup_smul_right π U r (z : cochain π U (unitModule X) 1)
      (w : cochain π U (unitModule X) 1)))

omit [Fintype ι] in
lemma cupZ_apply (z w : LinearMap.ker (dCochain π U (unitModule X) 1)) :
    ((cupZ π U z w : LinearMap.ker (dCochain π U (unitModule X) 2)) :
      cochain π U (unitModule X) 2) = cup π U z w := by
  rw [cupZ, LinearMap.mk₂_apply]

/-- The product of cocycles followed by the cohomology class. -/
def cupClassZ :
    LinearMap.ker (dCochain π U (unitModule X) 1) →ₗ[R]
      LinearMap.ker (dCochain π U (unitModule X) 1) →ₗ[R]
        (cochainComplex π U (unitModule X)).homology 2 :=
  (cupZ π U).compr₂ (classMap π U (unitModule X) 1)

lemma cupClassZ_eq_zero_of_left (z w : LinearMap.ker (dCochain π U (unitModule X) 1))
    (hz : classMap π U (unitModule X) 0 z = 0) : cupClassZ π U z w = 0 := by
  obtain ⟨y, hy⟩ := (classMap_eq_zero_iff π U _ 0 z).1 hz
  obtain ⟨c, hc⟩ := cup_dCochain_zero π U y w.2
  rw [cupClassZ, LinearMap.compr₂_apply, classMap_eq_zero_iff]
  refine ⟨c, ?_⟩
  rw [cupZ_apply, ← hy]
  exact hc.symm

lemma cupClassZ_eq_zero_of_right (z w : LinearMap.ker (dCochain π U (unitModule X) 1))
    (hw : classMap π U (unitModule X) 0 w = 0) : cupClassZ π U z w = 0 := by
  obtain ⟨y, hy⟩ := (classMap_eq_zero_iff π U _ 0 w).1 hw
  rw [cupClassZ, LinearMap.compr₂_apply, classMap_eq_zero_iff]
  refine ⟨-cup π U z y, ?_⟩
  rw [cupZ_apply, map_neg, dCochain_cup π U z.2, hy, neg_neg]

/-- The cup product `H¹ × H¹ ⟶ H²` on ordered Čech cohomology of the structure sheaf. -/
def cupH :
    (cochainComplex π U (unitModule X)).homology 1 →ₗ[R]
      (cochainComplex π U (unitModule X)).homology 1 →ₗ[R]
        (cochainComplex π U (unitModule X)).homology 2 :=
  let e := (classMap π U (unitModule X) 0).quotKerEquivOfSurjective
    (classMap_surjective π U (unitModule X) 0)
  let K := LinearMap.ker (classMap π U (unitModule X) 0)
  let G := K.liftQ (cupClassZ π U).flip (fun w hw => by
    rw [LinearMap.mem_ker] at hw ⊢
    ext z
    exact cupClassZ_eq_zero_of_right π U z w hw)
  let H := K.liftQ G.flip (fun z hz => by
    rw [LinearMap.mem_ker] at hz ⊢
    ext w
    exact cupClassZ_eq_zero_of_left π U z w hz)
  H.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap

lemma cupH_classMap (z w : LinearMap.ker (dCochain π U (unitModule X) 1)) :
    cupH π U (classMap π U (unitModule X) 0 z) (classMap π U (unitModule X) 0 w) =
      classMap π U (unitModule X) 1 (cupZ π U z w) := by
  simp only [cupH, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

lemma cupH_add_swap (x y : (cochainComplex π U (unitModule X)).homology 1) :
    cupH π U x y + cupH π U y x = 0 := by
  obtain ⟨z, rfl⟩ := classMap_surjective π U (unitModule X) 0 x
  obtain ⟨w, rfl⟩ := classMap_surjective π U (unitModule X) 0 y
  rw [cupH_classMap, cupH_classMap, ← map_add, classMap_eq_zero_iff]
  set z' : C (ab X.presheaf) U 1 := (z : cochain π U (unitModule X) 1) with hz'
  set w' : C (ab X.presheaf) U 1 := (w : cochain π U (unitModule X) 1) with hw'
  refine ⟨-(mulPt X.presheaf z' w' : C (ab X.presheaf) U 1), ?_⟩
  have hz : Cech.d (ab X.presheaf) U 1 z' = 0 := by
    rw [hz', ← dCochain_unit]; exact z.2
  have hw : Cech.d (ab X.presheaf) U 1 w' = 0 := by
    rw [hw', ← dCochain_unit]; exact w.2
  rw [Submodule.coe_add, cupZ_apply, cupZ_apply]
  exact (dCochain_unit π U 1 _).trans (cup₁_add_cup₁_swap X.presheaf hz hw).symm

/-- Graded anticommutativity of the cup product on `H¹`. -/
lemma cupH_swap (x y : (cochainComplex π U (unitModule X)).homology 1) :
    cupH π U x y = -cupH π U y x :=
  eq_neg_of_add_eq_zero_left (cupH_add_swap π U x y)

end Cup

section Naturality

open Cech DerivedSections

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)} (h : Y ⟶ X)
  {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (α : κ → ι) (hα : ∀ j, V j ≤ h.left ⁻¹ᵁ U (α j))

/-- The ordered Čech map of the structure map `𝒪_X ⟶ h_* 𝒪_Y` along `α`. -/
abbrev unitCochainMap :
    cochainComplex X.hom U (unitModule X.left) ⟶ cochainComplex Y.hom V (unitModule Y.left) :=
  cochainMap h (Langlands.Scheme.Modules.unitToPushforwardUnit h.left) U V α hα

lemma unitCochainMap_eq_pull (p : ℕ) (c : cochain X.hom U (unitModule X.left) p) :
    ((unitCochainMap h U V α hα).f p c : C (ab Y.left.presheaf) V p) =
      pull h.left U V α hα p (c : C (ab X.left.presheaf) U p) := by
  funext τ
  rw [cochainMap_unit_f_apply]
  rfl

omit [Fintype ι] [Fintype κ] in
lemma cup₁_eq_prod {T : TopCat.{u}} (P : TopCat.Presheaf CommRingCat.{u} T) {ι : Type u}
    {U : ι → TopologicalSpace.Opens T} (z w : C (ab P) U 1) :
    cup₁ P U z w = prod P U 2 ![z, w] := by
  rw [prod_succ, prod_one]
  rfl

lemma unitCochainMap_cup (z w : cochain X.hom U (unitModule X.left) 1) :
    (unitCochainMap h U V α hα).f 2 (cup X.hom U z w) =
      cup Y.hom V ((unitCochainMap h U V α hα).f 1 z) ((unitCochainMap h U V α hα).f 1 w) := by
  change ((unitCochainMap h U V α hα).f 2 (cup X.hom U z w) : C (ab Y.left.presheaf) V 2) =
    cup₁ Y.left.presheaf V ((unitCochainMap h U V α hα).f 1 z : C (ab Y.left.presheaf) V 1)
      ((unitCochainMap h U V α hα).f 1 w : C (ab Y.left.presheaf) V 1)
  rw [unitCochainMap_eq_pull, unitCochainMap_eq_pull, unitCochainMap_eq_pull, cup,
    cup₁_eq_prod, pull_prod, cup₁_eq_prod]
  congr 1
  funext k
  fin_cases k <;> rfl

lemma chainMap_mem_ker {π : X.left ⟶ Spec R} {π' : Y.left ⟶ Spec R} {M : X.left.Modules}
    {N : Y.left.Modules} (φ : cochainComplex π U M ⟶ cochainComplex π' V N) (n : ℕ)
    (z : LinearMap.ker (dCochain π U M (n + 1))) :
    φ.f (n + 1) (show (cochainComplex π U M).X (n + 1) from (z : cochain π U M (n + 1))) ∈
      LinearMap.ker (dCochain π' V N (n + 1)) := by
  rw [LinearMap.mem_ker]
  have e := congrArg (fun f => f (show (cochainComplex π U M).X (n + 1) from
    (z : cochain π U M (n + 1)))) (φ.comm (n + 1) (n + 2))
  simp only [ConcreteCategory.comp_apply, cochainComplex_d] at e
  refine e.trans ?_
  change φ.f (n + 2) (dCochain π U M (n + 1) (z : cochain π U M (n + 1))) = 0
  rw [z.2, map_zero]

/-- The ordered Čech pullback of structure-sheaf classes commutes with the cup product. -/
lemma homologyMap_cupH (x y : (cochainComplex X.hom U (unitModule X.left)).homology 1) :
    HomologicalComplex.homologyMap (unitCochainMap h U V α hα) 2 (cupH X.hom U x y) =
      cupH Y.hom V (HomologicalComplex.homologyMap (unitCochainMap h U V α hα) 1 x)
        (HomologicalComplex.homologyMap (unitCochainMap h U V α hα) 1 y) := by
  obtain ⟨z, rfl⟩ := classMap_surjective X.hom U (unitModule X.left) 0 x
  obtain ⟨w, rfl⟩ := classMap_surjective X.hom U (unitModule X.left) 0 y
  rw [cupH_classMap, homologyMap_classMap _ 1 _ (chainMap_mem_ker U V _ 1 _),
    homologyMap_classMap _ 0 _ (chainMap_mem_ker U V _ 0 z),
    homologyMap_classMap _ 0 _ (chainMap_mem_ker U V _ 0 w), cupH_classMap]
  congr 1
  apply Subtype.ext
  simp only [cupZ_apply]
  exact unitCochainMap_cup h U V α hα z w

end Naturality

section Canonical

open DerivedSections

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) [IsSeparated π]
  {ι : Type u} [Fintype ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hUa : ∀ i, IsAffineOpen (U i))

/-- The ordered Čech description of structure-sheaf cohomology as a linear equivalence. -/
abbrev cohomologyEquiv (n : ℕ) :
    (cochainComplex π U (unitModule X)).homology n ≃ₗ[R]
      (relativeCohomology π n).obj (unitModule X) :=
  (cohomologyIso π U (unitModule X) hU hUa n).toLinearEquiv

/-- The cup product `H¹(X, 𝒪_X) × H¹(X, 𝒪_X) ⟶ H²(X, 𝒪_X)` on actual cohomology, computed with
the ordered Čech complex of the covering family `U`. -/
def cupCanonical :
    (relativeCohomology π 1).obj (unitModule X) →ₗ[R]
      (relativeCohomology π 1).obj (unitModule X) →ₗ[R]
        (relativeCohomology π 2).obj (unitModule X) :=
  ((cupH π U).compl₁₂ (cohomologyEquiv π U hU hUa 1).symm.toLinearMap
    (cohomologyEquiv π U hU hUa 1).symm.toLinearMap).compr₂
      (cohomologyEquiv π U hU hUa 2).toLinearMap

lemma cupCanonical_apply (x y : (relativeCohomology π 1).obj (unitModule X)) :
    cupCanonical π U hU hUa x y =
      cohomologyEquiv π U hU hUa 2 (cupH π U ((cohomologyEquiv π U hU hUa 1).symm x)
        ((cohomologyEquiv π U hU hUa 1).symm y)) := rfl

/-- The actual cohomology class of an ordered Čech cocycle of the structure sheaf. -/
def canonicalClass (n : ℕ) :
    LinearMap.ker (dCochain π U (unitModule X) (n + 1)) →ₗ[R]
      (relativeCohomology π (n + 1)).obj (unitModule X) :=
  (cohomologyEquiv π U hU hUa (n + 1)).toLinearMap ∘ₗ classMap π U (unitModule X) n

lemma canonicalClass_surjective (n : ℕ) :
    Function.Surjective (canonicalClass π U hU hUa n) := by
  intro x
  obtain ⟨y, rfl⟩ := (cohomologyEquiv π U hU hUa (n + 1)).surjective x
  obtain ⟨z, rfl⟩ := classMap_surjective π U (unitModule X) n y
  exact ⟨z, rfl⟩

lemma canonicalClass_eq_zero_iff (n : ℕ) (z : LinearMap.ker (dCochain π U (unitModule X) (n + 1))) :
    canonicalClass π U hU hUa n z = 0 ↔ ∃ y, dCochain π U (unitModule X) n y = z := by
  rw [canonicalClass, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.map_eq_zero_iff, classMap_eq_zero_iff]

/-- On classes of cocycles, the cup product is the product of ordered Čech cocycles. -/
lemma cupCanonical_canonicalClass (z w : LinearMap.ker (dCochain π U (unitModule X) 1)) :
    cupCanonical π U hU hUa (canonicalClass π U hU hUa 0 z) (canonicalClass π U hU hUa 0 w) =
      canonicalClass π U hU hUa 1 (cupZ π U z w) := by
  simp only [canonicalClass, LinearMap.comp_apply, LinearEquiv.coe_coe, cupCanonical_apply,
    LinearEquiv.symm_apply_apply]
  rw [cupH_classMap]

/-- Graded anticommutativity of the cup product on `H¹(X, 𝒪_X)`. -/
lemma cupCanonical_swap (x y : (relativeCohomology π 1).obj (unitModule X)) :
    cupCanonical π U hU hUa x y = -cupCanonical π U hU hUa y x := by
  rw [cupCanonical_apply, cupCanonical_apply, cupH_swap, map_neg]

end Canonical

section CanonicalNaturality

open DerivedSections

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)} (h : Y ⟶ X) [IsSeparated X.hom]
  [IsSeparated Y.hom] {ι κ : Type u} [Fintype ι] [Fintype κ] (U : ι → X.left.Opens)
  (V : κ → Y.left.Opens) (α : κ → ι) (hα : ∀ j, V j ≤ h.left ⁻¹ᵁ U (α j))
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ j, V j = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
  (hVa : ∀ j, IsAffineOpen (V j))

lemma pull_cohomologyEquiv (n : ℕ) (w : (cochainComplex X.hom U (unitModule X.left)).homology n) :
    (relativeCohomologyPullback h (unitModule X.left) n ≫
        (relativeCohomology Y.hom n).map (Langlands.Scheme.Modules.pullbackUnitIso h.left).hom)
        (cohomologyEquiv X.hom U hU hUa n w) =
      cohomologyEquiv Y.hom V hV hVa n
        (HomologicalComplex.homologyMap (unitCochainMap h U V α hα) n w) := by
  have key := cohomologyIso_comp_relativeCohomologyPullback_unit h U V α hα hU hV hUa hVa n
  have := congrArg (fun f => f w) key
  simp only [ConcreteCategory.comp_apply] at this ⊢
  exact this

include α hα in
/-- **The canonical structure-sheaf pullback commutes with the cup product.** Here the
pullback is `relativeCohomologyPullback h 𝒪_X n` followed by the unit comparison
`h^* 𝒪_X ≅ 𝒪_Y`, as in `FieldH2ExteriorCoproductComparisonStatement`. -/
theorem pull_cupCanonical (x y : (relativeCohomology X.hom 1).obj (unitModule X.left)) :
    (relativeCohomologyPullback h (unitModule X.left) 2 ≫
        (relativeCohomology Y.hom 2).map (Langlands.Scheme.Modules.pullbackUnitIso h.left).hom)
        (cupCanonical X.hom U hU hUa x y) =
      cupCanonical Y.hom V hV hVa
        ((relativeCohomologyPullback h (unitModule X.left) 1 ≫
          (relativeCohomology Y.hom 1).map (Langlands.Scheme.Modules.pullbackUnitIso h.left).hom) x)
        ((relativeCohomologyPullback h (unitModule X.left) 1 ≫
          (relativeCohomology Y.hom 1).map (Langlands.Scheme.Modules.pullbackUnitIso h.left).hom) y) := by
  obtain ⟨x', rfl⟩ := (cohomologyEquiv X.hom U hU hUa 1).surjective x
  obtain ⟨y', rfl⟩ := (cohomologyEquiv X.hom U hU hUa 1).surjective y
  rw [cupCanonical_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    pull_cohomologyEquiv h U V α hα hU hV hUa hVa, homologyMap_cupH,
    pull_cohomologyEquiv h U V α hα hU hV hUa hVa,
    pull_cohomologyEquiv h U V α hα hU hV hUa hVa, cupCanonical_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

include α hα in
/-- On classes of cocycles, the canonical structure-sheaf pullback is the pullback of ordered
Čech cocycles `Langlands.Cohomology.Cech.pull` along `h` and `α`. -/
theorem pull_canonicalClass (n : ℕ)
    (z : LinearMap.ker (dCochain X.hom U (unitModule X.left) (n + 1))) :
    (relativeCohomologyPullback h (unitModule X.left) (n + 1) ≫
        (relativeCohomology Y.hom (n + 1)).map
          (Langlands.Scheme.Modules.pullbackUnitIso h.left).hom)
        (canonicalClass X.hom U hU hUa n z) =
      canonicalClass Y.hom V hV hVa n ⟨_, chainMap_mem_ker U V (unitCochainMap h U V α hα) n z⟩ := by
  rw [canonicalClass, LinearMap.comp_apply, LinearEquiv.coe_coe,
    pull_cohomologyEquiv h U V α hα hU hV hUa hVa, homologyMap_classMap]
  rfl

end CanonicalNaturality

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

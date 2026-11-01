import Langlands.AlgebraicGeometry.Modules.CechResolution.Comparison
import Langlands.AlgebraicGeometry.Modules.CechDegreeOne
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.OrderedAffineCoverCompact

/-!
# Čech cohomology computes actual `R`-module cohomology

Let `π : X ⟶ Spec R` be separated, `𝒰` a finite ordered affine cover of `X` and `M` a
quasi-coherent `𝒪_X`-module. This file proves:

* `cechCohomologyIso`: the homology of the alternating Čech cochain complex
  `cechCochainComplex π 𝒰 M` is, in every degree, isomorphic to the actual `R`-module cohomology
  `(relativeCohomology π n).obj M`;
* `cechH1Equiv`: in degree one, the quotient `HSucc 𝒰 0` of alternating Čech `1`-cocycles by
  Čech coboundaries is `R`-linearly equivalent to `H¹`;
* `allPairsH1Equiv`, `allPairsH1Map`: the same for Čech `1`-cochains indexed by all ordered pairs
  of cover indices, with cocycles and coboundaries exactly `CechDegreeOne.IsCocycle` and
  `CechDegreeOne.IsCoboundary`.

The all-pairs comparison with alternating cochains (`alternatingEquiv`) is proved for an
arbitrary presheaf of modules `F : OModulePresheaf ρ`. The structure-sheaf application uses the
published quasi-coherence instance from `CechDegreeOne`. The file also records that a scheme
quasi-compact over an affine base has a finite ordered affine cover.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution
  Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! ### Čech cohomology and actual cohomology -/

section Comparison

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  (𝒰 : X.OrderedAffineCover) (M : X.Modules)

/-- The degree-one homology of the Čech cochain complex is the quotient `HSucc 𝒰 0` of the
alternating Čech `1`-cocycles by the image of the Čech differential in degree zero. -/
def cechHomologyOneEquiv :
    (cechCochainComplex π 𝒰 M).homology 1 ≃ₗ[R]
      (OModulePresheaf.ofModules π M).HSucc 𝒰 0 := by
  let K := cechCochainComplex π 𝒰 M
  let F := OModulePresheaf.ofModules π M
  let S := ModuleCat.shortComplexOfCompEqZero (F.d 𝒰 0) (F.d 𝒰 1)
    (OModulePresheaf.d_comp_d F 𝒰 0)
  have h₀ : K.d 0 1 = ModuleCat.ofHom (F.d 𝒰 0) :=
    CochainComplex.of_d (V := ModuleCat.{u} R)
      (fun i => ModuleCat.of R ((OModulePresheaf.ofModules π M).cochain 𝒰 i))
      (fun i => ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 i)) 0
  have h₁ : K.d 1 2 = ModuleCat.ofHom (F.d 𝒰 1) :=
    CochainComplex.of_d (V := ModuleCat.{u} R)
      (fun i => ModuleCat.of R ((OModulePresheaf.ofModules π M).cochain 𝒰 i))
      (fun i => ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 i)) 1
  let e : K.sc' 0 1 2 ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom]; exact h₀.symm)
      (by simp only [Iso.refl_hom]; exact h₁.symm)
  exact (K.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫ ShortComplex.homologyMapIso e ≪≫
    S.moduleCatHomologyIso).toLinearEquiv ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (LinearMap.range_codRestrict _ _ _)

variable [IsSeparated π] [M.IsQuasicoherent]

attribute [local instance] quasiIso_cechAug

/-- The comparison map from the Čech resolution to the actual right derived functors of
`R`-module global sections is an isomorphism in every degree. -/
theorem isIso_resolutionComparison_cechAug (n : ℕ) :
    IsIso (resolutionComparison (relativeGlobalSections π) (cechAug 𝒰 M) n) := by
  exact (acyclicResolutionComparisonStatement _ _ (relativeGlobalSections π) M
    (cechComplex 𝒰 M) (cechAug 𝒰 M) inferInstance
    (fun i n => isZero_relativeCohomology_cechTerm π 𝒰 M i n) (injectiveResolution M) _
    (comp_lift_id _ _)).2 n

/-- The homology of the alternating Čech cochain complex of a quasi-coherent module on a scheme
separated over `Spec R` is its actual `R`-module cohomology. -/
def cechCohomologyIso (n : ℕ) :
    (cechCochainComplex π 𝒰 M).homology n ≅ (relativeCohomology π n).obj M :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (sectionsComplexIso π 𝒰 M).symm ≪≫
    @asIso _ _ _ _ _ (isIso_resolutionComparison_cechAug π 𝒰 M n)

/-- Degree-one alternating Čech cohomology of a quasi-coherent module on a scheme separated over
`Spec R` is its actual first `R`-module cohomology. -/
def cechH1Equiv :
    (OModulePresheaf.ofModules π M).HSucc 𝒰 0 ≃ₗ[R] (relativeCohomology π 1).obj M :=
  (cechHomologyOneEquiv π 𝒰 M).symm ≪≫ₗ (cechCohomologyIso π 𝒰 M 1).toLinearEquiv

end Comparison

/-! ### All-pairs and alternating Čech `1`-cochains -/

/-- A family `r a b` in an additive group, indexed by pairs from a linear order, that vanishes on
the diagonal, is antisymmetric and satisfies `r a b + r b c = r a c` for `a < b < c` satisfies
this identity for all `a`, `b`, `c`. -/
theorem add_eq_of_strict {ι G : Type*} [LinearOrder ι] [AddCommGroup G] (r : ι → ι → G)
    (h0 : ∀ a, r a a = 0) (hs : ∀ a b, r b a = -r a b)
    (h : ∀ a b c, a < b → b < c → r a b + r b c = r a c) (a b c : ι) :
    r a b + r b c = r a c := by
  rcases eq_or_ne a b with rfl | hab
  · rw [h0, zero_add]
  rcases eq_or_ne b c with rfl | hbc
  · rw [h0, add_zero]
  rcases eq_or_ne a c with rfl | hac
  · rw [hs a b, add_neg_cancel, h0]
  rcases lt_or_gt_of_ne hab with hab | hab <;> rcases lt_or_gt_of_ne hbc with hbc | hbc <;>
    rcases lt_or_gt_of_ne hac with hac | hac
  · exact h a b c hab hbc
  · exact (lt_asymm hac (hab.trans hbc)).elim
  · rw [hs c b, ← h a c b hac hbc]; abel
  · rw [hs c b, hs c a, ← h c a b hac hab]; abel
  · rw [hs b a, ← h b a c hab hac]; abel
  · rw [hs b a, hs c a, ← h b c a hbc hac]; abel
  · exact (lt_asymm hac (hbc.trans hab)).elim
  · rw [hs b a, hs c b, hs c a, ← h c b a hbc hab]; abel

section AllPairs

variable {S : Type u} [CommRing S] {V : Scheme.{u}} {ρ : V ⟶ Spec (.of S)}
  (F : OModulePresheaf ρ) (𝒰 : V.OrderedAffineCover)

/-- The degree-zero index `(a)`. -/
def singleIdx (a : 𝒰.ι) : 𝒰.Idx 0 :=
  ⟨fun _ => a, Fin.strictMono_iff_lt_succ.2 fun i => i.elim0⟩

/-- The degree-one index `(a, b)` for `a < b`. -/
def pairIdx {a b : 𝒰.ι} (h : a < b) : 𝒰.Idx 1 :=
  ⟨![a, b], Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; exact h⟩

/-- The degree-two index `(a, b, c)` for `a < b < c`. -/
def tripleIdx {a b c : 𝒰.ι} (hab : a < b) (hbc : b < c) : 𝒰.Idx 2 :=
  ⟨![a, b, c], Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; exacts [hab, hbc]⟩

theorem le_inter_singleIdx (a : 𝒰.ι) : 𝒰.U a ≤ 𝒰.inter (singleIdx 𝒰 a) :=
  le_iInf fun _ => le_rfl

theorem le_inter_pairIdx {a b : 𝒰.ι} (h : a < b) : 𝒰.U a ⊓ 𝒰.U b ≤ 𝒰.inter (pairIdx 𝒰 h) :=
  le_iInf fun j => by fin_cases j; exacts [inf_le_left, inf_le_right]

theorem inter_le_pair (s : 𝒰.Idx 1) : 𝒰.inter s ≤ 𝒰.U (s.1 0) ⊓ 𝒰.U (s.1 1) :=
  le_inf (𝒰.inter_le s 0) (𝒰.inter_le s 1)

/-- Restrictions of a cochain at equal indices agree. -/
theorem res_cochain_congr {i : ℕ} (c : F.cochain 𝒰 i) {s s' : 𝒰.Idx i} (h : s = s')
    {O : V.Opens} (hO : O ≤ 𝒰.inter s) (hO' : O ≤ 𝒰.inter s') :
    F.res hO (c s) = F.res hO' (c s') := by
  subst h
  rfl

/-- Čech `1`-cochains indexed by all ordered pairs of cover indices: a section over
`U a ⊓ U b` for every `a` and `b`. -/
abbrev AllPairsCochain : Type u := ∀ a b : 𝒰.ι, F.obj (𝒰.U a ⊓ 𝒰.U b)

/-- All-pairs Čech `1`-cocycles: `z a b + z b c = z a c` on every open contained in
`U a ⊓ U b ⊓ U c`. -/
def allPairsCocycles : Submodule S (AllPairsCochain F 𝒰) where
  carrier := {z | ∀ a b c {O : V.Opens} (h₁ : O ≤ 𝒰.U a ⊓ 𝒰.U b) (h₂ : O ≤ 𝒰.U b ⊓ 𝒰.U c)
    (h₃ : O ≤ 𝒰.U a ⊓ 𝒰.U c), F.res h₁ (z a b) + F.res h₂ (z b c) = F.res h₃ (z a c)}
  zero_mem' := by
    intro a b c O h₁ h₂ h₃
    simp
  add_mem' := by
    intro x y hx hy a b c O h₁ h₂ h₃
    simp only [Pi.add_apply, map_add]
    rw [← hx a b c h₁ h₂ h₃, ← hy a b c h₁ h₂ h₃]
    abel
  smul_mem' := by
    intro r x hx a b c O h₁ h₂ h₃
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_add, hx a b c h₁ h₂ h₃]

/-- The all-pairs Čech differential in degree zero, `g ↦ (g b - g a)` on `U a ⊓ U b`. -/
def allPairsD0 : (∀ a, F.obj (𝒰.U a)) →ₗ[S] AllPairsCochain F 𝒰 where
  toFun g a b := F.res inf_le_right (g b) - F.res inf_le_left (g a)
  map_add' g g' := by
    funext a b
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' r g := by
    funext a b
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub]

theorem allPairsD0_apply (g : ∀ a, F.obj (𝒰.U a)) (a b : 𝒰.ι) :
    allPairsD0 F 𝒰 g a b = F.res inf_le_right (g b) - F.res inf_le_left (g a) :=
  rfl

/-- All-pairs Čech `1`-coboundaries. -/
def allPairsCoboundaries : Submodule S (AllPairsCochain F 𝒰) :=
  LinearMap.range (allPairsD0 F 𝒰)

theorem allPairsD0_mem_allPairsCocycles (g : ∀ a, F.obj (𝒰.U a)) :
    allPairsD0 F 𝒰 g ∈ allPairsCocycles F 𝒰 := by
  intro a b c O h₁ h₂ h₃
  simp only [allPairsD0_apply, map_sub, F.res_res]
  abel

theorem allPairsCoboundaries_le : allPairsCoboundaries F 𝒰 ≤ allPairsCocycles F 𝒰 := by
  rintro _ ⟨g, rfl⟩
  exact allPairsD0_mem_allPairsCocycles F 𝒰 g

/-- All-pairs Čech cohomology in degree one: cocycles modulo coboundaries. -/
abbrev AllPairsH1 : Type u :=
  allPairsCocycles F 𝒰 ⧸ (allPairsCoboundaries F 𝒰).comap (allPairsCocycles F 𝒰).subtype

variable {F 𝒰} in
theorem allPairs_self {z : AllPairsCochain F 𝒰} (hz : z ∈ allPairsCocycles F 𝒰) (a : 𝒰.ι) :
    z a a = 0 := by
  have h := hz a a a (le_refl (𝒰.U a ⊓ 𝒰.U a)) (le_refl _) (le_refl _)
  rw [F.res_refl_apply] at h
  exact (add_right_inj (z a a)).1 (h.trans (add_zero _).symm)

variable {F 𝒰} in
theorem allPairs_swap {z : AllPairsCochain F 𝒰} (hz : z ∈ allPairsCocycles F 𝒰) (a b : 𝒰.ι) :
    z a b = -F.res (inf_comm (𝒰.U a) (𝒰.U b)).le (z b a) := by
  have h := hz a b a (le_refl (𝒰.U a ⊓ 𝒰.U b)) (inf_comm (𝒰.U a) (𝒰.U b)).le
    (le_inf inf_le_left inf_le_left)
  rw [F.res_refl_apply, allPairs_self hz a, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Restriction of an all-pairs cochain to the alternating cochain on increasing pairs. -/
def toAlternating : AllPairsCochain F 𝒰 →ₗ[S] F.cochain 𝒰 1 where
  toFun z s := F.res (inter_le_pair 𝒰 s) (z (s.1 0) (s.1 1))
  map_add' z z' := by
    funext s
    simp only [Pi.add_apply, map_add]
  map_smul' r z := by
    funext s
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

theorem toAlternating_apply (z : AllPairsCochain F 𝒰) (s : 𝒰.Idx 1) :
    toAlternating F 𝒰 z s = F.res (inter_le_pair 𝒰 s) (z (s.1 0) (s.1 1)) :=
  rfl

/-- The all-pairs cochain of an alternating cochain: `c (a, b)` for `a < b`, `-c (b, a)` for
`b < a` and `0` on the diagonal. -/
def ofAlternating : F.cochain 𝒰 1 →ₗ[S] AllPairsCochain F 𝒰 where
  toFun c a b :=
    if h : a < b then F.res (le_inter_pairIdx 𝒰 h) (c (pairIdx 𝒰 h))
    else if h' : b < a then
      -F.res ((inf_comm (𝒰.U a) (𝒰.U b)).le.trans (le_inter_pairIdx 𝒰 h')) (c (pairIdx 𝒰 h'))
    else 0
  map_add' c c' := by
    funext a b
    simp only [Pi.add_apply]
    split_ifs <;> simp only [map_add, neg_add, add_zero]
  map_smul' r c := by
    funext a b
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp only [map_smul, smul_neg, smul_zero]

theorem ofAlternating_apply_of_lt (c : F.cochain 𝒰 1) {a b : 𝒰.ι} (h : a < b) :
    ofAlternating F 𝒰 c a b = F.res (le_inter_pairIdx 𝒰 h) (c (pairIdx 𝒰 h)) := by
  simp only [ofAlternating, LinearMap.coe_mk, AddHom.coe_mk, h, ↓reduceDIte]

theorem ofAlternating_apply_of_gt (c : F.cochain 𝒰 1) {a b : 𝒰.ι} (h : b < a) :
    ofAlternating F 𝒰 c a b =
      -F.res ((inf_comm (𝒰.U a) (𝒰.U b)).le.trans (le_inter_pairIdx 𝒰 h)) (c (pairIdx 𝒰 h)) := by
  simp only [ofAlternating, LinearMap.coe_mk, AddHom.coe_mk, lt_asymm h, h, ↓reduceDIte]

theorem ofAlternating_self (c : F.cochain 𝒰 1) (a : 𝒰.ι) : ofAlternating F 𝒰 c a a = 0 := by
  simp only [ofAlternating, LinearMap.coe_mk, AddHom.coe_mk, lt_irrefl, ↓reduceDIte]

theorem toAlternating_ofAlternating (c : F.cochain 𝒰 1) :
    toAlternating F 𝒰 (ofAlternating F 𝒰 c) = c := by
  funext s
  have hs : s.1 0 < s.1 1 := s.2 (show (0 : Fin 2) < 1 by decide)
  have e : pairIdx 𝒰 hs = s := Subtype.ext (funext fun j => by fin_cases j <;> rfl)
  rw [toAlternating_apply, ofAlternating_apply_of_lt F 𝒰 c hs, F.res_res,
    res_cochain_congr F 𝒰 c e _ (le_refl _), F.res_refl_apply]

theorem ofAlternating_toAlternating {z : AllPairsCochain F 𝒰}
    (hz : z ∈ allPairsCocycles F 𝒰) : ofAlternating F 𝒰 (toAlternating F 𝒰 z) = z := by
  funext a b
  rcases lt_trichotomy a b with h | rfl | h
  · rw [ofAlternating_apply_of_lt F 𝒰 _ h, toAlternating_apply, F.res_res]
    exact F.res_refl_apply _ _
  · rw [ofAlternating_self, allPairs_self hz]
  · rw [ofAlternating_apply_of_gt F 𝒰 _ h, toAlternating_apply, F.res_res, allPairs_swap hz a b]
    rfl

theorem d_toAlternating {z : AllPairsCochain F 𝒰} (hz : z ∈ allPairsCocycles F 𝒰) :
    F.d 𝒰 1 (toAlternating F 𝒰 z) = 0 := by
  funext t
  have h₀₁ : 𝒰.inter t ≤ 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) := le_inf (𝒰.inter_le t 0) (𝒰.inter_le t 1)
  have h₁₂ : 𝒰.inter t ≤ 𝒰.U (t.1 1) ⊓ 𝒰.U (t.1 2) := le_inf (𝒰.inter_le t 1) (𝒰.inter_le t 2)
  have h₀₂ : 𝒰.inter t ≤ 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 2) := le_inf (𝒰.inter_le t 0) (𝒰.inter_le t 2)
  have e₀ : F.res (𝒰.inter_le_inter_face t (0 : Fin 3)) (toAlternating F 𝒰 z (𝒰.face t (0 : Fin 3))) =
      F.res h₁₂ (z (t.1 1) (t.1 2)) := by
    rw [toAlternating_apply, F.res_res]
    rfl
  have e₁ : F.res (𝒰.inter_le_inter_face t (1 : Fin 3)) (toAlternating F 𝒰 z (𝒰.face t (1 : Fin 3))) =
      F.res h₀₂ (z (t.1 0) (t.1 2)) := by
    rw [toAlternating_apply, F.res_res]
    rfl
  have e₂ : F.res (𝒰.inter_le_inter_face t (2 : Fin 3)) (toAlternating F 𝒰 z (𝒰.face t (2 : Fin 3))) =
      F.res h₀₁ (z (t.1 0) (t.1 1)) := by
    rw [toAlternating_apply, F.res_res]
    rfl
  rw [OModulePresheaf.d_apply, Fin.sum_univ_three, e₀, e₁, e₂, Pi.zero_apply,
    ← hz (t.1 0) (t.1 1) (t.1 2) h₀₁ h₁₂ h₀₂]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_smul,
    neg_smul]
  abel

/-- The Čech differential of an alternating `1`-cochain at `(a, b, c)`, restricted to `O`. -/
theorem res_d_tripleIdx (w : F.cochain 𝒰 1) {a b c : 𝒰.ι} (hab : a < b) (hbc : b < c)
    {O : V.Opens} (hO : O ≤ 𝒰.inter (tripleIdx 𝒰 hab hbc)) (h₁ : O ≤ 𝒰.inter (pairIdx 𝒰 hab))
    (h₂ : O ≤ 𝒰.inter (pairIdx 𝒰 hbc)) (h₃ : O ≤ 𝒰.inter (pairIdx 𝒰 (hab.trans hbc))) :
    F.res hO (F.d 𝒰 1 w (tripleIdx 𝒰 hab hbc)) =
      F.res h₂ (w (pairIdx 𝒰 hbc)) - F.res h₃ (w (pairIdx 𝒰 (hab.trans hbc))) +
        F.res h₁ (w (pairIdx 𝒰 hab)) := by
  have e₀ : 𝒰.face (tripleIdx 𝒰 hab hbc) (0 : Fin 3) = pairIdx 𝒰 hbc :=
    Subtype.ext (funext fun j => by fin_cases j <;> rfl)
  have e₁ : 𝒰.face (tripleIdx 𝒰 hab hbc) (1 : Fin 3) = pairIdx 𝒰 (hab.trans hbc) :=
    Subtype.ext (funext fun j => by fin_cases j <;> rfl)
  have e₂ : 𝒰.face (tripleIdx 𝒰 hab hbc) (2 : Fin 3) = pairIdx 𝒰 hab :=
    Subtype.ext (funext fun j => by fin_cases j <;> rfl)
  rw [OModulePresheaf.d_apply, Fin.sum_univ_three]
  simp only [map_add, map_zsmul, F.res_res]
  rw [res_cochain_congr F 𝒰 w e₀ _ h₂, res_cochain_congr F 𝒰 w e₁ _ h₃,
    res_cochain_congr F 𝒰 w e₂ _ h₁]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_smul,
    neg_smul]
  abel

theorem ofAlternating_mem_allPairsCocycles {w : F.cochain 𝒰 1}
    (hw : w ∈ LinearMap.ker (F.d 𝒰 1)) : ofAlternating F 𝒰 w ∈ allPairsCocycles F 𝒰 := by
  rw [LinearMap.mem_ker] at hw
  intro a b c O h₁ h₂ h₃
  have hself : ∀ x : {x // O ≤ 𝒰.U x},
      F.res (le_inf x.2 x.2) (ofAlternating F 𝒰 w x.1 x.1) = 0 := by
    intro x
    rw [ofAlternating_self, map_zero]
  have hswap : ∀ x y : {x // O ≤ 𝒰.U x},
      F.res (le_inf y.2 x.2) (ofAlternating F 𝒰 w y.1 x.1) =
        -F.res (le_inf x.2 y.2) (ofAlternating F 𝒰 w x.1 y.1) := by
    intro x y
    rcases lt_trichotomy x.1 y.1 with h | h | h
    · rw [ofAlternating_apply_of_gt F 𝒰 w h, ofAlternating_apply_of_lt F 𝒰 w h, map_neg,
        F.res_res, F.res_res]
    · obtain rfl : x = y := Subtype.ext h
      rw [ofAlternating_self, map_zero, neg_zero]
    · rw [ofAlternating_apply_of_lt F 𝒰 w h, ofAlternating_apply_of_gt F 𝒰 w h, map_neg,
        F.res_res, F.res_res, neg_neg]
  have htriple : ∀ x y z : {x // O ≤ 𝒰.U x}, x < y → y < z →
      F.res (le_inf x.2 y.2) (ofAlternating F 𝒰 w x.1 y.1) +
          F.res (le_inf y.2 z.2) (ofAlternating F 𝒰 w y.1 z.1) =
        F.res (le_inf x.2 z.2) (ofAlternating F 𝒰 w x.1 z.1) := by
    intro x y z hxy hyz
    have hxy' : x.1 < y.1 := hxy
    have hyz' : y.1 < z.1 := hyz
    have hO : O ≤ 𝒰.inter (tripleIdx 𝒰 hxy' hyz') :=
      le_iInf fun j => by fin_cases j; exacts [x.2, y.2, z.2]
    have key := res_d_tripleIdx F 𝒰 w hxy' hyz' hO
      ((le_inf x.2 y.2).trans (le_inter_pairIdx 𝒰 hxy'))
      ((le_inf y.2 z.2).trans (le_inter_pairIdx 𝒰 hyz'))
      ((le_inf x.2 z.2).trans (le_inter_pairIdx 𝒰 (hxy'.trans hyz')))
    rw [hw, Pi.zero_apply, map_zero] at key
    rw [ofAlternating_apply_of_lt F 𝒰 w hxy', ofAlternating_apply_of_lt F 𝒰 w hyz',
      ofAlternating_apply_of_lt F 𝒰 w (hxy'.trans hyz'), F.res_res, F.res_res, F.res_res,
      ← sub_eq_zero]
    convert key.symm using 1
    abel
  exact add_eq_of_strict
    (fun x y : {x // O ≤ 𝒰.U x} => F.res (le_inf x.2 y.2) (ofAlternating F 𝒰 w x.1 y.1))
    hself hswap htriple ⟨a, h₁.trans inf_le_left⟩ ⟨b, h₁.trans inf_le_right⟩
    ⟨c, h₂.trans inf_le_right⟩

/-- All-pairs Čech `1`-cocycles are equivalent to alternating Čech `1`-cocycles. -/
def alternatingEquiv : allPairsCocycles F 𝒰 ≃ₗ[S] LinearMap.ker (F.d 𝒰 1) where
  toFun z := ⟨toAlternating F 𝒰 z, LinearMap.mem_ker.2 (d_toAlternating F 𝒰 z.2)⟩
  map_add' z z' := Subtype.ext (map_add (toAlternating F 𝒰) z.1 z'.1)
  map_smul' r z := Subtype.ext (map_smul (toAlternating F 𝒰) r z.1)
  invFun w := ⟨ofAlternating F 𝒰 w, ofAlternating_mem_allPairsCocycles F 𝒰 w.2⟩
  left_inv z := Subtype.ext (ofAlternating_toAlternating F 𝒰 z.2)
  right_inv w := Subtype.ext (toAlternating_ofAlternating F 𝒰 w)

theorem alternatingEquiv_apply_coe (z : allPairsCocycles F 𝒰) :
    (alternatingEquiv F 𝒰 z : F.cochain 𝒰 1) = toAlternating F 𝒰 z :=
  rfl

theorem alternatingEquiv_symm_apply_coe (w : LinearMap.ker (F.d 𝒰 1)) :
    ((alternatingEquiv F 𝒰).symm w : AllPairsCochain F 𝒰) = ofAlternating F 𝒰 w :=
  rfl

/-- Families of degree-zero sections give alternating `0`-cochains. -/
def toCochainZero : (∀ a, F.obj (𝒰.U a)) →ₗ[S] F.cochain 𝒰 0 where
  toFun g s := F.res (𝒰.inter_le s 0) (g (s.1 0))
  map_add' g g' := by
    funext s
    simp only [Pi.add_apply, map_add]
  map_smul' r g := by
    funext s
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

theorem toCochainZero_apply (g : ∀ a, F.obj (𝒰.U a)) (s : 𝒰.Idx 0) :
    toCochainZero F 𝒰 g s = F.res (𝒰.inter_le s 0) (g (s.1 0)) :=
  rfl

theorem toCochainZero_surjective : Function.Surjective (toCochainZero F 𝒰) := by
  intro c
  refine ⟨fun a => F.res (le_inter_singleIdx 𝒰 a) (c (singleIdx 𝒰 a)), funext fun s => ?_⟩
  have e : singleIdx 𝒰 (s.1 0) = s := Subtype.ext (funext fun j => by fin_cases j; rfl)
  rw [toCochainZero_apply, F.res_res, res_cochain_congr F 𝒰 c e _ (le_refl _),
    F.res_refl_apply]

theorem d_toCochainZero (g : ∀ a, F.obj (𝒰.U a)) :
    F.d 𝒰 0 (toCochainZero F 𝒰 g) = toAlternating F 𝒰 (allPairsD0 F 𝒰 g) := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two, toAlternating_apply, allPairsD0_apply, map_sub,
    toCochainZero_apply, toCochainZero_apply, F.res_res, F.res_res, F.res_res, F.res_res]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [sub_eq_add_neg]
  rfl

theorem mem_allPairsCoboundaries_iff_toAlternating {z : AllPairsCochain F 𝒰}
    (hz : z ∈ allPairsCocycles F 𝒰) :
    z ∈ allPairsCoboundaries F 𝒰 ↔ toAlternating F 𝒰 z ∈ LinearMap.range (F.d 𝒰 0) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨toCochainZero F 𝒰 g, d_toCochainZero F 𝒰 g⟩
  · rintro ⟨c, hc⟩
    obtain ⟨g, rfl⟩ := toCochainZero_surjective F 𝒰 c
    refine ⟨g, ?_⟩
    rw [d_toCochainZero] at hc
    rw [← ofAlternating_toAlternating F 𝒰 (allPairsD0_mem_allPairsCocycles F 𝒰 g), hc,
      ofAlternating_toAlternating F 𝒰 hz]

/-- All-pairs Čech `H¹` is alternating Čech `H¹`. -/
def allPairsH1EquivHSucc : AllPairsH1 F 𝒰 ≃ₗ[S] F.HSucc 𝒰 0 :=
  Submodule.Quotient.equiv _ _ (alternatingEquiv F 𝒰) (by
    ext w
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.subtype_apply,
      mem_allPairsCoboundaries_iff_toAlternating F 𝒰 ((alternatingEquiv F 𝒰).symm w).2,
      alternatingEquiv_symm_apply_coe, toAlternating_ofAlternating])

end AllPairs

/-! ### All-pairs Čech cocycles of a module and actual `H¹` -/

section OfModules

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  (𝒰 : X.OrderedAffineCover) (M : X.Modules)

theorem mem_allPairsCocycles_ofModules_iff
    (z : AllPairsCochain (OModulePresheaf.ofModules π M) 𝒰) :
    z ∈ allPairsCocycles (OModulePresheaf.ofModules π M) 𝒰 ↔
      CechDegreeOne.IsCocycle (G := M) 𝒰.U z :=
  Iff.rfl

theorem mem_allPairsCoboundaries_ofModules_iff
    (z : AllPairsCochain (OModulePresheaf.ofModules π M) 𝒰) :
    z ∈ allPairsCoboundaries (OModulePresheaf.ofModules π M) 𝒰 ↔
      CechDegreeOne.IsCoboundary (G := M) 𝒰.U z :=
  ⟨fun ⟨g, hg⟩ => ⟨g, fun a b => (congrFun (congrFun hg a) b).symm⟩,
    fun ⟨g, hg⟩ => ⟨g, funext fun a => funext fun b => (hg a b).symm⟩⟩

variable [IsSeparated π] [M.IsQuasicoherent]

/-- All-pairs Čech `H¹` of a quasi-coherent module on a scheme separated over `Spec R` is its
actual first `R`-module cohomology. -/
def allPairsH1Equiv :
    AllPairsH1 (OModulePresheaf.ofModules π M) 𝒰 ≃ₗ[R] (relativeCohomology π 1).obj M :=
  allPairsH1EquivHSucc _ 𝒰 ≪≫ₗ cechH1Equiv π 𝒰 M

/-- The class in actual `H¹` of an all-pairs Čech `1`-cocycle. -/
def allPairsH1Map :
    allPairsCocycles (OModulePresheaf.ofModules π M) 𝒰 →ₗ[R] (relativeCohomology π 1).obj M :=
  (allPairsH1Equiv π 𝒰 M).toLinearMap ∘ₗ Submodule.mkQ _

theorem allPairsH1Map_surjective : Function.Surjective (allPairsH1Map π 𝒰 M) :=
  (allPairsH1Equiv π 𝒰 M).surjective.comp (Submodule.mkQ_surjective _)

theorem allPairsH1Map_eq_zero_iff (z : allPairsCocycles (OModulePresheaf.ofModules π M) 𝒰) :
    allPairsH1Map π 𝒰 M z = 0 ↔ CechDegreeOne.IsCoboundary (G := M) 𝒰.U z.1 := by
  rw [allPairsH1Map, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply, mem_allPairsCoboundaries_ofModules_iff]

end OfModules

/-! ### The structure sheaf and finite affine covers -/

/-- A finite ordered affine open cover of a scheme that is quasi-compact over an affine
base. -/
def orderedAffineCoverOfQuasiCompact {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
    [QuasiCompact π] : X.OrderedAffineCover :=
  haveI := QuasiCompact.compactSpace_of_compactSpace π
  Scheme.OrderedAffineCover.ofCompactSpace X

end Langlands.AlgebraicGeometry.Modules.CechResolution

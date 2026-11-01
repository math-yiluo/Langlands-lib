import Langlands.AlgebraicGeometry.Modules.BiCech.Complex
import Langlands.AlgebraicGeometry.Modules.CechResolution.Comparison

/-!
# Global sections of the bi-Čech terms

For a `BiCover P`, an `𝒪_P`-module `F` and `π : P ⟶ Spec R`, a global section `z` of the
degree-`n` bi-Čech term has components `compF z p q h s t ∈ F(biOpen s t)`, the restrictions of
its `(s, t)`-components from `biOpen s t ∩ ⊤` to the equal open `biOpen s t`. A section is
determined by its components, and the components are `R`-linear for the module structures
given by `π` (`OModulePresheaf.ofModules`).

Conversely, for a fixed bidegree `(p, q)` with `p + q = n`, a family `c s t ∈ F(biOpen s t)`
gives the section `insT h c`, the sum of the images of the `c s t` under the biproduct
inclusions. Its components in bidegree `(p, q)` are `c`, and its components in every other
bidegree vanish.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open CechResolution

variable {P : Scheme.{u}} {𝒲 : BiCover P} {F : P.Modules}

lemma le_image_preimage_top (W : P.Opens) : W ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ ⊤) := by
  rw [image_preimage_eq, inf_top_eq]

lemma image_preimage_top_le (W : P.Opens) : W.ι ''ᵁ (W.ι ⁻¹ᵁ ⊤) ≤ W := by
  rw [image_preimage_eq, inf_top_eq]

lemma biOpen_le_bo {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    biOpen 𝒲 s t ≤ bo 𝒲 ⊤ s t :=
  le_image_preimage_top _

/-- Global sections of `sheafOn F W` as sections of `F` over `W`. -/
def ofSheafOn {W : P.Opens} (x : Γ(sheafOn F W, ⊤)) : Γ(F, W) :=
  F.presheaf.map (homOfLE (le_image_preimage_top W)).op x

/-- Sections of `F` over `W` as global sections of `sheafOn F W`. -/
def toSheafOn {W : P.Opens} (x : Γ(F, W)) : Γ(sheafOn F W, ⊤) :=
  F.presheaf.map (homOfLE (image_preimage_top_le W)).op x

lemma ofSheafOn_toSheafOn {W : P.Opens} (x : Γ(F, W)) : ofSheafOn (toSheafOn x) = x :=
  map_map_of_le_of_le (M := F) (le_image_preimage_top W) (image_preimage_top_le W) x

lemma toSheafOn_ofSheafOn {W : P.Opens} (x : Γ(sheafOn F W, ⊤)) : toSheafOn (ofSheafOn x) = x :=
  map_map_of_le_of_le (M := F) (image_preimage_top_le W) (le_image_preimage_top W) x

lemma ofSheafOn_injective {W : P.Opens} : Function.Injective (ofSheafOn (F := F) (W := W)) :=
  fun x y e => by rw [← toSheafOn_ofSheafOn x, e, toSheafOn_ofSheafOn]

lemma ofSheafOn_add {W : P.Opens} (x y : Γ(sheafOn F W, ⊤)) :
    ofSheafOn (x + y) = ofSheafOn x + ofSheafOn y := by
  unfold ofSheafOn
  erw [map_add]

lemma ofSheafOn_zero {W : P.Opens} : ofSheafOn (0 : Γ(sheafOn F W, ⊤)) = 0 := by
  unfold ofSheafOn
  erw [map_zero]

lemma ofSheafOn_sum {W : P.Opens} {ι : Type*} (S : Finset ι) (x : ι → Γ(sheafOn F W, ⊤)) :
    ofSheafOn (∑ i ∈ S, x i) = ∑ i ∈ S, ofSheafOn (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, ofSheafOn_zero]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ofSheafOn_add, ih]

lemma toSheafOn_add {W : P.Opens} (x y : Γ(F, W)) :
    toSheafOn (x + y) = toSheafOn x + toSheafOn y := by
  unfold toSheafOn
  erw [map_add]
  rfl

/-- The `(s, t)`-component of a global section of the degree-`n` term, as a section over
`biOpen s t`. -/
def compF {n : ℕ} (z : Γ(term 𝒲 F n, ⊤)) (p q : ℕ) (h : p + q = n) (s : 𝒲.𝒰.Idx p)
    (t : 𝒲.𝒱.Idx q) : Γ(F, biOpen 𝒲 s t) :=
  ofSheafOn ((πT 𝒲 F h s t).app ⊤ z)

lemma compF_eq_iff {n : ℕ} (z z' : Γ(term 𝒲 F n, ⊤)) :
    z = z' ↔ ∀ p q (h : p + q = n) s t, compF z p q h s t = compF z' p q h s t := by
  refine ⟨fun e => by subst e; exact fun _ _ _ _ _ => rfl, fun H => toT_injective ⊤ ?_⟩
  funext p q h s t
  change (πT 𝒲 F h s t).app ⊤ z = (πT 𝒲 F h s t).app ⊤ z'
  exact ofSheafOn_injective (W := biOpen 𝒲 s t) (H p q h s t)

lemma compF_add {n : ℕ} (z z' : Γ(term 𝒲 F n, ⊤)) (p q : ℕ) (h : p + q = n)
    (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    compF (z + z') p q h s t = compF z p q h s t + compF z' p q h s t := by
  rw [compF, map_add, ofSheafOn_add]
  rfl

lemma compF_zero {n : ℕ} (p q : ℕ) (h : p + q = n) (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    compF (0 : Γ(term 𝒲 F n, ⊤)) p q h s t = 0 := by
  rw [compF, map_zero, ofSheafOn_zero]

lemma compF_sum {n : ℕ} {ι : Type*} (S : Finset ι) (z : ι → Γ(term 𝒲 F n, ⊤)) (p q : ℕ)
    (h : p + q = n) (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    compF (∑ i ∈ S, z i) p q h s t = ∑ i ∈ S, compF (z i) p q h s t := by
  rw [compF, map_sum, ofSheafOn_sum]
  rfl

lemma compF_smul {n : ℕ} (r : Γ(P, ⊤)) (z : Γ(term 𝒲 F n, ⊤)) (p q : ℕ) (h : p + q = n)
    (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    compF (r • z) p q h s t =
      P.presheaf.map (homOfLE (biOpen_le_bo s t)).op
          (((biOpen 𝒲 s t).ι.app ⊤ ≫
            ((biOpen 𝒲 s t).ι.appIso ((biOpen 𝒲 s t).ι ⁻¹ᵁ ⊤)).inv) r) •
        compF z p q h s t := by
  have e : (πT 𝒲 F h s t).app ⊤ (r • z) = r • (πT 𝒲 F h s t).app ⊤ z :=
    Scheme.Modules.Hom.app_smul _ r z
  rw [compF, e, compF, ofSheafOn, ofSheafOn, smul_eq]
  exact Scheme.Modules.map_smul F _ _ _

lemma structureRingHom_comp_biOpen {R : CommRingCat.{u}} (π : P ⟶ Spec R) (W : P.Opens)
    (hW : W ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ ⊤)) :
    DerivedSections.structureRingHom π ≫
        (W.ι.app ⊤ ≫ (W.ι.appIso (W.ι ⁻¹ᵁ ⊤)).inv) ≫ P.presheaf.map (homOfLE hW).op =
      (Scheme.ΓSpecIso R).inv ≫ π.appLE ⊤ W le_top := by
  rw [Scheme.Hom.app_appIso_inv]
  simp only [DerivedSections.structureRingHom, Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact (P.presheaf.map_comp _ _).symm

section Insert

variable {n p q : ℕ} (h : p + q = n)

/-- The global section of the degree-`n` term with components `c` in bidegree `(p, q)` and
zero components in all other bidegrees. -/
def insT (c : ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), Γ(F, biOpen 𝒲 s t)) : Γ(term 𝒲 F n, ⊤) :=
  ∑ s, ∑ t, (biproduct.ι (summand 𝒲 F) (tidx 𝒲 h s t)).app ⊤ (toSheafOn (c s t))

lemma tidx_ne_of_ne {p' q' : ℕ} (h' : p' + q' = n) (hne : (p', q') ≠ (p, q)) (s : 𝒲.𝒰.Idx p)
    (t : 𝒲.𝒱.Idx q) (s' : 𝒲.𝒰.Idx p') (t' : 𝒲.𝒱.Idx q') :
    tidx 𝒲 h s t ≠ tidx 𝒲 h' s' t' := fun e =>
  hne (congrArg (fun x : TIdx 𝒲 n => x.1.1) e).symm

lemma tidx_ne_of_ne_idx (h' : p + q = n) {s s' : 𝒲.𝒰.Idx p} {t t' : 𝒲.𝒱.Idx q}
    (hne : (s, t) ≠ (s', t')) : tidx 𝒲 h s t ≠ tidx 𝒲 h' s' t' := by
  intro e
  have e2 := (Sigma.mk.inj_iff.1 e).2
  exact hne (eq_of_heq e2)

lemma πT_ι_ne {p' q' : ℕ} (h' : p' + q' = n) {s : 𝒲.𝒰.Idx p} {t : 𝒲.𝒱.Idx q}
    {s' : 𝒲.𝒰.Idx p'} {t' : 𝒲.𝒱.Idx q'} (hne : tidx 𝒲 h s t ≠ tidx 𝒲 h' s' t')
    (y : Γ(sheafOn F (biOpen 𝒲 s t), ⊤)) :
    (πT 𝒲 F h' s' t').app ⊤ ((biproduct.ι (summand 𝒲 F) (tidx 𝒲 h s t)).app ⊤ y) = 0 := by
  rw [← comp_app_apply, biproduct.ι_π_ne _ hne, zero_app_apply]

lemma πT_ι_self (h' : p + q = n) (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q)
    (y : Γ(sheafOn F (biOpen 𝒲 s t), ⊤)) :
    (πT 𝒲 F h' s t).app ⊤ ((biproduct.ι (summand 𝒲 F) (tidx 𝒲 h s t)).app ⊤ y) = y := by
  rw [← comp_app_apply, biproduct.ι_π_self]
  rfl

lemma compF_insT_ne {p' q' : ℕ} (h' : p' + q' = n) (hne : (p', q') ≠ (p, q))
    (c : ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), Γ(F, biOpen 𝒲 s t)) (s' : 𝒲.𝒰.Idx p')
    (t' : 𝒲.𝒱.Idx q') : compF (insT h c) p' q' h' s' t' = 0 := by
  rw [insT, compF_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [compF_sum]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [compF, πT_ι_ne h h' (tidx_ne_of_ne h h' hne s t s' t'), ofSheafOn_zero]

lemma compF_insT_self (h' : p + q = n)
    (c : ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), Γ(F, biOpen 𝒲 s t)) (s' : 𝒲.𝒰.Idx p)
    (t' : 𝒲.𝒱.Idx q) : compF (insT h c) p q h' s' t' = c s' t' := by
  rw [insT, compF_sum, Finset.sum_eq_single s']
  · rw [compF_sum, Finset.sum_eq_single t']
    · rw [compF, πT_ι_self, ofSheafOn_toSheafOn]
    · intro t _ ht
      rw [compF, πT_ι_ne h h' (tidx_ne_of_ne_idx h h' (fun e => ht (congrArg Prod.snd e))),
        ofSheafOn_zero]
    · intro ht
      exact absurd (Finset.mem_univ _) ht
  · intro s _ hs
    rw [compF_sum]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [compF, πT_ι_ne h h' (tidx_ne_of_ne_idx h h' (fun e => hs (congrArg Prod.fst e))),
      ofSheafOn_zero]
  · intro hs
    exact absurd (Finset.mem_univ _) hs

end Insert

section Differential

/-- Restriction from `biOpen s t ∩ ⊤` to `biOpen s t`. -/
def ofBo {p q : ℕ} {s : 𝒲.𝒰.Idx p} {t : 𝒲.𝒱.Idx q} (x : Γ(F, bo 𝒲 ⊤ s t)) :
    Γ(F, biOpen 𝒲 s t) :=
  F.presheaf.map (homOfLE (biOpen_le_bo s t)).op x

lemma compF_eq_ofBo {n : ℕ} (z : Γ(term 𝒲 F n, ⊤)) (p q : ℕ) (h : p + q = n)
    (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) : compF z p q h s t = ofBo (toT ⊤ z p q h s t) :=
  rfl

lemma ofBo_add {p q : ℕ} {s : 𝒲.𝒰.Idx p} {t : 𝒲.𝒱.Idx q} (x y : Γ(F, bo 𝒲 ⊤ s t)) :
    ofBo (x + y) = ofBo x + ofBo y :=
  map_add _ x y

lemma ofBo_zsmul {p q : ℕ} {s : 𝒲.𝒰.Idx p} {t : 𝒲.𝒱.Idx q} (k : ℤ) (x : Γ(F, bo 𝒲 ⊤ s t)) :
    ofBo (k • x) = k • ofBo x :=
  map_zsmul _ k x

lemma ofBo_sum {p q : ℕ} {s : 𝒲.𝒰.Idx p} {t : 𝒲.𝒱.Idx q} {ι : Type*} (S : Finset ι)
    (x : ι → Γ(F, bo 𝒲 ⊤ s t)) : ofBo (∑ i ∈ S, x i) = ∑ i ∈ S, ofBo (x i) :=
  map_sum _ x S

/-- The alternating Čech differential in the first index on families over the opens
`biOpen s t`. -/
def horF {p q : ℕ} (c : ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), Γ(F, biOpen 𝒲 s t))
    (s : 𝒲.𝒰.Idx (p + 1)) (t : 𝒲.𝒱.Idx q) : Γ(F, biOpen 𝒲 s t) :=
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    F.presheaf.map (homOfLE (biOpen_le_face₁ s t j)).op (c (𝒲.𝒰.face s j) t)

/-- The alternating Čech differential in the second index on families over the opens
`biOpen s t`. -/
def verF {p q : ℕ} (c : ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), Γ(F, biOpen 𝒲 s t))
    (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx (q + 1)) : Γ(F, biOpen 𝒲 s t) :=
  ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    F.presheaf.map (homOfLE (biOpen_le_face₂ s t j)).op (c s (𝒲.𝒱.face t j))

lemma ofBo_δ₁ {p q : ℕ} (c : B 𝒲 F p q ⊤) (s : 𝒲.𝒰.Idx (p + 1)) (t : 𝒲.𝒱.Idx q) :
    ofBo (δ₁ c s t) = horF (fun s t => ofBo (c s t)) s t := by
  rw [δ₁_apply, ofBo_sum, horF]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ofBo_zsmul, ofBo, ofBo, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma ofBo_δ₂ {p q : ℕ} (c : B 𝒲 F p q ⊤) (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx (q + 1)) :
    ofBo (δ₂ c s t) = verF (fun s t => ofBo (c s t)) s t := by
  rw [δ₂_apply, ofBo_sum, verF]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ofBo_zsmul, ofBo, ofBo, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

variable (𝒲 F) in
lemma compF_D_zero_succ {n : ℕ} (z : Γ(term 𝒲 F n, ⊤)) (q : ℕ) (h : 0 + (q + 1) = n + 1)
    (s : 𝒲.𝒰.Idx 0) (t : 𝒲.𝒱.Idx (q + 1)) :
    compF ((D 𝒲 F n).app ⊤ z) 0 (q + 1) h s t =
      verF (fun s t => compF z 0 q (by omega) s t) s t := by
  rw [compF_eq_ofBo, toT_D, DT_zero_succ, ofBo_δ₂]
  rfl

variable (𝒲 F) in
lemma compF_D_succ_zero {n : ℕ} (z : Γ(term 𝒲 F n, ⊤)) (p : ℕ) (h : p + 1 + 0 = n + 1)
    (s : 𝒲.𝒰.Idx (p + 1)) (t : 𝒲.𝒱.Idx 0) :
    compF ((D 𝒲 F n).app ⊤ z) (p + 1) 0 h s t =
      horF (fun s t => compF z p 0 (by omega) s t) s t := by
  rw [compF_eq_ofBo, toT_D, DT_succ_zero, ofBo_δ₁]
  rfl

variable (𝒲 F) in
lemma compF_D_succ_succ {n : ℕ} (z : Γ(term 𝒲 F n, ⊤)) (p q : ℕ)
    (h : p + 1 + (q + 1) = n + 1) (s : 𝒲.𝒰.Idx (p + 1)) (t : 𝒲.𝒱.Idx (q + 1)) :
    compF ((D 𝒲 F n).app ⊤ z) (p + 1) (q + 1) h s t =
      horF (fun s t => compF z p (q + 1) (by omega) s t) s t +
        ((-1 : ℤ) ^ (p + 1)) • verF (fun s t => compF z (p + 1) q (by omega) s t) s t := by
  rw [compF_eq_ofBo, toT_D, DT_succ_succ, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
    Pi.smul_apply, ofBo_add, ofBo_zsmul, ofBo_δ₁, ofBo_δ₂]
  rfl

lemma horF_zero {p q : ℕ} (s : 𝒲.𝒰.Idx (p + 1)) (t : 𝒲.𝒱.Idx q) :
    horF (F := F) (fun (_ : 𝒲.𝒰.Idx p) (_ : 𝒲.𝒱.Idx q) => 0) s t = 0 := by
  simp only [horF, map_zero, smul_zero, Finset.sum_const_zero]

lemma verF_zero {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx (q + 1)) :
    verF (F := F) (fun (_ : 𝒲.𝒰.Idx p) (_ : 𝒲.𝒱.Idx q) => 0) s t = 0 := by
  simp only [verF, map_zero, smul_zero, Finset.sum_const_zero]

lemma compF_zsmul {n : ℕ} (k : ℤ) (z : Γ(term 𝒲 F n, ⊤)) (p q : ℕ) (h : p + q = n)
    (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) : compF (k • z) p q h s t = k • compF z p q h s t := by
  rw [compF_eq_ofBo, compF_eq_ofBo, ← ofBo_zsmul]
  congr 1
  exact map_zsmul ((πT 𝒲 F h s t).app ⊤).hom k z

variable (𝒲 F) in
/-- The bi-Čech differential of a section concentrated in bidegree `(p, q)`. -/
theorem D_insT {n p q : ℕ} (h : p + q = n)
    (c : ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), Γ(F, biOpen 𝒲 s t)) :
    (D 𝒲 F n).app ⊤ (insT h c) =
      insT (by omega : p + 1 + q = n + 1) (horF c) +
        ((-1 : ℤ) ^ p) • insT (by omega : p + (q + 1) = n + 1) (verF c) := by
  rw [compF_eq_iff]
  intro p' q' h' s' t'
  rw [compF_add, compF_zsmul]
  have hc : ∀ (hpq : p + q = n), (fun s t => compF (insT h c) p q hpq s t) = c :=
    fun hpq => funext fun s => funext fun t => compF_insT_self h hpq c s t
  have hz : ∀ (p'' q'' : ℕ) (hpq : p'' + q'' = n), (p'', q'') ≠ (p, q) →
      (fun s t => compF (insT h c) p'' q'' hpq s t) = fun _ _ => 0 :=
    fun p'' q'' hpq hne => funext fun s => funext fun t => compF_insT_ne h hpq hne c s t
  rcases p' with _ | p' <;> rcases q' with _ | q'
  · omega
  · rw [compF_D_zero_succ]
    by_cases e : (0, q') = (p, q)
    · obtain ⟨hp, hq⟩ := Prod.mk.inj e
      subst hp hq
      rw [hc, compF_insT_ne _ _ (by simp), compF_insT_self, pow_zero, one_smul, zero_add]
    · rw [hz _ _ _ e, verF_zero, compF_insT_ne _ _ (by simp), compF_insT_ne _ _ (by
        intro e'
        obtain ⟨hp, hq⟩ := Prod.mk.inj e'
        exact e (Prod.ext hp (by omega))), smul_zero, add_zero]
  · rw [compF_D_succ_zero]
    by_cases e : (p', 0) = (p, q)
    · obtain ⟨hp, hq⟩ := Prod.mk.inj e
      subst hp hq
      rw [hc, compF_insT_self, compF_insT_ne _ _ (by simp), smul_zero, add_zero]
    · rw [hz _ _ _ e, horF_zero, compF_insT_ne _ _ (by
        intro e'
        obtain ⟨hp, hq⟩ := Prod.mk.inj e'
        exact e (Prod.ext (by omega) hq)), compF_insT_ne _ _ (by simp), smul_zero, add_zero]
  · rw [compF_D_succ_succ]
    by_cases e₁ : (p', q' + 1) = (p, q)
    · obtain ⟨hp, hq⟩ := Prod.mk.inj e₁
      subst hp hq
      rw [hc, hz _ _ _ (by simp), verF_zero, smul_zero, add_zero, compF_insT_self,
        compF_insT_ne _ _ (by simp), smul_zero, add_zero]
    · by_cases e₂ : (p' + 1, q') = (p, q)
      · obtain ⟨hp, hq⟩ := Prod.mk.inj e₂
        subst hp hq
        rw [hc, hz _ _ _ (by simp), horF_zero, zero_add, compF_insT_ne _ _ (by simp),
          compF_insT_self, zero_add]
      · rw [hz _ _ _ e₁, hz _ _ _ e₂, horF_zero, verF_zero, smul_zero, add_zero,
          compF_insT_ne _ _ (by
            intro e'
            obtain ⟨hp, hq⟩ := Prod.mk.inj e'
            exact e₁ (Prod.ext (by omega) hq)),
          compF_insT_ne _ _ (by
            intro e'
            obtain ⟨hp, hq⟩ := Prod.mk.inj e'
            exact e₂ (Prod.ext hp (by omega))), smul_zero, add_zero]

end Differential

end Langlands.AlgebraicGeometry.Modules.BiCech

import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Sufficiency
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.AltCocycle
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePullback

/-! # Gluing a deformation from an obstruction-cone cocycle -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections CocycleGluing Langlands.Algebra

/-- The unit `1 + x` for a square-zero element `x`. -/
def unitOfSq {S : Type*} [CommRing S] (x : S) (hx : x * x = 0) : Sˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by linear_combination (-1 : S) * hx
  inv_val := by linear_combination (-1 : S) * hx

@[simp] lemma unitOfSq_val {S : Type*} [CommRing S] (x : S) (hx : x * x = 0) :
    (unitOfSq x hx : S) = 1 + x := rfl

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)

section Edges

variable {Y : Scheme.{u}} (K' : Y.OrderedAffineCover)

lemma edge_eq (σ : K'.Idx 1) (h : σ.1 0 < σ.1 1) : edge K' (σ.1 0) (σ.1 1) h = σ :=
  Subtype.ext (funext fun k => by fin_cases k <;> rfl)

lemma lt_of_idx_one (σ : K'.Idx 1) : σ.1 0 < σ.1 1 := σ.2 (by decide)

lemma res_cochain_congr₁ {S : Type u} [CommRing S] (π : Y ⟶ Spec (CommRingCat.of S))
    (c : (OModulePresheaf.unit π).cochain K' 1) {τ τ' : K'.Idx 1}
    (hτ : τ = τ') {W : Y.Opens} (h : W ≤ K'.inter τ) (h' : W ≤ K'.inter τ') :
    (Y.presheaf.map (homOfLE h).op).hom (c τ) = (Y.presheaf.map (homOfLE h').op).hom (c τ') := by
  subst hτ
  rfl

end Edges

/-- The ring identity behind the cocycle condition of the glued transition functions. -/
lemma glue_core {T : Type*} [CommRing T] (P01 P12 P02 G01 G12 G02 I01 I12 I02 : T)
    (hGI01 : G01 * I01 = 1) (hGI12 : G12 * I12 = 1) (hGI02 : G02 * I02 = 1)
    (hsum : (P12 * I12 - 1) - (P02 * I02 - 1) + (P01 * I01 - 1) + (G01 * G12 * I02 - 1) = 0)
    (h1 : (P01 * I01 - 1) * (P12 * I12 - 1) = 0)
    (h2 : (P01 * I01 - 1) * (G01 * G12 * I02 - 1) = 0)
    (h3 : (P12 * I12 - 1) * (G01 * G12 * I02 - 1) = 0) :
    P01 * P12 = P02 := by
  have e01 : P01 = G01 * (1 + (P01 * I01 - 1)) := by linear_combination (-P01) * hGI01
  have e12 : P12 = G12 * (1 + (P12 * I12 - 1)) := by linear_combination (-P12) * hGI12
  have e02 : P02 = G02 * (1 + (P02 * I02 - 1)) := by linear_combination (-P02) * hGI02
  have eG : G01 * G12 = G02 * (1 + (G01 * G12 * I02 - 1)) := by
    linear_combination (-(G01 * G12)) * hGI02
  have key : (1 + (G01 * G12 * I02 - 1)) * (1 + (P01 * I01 - 1)) * (1 + (P12 * I12 - 1)) =
      1 + (P02 * I02 - 1) := by
    linear_combination hsum + h1 + h2 + h3 + (P12 * I12 - 1) * h2
  calc P01 * P12 = G01 * G12 * ((1 + (P01 * I01 - 1)) * (1 + (P12 * I12 - 1))) := by
        linear_combination P12 * e01 + G01 * (1 + (P01 * I01 - 1)) * e12
    _ = G02 * ((1 + (G01 * G12 * I02 - 1)) * (1 + (P01 * I01 - 1)) * (1 + (P12 * I12 - 1))) := by
        linear_combination ((1 + (P01 * I01 - 1)) * (1 + (P12 * I12 - 1))) * eG
    _ = P02 := by linear_combination G02 * key - e02

/-- The ring identity extracting the obstruction cochain from a gauge relation. -/
lemma extract_core {T : Type*} [CommRing T] (ai aj R Gv Ginv Cv : T) (hGI : Gv * Ginv = 1)
    (hrel : ai * R = Gv * (1 + Cv) * aj) (h1 : (ai - 1) * (R * Ginv - 1) = 0)
    (h2 : Cv * (aj - 1) = 0) :
    Cv = (ai - 1 - (aj - 1)) + (R * Ginv - 1) := by
  linear_combination (-Ginv) * hrel - ((1 + Cv) * aj) * hGI + h1 - h2

section Glue

variable (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
  {A : Type u} [CommRing A] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
  (I : Ideal A) (hI : ∀ k ∈ I, ∀ k' ∈ I, k * k' = 0)
  (C : (OModulePresheaf.unit (relProj f A)).cochain (testCover f K A) 1)
  (hC : ∀ σ, C σ ∈ I.map (structureHom f A ((testCover f K A).inter σ)).hom)

/-- The correction on the pair `i < j`: the value of `C` on the edge `(i, j)`. -/
def corrPair (i j : K.ι) :
    Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j) :=
  if h : i < j then
    (relSpace f A).presheaf.map (homOfLE (le_inter_edge (testCover f K A) i j h)).op
      (C (edge (testCover f K A) i j h))
  else 0

include hC in
lemma corrPair_mem (i j : K.ι) :
    corrPair f K C i j ∈
      I.map (structureHom f A ((testCover f K A).U i ⊓ (testCover f K A).U j)).hom := by
  unfold corrPair
  split_ifs with h
  · exact res_mem_map f A _ I (hC _)
  · exact zero_mem _

include hI hC in
lemma corrPair_sq (i j : K.ι) : corrPair f K C i j * corrPair f K C i j = 0 :=
  mul_eq_zero_of_mem_map_sq _ I hI (corrPair_mem f K I C hC i j) (corrPair_mem f K I C hC i j)

/-- The ordered transition units `G i j (1 + C i j)` for `i < j`, with `G` the pushed `g`. -/
def corrUnits (i j : K.ι) :
    (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ :=
  if i < j then
    pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g i j *
      unitOfSq (corrPair f K C i j) (corrPair_sq f K I hI C hC i j)
  else 1

/-- The glued transition functions: the alternating extension of `corrUnits`. -/
def glueUnits : ∀ i j : K.ι,
    (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ :=
  altExt (corrUnits f K g I hI C hC)

lemma glueUnits_of_lt {i j : K.ι} (h : i < j) :
    (glueUnits f K g I hI C hC i j : Γ(relSpace f A, _)) =
      (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g i j :
        Γ(relSpace f A, _)) * (1 + corrPair f K C i j) := by
  rw [glueUnits, altExt_of_lt _ h, corrUnits]
  simp only [h, ↓reduceIte, Units.val_mul, unitOfSq_val]

lemma res_corrPair (σ : K.Idx 1) :
    ((relSpace f A).presheaf.map (homOfLE (le_inf ((testCover f K A).inter_le σ 0)
      ((testCover f K A).inter_le σ 1))).op).hom (corrPair f K C (σ.1 0) (σ.1 1)) = C σ := by
  have hlt : σ.1 0 < σ.1 1 := lt_of_idx_one K σ
  simp only [corrPair, hlt, ↓reduceDIte]
  rw [map_map_apply]
  refine (res_cochain_congr₁ (testCover f K A) (relProj f A) C (edge_eq _ σ hlt) _ le_rfl).trans ?_
  change ((relSpace f A).presheaf.map (𝟙 _)).hom (C σ) = C σ
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma cvec_glueUnits (σ : K.Idx 1) : cvec f K g (glueUnits f K g I hI C hC) σ = C σ := by
  have hlt : σ.1 0 < σ.1 1 := lt_of_idx_one K σ
  have hle : (testCover f K A).inter σ ≤
      (testCover f K A).U (σ.1 0) ⊓ (testCover f K A).U (σ.1 1) :=
    le_inf ((testCover f K A).inter_le σ 0) ((testCover f K A).inter_le σ 1)
  have hcorr : ((relSpace f A).presheaf.map (homOfLE hle).op).hom
      (corrPair f K C (σ.1 0) (σ.1 1)) = C σ := by
    simp only [corrPair, hlt, ↓reduceDIte]
    rw [map_map_apply]
    refine (res_cochain_congr₁ (testCover f K A) (relProj f A) C (edge_eq _ σ hlt) _
      le_rfl).trans ?_
    change ((relSpace f A).presheaf.map (𝟙 _)).hom (C σ) = C σ
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hGI := congrArg (fun u => ((relSpace f A).presheaf.map (homOfLE hle).op).hom u)
    (Units.mul_inv (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g
      (σ.1 0) (σ.1 1)))
  simp only [map_mul, map_one] at hGI
  unfold cvec pr
  change ((relSpace f A).presheaf.map (homOfLE hle).op).hom
      (glueUnits f K g I hI C hC (σ.1 0) (σ.1 1) : Γ(relSpace f A, _)) *
    ((relSpace f A).presheaf.map (homOfLE hle).op).hom
      (((pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g (σ.1 0) (σ.1 1))⁻¹ :
        (Γ(relSpace f A, _))ˣ) : Γ(relSpace f A, _)) - 1 = C σ
  rw [glueUnits_of_lt f K g I hI C hC hlt, map_mul, map_add, map_one, hcorr]
  linear_combination (1 + (show Γ(relSpace f A, (testCover f K A).inter σ) from C σ)) * hGI

end Glue

section Cocycle

variable {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]
  [IsSeparated f] (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra P A]
  [IsScalarTower R P A] (χ : A₀ →ₐ[R] B) (q : A →ₐ[R] B)
  (hqρ : q.comp (IsScalarTower.toAlgHom R P A) = χ.comp (IsScalarTower.toAlgHom R P A₀))
  {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]
  {M : Type u} [AddCommGroup M] [Module A₀ M] [Module P M] [IsScalarTower P A₀ M]
  (jM : M →ₗ[P] A) (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
  (hjMsq : ∀ m m', jM m * jM m' = 0)

omit [Algebra R A₀] [IsScalarTower R P A₀] in
include hjMr in
lemma compMap_mem (c : cplx f K A₀ 1 ⊗[A₀] M) (σ : K.Idx 1) :
    compMap f K jM 1 c σ ∈ (RingHom.ker q.toRingHom).map
      (structureHom f A ((testCover f K A).inter σ)).hom :=
  (exists_compMap_eq_iff f K jM _ hjMr _).mp ⟨c, rfl⟩ σ

/-- The transition functions glued from a cochain `c`. -/
abbrev glueC (c : cplx f K A₀ 1 ⊗[A₀] M) :
    ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ :=
  glueUnits f K g (RingHom.ker q.toRingHom) (ker_sq_zero q jM hjMr hjMsq) (compMap f K jM 1 c)
    (compMap_mem f K q jM hjMr c)

include hqρ in
/-- The glued transition functions satisfy the cocycle identity on ordered triples, as soon as
`d c + φ_* z = 0`. -/
lemma glueC_pr_cocycle (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom)
    (hjMinj : Function.Injective jM) (c : cplx f K A₀ 1 ⊗[A₀] M)
    (hcc : (dif f K A₀ 1).rTensor M c +
      (phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr).lTensor (cplx f K A₀ 2)
        (zObs f K jQ hjQ g hg) = 0) (s : K.Idx 2) :
    pr (testCover f K A) (uval _ (glueC f K g q jM hjMr hjMsq c)) s 0 1 *
        pr (testCover f K A) (uval _ (glueC f K g q jM hjMr hjMsq c)) s 1 2 =
      pr (testCover f K A) (uval _ (glueC f K g q jM hjMr hjMsq c)) s 0 2 := by
  set h' := glueC f K g q jM hjMr hjMsq c with hh'
  set T := testCover f K A with hT
  have hc : compMap f K jM 1 c =
      fun σ : K.Idx 1 => (cvec f K g h' σ : Γ(relSpace f A, (testCover f K A).inter σ)) :=
    funext fun σ => (cvec_glueUnits f K g _ _ _ _ σ).symm
  have hI : ∀ k ∈ RingHom.ker q.toRingHom, ∀ k' ∈ RingHom.ker q.toRingHom, k * k' = 0 :=
    ker_sq_zero q jM hjMr hjMsq
  -- the differential of `c`
  have e1 : (show Γ(relSpace f A, (testCover f K A).inter s) from
      compMap f K jM 2 ((dif f K A₀ 1).rTensor M c) s) =
      (relSpace f A).presheaf.map (homOfLE ((testCover f K A).inter_le_inter_face s 0)).op
          (cvec f K g h' ((testCover f K A).face s 0)) -
        (relSpace f A).presheaf.map (homOfLE ((testCover f K A).inter_le_inter_face s 1)).op
          (cvec f K g h' ((testCover f K A).face s 1)) +
        (relSpace f A).presheaf.map (homOfLE ((testCover f K A).inter_le_inter_face s 2)).op
          (cvec f K g h' ((testCover f K A).face s 2)) := by
    refine (congrFun (compMap_dif f K jM 1 c) s).trans ?_
    rw [hc]
    exact d_one_apply (testCover f K A) (relProj f A) _ s
  -- the pushed obstruction
  have e2 : (show Γ(relSpace f A, (testCover f K A).inter s) from
      compMap f K jM 2 ((phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr).lTensor
        (cplx f K A₀ 2) (zObs f K jQ hjQ g hg)) s) =
      (secMap (A := A) f K s).hom (defect f K g s) := by
    have hnat := compMap_natural f K jQ jM (Algebra.ofId P A)
      (phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr)
      (fun x => jM_phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr x)
      (zObs f K jQ hjQ g hg) s
    refine hnat.symm.trans ?_
    refine (congrArg (testMap f K (Algebra.ofId P A) s).hom
      (congrFun (compMap_zObs f K jQ hjQ g hg) s)).trans ?_
    exact ConcreteCategory.congr_hom (secMap_comp_testMap f K (Algebra.ofId P A) s) _
  have hsum0 := congrArg (fun y => (show Γ(relSpace f A, (testCover f K A).inter s) from
    compMap f K jM 2 y s)) hcc
  simp only [map_add, map_zero] at hsum0
  change (show Γ(relSpace f A, (testCover f K A).inter s) from
      compMap f K jM 2 ((dif f K A₀ 1).rTensor M c) s) +
    (show Γ(relSpace f A, (testCover f K A).inter s) from
      compMap f K jM 2 ((phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr).lTensor
        (cplx f K A₀ 2) (zObs f K jQ hjQ g hg)) s) = 0 at hsum0
  rw [e1, e2, res_cvec_face f K g h' s 0 1 2 rfl rfl, res_cvec_face f K g h' s 1 0 2 rfl rfl,
    res_cvec_face f K g h' s 2 0 1 rfl rfl] at hsum0
  unfold defect at hsum0
  simp only [map_sub, map_mul, map_one] at hsum0
  set G := pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g with hG
  have hval : ∀ a b : Fin 3, (secMap (A := A) f K s).hom (pr K (uval K g) s a b) =
      pr T (uval T G) s a b := fun a b => by
    have := pr_pairUnitsAlong_val f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g s a b
    rw [secMapAlong_toAlgHom] at this
    exact this.symm
  have hinv : ∀ a b : Fin 3, (secMap (A := A) f K s).hom (pr K (uinv K g) s a b) =
      pr T (uinv T G) s a b := fun a b => by
    have := pr_pairUnitsAlong_inv f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g s a b
    rw [secMapAlong_toAlgHom] at this
    exact this.symm
  -- membership in the extension of `ker q`
  have hx : ∀ (j a' b' : Fin 3) (ha : s.1 (j.succAbove 0) = s.1 a')
      (hb : s.1 (j.succAbove 1) = s.1 b'),
      pr T (uval T h') s a' b' * pr T (uinv T G) s a' b' - 1 ∈
        (RingHom.ker q.toRingHom).map (structureHom f A (T.inter s)).hom := by
    intro j a' b' ha hb
    rw [← res_cvec_face f K g h' s j a' b' ha hb]
    refine res_mem_map f A _ _ ?_
    rw [← congrFun hc]
    exact compMap_mem f K q jM hjMr c _
  have hw : pr T (uval T G) s 0 1 * pr T (uval T G) s 1 2 * pr T (uinv T G) s 0 2 - 1 ∈
      (RingHom.ker q.toRingHom).map (structureHom f A (T.inter s)).hom := by
    have hmem := secMap_mem_map (A := A) f K _ s (hg s)
    unfold defect at hmem
    simp only [map_sub, map_mul, map_one] at hmem
    rw [hval, hval, hinv] at hmem
    refine Ideal.map_mono ?_ hmem
    rw [Ideal.map_le_iff_le_comap]
    intro k hk
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun h : P →ₐ[R] B => h k) hqρ
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    change q (algebraMap P A k) = 0
    rw [this, RingHom.mem_ker.mp hk, map_zero]
  rw [hval 0 1, hval 1 2, hinv 0 2] at hsum0
  have hx01 := hx 2 0 1 rfl rfl
  have hx12 := hx 0 1 2 rfl rfl
  exact glue_core _ _ _ _ _ _ _ _ _ (pr_val_mul_pr_inv T G s 0 1) (pr_val_mul_pr_inv T G s 1 2)
    (pr_val_mul_pr_inv T G s 0 2) hsum0
    (mul_eq_zero_of_mem_map_sq _ _ hI hx01 hx12)
    (mul_eq_zero_of_mem_map_sq _ _ hI hx01 hw)
    (mul_eq_zero_of_mem_map_sq _ _ hI hx12 hw)

include hqρ in
/-- The glued transition functions form a cocycle. -/
theorem isCocycle_glueC (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom)
    (hjMinj : Function.Injective jM) (c : cplx f K A₀ 1 ⊗[A₀] M)
    (hcc : (dif f K A₀ 1).rTensor M c +
      (phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr).lTensor (cplx f K A₀ 2)
        (zObs f K jQ hjQ g hg) = 0) :
    IsCocycle (glueC f K g q jM hjMr hjMsq c) := by
  apply isCocycle_altExt
  intro i j k hij hjk
  let s : (testCover f K A).Idx 2 :=
    Langlands.AlgebraicGeometry.Modules.CechResolution.tripleIdx (testCover f K A) hij hjk
  have h := glueC_pr_cocycle f K g χ q hqρ jM hjMr hjMsq hπ jQ hjQ hg hjMinj c hcc s
  have hW : (testCover f K A).U i ⊓ (testCover f K A).U j ⊓ (testCover f K A).U k ≤
      (testCover f K A).inter s := le_iInf fun l => by
    fin_cases l
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have h' := congrArg (fun v => ((relSpace f A).presheaf.map (homOfLE hW).op).hom v) h
  simp only [map_mul] at h'
  unfold pr at h'
  rw [map_map_apply, map_map_apply, map_map_apply] at h'
  have e01 : (glueC f K g q jM hjMr hjMsq c (s.1 0) (s.1 1)) =
      corrUnits f K g (RingHom.ker q.toRingHom) (ker_sq_zero q jM hjMr hjMsq)
        (compMap f K jM 1 c) (compMap_mem f K q jM hjMr c) i j :=
    altExt_of_lt _ (show s.1 0 < s.1 1 from hij)
  have e12 : (glueC f K g q jM hjMr hjMsq c (s.1 1) (s.1 2)) =
      corrUnits f K g (RingHom.ker q.toRingHom) (ker_sq_zero q jM hjMr hjMsq)
        (compMap f K jM 1 c) (compMap_mem f K q jM hjMr c) j k :=
    altExt_of_lt _ (show s.1 1 < s.1 2 from hjk)
  have e02 : (glueC f K g q jM hjMr hjMsq c (s.1 0) (s.1 2)) =
      corrUnits f K g (RingHom.ker q.toRingHom) (ker_sq_zero q jM hjMr hjMsq)
        (compMap f K jM 1 c) (compMap_mem f K q jM hjMr c) i k :=
    altExt_of_lt _ (show s.1 0 < s.1 2 from hij.trans hjk)
  simp only [uval] at h'
  rw [e01, e12, e02] at h'
  exact h'

include hqρ in
/-- The reduction of the glued transition functions along `q` is the pushed family `g`, on
ordered pairs. -/
lemma glueC_reduction (hq : Function.Surjective q) (c : cplx f K A₀ 1 ⊗[A₀] M) {i j : K.ι}
    (hij : i < j) :
    CocycleGluing.pullbackCocycle (relMap f q) (glueC f K g q jM hjMr hjMsq c) i j =
      pushUnits f K (relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀))
        (fun i => relMap f q ⁻¹ᵁ (testCover f K A).U i) (testCover_pair_le f K χ q hqρ) g i j := by
  apply Units.ext
  rw [CocycleGluing.pullbackCocycle_val, glueUnits_of_lt f K g _ _ _ _ hij, map_mul, map_add,
    map_one]
  have hmem := corrPair_mem f K (RingHom.ker q.toRingHom) (compMap f K jM 1 c)
    (compMap_mem f K q jM hjMr c) i j
  rw [← ker_appLE_eq_map f q hq _ (isAffineOpen_testCover_inf f K i j), RingHom.mem_ker] at hmem
  erw [hmem]
  rw [add_zero, mul_one]
  change ((pairMapAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) i j ≫
      (relMap f q).appLE _ _ le_rfl).hom (g i j : Γ(relSpace f P, K.U i ⊓ K.U j))) =
    ((relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀)).appLE (K.U i ⊓ K.U j) _
      (testCover_pair_le f K χ q hqρ i j)).hom (g i j : Γ(relSpace f P, K.U i ⊓ K.U j))
  rw [pairMapAlong, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ : Γ(relSpace f P, K.U i ⊓ K.U j) ⟶ Γ(relSpace f B, _) =>
      φ.hom (g i j : Γ(relSpace f P, K.U i ⊓ K.U j)))
    (appLE_congr (by rw [← relMap_comp, ← relMap_comp, hqρ]) _ _ _ _)

/-- The local generators of a glued sheaf have the cocycle as transition functions. -/
lemma isTransition_genSec {Y : Scheme.{u}} {ι : Type u} {T : ι → Y.Opens}
    (h : ∀ i j : ι, (Γ(Y, T i ⊓ T j))ˣ) (hh : IsCocycle h) :
    IsTransition (fun i => genSec h hh i (le_refl (T i))) h := by
  intro i j
  rw [map_genSec h hh j _ le_rfl, map_genSec h hh i _ le_rfl,
    genSec_eq_smul_genSec hh (inf_le_left : T i ⊓ T j ≤ T i) inf_le_right]
  congr 1
  exact CocycleGluing.res_self _ _

include hqρ in
/-- **The glued deformation.** If `d c + φ_* z = 0`, the transition functions glued from `c`
define a line bundle `N` on the relative space of `A` with frames, together with an
isomorphism from the pullback of `L₀` along `χ` to the reduction of `N`, which has coordinate
`1` with respect to the frames. -/
theorem exists_deformation (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom)
    (hq : Function.Surjective q) (hjMinj : Function.Injective jM) (c : cplx f K A₀ 1 ⊗[A₀] M)
    (hcc : (dif f K A₀ 1).rTensor M c +
      (phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr).lTensor (cplx f K A₀ 2)
        (zObs f K jQ hjQ g hg) = 0)
    {L₀ : LineBundle (relSpace f A₀)} (e : ∀ i, Γ(L₀.obj, (testCover f K A₀).U i))
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover f K A₀).U i))
    (hge : IsTransition e
      (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
        (fun _ _ => le_rfl) g)) :
    ∃ (N : LineBundle (relSpace f A)) (fN : ∀ i, Γ(N.obj, (testCover f K A).U i))
      (_ : ∀ i, Scheme.Modules.IsFrameOn (fN i) ((testCover f K A).U i))
      (φ : (Scheme.Modules.pullback (relMap f χ)).obj L₀.obj ≅
        (Scheme.Modules.pullback (relMap f q)).obj N.obj),
      IsTransition fN (glueC f K g q jM hjMr hjMsq c) ∧
        ∀ i, HasCoord φ.hom (e i) (fN i) (testCover_preimage_le f K χ q hqρ i) le_rfl 1 := by
  set h' := glueC f K g q jM hjMr hjMsq c with hh'
  have hcoc : IsCocycle h' := isCocycle_glueC f K g χ q hqρ jM hjMr hjMsq hπ jQ hjQ hg hjMinj c hcc
  have hT : (⨆ i, (testCover f K A).U i) = ⊤ := (testCover f K A).iSup_eq_top
  let N : LineBundle (relSpace f A) := ⟨glued h', isLocallyFreeRankOne_glued h' hT hcoc⟩
  let fN : ∀ i, Γ(N.obj, (testCover f K A).U i) := fun i => genSec h' hcoc i le_rfl
  have hfN : ∀ i, Scheme.Modules.IsFrameOn (fN i) ((testCover f K A).U i) := fun i =>
    isFrameOn_genSec h' hcoc i
  have hfN_trans : IsTransition fN h' := isTransition_genSec h' hcoc
  -- frames on the relative space of `B`
  set W : K.ι → (relSpace f B).Opens := fun i => relMap f q ⁻¹ᵁ (testCover f K A).U i with hW
  have hu := testCover_preimage_le f K χ q hqρ
  set sB : ∀ i, Γ((Scheme.Modules.pullback (relMap f χ)).obj L₀.obj, W i) := fun i =>
    ((Scheme.Modules.pullback (relMap f χ)).obj L₀.obj).presheaf.map (homOfLE (hu i)).op
      (Scheme.Modules.pullbackLocalSection (relMap f χ) (e i)) with hsB
  have hsB : ∀ i, Scheme.Modules.IsFrameOn (sB i) (W i) := fun i =>
    (((he i).pullbackLocalSection (relMap f χ)).map (homOfLE (hu i))).mono (hu i)
  have hsB_trans := isTransition_pullback_push f K (relMap f (IsScalarTower.toAlgHom R P A₀))
    (testCover f K A₀).U (fun _ _ => le_rfl) e g hge (relMap f χ) W hu
    (testCover_pair_le f K χ q hqρ)
  set tB : ∀ i, Γ((Scheme.Modules.pullback (relMap f q)).obj N.obj, W i) := fun i =>
    Scheme.Modules.pullbackLocalSection (relMap f q) (fN i) with htB
  have htB : ∀ i, Scheme.Modules.IsFrameOn (tB i) (W i) := fun i =>
    (hfN i).pullbackLocalSection (relMap f q)
  have htB_trans := LineHom.isTransition_pullback (relMap f q) hfN_trans
  have hcocα := CocycleGluing.isCocycle_of_isTransition hsB hsB_trans
  have hcocβ := CocycleGluing.isCocycle_of_isTransition htB htB_trans
  have hgauge := (LineHom.isGaugeFamily_iff_of_lt hcocα hcocβ (fun _ => 1)).mpr fun i j hij => by
    rw [map_one, map_one, one_mul, mul_one]
    exact congrArg Units.val (glueC_reduction f K g χ q hqρ jM hjMr hjMsq hq c hij).symm
  have hWcov : (⨆ i, W i) = ⊤ := LineHom.iSup_preimage_eq_top (relMap f q) hT
  obtain ⟨φ, hφ⟩ := exists_iso_of_gauge hWcov hsB htB hsB_trans htB_trans (fun _ => 1) hgauge
    (fun _ => isUnit_one)
  refine ⟨N, fN, hfN, φ, hfN_trans, fun i => ?_⟩
  unfold HasCoord
  exact (hφ i).trans (congrArg ((1 : Γ(relSpace f B, W i)) • ·)
    (CocycleGluing.mres_self (M := (Scheme.Modules.pullback (relMap f q)).obj N.obj)
      (le_rfl : W i ≤ W i) (tB i)).symm)

omit [IsSeparated f] [Module A₀ M] [IsScalarTower P A₀ M] in
include hqρ hjMr hjMsq in
/-- A lift `χ' : A₀ → A` of `χ` differs from `P → A` by a derivation with values in `M`. -/
lemma exists_derivation_of_lift [Module R M] [IsScalarTower R P M]
    (hjMinj : Function.Injective jM) (χ' : A₀ →ₐ[R] A) (hχ' : q.comp χ' = χ) :
    ∃ δ : Derivation R P M, ∀ p, jM (δ p) =
      (χ'.comp (IsScalarTower.toAlgHom R P A₀)) p - IsScalarTower.toAlgHom R P A p := by
  have hmem : ∀ p, (χ'.comp (IsScalarTower.toAlgHom R P A₀)) p -
      IsScalarTower.toAlgHom R P A p ∈ RingHom.ker q.toRingHom := by
    intro p
    rw [RingHom.mem_ker]
    change q (χ' (algebraMap P A₀ p) - algebraMap P A p) = 0
    have h1 := congrArg (fun h : A₀ →ₐ[R] B => h (algebraMap P A₀ p)) hχ'
    have h2 := congrArg (fun h : P →ₐ[R] B => h p) hqρ
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2
    rw [map_sub, h1, h2, sub_self]
  choose δf hδf using fun p => (hjMr _).mp (hmem p)
  refine ⟨{ toFun := δf
            map_add' := fun a b => hjMinj (by rw [map_add, hδf, hδf, hδf, map_add, map_add]; ring)
            map_smul' := fun r a => hjMinj (by
              rw [hδf, RingHom.id_apply, LinearMap.map_smul_of_tower, hδf, map_smul, map_smul,
                smul_sub])
            map_one_eq_zero' := hjMinj (by
              change jM (δf 1) = jM 0
              rw [hδf, map_one, map_one, sub_self, map_zero])
            leibniz' := fun a b => hjMinj (by
              change jM (δf (a * b)) = jM (a • δf b + b • δf a)
              have ha := hδf a
              have hb := hδf b
              rw [hδf, map_add, jM.map_smul, jM.map_smul, Algebra.smul_def, Algebra.smul_def,
                map_mul, map_mul]
              have hsq := hjMsq (δf a) (δf b)
              change _ = algebraMap P A a * jM (δf b) + algebraMap P A b * jM (δf a)
              rw [ha, hb] at hsq
              rw [ha, hb]
              change _ = IsScalarTower.toAlgHom R P A a * _ + IsScalarTower.toAlgHom R P A b * _
              linear_combination hsq) }, fun p => hδf p⟩

section Extract

variable {F : Type u} [AddCommGroup F] [Module A₀ F] [Module P F] [IsScalarTower P A₀ F]
  [Module R F]

include hqρ in
/-- **Extraction.** A lift of the glued deformation over the identity test gives a
`0`-cochain `b` with `c = d b + D''_* θ`, where `D''` describes the lift `χ'`. -/
theorem exists_b_of_lift [Flat f] (hq : Function.Surjective q) (hjMinj : Function.Injective jM)
    (c : cplx f K A₀ 1 ⊗[A₀] M)
    {L₀ : LineBundle (relSpace f A₀)} (e : ∀ i, Γ(L₀.obj, (testCover f K A₀).U i))
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover f K A₀).U i))
    (hge : IsTransition e
      (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
        (fun _ _ => le_rfl) g))
    (N : LineBundle (relSpace f A)) (fN : ∀ i, Γ(N.obj, (testCover f K A).U i))
    (hfN : ∀ i, Scheme.Modules.IsFrameOn (fN i) ((testCover f K A).U i))
    (hfN_trans : IsTransition fN (glueC f K g q jM hjMr hjMsq c))
    (φ : (Scheme.Modules.pullback (relMap f χ)).obj L₀.obj ≅
      (Scheme.Modules.pullback (relMap f q)).obj N.obj)
    (hφ : ∀ i, HasCoord φ.hom (e i) (fN i) (testCover_preimage_le f K χ q hqρ i) le_rfl 1)
    (D'' : F →ₗ[A₀] M) (D : Derivation R P F) (χ' : A₀ →ₐ[R] A) (hχ' : q.comp χ' = χ)
    (hχ'comp : χ'.comp (IsScalarTower.toAlgHom R P A₀) = rhoCorr jM hjMsq D'' D)
    (ψ : (Scheme.Modules.pullback (relMap f χ')).obj L₀.obj ≅
      (Scheme.Modules.pullback (𝟙 (relSpace f A))).obj N.obj)
    (htr : Langlands.Scheme.Modules.LineBundleFlatDescent.tr (relMap f q)
        (by rw [← relMap_comp, hχ']) (Category.comp_id _) ψ.hom = φ.hom) :
    ∃ b : cplx f K A₀ 0 ⊗[A₀] M,
      c = (dif f K A₀ 0).rTensor M b + D''.lTensor (cplx f K A₀ 1)
        (thetaObs (A₀ := A₀) f K D g) := by
  have hI := ker_sq_zero q jM hjMr hjMsq
  have hn : IsNilpotent (RingHom.ker q.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [Submodule.zero_eq_bot, eq_bot_iff, pow_two]
    refine Ideal.mul_le.mpr fun a ha b hb => ?_
    rw [hI a ha b hb]
    exact Submodule.zero_mem _
  have hs : ∀ V, relMap f (χ'.comp (IsScalarTower.toAlgHom R P A₀)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V := by
    rw [hχ'comp]
    exact preimage_rhoCorr f q hq hn jM hjMr hjMsq D'' D
  have hu : ∀ i, (testCover f K A).U i ≤ relMap f χ' ⁻¹ᵁ (testCover f K A₀).U i :=
    testCover_le_preimage f K χ' hs
  set sF : ∀ i, Γ((Scheme.Modules.pullback (relMap f χ')).obj L₀.obj, (testCover f K A).U i) :=
    fun i =>
    ((Scheme.Modules.pullback (relMap f χ')).obj L₀.obj).presheaf.map (homOfLE (hu i)).op
      (Scheme.Modules.pullbackLocalSection (relMap f χ') (e i)) with hsF
  have hsF_frame : ∀ i, Scheme.Modules.IsFrameOn (sF i) ((testCover f K A).U i) := fun i =>
    (((he i).pullbackLocalSection (relMap f χ')).map (homOfLE (hu i))).mono (hu i)
  have hW' : ∀ i j, (testCover f K A).U i ⊓ (testCover f K A).U j ≤
      (relMap f χ' ≫ relMap f (IsScalarTower.toAlgHom R P A₀)) ⁻¹ᵁ (K.U i ⊓ K.U j) := by
    intro i j
    rw [← relMap_comp, hχ'comp]
    exact pair_le f K _ (preimage_rhoCorr f q hq hn jM hjMr hjMsq D'' D) i j
  have hsF_trans := isTransition_pullback_push f K (relMap f (IsScalarTower.toAlgHom R P A₀))
    (testCover f K A₀).U (fun _ _ => le_rfl) e g hge (relMap f χ') (testCover f K A).U hu hW'
  set tF : ∀ i, Γ((Scheme.Modules.pullback (𝟙 (relSpace f A))).obj N.obj, (testCover f K A).U i) :=
    fun i =>
    Scheme.Modules.pullbackLocalSection (𝟙 (relSpace f A)) (fN i) with htF
  have htF_frame : ∀ i, Scheme.Modules.IsFrameOn (tF i) ((testCover f K A).U i) := fun i =>
    (hfN i).pullbackLocalSection (𝟙 (relSpace f A))
  have htF_trans := LineHom.isTransition_pullback (𝟙 (relSpace f A)) hfN_trans
  have hTcov : (⨆ i, (testCover f K A).U i) = ⊤ := (testCover f K A).iSup_eq_top
  -- the coordinates of `ψ`
  set a := (LineHom.frameHomEquiv hsF_frame htF_frame hsF_trans htF_trans hTcov ψ.hom).1 with ha
  have ha_gauge := (LineHom.frameHomEquiv hsF_frame htF_frame hsF_trans htF_trans hTcov ψ.hom).2
  have ha_spec : ∀ i, ψ.hom.app ((testCover f K A).U i) (sF i) = a i • tF i := fun i =>
    LineHom.frameHomEquiv_spec hsF_frame htF_frame hsF_trans htF_trans hTcov ψ.hom i
  have hcoordψ : ∀ i, HasCoord ψ.hom (e i) (fN i) (hu i)
      (le_rfl : (testCover f K A).U i ≤ 𝟙 (relSpace f A) ⁻¹ᵁ (testCover f K A).U i) (a i) :=
      fun i => by
    unfold HasCoord
    exact (ha_spec i).trans (congrArg (a i • ·)
      (CocycleGluing.mres_self (M := (Scheme.Modules.pullback (𝟙 (relSpace f A))).obj N.obj)
        (le_rfl : (testCover f K A).U i ≤ (testCover f K A).U i) (tF i)).symm)
  have hle := testCover_preimage_le f K χ q hqρ
  have hone : ∀ i, ((relMap f q).appLE ((testCover f K A).U i)
      (relMap f q ⁻¹ᵁ (testCover f K A).U i) le_rfl).hom (a i) = 1 := by
    intro i
    have h1 := (hcoordψ i).tr (relMap f q) (by rw [← relMap_comp, hχ']) (Category.comp_id _)
      (le_rfl : relMap f q ⁻¹ᵁ (testCover f K A).U i ≤ relMap f q ⁻¹ᵁ (testCover f K A).U i)
      (hle i) le_rfl
    rw [htr] at h1
    exact HasCoord.unique (hfN i) h1 (hφ i)
  have hamem : ∀ i, a i - 1 ∈
      (RingHom.ker q.toRingHom).map (structureHom f A ((testCover f K A).U i)).hom := by
    intro i
    rw [← ker_appLE_eq_map f q hq _ ((testCover f K A).isAffineOpen i), RingHom.mem_ker, map_sub,
      map_one,
      hone, sub_self]
  -- the `0`-cochain
  have hamem' : ∀ i, 1 - a i ∈ (RingHom.ker q.toRingHom).map
      (structureHom f A ((testCover f K A).U i)).hom := fun i => by
    have := neg_mem (hamem i)
    rwa [neg_sub] at this
  let bc : (OModulePresheaf.unit (relProj f A)).cochain (testCover f K A) 0 := fun τ =>
    ((relSpace f A).presheaf.map (homOfLE ((testCover f K A).inter_le τ 0)).op).hom (1 - a (τ.1 0))
  obtain ⟨b, hb⟩ := (exists_compMap_eq_iff f K (A₀ := A₀) jM _ hjMr bc).mpr
    (fun τ => res_mem_map f A _ _ (hamem' _))
  refine ⟨b, ?_⟩
  apply compMap_injective f K jM hjMinj 1
  rw [map_add]
  funext σ
  have hlt : σ.1 0 < σ.1 1 := lt_of_idx_one K σ
  have hle : (testCover f K A).inter σ ≤
      (testCover f K A).U (σ.1 0) ⊓ (testCover f K A).U (σ.1 1) :=
    le_inf ((testCover f K A).inter_le σ 0) ((testCover f K A).inter_le σ 1)
  -- the gauge relation on the pair `(σ 0, σ 1)`, restricted to the intersection of `σ`
  have hg0 := ha_gauge (σ.1 0) (σ.1 1)
  have hα := congrArg (fun u => Units.val (u (σ.1 0) (σ.1 1)))
    (pushUnits_congr f K (w' := relMap f (rhoCorr jM hjMsq D'' D))
      (by rw [← relMap_comp, hχ'comp]) (testCover f K A).U hW'
      (pair_le f K _ (preimage_rhoCorr f q hq hn jM hjMr hjMsq D'' D)) g)
  have hβ : Units.val (CocycleGluing.pullbackCocycle (𝟙 (relSpace f A))
      (glueC f K g q jM hjMr hjMsq c) (σ.1 0) (σ.1 1)) =
      Units.val (glueC f K g q jM hjMr hjMsq c (σ.1 0) (σ.1 1)) := by
    rw [CocycleGluing.pullbackCocycle_val, id_appLE_apply]
    change (relSpace f A).presheaf.map (𝟙 _) _ = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  simp only at hα
  rw [hα, hβ, glueUnits_of_lt f K g _ _ _ _ hlt] at hg0
  have key := congrArg ((relSpace f A).presheaf.map (homOfLE hle).op).hom hg0
  simp only [map_mul, map_add, map_one] at key
  rw [map_map_apply, map_map_apply, res_corrPair] at key
  -- identification of the terms
  have hR := pr_pairMapAlong f K (rhoCorr jM hjMsq D'' D)
    (preimage_rhoCorr f q hq hn jM hjMr hjMsq D'' D) (uval K g) σ 0 1
  have hGv := pr_pairUnitsAlong_inv f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g σ 0 1
  rw [secMapAlong_toAlgHom] at hGv
  have hGI := pr_val_mul_pr_inv (testCover f K A)
    (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g) σ 0 1
  have hθ := compMap_thetaObs_ev f K g q hq hn jM hjMr hjMsq D'' D σ
  have hdb := (congrFun (compMap_dif f K jM 0 b) σ).trans
    (d_zero_apply (testCover f K A) (relProj f A) _ σ)
  rw [hb] at hdb
  -- notation
  set ai := ((relSpace f A).presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom (a (σ.1 0))
    with hai
  set aj := ((relSpace f A).presheaf.map (homOfLE (hle.trans inf_le_right)).op).hom (a (σ.1 1))
    with haj
  set Rv := (secMapAlong f K (rhoCorr jM hjMsq D'' D)
    (preimage_rhoCorr f q hq hn jM hjMr hjMsq D'' D) σ).hom (pr K (uval K g) σ 0 1) with hRv
  set Gv := pr (testCover f K A) (uval (testCover f K A)
    (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g)) σ 0 1 with hGvdef
  set Ginv := (secMap (A := A) f K σ).hom (pr K (uinv K g) σ 0 1) with hGinv
  set Cv := (show Γ(relSpace f A, (testCover f K A).inter σ) from compMap f K jM 1 c σ) with hCv
  have hdb' : (show Γ(relSpace f A, (testCover f K A).inter σ) from
      compMap f K jM 1 ((dif f K A₀ 0).rTensor M b) σ) = ai - 1 - (aj - 1) := by
    refine hdb.trans ?_
    simp only [bc]
    rw [map_map_apply, map_map_apply, map_sub, map_one, map_sub, map_one]
    change (1 - aj) - (1 - ai) = _
    ring
  have hrel : ai * Rv = Gv * (1 + Cv) * aj := by
    rw [← hR]
    exact key
  have hGI' : Gv * Ginv = 1 := by
    rw [← hGv]
    exact hGI
  -- membership facts
  have hθmem : Rv * Ginv - 1 ∈ (RingHom.ker q.toRingHom).map
      (structureHom f A ((testCover f K A).inter σ)).hom := by
    rw [← hθ]
    exact (exists_compMap_eq_iff f K (A₀ := A₀) jM _ hjMr _).mp ⟨_, rfl⟩ σ
  have haimem : ai - 1 ∈ (RingHom.ker q.toRingHom).map
      (structureHom f A ((testCover f K A).inter σ)).hom := by
    have := res_mem_map f A (hle.trans inf_le_left) _ (hamem (σ.1 0))
    rwa [map_sub, map_one] at this
  have hajmem : aj - 1 ∈ (RingHom.ker q.toRingHom).map
      (structureHom f A ((testCover f K A).inter σ)).hom := by
    have := res_mem_map f A (hle.trans inf_le_right) _ (hamem (σ.1 1))
    rwa [map_sub, map_one] at this
  have hCmem : Cv ∈ (RingHom.ker q.toRingHom).map
      (structureHom f A ((testCover f K A).inter σ)).hom := compMap_mem f K q jM hjMr c σ
  have hext := extract_core ai aj Rv Gv Ginv Cv hGI' hrel
    (mul_eq_zero_of_mem_map_sq _ _ hI haimem hθmem)
    (mul_eq_zero_of_mem_map_sq _ _ hI hCmem hajmem)
  -- conclusion
  have hgoal : Cv = (show Γ(relSpace f A, (testCover f K A).inter σ) from
      compMap f K jM 1 ((dif f K A₀ 0).rTensor M b) σ) +
    (show Γ(relSpace f A, (testCover f K A).inter σ) from
      compMap f K jM 1 (D''.lTensor (cplx f K A₀ 1) (thetaObs (A₀ := A₀) f K D g)) σ) := by
    rw [hdb', hθ]
    exact hext
  exact hgoal

end Extract

end Cocycle

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

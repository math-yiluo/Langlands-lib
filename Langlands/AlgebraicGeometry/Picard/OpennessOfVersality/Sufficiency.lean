import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Transitions
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NilpotentFrame
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import Langlands.Cohomology.ModuleComplex.ObstructionConeOpenStatement

/-! # Sufficiency: vanishing of the obstruction cohomology gives lifts -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections CocycleGluing Langlands.Algebra

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]

section FramesN

variable {L₀ : LineBundle (relSpace f A₀)} (e : ∀ i, Γ(L₀.obj, (testCover f K A₀).U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover f K A₀).U i))
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (χ : A₀ →ₐ[R] B) (q : A →ₐ[R] B) (hq : Function.Surjective q)
  (hn : IsNilpotent (RingHom.ker q.toRingHom))

include he hq hn in
/-- Frames of the bundle `N` on affine opens `U i`, lifting the images of the pulled-back frames
under an isomorphism `φ` on the reduction. -/
lemma exists_frames_lift (N : LineBundle (relSpace f A))
    (φ : (Scheme.Modules.pullback (relMap f χ)).obj L₀.obj ≅
      (Scheme.Modules.pullback (relMap f q)).obj N.obj)
    (U : K.ι → (relSpace f A).Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hle : ∀ i, relMap f q ⁻¹ᵁ U i ≤ relMap f χ ⁻¹ᵁ (testCover f K A₀).U i) :
    ∃ fr : ∀ i, Γ(N.obj, U i), (∀ i, Scheme.Modules.IsFrameOn (fr i) (U i)) ∧
      ∀ i, HasCoord φ.hom (e i) (fr i) (hle i) le_rfl 1 := by
  have key : ∀ i, ∃ s : Γ(N.obj, U i), Scheme.Modules.IsFrameOn s (U i) ∧
      HasCoord φ.hom (e i) s (hle i) le_rfl 1 := by
    intro i
    have h₁ := ((he i).pullbackLocalSection (relMap f χ)).map (homOfLE (hle i))
    have h₂ := (h₁.mono (hle i)).map_iso φ
    obtain ⟨s, hs, hst⟩ := exists_frame_lift f q hq hn N (U i) (hU i) _ h₂
    refine ⟨s, hs, ?_⟩
    unfold HasCoord
    rw [CocycleGluing.mres_self, hst, one_smul]
  choose fr hfr hcoord using key
  exact ⟨fr, hfr, hcoord⟩

/-- The transition functions of the lifted frames reduce to the pushed family `g`. -/
lemma pullbackCocycle_frameCocycle_eq (hge : IsTransition e
      (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
        (fun _ _ => le_rfl) g))
    (N : LineBundle (relSpace f A))
    (φ : (Scheme.Modules.pullback (relMap f χ)).obj L₀.obj ≅
      (Scheme.Modules.pullback (relMap f q)).obj N.obj)
    (U : K.ι → (relSpace f A).Opens)
    (hle : ∀ i, relMap f q ⁻¹ᵁ U i ≤ relMap f χ ⁻¹ᵁ (testCover f K A₀).U i)
    (fr : ∀ i, Γ(N.obj, U i)) (hfr : ∀ i, Scheme.Modules.IsFrameOn (fr i) (U i))
    (hcoord : ∀ i, HasCoord φ.hom (e i) (fr i) (hle i) le_rfl 1)
    (hW : ∀ i j, relMap f q ⁻¹ᵁ U i ⊓ relMap f q ⁻¹ᵁ U j ≤
      (relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀)) ⁻¹ᵁ (K.U i ⊓ K.U j)) :
    CocycleGluing.pullbackCocycle (relMap f q) (CocycleGluing.frameCocycle fr hfr) =
      pushUnits f K (relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀))
        (fun i => relMap f q ⁻¹ᵁ U i) hW g := by
  have ha := LineHom.isTransition_pullback (relMap f q) (CocycleGluing.isTransition_frameCocycle hfr)
  have hb := isTransition_map
    (isTransition_pullback_push f K (relMap f (IsScalarTower.toAlgHom R P A₀))
      (testCover f K A₀).U (fun _ _ => le_rfl) e g hge (relMap f χ)
      (fun i => relMap f q ⁻¹ᵁ U i) hle hW) φ.hom
  have heq : (fun i => φ.hom.app (relMap f q ⁻¹ᵁ U i)
      (((Scheme.Modules.pullback (relMap f χ)).obj L₀.obj).presheaf.map (homOfLE (hle i)).op
        (Scheme.Modules.pullbackLocalSection (relMap f χ) (e i)))) =
      fun i => Scheme.Modules.pullbackLocalSection (relMap f q) (fr i) := by
    funext i
    have := hcoord i
    unfold HasCoord at this
    rw [this, CocycleGluing.mres_self, one_smul]
  rw [heq] at hb
  exact CocycleGluing.IsTransition.unique (fun i => (hfr i).pullbackLocalSection (relMap f q)) ha hb

end FramesN

/-- The ring identity behind the cocycle condition `d c + φ_* z = 0`. -/
lemma dc_core' {T : Type*} [CommRing T] (A01 A12 I01 I12 I02 J02 B01 B12 B02 B'02 : T)
    (hA01 : A01 * I01 = 1) (hA12 : A12 * I12 = 1) (hB02 : B02 * B'02 = 1)
    (hcoc : B01 * B12 * B'02 = 1) (hJ : J02 = I02)
    (h1 : (B01 * I01 - 1) * (B12 * I12 - 1) = 0)
    (h2 : (B01 * I01 - 1) * (A01 * A12 * J02 - 1) = 0)
    (h3 : (B12 * I12 - 1) * (A01 * A12 * J02 - 1) = 0) :
    (B12 * I12 - 1) - (B02 * I02 - 1) + (B01 * I01 - 1) + (A01 * A12 * J02 - 1) = 0 := by
  subst hJ
  linear_combination (B01 * B12 * J02 * (A12 * I12)) * hA01 + (B01 * B12 * J02) * hA12 -
    (B01 * B12 * J02) * hB02 + (B02 * J02) * hcoc - h1 - h2 - h3 -
    (A01 * A12 * J02 - 1) * h1

section Simplices

variable {Y : Scheme.{u}} (K' : Y.OrderedAffineCover)

/-- The vertex `i` as a `0`-simplex. -/
def vtx (i : K'.ι) : K'.Idx 0 :=
  ⟨fun _ => i, fun a b hab => absurd hab (by
    have := a.isLt
    have := b.isLt
    rw [Fin.lt_def]
    omega)⟩

/-- The edge `i < j` as a `1`-simplex. -/
def edge (i j : K'.ι) (h : i < j) : K'.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr fun k => by
    fin_cases k
    simpa using h⟩

lemma le_inter_vtx (i : K'.ι) : K'.U i ≤ K'.inter (vtx K' i) :=
  le_iInf fun _ => le_rfl

lemma le_inter_edge (i j : K'.ι) (h : i < j) : K'.U i ⊓ K'.U j ≤ K'.inter (edge K' i j h) :=
  le_iInf fun k => by
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right

lemma face_edge_zero (i j : K'.ι) (h : i < j) : K'.face (edge K' i j h) 0 = vtx K' j :=
  Subtype.ext (funext fun k => by fin_cases k; rfl)

lemma face_edge_one (i j : K'.ι) (h : i < j) : K'.face (edge K' i j h) 1 = vtx K' i :=
  Subtype.ext (funext fun k => by fin_cases k; rfl)

lemma res_pr_edge (u : ∀ i j : K'.ι, Γ(Y, K'.U i ⊓ K'.U j)) (i j : K'.ι) (h : i < j) :
    Y.presheaf.map (homOfLE (le_inter_edge K' i j h)).op (pr K' u (edge K' i j h) 0 1) = u i j := by
  rw [pr, map_map_apply]
  change (Y.presheaf.map (𝟙 _)).hom (u i j) = u i j
  rw [CategoryTheory.Functor.map_id]
  rfl

variable {S : Type u} [CommRing S] (π : Y ⟶ Spec (CommRingCat.of S))

lemma d_zero_apply (c : (OModulePresheaf.unit π).cochain K' 0) (s : K'.Idx 1) :
    (show Γ(Y, K'.inter s) from (OModulePresheaf.unit π).d K' 0 c s) =
      (Y.presheaf.map (homOfLE (K'.inter_le_inter_face s 0)).op).hom (c (K'.face s 0)) -
        (Y.presheaf.map (homOfLE (K'.inter_le_inter_face s 1)).op).hom (c (K'.face s 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_zsmul, sub_eq_add_neg]
  rfl

end Simplices

/-- The ring identity behind the gauge relation, with two names for the same inverse. -/
lemma gauge_core' {T : Type*} [CommRing T] (H' Hpp Hr Hrinv Hrinv' bi bj : T)
    (hrel : H' * Hrinv - 1 = (bj - bi) + (Hpp * Hrinv' - 1)) (hI : Hrinv' = Hrinv)
    (hinv : Hr * Hrinv = 1) (hbb : bi * bj = 0) (hjj : bj * bj = 0) (hpi : (Hpp - Hr) * bi = 0)
    (hpj : (Hpp - Hr) * bj = 0) :
    (1 - bi) * Hpp = H' * (1 - bj) := by
  subst hI
  linear_combination (-1 : T) * hpi + hpj + Hr * hjj - Hr * hbb + (1 - bj) * H' * hinv -
    (1 - bj) * Hr * hrel - (1 - bj) * Hpp * hinv

section Core

variable [IsSeparated f] (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra P A]
  [IsScalarTower R P A] (χ : A₀ →ₐ[R] B) (q : A →ₐ[R] B)
  (hqρ : q.comp (IsScalarTower.toAlgHom R P A) = χ.comp (IsScalarTower.toAlgHom R P A₀))

omit [IsSeparated f] in
include hqρ in
lemma testCover_preimage_le (i : K.ι) :
    relMap f q ⁻¹ᵁ (testCover f K A).U i ≤ relMap f χ ⁻¹ᵁ (testCover f K A₀).U i := by
  change relMap f q ⁻¹ᵁ (relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ K.U i) ≤
    relMap f χ ⁻¹ᵁ (relMap f (IsScalarTower.toAlgHom R P A₀) ⁻¹ᵁ K.U i)
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← relMap_comp, ← relMap_comp, hqρ]

omit [IsSeparated f] in
include hqρ in
lemma testCover_pair_le (i j : K.ι) :
    relMap f q ⁻¹ᵁ (testCover f K A).U i ⊓ relMap f q ⁻¹ᵁ (testCover f K A).U j ≤
      (relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀)) ⁻¹ᵁ (K.U i ⊓ K.U j) := by
  change relMap f q ⁻¹ᵁ (relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ K.U i) ⊓
      relMap f q ⁻¹ᵁ (relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ K.U j) ≤ _
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← relMap_comp, ← relMap_comp, hqρ]
  exact le_rfl

lemma isAffineOpen_testCover_inf (i j : K.ι) :
    IsAffineOpen ((testCover f K A).U i ⊓ (testCover f K A).U j) := by
  have := isSeparated_relProj f A
  exact (isAffineHom_diagonal_iff (f := relProj f A)).mp inferInstance ⊤ (isAffineOpen_top _)
    _ (by simp) _ (by simp) ((testCover f K A).isAffineOpen i) ((testCover f K A).isAffineOpen j)

include hqρ in
/-- On pairwise intersections, the transition functions of `N` and the pushed family agree modulo
the kernel of `q`. -/
lemma pair_sub_mem (hq : Function.Surjective q)
    (h' : ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ)
    (hh' : CocycleGluing.pullbackCocycle (relMap f q) h' =
      pushUnits f K (relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀))
        (fun i => relMap f q ⁻¹ᵁ (testCover f K A).U i) (testCover_pair_le f K χ q hqρ) g)
    (i j : K.ι) :
    (h' i j : Γ(relSpace f A, _)) -
        (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g i j : Γ(relSpace f A, _)) ∈
      (RingHom.ker q.toRingHom).map
        (structureHom f A ((testCover f K A).U i ⊓ (testCover f K A).U j)).hom := by
  rw [← ker_appLE_eq_map f q hq _ (isAffineOpen_testCover_inf f K i j), RingHom.mem_ker, map_sub,
    sub_eq_zero]
  have h1 := congrArg (fun u => Units.val (u i j)) hh'
  refine h1.trans ?_
  change ((relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀)).appLE _ _ _).hom (g i j).val =
    (pairMapAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) i j ≫
      (relMap f q).appLE _ _ le_rfl).hom (g i j).val
  rw [pairMapAlong, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ : Γ(relSpace f P, K.U i ⊓ K.U j) ⟶ Γ(relSpace f B, _) =>
      φ.hom (g i j).val)
    (appLE_congr (by rw [← relMap_comp, ← relMap_comp, hqρ]) _ _ _ _)


omit [IsSeparated f] in
/-- The cocycle identity, restricted to a triple intersection of an ordered cover. -/
lemma pr_cocycle {Y : Scheme.{u}} (K' : Y.OrderedAffineCover)
    (u : ∀ i j : K'.ι, (Γ(Y, K'.U i ⊓ K'.U j))ˣ) (hu : CocycleGluing.IsCocycle u)
    (s : K'.Idx 2) :
    pr K' (uval K' u) s 0 1 * pr K' (uval K' u) s 1 2 = pr K' (uval K' u) s 0 2 :=
  CocycleGluing.cocycle_res u hu (s.1 0) (s.1 1) (s.1 2) _ _ _

section Cochain

variable {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]
  {M : Type u} [AddCommGroup M] [Module A₀ M] [Module P M] [IsScalarTower P A₀ M]

omit [IsSeparated f] [Module A₀ Q] [IsScalarTower P A₀ Q] [Module A₀ M] [IsScalarTower P A₀ M] in
include hqρ in
lemma exists_jM_eq (jQ : Q →ₗ[P] P) (hjQ0 : ∀ x, algebraMap P A₀ (jQ x) = 0) (jM : M →ₗ[P] A)
    (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a) (x : Q) :
    ∃ m, jM m = algebraMap P A (jQ x) := by
  refine (hjMr _).mp (RingHom.mem_ker.mpr ?_)
  have := congrArg (fun h : P →ₐ[R] B => h (jQ x)) hqρ
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
  change q (algebraMap P A (jQ x)) = 0
  rw [this, hjQ0, map_zero]

omit [IsSeparated f] in
include hqρ in
/-- The obstruction map `Q → M` of the chosen lift `P → A`: `jM (φ x) = ρ' (jQ x)`. -/
noncomputable def phiQ (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ0 : ∀ x, algebraMap P A₀ (jQ x) = 0) (jM : M →ₗ[P] A) (hjMinj : Function.Injective jM)
    (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a) : Q →ₗ[A₀] M where
  toFun x := (exists_jM_eq χ q hqρ jQ hjQ0 jM hjMr x).choose
  map_add' x y := hjMinj (by
    have h1 := (exists_jM_eq χ q hqρ jQ hjQ0 jM hjMr (x + y)).choose_spec
    have h2 := (exists_jM_eq χ q hqρ jQ hjQ0 jM hjMr x).choose_spec
    have h3 := (exists_jM_eq χ q hqρ jQ hjQ0 jM hjMr y).choose_spec
    rw [h1, map_add jM, h2, h3, map_add, map_add])
  map_smul' a x := by
    obtain ⟨p, rfl⟩ := hπ a
    apply hjMinj
    have h1 := (exists_jM_eq χ q hqρ jQ hjQ0 jM hjMr (algebraMap P A₀ p • x)).choose_spec
    have h2 := (exists_jM_eq χ q hqρ jQ hjQ0 jM hjMr x).choose_spec
    rw [h1, RingHom.id_apply, algebraMap_smul, algebraMap_smul, jM.map_smul, h2, jQ.map_smul,
      smul_eq_mul, map_mul, Algebra.smul_def]

omit [IsSeparated f] in
lemma jM_phiQ (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ0 : ∀ x, algebraMap P A₀ (jQ x) = 0) (jM : M →ₗ[P] A) (hjMinj : Function.Injective jM)
    (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a) (x : Q) :
    jM (phiQ χ q hqρ hπ jQ hjQ0 jM hjMinj hjMr x) = algebraMap P A (jQ x) :=
  (exists_jM_eq χ q hqρ jQ hjQ0 jM hjMr x).choose_spec

/-- The one-cochain `h' / h - 1` of the transition functions `h'` of `N` relative to the family
`g` pushed along `P → A`. -/
def cvec (h' : ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ)
    (σ : K.Idx 1) : Γ(relSpace f A, (testCover f K A).inter σ) :=
  pr (testCover f K A) (uval _ h') σ 0 1 *
    pr (testCover f K A) (uinv _ (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A)
      (fun _ => rfl) g)) σ 0 1 - 1

include hqρ in
lemma cvec_mem (hq : Function.Surjective q)
    (h' : ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ)
    (hh' : CocycleGluing.pullbackCocycle (relMap f q) h' =
      pushUnits f K (relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀))
        (fun i => relMap f q ⁻¹ᵁ (testCover f K A).U i) (testCover_pair_le f K χ q hqρ) g)
    (σ : K.Idx 1) :
    cvec f K g h' σ ∈ (RingHom.ker q.toRingHom).map
      (structureHom f A ((testCover f K A).inter σ)).hom := by
  have hone := pr_val_mul_pr_inv (testCover f K A)
    (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g) σ 0 1
  have e : cvec f K g h' σ =
      (pr (testCover f K A) (uval _ h') σ 0 1 - pr (testCover f K A)
        (uval _ (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g)) σ 0 1) *
      pr (testCover f K A) (uinv _ (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A)
        (fun _ => rfl) g)) σ 0 1 := by
    rw [cvec, sub_mul, hone]
  rw [e]
  refine Ideal.mul_mem_right _ _ ?_
  have hmem := res_mem_map f A
    (le_inf ((testCover f K A).inter_le σ 0) ((testCover f K A).inter_le σ 1))
    (RingHom.ker q.toRingHom) (pair_sub_mem f K g χ q hqρ hq h' hh' (σ.1 0) (σ.1 1))
  rwa [map_sub] at hmem

include hqρ in
lemma exists_cObs (hq : Function.Surjective q) (jM : M →ₗ[P] A)
    (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
    (h' : ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ)
    (hh' : CocycleGluing.pullbackCocycle (relMap f q) h' =
      pushUnits f K (relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀))
        (fun i => relMap f q ⁻¹ᵁ (testCover f K A).U i) (testCover_pair_le f K χ q hqρ) g) :
    ∃ c : cplx f K A₀ 1 ⊗[A₀] M, compMap f K jM 1 c =
      fun σ : K.Idx 1 => (cvec f K g h' σ : Γ(relSpace f A, (testCover f K A).inter σ)) :=
  (exists_compMap_eq_iff f K jM (RingHom.ker q.toRingHom) hjMr _).mpr
    fun σ => cvec_mem f K g χ q hqρ hq h' hh' σ

omit [IsSeparated f] [Module A₀ Q] [IsScalarTower P A₀ Q] [Module A₀ M] [IsScalarTower P A₀ M]
  [Algebra R P] [IsScalarTower R P A] in
lemma ker_sq_zero (jM : M →ₗ[P] A) (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
    (hjMsq : ∀ m m', jM m * jM m' = 0) :
    ∀ k ∈ RingHom.ker q.toRingHom, ∀ k' ∈ RingHom.ker q.toRingHom, k * k' = 0 := by
  intro k hk k' hk'
  obtain ⟨m, rfl⟩ := (hjMr k).mp hk
  obtain ⟨m', rfl⟩ := (hjMr k').mp hk'
  exact hjMsq m m'

omit [IsSeparated f] in
lemma res_cvec_face
    (h' : ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ)
    (s : K.Idx 2) (j : Fin 3) (a' b' : Fin 3) (ha : s.1 (j.succAbove 0) = s.1 a')
    (hb : s.1 (j.succAbove 1) = s.1 b') :
    (relSpace f A).presheaf.map (homOfLE ((testCover f K A).inter_le_inter_face s j)).op
        (cvec f K g h' ((testCover f K A).face s j)) =
      pr (testCover f K A) (uval _ h') s a' b' *
        pr (testCover f K A) (uinv _ (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A)
          (fun _ => rfl) g)) s a' b' - 1 := by
  unfold cvec
  rw [map_sub, map_mul, map_one, res_pr (testCover f K A) _ ((testCover f K A).face s j) s _ 0 1 a' b'
    ha hb, res_pr (testCover f K A) _ ((testCover f K A).face s j) s _ 0 1 a' b' ha hb]

include hqρ in
/-- The cocycle condition `d c + φ_* z = 0`, pointwise on triple intersections. -/
lemma cObs_cocycle_apply (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom)
    (hq : Function.Surjective q) (jM : M →ₗ[P] A) (hjMinj : Function.Injective jM)
    (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
    (hjMsq : ∀ m m', jM m * jM m' = 0)
    (h' : ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ)
    (hh' : CocycleGluing.pullbackCocycle (relMap f q) h' =
      pushUnits f K (relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀))
        (fun i => relMap f q ⁻¹ᵁ (testCover f K A).U i) (testCover_pair_le f K χ q hqρ) g)
    (hcoc : CocycleGluing.IsCocycle h') (c : cplx f K A₀ 1 ⊗[A₀] M)
    (hc : compMap f K jM 1 c =
      fun σ : K.Idx 1 => (cvec f K g h' σ : Γ(relSpace f A, (testCover f K A).inter σ)))
    (s : K.Idx 2) :
    (show Γ(relSpace f A, (testCover f K A).inter s) from
      compMap f K jM 2 ((dif f K A₀ 1).rTensor M c) s) +
      (show Γ(relSpace f A, (testCover f K A).inter s) from
        compMap f K jM 2 ((phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr).lTensor
          (cplx f K A₀ 2) (zObs f K jQ hjQ g hg)) s) = 0 := by
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
  rw [e1, e2, res_cvec_face f K g h' s 0 1 2 rfl rfl, res_cvec_face f K g h' s 1 0 2 rfl rfl,
    res_cvec_face f K g h' s 2 0 1 rfl rfl]
  unfold defect
  simp only [map_sub, map_mul, map_one]
  -- notation for the ring elements
  set T := testCover f K A with hT
  set hρ := pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g with hhρ
  have hI : ∀ k ∈ RingHom.ker q.toRingHom, ∀ k' ∈ RingHom.ker q.toRingHom, k * k' = 0 :=
    ker_sq_zero q jM hjMr hjMsq
  have hval : ∀ a b : Fin 3, pr T (uval T hρ) s a b = (secMap (A := A) f K s).hom (pr K (uval K g) s a b) :=
    fun a b => pr_pairUnitsAlong_val f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g s a b
  have hinv : ∀ a b : Fin 3, pr T (uinv T hρ) s a b = (secMap (A := A) f K s).hom (pr K (uinv K g) s a b) :=
    fun a b => pr_pairUnitsAlong_inv f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g s a b
  have hAI : ∀ a b : Fin 3, (secMap (A := A) f K s).hom (pr K (uval K g) s a b) *
      pr T (uinv T hρ) s a b = 1 := fun a b => by
    rw [← hval]
    exact pr_val_mul_pr_inv T hρ s a b
  -- membership of the differences in the extension of `ker q`
  have hx : ∀ a b : Fin 3, pr T (uval T h') s a b * pr T (uinv T hρ) s a b - 1 ∈
      (RingHom.ker q.toRingHom).map (structureHom f A (T.inter s)).hom := fun a b => by
    have hone := pr_val_mul_pr_inv T hρ s a b
    have e : pr T (uval T h') s a b * pr T (uinv T hρ) s a b - 1 =
        (pr T (uval T h') s a b - pr T (uval T hρ) s a b) * pr T (uinv T hρ) s a b := by
      rw [sub_mul, hone]
    rw [e]
    refine Ideal.mul_mem_right _ _ ?_
    have hmem := res_mem_map f A (le_inf (T.inter_le s a) (T.inter_le s b))
      (RingHom.ker q.toRingHom) (pair_sub_mem f K g χ q hqρ hq h' hh' (s.1 a) (s.1 b))
    rwa [map_sub] at hmem
  have hw : (secMap (A := A) f K s).hom (pr K (uval K g) s 0 1) *
        (secMap (A := A) f K s).hom (pr K (uval K g) s 1 2) *
        (secMap (A := A) f K s).hom (pr K (uinv K g) s 0 2) - 1 ∈
      (RingHom.ker q.toRingHom).map (structureHom f A (T.inter s)).hom := by
    have hmem := secMap_mem_map (A := A) f K _ s (hg s)
    unfold defect at hmem
    simp only [map_sub, map_mul, map_one] at hmem
    refine Ideal.map_mono ?_ hmem
    rw [Ideal.map_le_iff_le_comap]
    intro k hk
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun h : P →ₐ[R] B => h k) hqρ
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    change q (algebraMap P A k) = 0
    rw [this, RingHom.mem_ker.mp hk, map_zero]
  have hcoc' := pr_cocycle T h' hcoc s
  have hB02 := pr_val_mul_pr_inv T h' s 0 2
  exact dc_core' _ _ _ _ _ _ _ _ _ (pr T (uinv T h') s 0 2) (hAI 0 1) (hAI 1 2) hB02
    (by rw [hcoc']; exact hB02)
    (hinv 0 2).symm
    (mul_eq_zero_of_mem_map_sq _ _ hI (hx 0 1) (hx 1 2))
    (mul_eq_zero_of_mem_map_sq _ _ hI (hx 0 1) hw)
    (mul_eq_zero_of_mem_map_sq _ _ hI (hx 1 2) hw)

include hqρ in
/-- The cocycle condition `d c + φ_* z = 0`. -/
lemma cObs_cocycle [Flat f] (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom)
    (hq : Function.Surjective q) (jM : M →ₗ[P] A) (hjMinj : Function.Injective jM)
    (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
    (hjMsq : ∀ m m', jM m * jM m' = 0)
    (h' : ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ)
    (hh' : CocycleGluing.pullbackCocycle (relMap f q) h' =
      pushUnits f K (relMap f χ ≫ relMap f (IsScalarTower.toAlgHom R P A₀))
        (fun i => relMap f q ⁻¹ᵁ (testCover f K A).U i) (testCover_pair_le f K χ q hqρ) g)
    (hcoc : CocycleGluing.IsCocycle h') (c : cplx f K A₀ 1 ⊗[A₀] M)
    (hc : compMap f K jM 1 c =
      fun σ : K.Idx 1 => (cvec f K g h' σ : Γ(relSpace f A, (testCover f K A).inter σ))) :
    (dif f K A₀ 1).rTensor M c +
      (phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr).lTensor (cplx f K A₀ 2)
        (zObs f K jQ hjQ g hg) = 0 := by
  apply compMap_injective f K jM hjMinj 2
  rw [map_zero, map_add]
  funext s
  exact cObs_cocycle_apply f K g χ q hqρ hπ jQ hjQ hg hq jM hjMinj hjMr hjMsq h' hh' hcoc c hc s

end Cochain

section Lift

variable {M : Type u} [AddCommGroup M] [Module A₀ M] [Module P M] [IsScalarTower P A₀ M]
  {F : Type u} [AddCommGroup F] [Module A₀ F] [Module P F] [IsScalarTower P A₀ F] [Module R F]

omit [IsSeparated f] [IsScalarTower R P A] in
/-- The `P`-algebra map `Thick P F → A`, `(p, x) ↦ ρ' p + jM (D' x)`. -/
def evMap (jM : M →ₗ[P] A) (hjMsq : ∀ m m', jM m * jM m' = 0) (D' : F →ₗ[A₀] M) :
    Thick P F →ₐ[P] A :=
  { Thick.lift (algebraMap P A) ((jM : M →+ A).comp (D' : F →+ M))
      (fun p x => by
        change jM (D' (p • x)) = algebraMap P A p * jM (D' x)
        rw [← algebraMap_smul A₀ p x, D'.map_smul, algebraMap_smul, jM.map_smul,
          Algebra.smul_def])
      (fun x y => hjMsq (D' x) (D' y)) with
    commutes' := fun p => by
      change algebraMap P A (Thick.fst (algebraMap P (Thick P F) p)) +
        jM (D' (Thick.snd (algebraMap P (Thick P F) p))) = algebraMap P A p
      simp }

omit [IsSeparated f] [IsScalarTower R P A] in
lemma evMap_apply (jM : M →ₗ[P] A) (hjMsq : ∀ m m', jM m * jM m' = 0) (D' : F →ₗ[A₀] M)
    (x : Thick P F) :
    evMap jM hjMsq D' x = algebraMap P A (Thick.fst x) + jM (D' (Thick.snd x)) := rfl

/-- The corrected lift `ρ'' = ρ' + jM ∘ D' ∘ D : P → A`. -/
def rhoCorr (jM : M →ₗ[P] A) (hjMsq : ∀ m m', jM m * jM m' = 0) (D' : F →ₗ[A₀] M)
    (D : Derivation R P F) : P →ₐ[R] A :=
  ((evMap jM hjMsq D').restrictScalars R).comp (Thick.ofDerivation D)

omit [Algebra R A₀] [IsScalarTower R P A₀] in
lemma rhoCorr_apply (jM : M →ₗ[P] A) (hjMsq : ∀ m m', jM m * jM m' = 0) (D' : F →ₗ[A₀] M)
    (D : Derivation R P F) (p : P) :
    rhoCorr jM hjMsq D' D p = algebraMap P A p + jM (D' (D p)) := rfl

omit [IsSeparated f] [Algebra P A] [IsScalarTower R P A] in
/-- An `R`-algebra map `P → A` killing the kernel of the surjection `P → A₀` descends. -/
noncomputable def descendAlg (hπ : Function.Surjective (algebraMap P A₀)) (ρ : P →ₐ[R] A)
    (hρ : ∀ k, algebraMap P A₀ k = 0 → ρ k = 0) : A₀ →ₐ[R] A :=
  { (algebraMap P A₀).liftOfSurjective hπ ⟨ρ.toRingHom, fun k hk => hρ k hk⟩ with
    commutes' := fun r => by
      change (algebraMap P A₀).liftOfSurjective hπ ⟨ρ.toRingHom, _⟩ (algebraMap R A₀ r) = _
      rw [IsScalarTower.algebraMap_apply R P A₀, RingHom.liftOfSurjective_comp_apply]
      exact ρ.commutes r }

omit [IsSeparated f] [Algebra P A] [IsScalarTower R P A] in
lemma descendAlg_comp (hπ : Function.Surjective (algebraMap P A₀)) (ρ : P →ₐ[R] A)
    (hρ : ∀ k, algebraMap P A₀ k = 0 → ρ k = 0) :
    (descendAlg hπ ρ hρ).comp (IsScalarTower.toAlgHom R P A₀) = ρ :=
  AlgHom.ext fun p => RingHom.liftOfSurjective_comp_apply _ hπ _ p

omit [IsSeparated f] [Algebra R A₀] [IsScalarTower R P A₀] in
lemma secMapAlong_comp_testMap {A' : Type u} [CommRing A'] [Algebra R A'] [Algebra P A']
    [IsScalarTower R P A'] (s : P →ₐ[R] A')
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A') ⁻¹ᵁ V)
    (h : A' →ₐ[P] A)
    (hs' : ∀ V, relMap f ((h.restrictScalars R).comp s) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V) {p : ℕ} (σ : K.Idx p) :
    secMapAlong f K s hs σ ≫ testMap f K h σ = secMapAlong f K ((h.restrictScalars R).comp s) hs' σ := by
  rw [secMapAlong, testMap, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr (relMap_comp f s _).symm _ _ _ _

omit [IsSeparated f] [IsScalarTower R P A] in
lemma evMap_inr (jM : M →ₗ[P] A) (hjMsq : ∀ m m', jM m * jM m' = 0) (D' : F →ₗ[A₀] M) (x : F) :
    evMap jM hjMsq D' (Thick.inr x) = jM (D' x) := by
  rw [evMap_apply]
  simp

omit [Algebra R A₀] [IsScalarTower R P A₀] [IsSeparated f] in
lemma preimage_rhoCorr (q : A →ₐ[R] B) (hq : Function.Surjective q)
    (hn : IsNilpotent (RingHom.ker q.toRingHom)) (jM : M →ₗ[P] A)
    (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
    (hjMsq : ∀ m m', jM m * jM m' = 0) (D' : F →ₗ[A₀] M) (D : Derivation R P F)
    (V : (relSpace f P).Opens) :
    relMap f (rhoCorr jM hjMsq D' D) ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V := by
  refine preimage_relMap_eq f _ _ q (AlgHom.ext fun p => ?_) ?_ V
  · change q (algebraMap P A p + jM (D' (D p))) = q (algebraMap P A p)
    have hk : q (jM (D' (D p))) = 0 := RingHom.mem_ker.mp ((hjMr _).mpr ⟨_, rfl⟩)
    rw [map_add, hk, add_zero]
  · exact surjective_relMap f q hq fun x hx => by
      obtain ⟨n, hn⟩ := hn
      refine ⟨n, ?_⟩
      have : x ^ n ∈ RingHom.ker q.toRingHom ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at this
      exact Ideal.mem_bot.mp this

omit [Algebra R A₀] [IsScalarTower R P A₀] in
/-- The pushed first obstruction cochain is the cochain of the corrected lift. -/
lemma compMap_thetaObs_ev (q : A →ₐ[R] B) (hq : Function.Surjective q)
    (hn : IsNilpotent (RingHom.ker q.toRingHom)) (jM : M →ₗ[P] A)
    (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
    (hjMsq : ∀ m m', jM m * jM m' = 0) (D' : F →ₗ[A₀] M) (D : Derivation R P F)
    (σ : K.Idx 1) :
    (show Γ(relSpace f A, (testCover f K A).inter σ) from
      compMap f K jM 1 (D'.lTensor (cplx f K A₀ 1) (thetaObs (A₀ := A₀) f K D g)) σ) =
      (secMapAlong f K (rhoCorr jM hjMsq D' D)
          (preimage_rhoCorr f q hq hn jM hjMr hjMsq D' D) σ).hom (pr K (uval K g) σ 0 1) *
        (secMap (A := A) f K σ).hom (pr K (uinv K g) σ 0 1) - 1 := by
  have hnat := compMap_natural f K (Thick.inr : F →ₗ[P] Thick P F) jM (evMap jM hjMsq D') D'
    (fun x => (evMap_inr jM hjMsq D' x).symm) (thetaObs (A₀ := A₀) f K D g) σ
  refine hnat.symm.trans ?_
  refine (congrArg (testMap f K (evMap jM hjMsq D') σ).hom
    (congrFun (compMap_thetaObs (A₀ := A₀) f K D g) σ)).trans ?_
  unfold thetaCochain
  rw [map_sub, map_mul, map_one]
  have e₁ := ConcreteCategory.congr_hom (secMapAlong_comp_testMap f K (Thick.ofDerivation D)
    (preimage_ofDerivation f D) (evMap jM hjMsq D')
    (preimage_rhoCorr f q hq hn jM hjMr hjMsq D' D) σ) (pr K (uval K g) σ 0 1)
  have e₂ := ConcreteCategory.congr_hom (secMap_comp_testMap f K (evMap jM hjMsq D') σ)
    (pr K (uinv K g) σ 0 1)
  exact congrArg₂ (fun a b => a * b - 1) e₁ e₂

omit [IsSeparated f] [Algebra R A₀] [IsScalarTower R P A₀] [IsScalarTower R P A] in
lemma res_cochain_congr {S : Type u} [CommRing S] {Y : Scheme.{u}} (π : Y ⟶ Spec (CommRingCat.of S))
    {K' : Y.OrderedAffineCover} (c : (OModulePresheaf.unit π).cochain K' 0) {τ τ' : K'.Idx 0}
    (hτ : τ = τ') {W : Y.Opens} (h : W ≤ K'.inter τ) (h' : W ≤ K'.inter τ') :
    (Y.presheaf.map (homOfLE h).op).hom (c τ) = (Y.presheaf.map (homOfLE h').op).hom (c τ') := by
  subst hτ
  rfl

/-- The value at a vertex of a degree-zero cochain, on the corresponding open. -/
def bvtx (bv : (OModulePresheaf.unit (relProj f A)).cochain (testCover f K A) 0) (i : K.ι) :
    Γ(relSpace f A, (testCover f K A).U i) :=
  ((relSpace f A).presheaf.map (homOfLE (le_inter_vtx (testCover f K A) i)).op).hom
    (bv (vtx (testCover f K A) i))

omit [Algebra R A₀] [IsScalarTower R P A₀] in
/-- The gauge relation on the intersection of an edge. -/
lemma gauge_sigma [Flat f] (hq : Function.Surjective q) (hn : IsNilpotent (RingHom.ker q.toRingHom))
    (jM : M →ₗ[P] A) (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
    (hjMsq : ∀ m m', jM m * jM m' = 0) (D' : F →ₗ[A₀] M) (D : Derivation R P F)
    (h' : ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ)
    (c : cplx f K A₀ 1 ⊗[A₀] M)
    (hc : compMap f K jM 1 c =
      fun σ : K.Idx 1 => (cvec f K g h' σ : Γ(relSpace f A, (testCover f K A).inter σ)))
    (b : cplx f K A₀ 0 ⊗[A₀] M)
    (hbc : c = (dif f K A₀ 0).rTensor M b + D'.lTensor (cplx f K A₀ 1)
      (thetaObs (A₀ := A₀) f K D g)) (σ : K.Idx 1) :
    (1 - (relSpace f A).presheaf.map
        (homOfLE ((testCover f K A).inter_le_inter_face σ 1)).op
          (compMap f K jM 0 b ((testCover f K A).face σ 1))) *
      (secMapAlong f K (rhoCorr jM hjMsq D' D)
        (preimage_rhoCorr f q hq hn jM hjMr hjMsq D' D) σ).hom (pr K (uval K g) σ 0 1) =
    pr (testCover f K A) (uval _ h') σ 0 1 *
      (1 - (relSpace f A).presheaf.map
        (homOfLE ((testCover f K A).inter_le_inter_face σ 0)).op
          (compMap f K jM 0 b ((testCover f K A).face σ 0))) := by
  have hI := ker_sq_zero q jM hjMr hjMsq
  have hσ : (show Γ(relSpace f A, (testCover f K A).inter σ) from compMap f K jM 1 c σ) =
      (show Γ(relSpace f A, (testCover f K A).inter σ) from
        compMap f K jM 1 ((dif f K A₀ 0).rTensor M b) σ) +
      (show Γ(relSpace f A, (testCover f K A).inter σ) from
        compMap f K jM 1 (D'.lTensor (cplx f K A₀ 1) (thetaObs (A₀ := A₀) f K D g)) σ) :=
    (congrArg (fun y => (compMap f K jM 1 y) σ) hbc).trans (congrFun (map_add _ _ _) σ)
  have e1 : (show Γ(relSpace f A, (testCover f K A).inter σ) from compMap f K jM 1 c σ) =
      cvec f K g h' σ := congrFun hc σ
  have e2 := (congrFun (compMap_dif f K jM 0 b) σ).trans
    (d_zero_apply (testCover f K A) (relProj f A) _ σ)
  have e3 := compMap_thetaObs_ev f K g q hq hn jM hjMr hjMsq D' D σ
  have hrel := e1.symm.trans (hσ.trans (congrArg₂ (· + ·) e2 e3))
  unfold cvec at hrel
  -- membership facts
  have hbv : ∀ τ, (compMap f K jM 0 b τ : Γ(relSpace f A, _)) ∈
      (RingHom.ker q.toRingHom).map (structureHom f A ((testCover f K A).inter τ)).hom :=
    (exists_compMap_eq_iff f K jM (RingHom.ker q.toRingHom) hjMr _).mp ⟨b, rfl⟩
  have hb : ∀ k : Fin 2, (relSpace f A).presheaf.map
      (homOfLE ((testCover f K A).inter_le_inter_face σ k)).op
        (compMap f K jM 0 b ((testCover f K A).face σ k)) ∈
      (RingHom.ker q.toRingHom).map (structureHom f A ((testCover f K A).inter σ)).hom :=
    fun k => res_mem_map f A _ _ (hbv _)
  have hpp := secMapAlong_sub_mem f K (rhoCorr jM hjMsq D' D)
    (IsScalarTower.toAlgHom R P A) (preimage_rhoCorr f q hq hn jM hjMr hjMsq D' D)
    (fun _ => rfl) q hq (AlgHom.ext fun p => by
      change q (algebraMap P A p + jM (D' (D p))) = q (algebraMap P A p)
      have hk : q (jM (D' (D p))) = 0 := RingHom.mem_ker.mp ((hjMr _).mpr ⟨_, rfl⟩)
      rw [map_add, hk, add_zero]) σ (pr K (uval K g) σ 0 1)
  have hval := pr_pairUnitsAlong_val f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g σ 0 1
  have hinv := pr_pairUnitsAlong_inv f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g σ 0 1
  rw [← hval] at hpp
  exact gauge_core' _ _ _ _ _ _ _ hrel hinv.symm
    (pr_val_mul_pr_inv (testCover f K A)
      (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) g) σ 0 1)
    (mul_eq_zero_of_mem_map_sq _ _ hI (hb 1) (hb 0))
    (mul_eq_zero_of_mem_map_sq _ _ hI (hb 0) (hb 0))
    (mul_eq_zero_of_mem_map_sq _ _ hI hpp (hb 1))
    (mul_eq_zero_of_mem_map_sq _ _ hI hpp (hb 0))

omit [Algebra R A₀] [IsScalarTower R P A₀] in
/-- The gauge relation on pairwise intersections. -/
lemma gauge_pair [Flat f] (hq : Function.Surjective q) (hn : IsNilpotent (RingHom.ker q.toRingHom))
    (jM : M →ₗ[P] A) (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
    (hjMsq : ∀ m m', jM m * jM m' = 0) (D' : F →ₗ[A₀] M) (D : Derivation R P F)
    (h' : ∀ i j : K.ι, (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ)
    (c : cplx f K A₀ 1 ⊗[A₀] M)
    (hc : compMap f K jM 1 c =
      fun σ : K.Idx 1 => (cvec f K g h' σ : Γ(relSpace f A, (testCover f K A).inter σ)))
    (b : cplx f K A₀ 0 ⊗[A₀] M)
    (hbc : c = (dif f K A₀ 0).rTensor M b + D'.lTensor (cplx f K A₀ 1)
      (thetaObs (A₀ := A₀) f K D g)) (i j : K.ι) (hij : i < j) :
    (relSpace f A).presheaf.map (homOfLE (inf_le_left : (testCover f K A).U i ⊓
        (testCover f K A).U j ≤ (testCover f K A).U i)).op
        (1 - bvtx f K (compMap f K jM 0 b) i) *
      (pairUnitsAlong f K (rhoCorr jM hjMsq D' D)
        (preimage_rhoCorr f q hq hn jM hjMr hjMsq D' D) g i j : Γ(relSpace f A, _)) =
    (h' i j : Γ(relSpace f A, _)) *
      (relSpace f A).presheaf.map (homOfLE (inf_le_right : (testCover f K A).U i ⊓
        (testCover f K A).U j ≤ (testCover f K A).U j)).op
        (1 - bvtx f K (compMap f K jM 0 b) j) := by
  set T := testCover f K A with hT
  set σ : K.Idx 1 := edge T i j hij with hσ
  have key := congrArg ((relSpace f A).presheaf.map (homOfLE (le_inter_edge T i j hij)).op).hom
    (gauge_sigma f K g q hq hn jM hjMr hjMsq D' D h' c hc b hbc σ)
  simp only [map_mul, map_sub, map_one] at key
  have hval := pr_pairUnitsAlong_val f K (rhoCorr jM hjMsq D' D)
    (preimage_rhoCorr f q hq hn jM hjMr hjMsq D' D) g σ 0 1
  rw [← hval, res_pr_edge, res_pr_edge] at key
  rw [map_sub, map_one, map_sub, map_one]
  unfold bvtx
  rw [map_map_apply, map_map_apply]
  rw [map_map_apply, map_map_apply] at key
  rw [res_cochain_congr (relProj f A) (compMap f K jM 0 b) (face_edge_one T i j hij).symm
      (inf_le_left.trans (le_inter_vtx T i)) _,
    res_cochain_congr (relProj f A) (compMap f K jM 0 b) (face_edge_zero T i j hij).symm
      (inf_le_right.trans (le_inter_vtx T j)) _]
  exact key

end Lift

lemma id_appLE_apply {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) (x : Γ(Y, U)) :
    ((𝟙 Y : Y ⟶ Y).appLE U V h).hom x = (Y.presheaf.map (homOfLE h).op).hom x := by
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]

section Main

variable {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]
  {M : Type u} [AddCommGroup M] [Module A₀ M] [Module P M] [IsScalarTower P A₀ M]
  {F : Type u} [AddCommGroup F] [Module A₀ F] [Module P F] [IsScalarTower P A₀ F] [Module R F]

open Langlands.Cohomology.ModuleComplex.ObstructionCone

set_option maxHeartbeats 1000000 in
include hqρ in
/-- **Sufficiency.** If the obstruction cone has vanishing first cohomology with coefficients in
the kernel `M` of `q : A → B`, every isomorphism on `relSpace f B` between a pullback of `L₀`
and the reduction of a line bundle `N` on `relSpace f A` lifts. -/
theorem exists_lift [Flat f] (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom)
    (D : Derivation R P F)
    {L₀ : LineBundle (relSpace f A₀)} (e : ∀ i, Γ(L₀.obj, (testCover f K A₀).U i))
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover f K A₀).U i))
    (hge : IsTransition e
      (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
        (fun _ _ => le_rfl) g))
    (hq : Function.Surjective q) (hn : IsNilpotent (RingHom.ker q.toRingHom))
    (jM : M →ₗ[P] A) (hjMinj : Function.Injective jM)
    (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
    (hjMsq : ∀ m m', jM m * jM m' = 0)
    (hH : HOneVanishes (cplx f K A₀) (dif f K A₀) (deltaMap hπ jQ (hjQ0_of jQ hjQ) D)
      (thetaObs (A₀ := A₀) f K D g) (zObs f K jQ hjQ g hg) M)
    (N : LineBundle (relSpace f A))
    (φ : (Scheme.Modules.pullback (relMap f χ)).obj L₀.obj ≅
      (Scheme.Modules.pullback (relMap f q)).obj N.obj) :
    ∃ (χ' : A₀ →ₐ[R] A) (hχ' : q.comp χ' = χ)
      (ψ : (Scheme.Modules.pullback (relMap f χ')).obj L₀.obj ≅
        (Scheme.Modules.pullback (𝟙 (relSpace f A))).obj N.obj),
      Langlands.Scheme.Modules.LineBundleFlatDescent.tr (relMap f q)
        (by rw [← relMap_comp, hχ']) (Category.comp_id _) ψ.hom = φ.hom := by
  -- frames of `N`
  obtain ⟨fr, hfr, hcoord⟩ := exists_frames_lift f K e he χ q hq hn N φ (testCover f K A).U
    (testCover f K A).isAffineOpen (testCover_preimage_le f K χ q hqρ)
  set h' := CocycleGluing.frameCocycle fr hfr with hh'def
  have hh' := pullbackCocycle_frameCocycle_eq f K (g := g) (e := e) (hge := hge) (χ := χ) (q := q)
    (N := N) (φ := φ) (U := (testCover f K A).U) (hle := testCover_preimage_le f K χ q hqρ)
    (fr := fr) (hfr := hfr) (hcoord := hcoord) (hW := testCover_pair_le f K χ q hqρ)
  have hcoc : CocycleGluing.IsCocycle h' :=
    CocycleGluing.isCocycle_of_isTransition hfr (CocycleGluing.isTransition_frameCocycle hfr)
  -- the one-cochain and its cocycle condition
  obtain ⟨c, hc⟩ := exists_cObs f K g χ q hqρ hq jM hjMr h' hh'
  have hcc := cObs_cocycle f K g χ q hqρ hπ jQ hjQ hg hq jM hjMinj hjMr hjMsq h' hh' hcoc c hc
  -- vanishing of the obstruction cohomology
  obtain ⟨b, D', hbc, hφD⟩ := hH c (phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr) hcc
  have hI := ker_sq_zero q jM hjMr hjMsq
  have hqjM : ∀ m, q (jM m) = 0 := fun m => RingHom.mem_ker.mp ((hjMr _).mpr ⟨m, rfl⟩)
  -- the corrected lift `ρ''` and its descent `χ'`
  have hρ''ker : ∀ k, algebraMap P A₀ k = 0 → rhoCorr jM hjMsq D' D k = 0 := by
    intro k hk
    obtain ⟨x, rfl⟩ := (hjQ k).mp (RingHom.mem_ker.mpr hk)
    rw [rhoCorr_apply, ← jM_phiQ χ q hqρ hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr x, ← map_add]
    have := congrArg (fun φ' : Q →ₗ[A₀] M => φ' x) hφD
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      deltaMap_apply] at this
    rw [this, map_zero]
  set χ' := descendAlg hπ (rhoCorr jM hjMsq D' D) hρ''ker with hχ'def
  have hχ'comp : χ'.comp (IsScalarTower.toAlgHom R P A₀) = rhoCorr jM hjMsq D' D :=
    descendAlg_comp hπ _ hρ''ker
  have hχ' : q.comp χ' = χ := by
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hπ a
    have h1 := congrArg (fun h : P →ₐ[R] A => q (h p)) hχ'comp
    have h2 := congrArg (fun h : P →ₐ[R] B => h p) hqρ
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2
    rw [AlgHom.comp_apply, h1, rhoCorr_apply, map_add, hqjM, add_zero, h2]
  refine ⟨χ', hχ', ?_⟩
  -- frames of the pullback of `L₀` and of `N` on the test cover
  have hs : ∀ V, relMap f (χ'.comp (IsScalarTower.toAlgHom R P A₀)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V := by
    rw [hχ'comp]
    exact preimage_rhoCorr f q hq hn jM hjMr hjMsq D' D
  set T := testCover f K A with hT
  have hu : ∀ i, T.U i ≤ relMap f χ' ⁻¹ᵁ (testCover f K A₀).U i :=
    testCover_le_preimage f K χ' hs
  set sF : ∀ i, Γ((Scheme.Modules.pullback (relMap f χ')).obj L₀.obj, T.U i) := fun i =>
    ((Scheme.Modules.pullback (relMap f χ')).obj L₀.obj).presheaf.map (homOfLE (hu i)).op
      (Scheme.Modules.pullbackLocalSection (relMap f χ') (e i)) with hsF
  have hsF_frame : ∀ i, Scheme.Modules.IsFrameOn (sF i) (T.U i) := fun i =>
    (((he i).pullbackLocalSection (relMap f χ')).map (homOfLE (hu i))).mono (hu i)
  have hW' : ∀ i j, T.U i ⊓ T.U j ≤
      (relMap f χ' ≫ relMap f (IsScalarTower.toAlgHom R P A₀)) ⁻¹ᵁ (K.U i ⊓ K.U j) := by
    intro i j
    rw [← relMap_comp, hχ'comp]
    exact pair_le f K _ (preimage_rhoCorr f q hq hn jM hjMr hjMsq D' D) i j
  have hsF_trans := isTransition_pullback_push f K (relMap f (IsScalarTower.toAlgHom R P A₀))
    (testCover f K A₀).U (fun _ _ => le_rfl) e g hge (relMap f χ') T.U hu hW'
  set tF : ∀ i, Γ((Scheme.Modules.pullback (𝟙 (relSpace f A))).obj N.obj, T.U i) := fun i =>
    Scheme.Modules.pullbackLocalSection (𝟙 (relSpace f A)) (fr i) with htF
  have htF_frame : ∀ i, Scheme.Modules.IsFrameOn (tF i) (T.U i) := fun i =>
    (hfr i).pullbackLocalSection (𝟙 (relSpace f A))
  have htF_trans := LineHom.isTransition_pullback (𝟙 (relSpace f A))
    (CocycleGluing.isTransition_frameCocycle hfr)
  have hTcov : (⨆ i, T.U i) = ⊤ := T.iSup_eq_top
  -- the gauge family `1 - b`
  have hbv : ∀ τ, (compMap f K jM 0 b τ : Γ(relSpace f A, _)) ∈
      (RingHom.ker q.toRingHom).map (structureHom f A (T.inter τ)).hom :=
    (exists_compMap_eq_iff f K jM (RingHom.ker q.toRingHom) hjMr _).mp ⟨b, rfl⟩
  have hbvtx : ∀ i, bvtx f K (compMap f K jM 0 b) i ∈
      (RingHom.ker q.toRingHom).map (structureHom f A (T.U i)).hom :=
    fun i => res_mem_map f A (le_inter_vtx T i) _ (hbv _)
  set av : ∀ i, Γ(relSpace f A, T.U i) := fun i => 1 - bvtx f K (compMap f K jM 0 b) i with hav
  have hav_unit : ∀ i, IsUnit (av i) := fun i => by
    have hsq := mul_eq_zero_of_mem_map_sq _ _ hI (hbvtx i) (hbvtx i)
    refine isUnit_iff_exists_inv.mpr ⟨1 + bvtx f K (compMap f K jM 0 b) i, ?_⟩
    rw [hav]
    linear_combination (-1 : Γ(relSpace f A, T.U i)) * hsq
  have hcocα := CocycleGluing.isCocycle_of_isTransition hsF_frame hsF_trans
  have hcocβ := CocycleGluing.isCocycle_of_isTransition htF_frame htF_trans
  have hgauge := (LineHom.isGaugeFamily_iff_of_lt hcocα hcocβ av).mpr fun i j hij => by
    have hp := gauge_pair f K g q hq hn jM hjMr hjMsq D' D h' c hc b hbc i j hij
    have hα := congrArg (fun u => Units.val (u i j))
      (pushUnits_congr f K (w' := relMap f (rhoCorr jM hjMsq D' D))
        (by rw [← relMap_comp, hχ'comp]) T.U hW'
        (pair_le f K _ (preimage_rhoCorr f q hq hn jM hjMr hjMsq D' D)) g)
    have hβ : Units.val (CocycleGluing.pullbackCocycle (𝟙 (relSpace f A)) h' i j) =
        Units.val (h' i j) := by
      rw [CocycleGluing.pullbackCocycle_val, id_appLE_apply]
      change (relSpace f A).presheaf.map (𝟙 _) _ = _
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [hα, hβ]
    exact hp
  -- the isomorphism `ψ`
  obtain ⟨ψ, hψ⟩ := exists_iso_of_gauge hTcov hsF_frame htF_frame hsF_trans htF_trans av hgauge
    hav_unit
  refine ⟨ψ, ?_⟩
  have hWcov : (⨆ i, relMap f q ⁻¹ᵁ T.U i) = ⊤ := LineHom.iSup_preimage_eq_top (relMap f q) hTcov
  have hle := testCover_preimage_le f K χ q hqρ
  have h1 : ∀ i, HasCoord ψ.hom (e i) (fr i) (hu i)
      (le_rfl : T.U i ≤ 𝟙 (relSpace f A) ⁻¹ᵁ T.U i) (av i) := fun i => by
    unfold HasCoord
    exact (hψ i).trans (congrArg (av i • ·)
      (CocycleGluing.mres_self (M := (Scheme.Modules.pullback (𝟙 (relSpace f A))).obj N.obj)
        (le_rfl : T.U i ≤ T.U i) (tF i)).symm)
  have hone : ∀ i, ((relMap f q).appLE (T.U i) (relMap f q ⁻¹ᵁ T.U i) le_rfl).hom (av i) = 1 :=
    fun i => by
      have hmem := hbvtx i
      rw [← ker_appLE_eq_map f q hq (T.U i) (T.isAffineOpen i), RingHom.mem_ker] at hmem
      rw [hav, map_sub, map_one, hmem, sub_zero]
  exact tr_eq_of_hasCoord (relMap f q) _ _ ψ.hom φ.hom (testCover f K A₀).U T.U e he fr hfr T.U hu
    (fun _ => le_rfl) av h1 (fun i => relMap f q ⁻¹ᵁ T.U i) hWcov (fun _ => le_rfl) hle
    (fun _ => le_rfl) hcoord hone

end Main

end Core

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

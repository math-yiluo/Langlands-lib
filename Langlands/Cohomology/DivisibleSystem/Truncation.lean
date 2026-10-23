import Langlands.Cohomology.DivisibleSystem.Resolution

/-!
# Truncated `ℓ`-divisible systems of resolutions

Harris 1999, §2, p.305, truncates the resolutions `F_m` of Lemma 2.2 in degree `D + 1`,
`G_m = τ_{≤ D+1}(F_m)`, where `τ_{≤ n}(C)^j` is `C^j` for `j < n`, the kernel of
`C^n ⟶ C^(n + 1)` for `j = n` and `0` for `j > n`; by Lemma 2.2 bis the `G^q_m` form
`ℓ`-divisible systems.

This file truncates a sequence of `ℓ`-divisible systems with differentials, as in
`Langlands.Cohomology.DivisibleSystem.ofDegrees`, in degree `D + 1`. The degree-`(D + 1)`
term is a given system `Z` with morphisms `p : S D ⟶ Z` and `ι : Z ⟶ S (D + 1)`, `ι`
levelwise monic, `p ≫ ι = d D` and `ι ≫ d (D + 1) = 0`. The result is an `ℓ`-divisible
system of cochain complexes, zero in degrees above `D + 1`, with a morphism to the
untruncated system that is a quasi-isomorphism in degrees `≤ D` at every level. For the
resolutions of `Langlands.Cohomology.DivisibleSystem.resolutionSystem` the system `Z` is the
residual system `R (D + 1)`, whose levels embed into `F^(D + 1)` as kernels of the
differentials `F^(D + 1) ⟶ F^(D + 2)`; every level of the truncation is then exact in positive
degrees and the morphism is a quasi-isomorphism at every level. These quasi-isomorphisms are of
complexes in `C`; acyclicity and complexes of sections are not treated here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe v u

namespace DivisibleSystem

section Zero

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}

variable (C ℓ) in
/-- The zero `ℓ`-divisible system: every level is the zero object. -/
def zeroSystem : DivisibleSystem C ℓ where
  tower := (Functor.const ℕᵒᵖ).obj 0
  inclusion _ := 0
  powSMul_eq_zero _ := (isZero_zero C).eq_of_src _ _
  inclusion_comp _ := (isZero_zero C).eq_of_src _ _
  shortExact _ :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
      mono_f := (isZero_zero C).mono _
      epi_g := (isZero_zero C).epi _ }
  torsion_exact _ := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
  flat _ _ := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)

lemma isZero_zeroSystem_tower_obj (m : ℕᵒᵖ) : IsZero ((zeroSystem C ℓ).tower.obj m) :=
  isZero_zero C

/-- The morphism from the zero system. -/
def fromZeroSystem (T : DivisibleSystem C ℓ) : zeroSystem C ℓ ⟶ T where
  tower :=
    { app := fun _ => 0
      naturality := fun _ _ _ => (isZero_zero C).eq_of_src _ _ }
  comm _ := (isZero_zero C).eq_of_src _ _

/-- The morphism to the zero system. -/
def toZeroSystem (T : DivisibleSystem C ℓ) : T ⟶ zeroSystem C ℓ where
  tower :=
    { app := fun _ => 0
      naturality := fun _ _ _ => (isZero_zero C).eq_of_tgt _ _ }
  comm _ := (isZero_zero C).eq_of_tgt _ _

lemma eqToHom_tower_app {T T' : DivisibleSystem C ℓ} (h : T = T') (m : ℕᵒᵖ) :
    (eqToHom h).tower.app m = eqToHom (by rw [h]) := by
  subst h
  rfl

end Zero

section OfDegreesHom

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
  {S S' : ℕ → DivisibleSystem C ℓ} {d : ∀ q, S q ⟶ S (q + 1)} {d' : ∀ q, S' q ⟶ S' (q + 1)}
  (sq : ∀ q m, (d q).tower.app m ≫ (d (q + 1)).tower.app m = 0)
  (sq' : ∀ q m, (d' q).tower.app m ≫ (d' (q + 1)).tower.app m = 0)
  (f : ∀ q, S q ⟶ S' q)
  (hf : ∀ q m, (f q).tower.app m ≫ (d' q).tower.app m = (d q).tower.app m ≫ (f (q + 1)).tower.app m)

/-- The chain map at level `m` with components `f q`. -/
def levelHom (m : ℕᵒᵖ) : levelComplex S d sq m ⟶ levelComplex S' d' sq' m :=
  CochainComplex.ofHom (fun q => (f q).tower.app m) (fun q => by
    rw [levelComplex_d, levelComplex_d]
    exact hf q m)

/-- The morphism of systems of cochain complexes with degree-`q` component `f q`. -/
def ofDegreesHom : ofDegrees S d sq ⟶ ofDegrees S' d' sq' where
  tower :=
    { app := fun m => levelHom sq sq' f hf m
      naturality := fun _ _ g => by
        ext q
        exact (f q).tower.naturality g }
  comm h := by
    ext q
    exact (f q).comm h

lemma ofDegreesHom_tower_app_f (m : ℕᵒᵖ) (q : ℕ) :
    ((ofDegreesHom sq sq' f hf).tower.app m).f q = (f q).tower.app m :=
  rfl

end OfDegreesHom

section Truncation

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
  (S : ℕ → DivisibleSystem C ℓ) (d : ∀ q, S q ⟶ S (q + 1))
  (sq : ∀ q m, (d q).tower.app m ≫ (d (q + 1)).tower.app m = 0)
  (D : ℕ) (Z : DivisibleSystem C ℓ) (p : S D ⟶ Z) (ι : Z ⟶ S (D + 1))

/-- The degree-`q` system of the truncation in degree `D + 1`: `S q` for `q ≤ D`, `Z` for
`q = D + 1` and the zero system above. -/
def truncationTerm (q : ℕ) : DivisibleSystem C ℓ :=
  if q ≤ D then S q else if q = D + 1 then Z else zeroSystem C ℓ

lemma truncationTerm_of_le {q : ℕ} (h : q ≤ D) : truncationTerm S D Z q = S q := by
  rw [truncationTerm, ite_eq_left h]

lemma truncationTerm_of_eq {q : ℕ} (h : q = D + 1) : truncationTerm S D Z q = Z := by
  rw [truncationTerm, ite_eq_right (by omega), ite_eq_left h]

lemma truncationTerm_of_lt {q : ℕ} (h : D + 1 < q) :
    truncationTerm S D Z q = zeroSystem C ℓ := by
  rw [truncationTerm, ite_eq_right (by omega), ite_eq_right (by omega)]

lemma isZero_truncationTerm_tower_obj {q : ℕ} (h : D + 1 < q) (m : ℕᵒᵖ) :
    IsZero ((truncationTerm S D Z q).tower.obj m) := by
  rw [truncationTerm_of_lt S D Z h]
  exact isZero_zero C

/-- The differentials of the truncation: `d q` for `q < D`, `p` for `q = D` and zero
above. -/
def truncationDifferential (q : ℕ) : truncationTerm S D Z q ⟶ truncationTerm S D Z (q + 1) :=
  if h : q < D then
    eqToHom (truncationTerm_of_le S D Z h.le) ≫ d q ≫
      eqToHom (truncationTerm_of_le S D Z (Nat.succ_le_of_lt h)).symm
  else if h' : q = D then
    eqToHom ((truncationTerm_of_le S D Z h'.le).trans (congrArg S h')) ≫ p ≫
      eqToHom (truncationTerm_of_eq S D Z (congrArg (· + 1) h')).symm
  else
    toZeroSystem _ ≫ eqToHom (truncationTerm_of_lt S D Z (by omega)).symm

lemma truncationDifferential_tower_app_of_lt {q : ℕ} (h : q < D) (m : ℕᵒᵖ) :
    (truncationDifferential S d D Z p q).tower.app m =
      eqToHom (by rw [truncationTerm_of_le S D Z h.le]) ≫ (d q).tower.app m ≫
        eqToHom (by rw [truncationTerm_of_le S D Z (Nat.succ_le_of_lt h)]) := by
  rw [truncationDifferential, dite_eq_left h]
  simp only [comp_tower, NatTrans.comp_app, eqToHom_tower_app]

lemma truncationDifferential_tower_app_self (m : ℕᵒᵖ) :
    (truncationDifferential S d D Z p D).tower.app m =
      eqToHom (by rw [truncationTerm_of_le S D Z le_rfl]) ≫ p.tower.app m ≫
        eqToHom (by rw [truncationTerm_of_eq S D Z rfl]) := by
  rw [truncationDifferential, dite_eq_right (lt_irrefl D), dite_eq_left rfl]
  simp only [comp_tower, NatTrans.comp_app, eqToHom_tower_app]

variable [∀ m, Mono (ι.tower.app m)]
  (hpι : ∀ m, p.tower.app m ≫ ι.tower.app m = (d D).tower.app m)

include sq hpι in
lemma truncationDifferential_comp_tower_app (q : ℕ) (m : ℕᵒᵖ) :
    (truncationDifferential S d D Z p q).tower.app m ≫
      (truncationDifferential S d D Z p (q + 1)).tower.app m = 0 := by
  rcases lt_trichotomy (q + 1) D with h | h | h
  · rw [truncationDifferential_tower_app_of_lt S d D Z p (by omega : q < D),
      truncationDifferential_tower_app_of_lt S d D Z p h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (sq q m), zero_comp, comp_zero]
  · subst h
    have h₀ : (d q).tower.app m ≫ p.tower.app m = 0 := by
      rw [← cancel_mono (ι.tower.app m), Category.assoc, hpι, zero_comp]
      exact sq q m
    rw [truncationDifferential_tower_app_of_lt S d (q + 1) Z p (Nat.lt_succ_self q),
      truncationDifferential_tower_app_self]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% h₀, zero_comp, comp_zero]
  · exact (isZero_truncationTerm_tower_obj S D Z (by omega) m).eq_of_tgt _ _

/-- The truncation in degree `D + 1`, as an `ℓ`-divisible system of cochain complexes. -/
def truncation : DivisibleSystem (CochainComplex C ℕ) ℓ :=
  ofDegrees (truncationTerm S D Z) (truncationDifferential S d D Z p)
    (truncationDifferential_comp_tower_app S d sq D Z p ι hpι)

lemma truncation_obj_d (m q : ℕ) :
    ((truncation S d sq D Z p ι hpι).obj m).d q (q + 1) =
      (truncationDifferential S d D Z p q).tower.app (op m) :=
  ofDegrees_obj_d _ _ _ m q

lemma isZero_truncation_obj_X (m : ℕ) {q : ℕ} (h : D + 1 < q) :
    IsZero (((truncation S d sq D Z p ι hpι).obj m).X q) :=
  isZero_truncationTerm_tower_obj S D Z h (op m)

/-- For `q ≤ D`, the degree-`q` system of the truncation is `S q`. -/
def truncationDegreeIsoOfLE {q : ℕ} (h : q ≤ D) :
    (truncation S d sq D Z p ι hpι).degree q ≅ S q :=
  ofDegreesDegreeIso _ _ _ q ≪≫ eqToIso (truncationTerm_of_le S D Z h)

/-- The degree-`(D + 1)` system of the truncation is `Z`. -/
def truncationDegreeIsoTop : (truncation S d sq D Z p ι hpι).degree (D + 1) ≅ Z :=
  ofDegreesDegreeIso _ _ _ (D + 1) ≪≫ eqToIso (truncationTerm_of_eq S D Z rfl)

/-- The components of the inclusion of the truncation: the identity in degrees `≤ D`, `ι` in
degree `D + 1` and zero above. -/
def truncationInclusion (q : ℕ) : truncationTerm S D Z q ⟶ S q :=
  if h : q ≤ D then eqToHom (truncationTerm_of_le S D Z h)
  else if h' : q = D + 1 then
    eqToHom (truncationTerm_of_eq S D Z h') ≫ ι ≫ eqToHom (congrArg S h'.symm)
  else eqToHom (truncationTerm_of_lt S D Z (by omega)) ≫ fromZeroSystem _

omit [∀ m, Mono (ι.tower.app m)] in
lemma truncationInclusion_tower_app_of_le {q : ℕ} (h : q ≤ D) (m : ℕᵒᵖ) :
    (truncationInclusion S D Z ι q).tower.app m =
      eqToHom (by rw [truncationTerm_of_le S D Z h]) := by
  rw [truncationInclusion, dite_eq_left h, eqToHom_tower_app]

omit [∀ m, Mono (ι.tower.app m)] in
lemma truncationInclusion_tower_app_top (m : ℕᵒᵖ) :
    (truncationInclusion S D Z ι (D + 1)).tower.app m =
      eqToHom (by rw [truncationTerm_of_eq S D Z rfl]) ≫ ι.tower.app m := by
  rw [truncationInclusion, dite_eq_right (by omega), dite_eq_left rfl]
  simp only [comp_tower, NatTrans.comp_app, eqToHom_tower_app, eqToHom_refl, Category.comp_id]

omit [∀ m, Mono (ι.tower.app m)] in
lemma isIso_truncationInclusion_tower_app {q : ℕ} (h : q ≤ D) (m : ℕᵒᵖ) :
    IsIso ((truncationInclusion S D Z ι q).tower.app m) := by
  rw [truncationInclusion_tower_app_of_le S D Z ι h]
  infer_instance

instance mono_truncationInclusion_tower_app (q : ℕ) (m : ℕᵒᵖ) :
    Mono ((truncationInclusion S D Z ι q).tower.app m) := by
  rcases lt_trichotomy q (D + 1) with h | h | h
  · have := isIso_truncationInclusion_tower_app S D Z ι (by omega : q ≤ D) m
    infer_instance
  · subst h
    rw [truncationInclusion_tower_app_top]
    infer_instance
  · exact (isZero_truncationTerm_tower_obj S D Z h m).mono _

variable (hιd : ∀ m, ι.tower.app m ≫ (d (D + 1)).tower.app m = 0)

include hpι hιd in
lemma truncationInclusion_comm (q : ℕ) (m : ℕᵒᵖ) :
    (truncationInclusion S D Z ι q).tower.app m ≫ (d q).tower.app m =
      (truncationDifferential S d D Z p q).tower.app m ≫
        (truncationInclusion S D Z ι (q + 1)).tower.app m := by
  rcases lt_trichotomy q D with h | h | h
  · rw [truncationInclusion_tower_app_of_le S D Z ι h.le,
      truncationDifferential_tower_app_of_lt S d D Z p h,
      truncationInclusion_tower_app_of_le S D Z ι (Nat.succ_le_of_lt h)]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · subst h
    rw [truncationInclusion_tower_app_of_le S q Z ι le_rfl, truncationDifferential_tower_app_self,
      truncationInclusion_tower_app_top]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, hpι]
  · rcases Nat.lt_or_ge (D + 1) q with h' | h'
    · exact (isZero_truncationTerm_tower_obj S D Z h' m).eq_of_src _ _
    · obtain rfl : q = D + 1 := by omega
      rw [truncationInclusion_tower_app_top, Category.assoc, hιd, comp_zero,
        (isZero_truncationTerm_tower_obj S D Z (by omega) m).eq_zero_of_tgt
          ((truncationDifferential S d D Z p (D + 1)).tower.app m), zero_comp]

/-- The inclusion of the truncation into the untruncated system of cochain complexes. -/
def truncationHom : truncation S d sq D Z p ι hpι ⟶ ofDegrees S d sq :=
  ofDegreesHom _ _ (truncationInclusion S D Z ι) (truncationInclusion_comm S d D Z p ι hpι hιd)

lemma truncationHom_tower_app_f (m : ℕᵒᵖ) (q : ℕ) :
    ((truncationHom S d sq D Z p ι hpι hιd).tower.app m).f q =
      (truncationInclusion S D Z ι q).tower.app m :=
  rfl

instance mono_truncationHom_tower_app (m : ℕᵒᵖ) :
    Mono ((truncationHom S d sq D Z p ι hpι hιd).tower.app m) := by
  apply HomologicalComplex.mono_of_mono_f
  intro q
  rw [truncationHom_tower_app_f]
  exact mono_truncationInclusion_tower_app S D Z ι q m

private lemma prev_le (q : ℕ) : (ComplexShape.up ℕ).prev q ≤ q := by
  rcases q with _ | q
  · rw [CochainComplex.prev_nat_zero]
  · rw [CochainComplex.prev_nat_succ]
    omega

/-- At every level, the inclusion of the truncation is a quasi-isomorphism in degrees
`≤ D`. -/
lemma truncationHom_quasiIsoAt_of_le (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    QuasiIsoAt ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m)) q := by
  rw [quasiIsoAt_iff]
  have := isIso_truncationInclusion_tower_app S D Z ι ((prev_le q).trans hq) (op m)
  have := isIso_truncationInclusion_tower_app S D Z ι hq (op m)
  have : Epi ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℕ) q).map
      ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m))).τ₁ :=
    show Epi ((truncationInclusion S D Z ι _).tower.app (op m)) from inferInstance
  have : IsIso ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℕ) q).map
      ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m))).τ₂ :=
    show IsIso ((truncationInclusion S D Z ι q).tower.app (op m)) from inferInstance
  have : Mono ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℕ) q).map
      ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m))).τ₃ :=
    show Mono ((truncationInclusion S D Z ι _).tower.app (op m)) from inferInstance
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono _

/-- If `p` is levelwise epic, every level of the truncation is exact in degree `D + 1`. -/
lemma truncation_obj_exactAt_top (hp : ∀ m, Epi (p.tower.app m)) (m : ℕ) :
    ((truncation S d sq D Z p ι hpι).obj m).ExactAt (D + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ D (D + 1) (D + 1 + 1) (CochainComplex.prev_nat_succ D)
    (CochainComplex.next ℕ (D + 1))]
  rw [ShortComplex.exact_iff_epi _
    ((isZero_truncation_obj_X S d sq D Z p ι hpι m (by omega)).eq_of_tgt _ _)]
  change Epi (((truncation S d sq D Z p ι hpι).obj m).d D (D + 1))
  rw [truncation_obj_d, truncationDifferential_tower_app_self]
  change Epi (_ ≫ _ : (truncationTerm S D Z D).tower.obj (op m) ⟶
    (truncationTerm S D Z (D + 1)).tower.obj (op m))
  have := hp (op m)
  infer_instance

/-- Every level of the truncation is exact in degrees above `D + 1`. -/
lemma truncation_obj_exactAt_of_lt (m : ℕ) {q : ℕ} (h : D + 1 < q) :
    ((truncation S d sq D Z p ι hpι).obj m).ExactAt q :=
  HomologicalComplex.ExactAt.of_isZero (isZero_truncation_obj_X S d sq D Z p ι hpι m h)

/-- If `p` is levelwise epic and the level-`m` complex of `S` is exact in degrees `≥ D + 1`,
the inclusion of the truncation is a quasi-isomorphism at level `m`. -/
lemma truncationHom_quasiIso (hp : ∀ m, Epi (p.tower.app m)) (m : ℕ)
    (hS : ∀ q, D + 1 ≤ q → ((ofDegrees S d sq).obj m).ExactAt q) :
    QuasiIso ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m)) := by
  rw [quasiIso_iff]
  intro q
  rcases Nat.lt_or_ge D q with h | h
  · rw [quasiIsoAt_iff_exactAt _ q _]
    · exact hS q h
    · rcases Nat.lt_or_ge (D + 1) q with h' | h'
      · exact truncation_obj_exactAt_of_lt S d sq D Z p ι hpι m h'
      · obtain rfl : q = D + 1 := by omega
        exact truncation_obj_exactAt_top S d sq D Z p ι hpι hp m
  · exact truncationHom_quasiIsoAt_of_le S d sq D Z p ι hpι hιd m h

end Truncation

section Resolution

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F) [∀ X : C, Mono (η.app X)] (T : DivisibleSystem C ℓ) (D : ℕ)

/-- Harris's truncation `G = τ_{≤ D+1}(F)` of the resolution system in degree `D + 1`: the
term systems `F^q` for `q ≤ D`, the residual system `R (D + 1)` in degree `D + 1` and zero
above. -/
def truncatedResolutionSystem : DivisibleSystem (CochainComplex C ℕ) ℓ :=
  truncation (T.termSystem F η) (T.termDifferential F η)
    (T.termDifferential_comp_termDifferential_tower_app F η) D (T.residualSystem F η (D + 1))
    (T.residualQuotient F η D) (T.residualInclusion F η (D + 1))
    (fun m => (T.termDifferential_tower_app F η D m).symm)

/-- The inclusion of the truncated resolution system into the resolution system. -/
def truncatedResolutionHom : T.truncatedResolutionSystem F η D ⟶ T.resolutionSystem F η :=
  truncationHom _ _ _ D _ _ _ _ (T.residualInclusion_termDifferential_tower_app F η (D + 1))

/-- Every level of the truncated resolution system is zero in degrees above `D + 1`. -/
lemma isZero_truncatedResolutionSystem_obj_X (m : ℕ) {q : ℕ} (h : D + 1 < q) :
    IsZero (((T.truncatedResolutionSystem F η D).obj m).X q) :=
  isZero_truncation_obj_X _ _ _ D _ _ _ _ m h

/-- At every level, the inclusion of the truncated resolution is a quasi-isomorphism. -/
instance truncatedResolutionHom_quasiIso (m : ℕ) :
    QuasiIso ((T.truncatedResolutionHom F η D).tower.app (op m)) :=
  truncationHom_quasiIso _ _ _ D _ _ _ _ _ (fun m => inferInstance) m (fun q hq => by
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    exact T.resolutionSystem_obj_exactAt F η m q)

/-- Every level of the truncated resolution system is exact in positive degrees. -/
lemma truncatedResolutionSystem_obj_exactAt (m q : ℕ) :
    ((T.truncatedResolutionSystem F η D).obj m).ExactAt (q + 1) :=
  (exactAt_iff_of_quasiIsoAt
    ((T.truncatedResolutionHom F η D).tower.app (op m)) (q + 1)).2
    (T.resolutionSystem_obj_exactAt F η m q)

end Resolution

section Smooth

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ)

/-- Harris's truncated system `G = τ_{≤ D+1}(F)` of the smooth Godement resolutions of the
levels of `T`, given that the degree-zero smooth Godement functor is exact. -/
def smoothGodementTruncatedResolutionSystem :
    DivisibleSystem (CochainComplex (SmoothTopologicalSheaf R G X) ℕ) ℓ :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  truncatedResolutionSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T D

/-- The inclusion of the truncated smooth Godement resolution system into the smooth Godement
resolution system. -/
def smoothGodementTruncatedResolutionHom :
    smoothGodementTruncatedResolutionSystem h T D ⟶ smoothGodementResolutionSystem h T :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  truncatedResolutionHom (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T D

/-- At every level, the inclusion of the truncated smooth Godement resolution is a
quasi-isomorphism. -/
lemma smoothGodementTruncatedResolutionHom_quasiIso (m : ℕ) :
    QuasiIso ((smoothGodementTruncatedResolutionHom h T D).tower.app (op m)) := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact truncatedResolutionHom_quasiIso (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
    T D m

end Smooth

end DivisibleSystem

end Langlands.Cohomology

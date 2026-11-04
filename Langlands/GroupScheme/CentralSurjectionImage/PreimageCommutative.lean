import Langlands.GroupScheme.CentralSurjectionImage.BimultRigidity
import Langlands.GroupScheme.Rational.Characters
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Tactic.Group

/-! # The preimage of a commutative subgroup under a central fppf surjection

Let `q : G → H` be a homomorphism of group schemes over `S` with central scheme-theoretic kernel,
and `j : T → H` a homomorphism from a commutative group scheme. The preimage
`M = G ×_H T` is a group scheme. If `q` is fpqc and `T` is a split torus over a field, `M` is
commutative: its commutator pairing descends to a bimultiplicative map `T × T → G`, which is
trivial by rigidity.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralSurjectionImage

set_option backward.isDefEq.respectTransparency false

section Preimage

variable {S : Scheme.{u}} {G H T : GroupScheme S} (q : G ⟶ H) (j : T ⟶ H)

/-- The preimage `G ×_H T` of `j` under `q`, as a group scheme. -/
abbrev preimage : GroupScheme S := pullback q j

/-- The inclusion of the preimage into `G`. -/
abbrev preι : preimage q j ⟶ G := pullback.fst q j

/-- The projection of the preimage onto `T`. -/
abbrev preπ : preimage q j ⟶ T := pullback.snd q j

theorem preι_comp : preι q j ≫ q = preπ q j ≫ j := pullback.condition

theorem preimage_isPullback :
    IsPullback (preι q j).hom.hom (preπ q j).hom.hom q.hom.hom j.hom.hom :=
  IsPullback.map (Grp.forget (Over S)) (IsPullback.of_hasPullback q j)

theorem preimage_isPullback_scheme :
    IsPullback (preι q j).hom.hom.left (preπ q j).hom.hom.left q.hom.hom.left j.hom.hom.left :=
  IsPullback.map (Over.forget S) (preimage_isPullback q j)

theorem preπ_flat [Flat q.hom.hom.left] : Flat (preπ q j).hom.hom.left :=
  MorphismProperty.of_isPullback (P := @Flat) (preimage_isPullback_scheme q j) inferInstance

theorem preπ_surjective [Surjective q.hom.hom.left] : Surjective (preπ q j).hom.hom.left :=
  MorphismProperty.of_isPullback (P := @Surjective) (preimage_isPullback_scheme q j) inferInstance

theorem preπ_locallyOfFinitePresentation [LocallyOfFinitePresentation q.hom.hom.left] :
    LocallyOfFinitePresentation (preπ q j).hom.hom.left :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (preimage_isPullback_scheme q j) inferInstance

theorem preι_isClosedImmersion [IsClosedImmersion j.hom.hom.left] :
    IsClosedImmersion (preι q j).hom.hom.left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (preimage_isPullback_scheme q j).flip inferInstance

instance preι_mono [Mono j.hom.hom] : Mono (preι q j).hom.hom :=
  (preimage_isPullback q j).mono_fst_of_mono

end Preimage

/-! ### Commutators with central differences -/

section Group

variable {Γ : Type*} [Group Γ]

/-- The commutator `a b a⁻¹ b⁻¹`. -/
def comm (a b : Γ) : Γ := a * b * a⁻¹ * b⁻¹

theorem comm_mul_central {a b z w : Γ} (hz : ∀ x, Commute z x) (hw : ∀ x, Commute w x) :
    comm (a * z) (b * w) = comm a b := by
  have e1 : z * (b * w) * z⁻¹ = b * w := by rw [(hz (b * w)).eq, mul_inv_cancel_right]
  have e2 : w * a⁻¹ * w⁻¹ = a⁻¹ := by rw [(hw a⁻¹).eq, mul_inv_cancel_right]
  calc comm (a * z) (b * w) = a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by
        simp only [comm]; group
    _ = a * (b * w) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [e1]
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = comm a b := by rw [e2]; rfl

theorem comm_mul_left {a a' b : Γ} (hc : ∀ x, Commute (comm a' b) x) :
    comm (a * a') b = comm a b * comm a' b := by
  calc comm (a * a') b = a * comm a' b * (b * a⁻¹ * b⁻¹) := by simp only [comm]; group
    _ = comm a' b * (a * (b * a⁻¹ * b⁻¹)) := by rw [(hc a).eq.symm, mul_assoc]
    _ = comm a' b * comm a b := by simp only [comm]; group
    _ = comm a b * comm a' b := ((hc _).eq)

theorem comm_one_right (a : Γ) : comm a 1 = 1 := by simp [comm]

theorem comm_eq_one_iff {a b : Γ} : comm a b = 1 ↔ a * b = b * a := by
  have : comm a b = a * b * (b * a)⁻¹ := by simp [comm, mul_inv_rev, mul_assoc]
  rw [this, mul_inv_eq_one]

end Group

/-! ### Commutators of points -/

section Points

variable {S : Scheme.{u}}

theorem comp_comm {X Y : Over S} {G : GroupScheme S} (f : X ⟶ Y) (g h : Y ⟶ G.X) :
    f ≫ comm g h = comm (f ≫ g) (f ≫ h) := by
  simp only [comm, MonObj.comp_mul, GrpObj.comp_inv]

theorem comm_comp {X : Over S} {G G' : GroupScheme S} (φ : G ⟶ G') (g h : X ⟶ G.X) :
    comm g h ≫ φ.hom.hom = comm (g ≫ φ.hom.hom) (h ≫ φ.hom.hom) := by
  simp only [comm, MonObj.mul_comp, GrpObj.inv_comp]

variable {G H T : GroupScheme S} (q : G ⟶ H) (j : T ⟶ H)

/-- A point of `G` killed by `q` commutes with every point when the kernel of `q` is central. -/
theorem commute_of_comp_eq_one (hq : IsCentral (kernelι q)) {U : Over S} (g : U ⟶ G.X)
    (hg : g ≫ q.hom.hom = 1) (x : U ⟶ G.X) : Commute g x := by
  let x₀ := (kernel_isPullback q).lift g (toUnit U) hg
  have h₀ : x₀ ≫ (kernelι q).hom.hom = g := (kernel_isPullback q).lift_fst _ _ _
  have hc := hq U x₀
  rw [h₀] at hc
  exact commute_of_mem_center hc x

/-- Points of the preimage with the same image in `T` differ by a central point of `G`. -/
theorem commute_inv_mul_of_comp_eq (hq : IsCentral (kernelι q)) {U : Over S}
    {m m' : U ⟶ (preimage q j).X} (h : m ≫ (preπ q j).hom.hom = m' ≫ (preπ q j).hom.hom)
    (x : U ⟶ G.X) :
    Commute ((m ≫ (preι q j).hom.hom)⁻¹ * (m' ≫ (preι q j).hom.hom)) x := by
  apply commute_of_comp_eq_one q hq
  have hc := congrArg (fun φ : preimage q j ⟶ H => φ.hom.hom) (preι_comp q j)
  simp only [Grp.comp_hom_hom] at hc
  rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hc, ← Category.assoc,
    ← Category.assoc, h, inv_mul_cancel]

/-- Commutators of points of the preimage are killed by `q` when `T` is commutative. -/
theorem comm_comp_eq_one (hT : ∀ (U : Over S) (t t' : U ⟶ T.X), t * t' = t' * t)
    {U : Over S} (m m' : U ⟶ (preimage q j).X) :
    comm (m ≫ (preι q j).hom.hom) (m' ≫ (preι q j).hom.hom) ≫ q.hom.hom = 1 := by
  have hc := congrArg (fun φ : preimage q j ⟶ H => φ.hom.hom) (preι_comp q j)
  simp only [Grp.comp_hom_hom] at hc
  rw [comm_comp, Category.assoc, Category.assoc, hc, ← Category.assoc, ← Category.assoc,
    ← comm_comp, comm_eq_one_iff.mpr (hT U _ _), MonObj.one_comp]

/-- The commutator morphism of the preimage, with values in `G`. -/
def commMor : (preimage q j).X ⊗ (preimage q j).X ⟶ G.X :=
  comm (fst _ _ ≫ (preι q j).hom.hom) (snd _ _ ≫ (preι q j).hom.hom)

theorem lift_commMor {U : Over S} (m m' : U ⟶ (preimage q j).X) :
    lift m m' ≫ commMor q j = comm (m ≫ (preι q j).hom.hom) (m' ≫ (preι q j).hom.hom) := by
  rw [commMor, comp_comm, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd]

/-- The commutator only depends on the images in `T`. -/
theorem lift_commMor_eq (hq : IsCentral (kernelι q)) {U : Over S}
    {m₁ m₁' m₂ m₂' : U ⟶ (preimage q j).X}
    (h₁ : m₁ ≫ (preπ q j).hom.hom = m₁' ≫ (preπ q j).hom.hom)
    (h₂ : m₂ ≫ (preπ q j).hom.hom = m₂' ≫ (preπ q j).hom.hom) :
    lift m₁ m₂ ≫ commMor q j = lift m₁' m₂' ≫ commMor q j := by
  rw [lift_commMor, lift_commMor]
  have e₁ : m₁' ≫ (preι q j).hom.hom = (m₁ ≫ (preι q j).hom.hom) *
      ((m₁ ≫ (preι q j).hom.hom)⁻¹ * (m₁' ≫ (preι q j).hom.hom)) := by group
  have e₂ : m₂' ≫ (preι q j).hom.hom = (m₂ ≫ (preι q j).hom.hom) *
      ((m₂ ≫ (preι q j).hom.hom)⁻¹ * (m₂' ≫ (preι q j).hom.hom)) := by group
  rw [e₁, e₂, comm_mul_central (commute_inv_mul_of_comp_eq q j hq h₁)
    (commute_inv_mul_of_comp_eq q j hq h₂)]

end Points

/-! ### Descent of the commutator -/

section Descent

variable {S : Scheme.{u}} {G H T : GroupScheme S} (q : G ⟶ H) (j : T ⟶ H)

/-- Quasi-compact, flat and surjective. -/
abbrev fpqcP : MorphismProperty Scheme.{u} := @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

theorem fpqcP_tensorHom {X₁ Y₁ X₂ Y₂ : Over S} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (hf : fpqcP f.left)
    (hg : fpqcP g.left) : fpqcP (f ⊗ₘ g).left :=
  MorphismProperty.pullbackMap (P := fpqcP) hf hg (Over.w f).symm (Over.w g).symm

theorem epi_of_fpqcP {X Y : Over S} (f : X ⟶ Y) (hf : fpqcP f.left) : Epi f := by
  have : QuasiCompact f.left := hf.1
  have : Flat f.left := hf.2.1
  have : Surjective f.left := hf.2.2
  exact Over.epi_of_epi_left _

variable (hπ : fpqcP (preπ q j).hom.hom.left) (hq : IsCentral (kernelι q))

/-- The product of the projection with itself. -/
abbrev πp : (preimage q j).X ⊗ (preimage q j).X ⟶ T.X ⊗ T.X :=
  (preπ q j).hom.hom ⊗ₘ (preπ q j).hom.hom

include hq in
theorem commMor_scheme_eq {Z : Scheme.{u}} (h h' : Z ⟶ ((preimage q j).X ⊗ (preimage q j).X).left)
    (he : h ≫ (πp q j).left = h' ≫ (πp q j).left) :
    h ≫ (commMor q j).left = h' ≫ (commMor q j).left := by
  have hs : h' ≫ ((preimage q j).X ⊗ (preimage q j).X).hom =
      h ≫ ((preimage q j).X ⊗ (preimage q j).X).hom := by
    rw [← Over.w (πp q j), ← Category.assoc, ← he, Category.assoc]
  let h₀ : Over.mk (h ≫ ((preimage q j).X ⊗ (preimage q j).X).hom) ⟶
      (preimage q j).X ⊗ (preimage q j).X := Over.homMk h rfl
  let h₁ : Over.mk (h ≫ ((preimage q j).X ⊗ (preimage q j).X).hom) ⟶
      (preimage q j).X ⊗ (preimage q j).X := Over.homMk h' hs
  have he' : h₀ ≫ πp q j = h₁ ≫ πp q j := Over.OverMorphism.ext he
  have k₁ : (h₀ ≫ fst _ _) ≫ (preπ q j).hom.hom = (h₁ ≫ fst _ _) ≫ (preπ q j).hom.hom := by
    simpa only [Category.assoc, tensorHom_fst] using congrArg (· ≫ fst _ _) he'
  have k₂ : (h₀ ≫ snd _ _) ≫ (preπ q j).hom.hom = (h₁ ≫ snd _ _) ≫ (preπ q j).hom.hom := by
    simpa only [Category.assoc, tensorHom_snd] using congrArg (· ≫ snd _ _) he'
  have key : h₀ ≫ commMor q j = h₁ ≫ commMor q j := by
    rw [← lift_comp_fst_snd h₀, ← lift_comp_fst_snd h₁]
    exact lift_commMor_eq q j hq k₁ k₂
  exact congrArg (fun x => x.left) key

include hπ in
theorem fpqcP_πp : fpqcP (πp q j).left :=
  fpqcP_tensorHom (preπ q j).hom.hom (preπ q j).hom.hom hπ hπ

include hπ in
theorem effectiveEpi_πp : EffectiveEpi (πp q j).left := by
  have hp := fpqcP_πp q j hπ
  have : QuasiCompact (πp q j).left := hp.1
  have : Flat (πp q j).left := hp.2.1
  have : Surjective (πp q j).left := hp.2.2
  infer_instance

/-- The descended underlying scheme morphism of the commutator pairing. -/
def descCommScheme : (T.X ⊗ T.X).left ⟶ G.X.left :=
  have := effectiveEpi_πp q j hπ
  EffectiveEpi.desc (πp q j).left (commMor q j).left
    (fun h h' he => commMor_scheme_eq q j hq h h' he)

theorem fac_descCommScheme :
    (πp q j).left ≫ descCommScheme q j hπ hq = (commMor q j).left :=
  have := effectiveEpi_πp q j hπ
  EffectiveEpi.fac (πp q j).left (commMor q j).left
    (fun h h' he => commMor_scheme_eq q j hq h h' he)

/-- The commutator pairing of the preimage, descended to `T × T`. -/
def descComm : T.X ⊗ T.X ⟶ G.X :=
  Over.homMk (descCommScheme q j hπ hq) (by
    have := effectiveEpi_πp q j hπ
    apply (cancel_epi (πp q j).left).mp
    rw [← Category.assoc, fac_descCommScheme, Over.w, Over.w])

theorem fac_descComm : πp q j ≫ descComm q j hπ hq = commMor q j :=
  Over.OverMorphism.ext (fac_descCommScheme q j hπ hq)

theorem lift_comp_descComm {U : Over S} (m m' : U ⟶ (preimage q j).X) :
    lift (m ≫ (preπ q j).hom.hom) (m' ≫ (preπ q j).hom.hom) ≫ descComm q j hπ hq =
      comm (m ≫ (preι q j).hom.hom) (m' ≫ (preι q j).hom.hom) := by
  rw [← lift_map_assoc, fac_descComm, lift_commMor]

include hπ hq in
/-- The descended commutator pairing is multiplicative in the first variable. -/
theorem descComm_mul (hT : ∀ (U : Over S) (t t' : U ⟶ T.X), t * t' = t' * t) {U : Over S}
    (x x' y : U ⟶ T.X) :
    lift (x * x') y ≫ descComm q j hπ hq =
      (lift x y ≫ descComm q j hπ hq) * (lift x' y ≫ descComm q j hπ hq) := by
  have hF : lift ((fst _ _ ≫ fst _ _) * (fst _ _ ≫ snd _ _)) (snd _ _) ≫ descComm q j hπ hq =
      (lift (fst _ _ ≫ fst _ _) (snd _ _) ≫ descComm q j hπ hq) *
        (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ descComm q j hπ hq :
          (T.X ⊗ T.X) ⊗ T.X ⟶ G.X) := by
    have hepi : Epi (πp q j ⊗ₘ (preπ q j).hom.hom) :=
      epi_of_fpqcP _ (fpqcP_tensorHom _ _ (fpqcP_πp q j hπ) hπ)
    apply (cancel_epi (πp q j ⊗ₘ (preπ q j).hom.hom)).mp
    have e₁ : (πp q j ⊗ₘ (preπ q j).hom.hom) ≫ fst _ _ ≫ fst _ _ =
        (fst _ _ ≫ fst _ _) ≫ (preπ q j).hom.hom := by simp
    have e₂ : (πp q j ⊗ₘ (preπ q j).hom.hom) ≫ fst _ _ ≫ snd _ _ =
        (fst _ _ ≫ snd _ _) ≫ (preπ q j).hom.hom := by simp
    have e₃ : (πp q j ⊗ₘ (preπ q j).hom.hom) ≫ snd _ _ =
        (snd _ _) ≫ (preπ q j).hom.hom := by simp
    rw [MonObj.comp_mul, comp_lift_assoc, comp_lift_assoc, comp_lift_assoc, MonObj.comp_mul, e₁, e₂,
      e₃, ← MonObj.mul_comp, lift_comp_descComm, lift_comp_descComm, lift_comp_descComm,
      MonObj.mul_comp]
    apply comm_mul_left
    exact commute_of_comp_eq_one q hq _ (comm_comp_eq_one q j hT _ _)
  have h := congrArg (lift (lift x x') y ≫ ·) hF
  simp only [MonObj.comp_mul, comp_lift_assoc, lift_fst_assoc, lift_snd, lift_fst] at h
  exact h

include hπ hq in
/-- The descended commutator pairing is trivial on `T × 1`. -/
theorem descComm_one {U : Over S} (x : U ⟶ T.X) : lift x 1 ≫ descComm q j hπ hq = 1 := by
  have hF : lift (𝟙 T.X) 1 ≫ descComm q j hπ hq = 1 := by
    have hepi : Epi (preπ q j).hom.hom := epi_of_fpqcP _ hπ
    apply (cancel_epi (preπ q j).hom.hom).mp
    have e : lift (preπ q j).hom.hom (1 : (preimage q j).X ⟶ T.X) ≫ descComm q j hπ hq = 1 := by
      have h := lift_comp_descComm q j hπ hq (𝟙 _) (1 : (preimage q j).X ⟶ (preimage q j).X)
      rw [Category.id_comp, MonObj.one_comp, Category.id_comp, MonObj.one_comp,
        comm_one_right] at h
      exact h
    rw [comp_lift_assoc, Category.comp_id, MonObj.comp_one, MonObj.comp_one]
    exact e
  have h := congrArg (x ≫ ·) hF
  simp only [comp_lift_assoc, Category.comp_id, MonObj.comp_one] at h
  exact h

end Descent

/-! ### Commutativity over a field -/

section Field

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  (q : G ⟶ H) {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ H)

/-- **Commutativity of the preimage.** Over a field, if `q` has central kernel, `T` is a split
torus and the projection of the preimage onto `T` is fpqc, then points of the preimage commute. -/
theorem preimage_mul_comm (hT : IsSplitTorus T.toGrp) (hπ : fpqcP (preπ q j).hom.hom.left)
    (hq : IsCentral (kernelι q)) [Mono (preι q j).hom.hom] {U : Over (Spec (CommRingCat.of k))}
    (m m' : U ⟶ (preimage q j).X) : m * m' = m' * m := by
  classical
  obtain ⟨I, hI, ⟨e₁⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let e : T.toGrp ≅ Dg (k := k) (I → ℤ) :=
    e₁ ≪≫ (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm
  have hTc : ∀ (U : Over (Spec (CommRingCat.of k))) (t t' : U ⟶ T.toGrp.X), t * t' = t' * t :=
    fun _ t t' => mul_comm t t'
  let β := descComm q j hπ hq
  let β' : (Dg (k := k) (I → ℤ)).X ⊗ (Dg (k := k) (I → ℤ)).X ⟶ G.X :=
    (e.inv.hom.hom ⊗ₘ e.inv.hom.hom) ≫ β
  have hβ' : ∀ {U : Over (Spec (CommRingCat.of k))} (x y : U ⟶ (Dg (k := k) (I → ℤ)).X),
      lift x y ≫ β' = 1 := by
    intro U x y
    refine lift_comp_eq_one_of_bimul β' (fun A _ _ x x' y => ?_) (fun A _ _ x => ?_) x y
    · simp only [β', lift_map_assoc, MonObj.mul_comp]
      exact descComm_mul q j hπ hq hTc _ _ _
    · simp only [β', lift_map_assoc, MonObj.one_comp]
      exact descComm_one q j hπ hq _
  have hβ : ∀ (t t' : U ⟶ T.toGrp.X), lift t t' ≫ β = 1 := by
    intro t t'
    have h := hβ' (t ≫ e.hom.hom.hom) (t' ≫ e.hom.hom.hom)
    have hei : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, e.hom_inv_id]
      rfl
    simp only [β', lift_map_assoc, Category.assoc, hei, Category.comp_id] at h
    exact h
  have hcm := lift_comp_descComm q j hπ hq m m'
  rw [hβ] at hcm
  have hc := comm_eq_one_iff.mp hcm.symm
  rw [← MonObj.mul_comp, ← MonObj.mul_comp] at hc
  exact (cancel_mono _).mp hc

/-- The preimage as a commutative group scheme. -/
def preimageComm (hT : IsSplitTorus T.toGrp) (hπ : fpqcP (preπ q j).hom.hom.left)
    (hq : IsCentral (kernelι q)) [Mono (preι q j).hom.hom] :
    CommGroupScheme (Spec (CommRingCat.of k)) where
  toGrp := preimage q j
  comm := (isCommMonObj_iff_isMulCommutative _).mpr fun _ =>
    ⟨⟨fun m m' => preimage_mul_comm q j hT hπ hq m m'⟩⟩

end Field

end Langlands.GroupScheme.CentralSurjectionImage

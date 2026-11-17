import Langlands.GroupScheme.SL2CentralExtension.Density
import Langlands.GroupScheme.Multiplicative

/-! # Natural maps on units are determined on roots of unity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace Langlands.GroupScheme.SL2CentralExtension

/-- The universal unit in the localization of `A[X]` away from `X`. -/
def laurentUnit (A : Type u) [CommRing A] :
    (Localization.Away (X : A[X]))ˣ where
  val := algebraMap A[X] (Localization.Away (X : A[X])) X
  inv := IsLocalization.Away.invSelf (X : A[X])
  val_inv := IsLocalization.Away.mul_invSelf _
  inv_val := by rw [mul_comm, IsLocalization.Away.mul_invSelf]

/-- A ring unit as a unit of the global sections of its spectrum. -/
def specUnit {A : CommRingCat.{u}} (s : Aˣ) : Γ(Spec A, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso A).inv.hom.toMonoidHom s

theorem specUnit_map {A B : CommRingCat.{u}} (f : A ⟶ B) (s : Aˣ) :
    Units.map (Spec.map f).appTop.hom.toMonoidHom (specUnit s) =
      specUnit (Units.map f.hom.toMonoidHom s) := by
  apply Units.ext
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ (s : A))
    (Scheme.ΓSpecIso_inv_naturality f)).symm

theorem specUnit_specialization (V : Scheme.{u}) {A : CommRingCat.{u}}
    (f : A ⟶ Γ(V, ⊤)) (s : Aˣ) :
    Units.map ((Gm.specHomEquiv V A).symm f).appTop.hom.toMonoidHom (specUnit s) =
      Units.map f.hom.toMonoidHom s := by
  apply Units.ext
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (s : A))
    ((Gm.specHomEquiv V A).apply_symm_apply f)

/-- Evaluation of the universal Laurent variable at a chosen unit. -/
def laurentEvaluation {A : Type u} [CommRing A] (s : Aˣ) :
    Localization.Away (X : A[X]) →+* A :=
  IsLocalization.Away.lift (X : A[X]) (g := evalRingHom (s : A))
    (by simp)

theorem laurentEvaluation_algebraMap {A : Type u} [CommRing A] (s : Aˣ) :
    (laurentEvaluation s).comp (algebraMap A (Localization.Away (X : A[X]))) =
      RingHom.id A := by
  ext a
  change laurentEvaluation s (algebraMap A[X] (Localization.Away (X : A[X])) (C a)) = a
  simp [laurentEvaluation]

theorem laurentEvaluation_unit {A : Type u} [CommRing A] (s : Aˣ) :
    Units.map (laurentEvaluation s).toMonoidHom (laurentUnit A) = s := by
  apply Units.ext
  change laurentEvaluation s (algebraMap A[X] (Localization.Away (X : A[X])) X) = (s : A)
  simp [laurentEvaluation]

/-- The projection of the universal Laurent test scheme to an affine scheme. -/
def laurentProjection (V : Scheme.{u}) [IsAffine V] :
    Spec (.of (Localization.Away (X : Γ(V, ⊤)[X]))) ⟶ V :=
  Spec.map (CommRingCat.ofHom
    (algebraMap Γ(V, ⊤) (Localization.Away (X : Γ(V, ⊤)[X])))) ≫ V.isoSpec.inv

/-- Specializing the universal Laurent test scheme at a global unit. -/
def laurentSpecialization (V : Scheme.{u}) (s : Γ(V, ⊤)ˣ) :
    V ⟶ Spec (.of (Localization.Away (X : Γ(V, ⊤)[X]))) :=
  (Gm.specHomEquiv V _).symm (CommRingCat.ofHom (laurentEvaluation s))

theorem laurentSpecialization_projection (V : Scheme.{u}) [IsAffine V]
    (s : Γ(V, ⊤)ˣ) : laurentSpecialization V s ≫ laurentProjection V = 𝟙 V := by
  have hc : CommRingCat.ofHom
      (algebraMap Γ(V, ⊤) (Localization.Away (X : Γ(V, ⊤)[X]))) ≫
      CommRingCat.ofHom (laurentEvaluation s) = 𝟙 Γ(V, ⊤) := by
    apply CommRingCat.hom_ext
    exact laurentEvaluation_algebraMap s
  change (V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (laurentEvaluation s))) ≫
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(V, ⊤) (Localization.Away (X : Γ(V, ⊤)[X])))) ≫ V.isoSpec.inv) = _
  rw [Category.assoc, ← Spec.map_comp_assoc, hc]
  rw [Spec.map_id Γ(V, ⊤), Category.id_comp]
  exact V.isoSpec.hom_inv_id

theorem laurentSpecialization_unit (V : Scheme.{u}) (s : Γ(V, ⊤)ˣ) :
    Units.map (laurentSpecialization V s).appTop.hom.toMonoidHom
      (specUnit (laurentUnit Γ(V, ⊤))) = s := by
  rw [laurentSpecialization, specUnit_specialization]
  exact laurentEvaluation_unit s

theorem laurentUnit_quotient_pow (A : Type u) [CommRing A] (n : ℕ) :
    (Units.map (Ideal.Quotient.mk (rootsOfUnityIdeal A n)).toMonoidHom (laurentUnit A)) ^
      (n + 1) = 1 := by
  apply Units.ext
  have hzero : Ideal.Quotient.mk (rootsOfUnityIdeal A n)
      (algebraMap A[X] (Localization.Away (X : A[X])) (X ^ (n + 1) - 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  change (Ideal.Quotient.mk (rootsOfUnityIdeal A n)
    (algebraMap A[X] (Localization.Away (X : A[X])) X)) ^ (n + 1) = 1
  simpa only [map_sub, map_pow, map_one, sub_eq_zero] using hzero

section NaturalFamilies

variable {S : Scheme.{u}} {Y : Over S} [IsSeparated Y.hom] {T : Over S}
    (F F' : ∀ ⦃V : Over S⦄ (_ : V ⟶ T), Γ(V.left, ⊤)ˣ → (V ⟶ Y))
    (hF : ∀ ⦃V W : Over S⦄ (g : V ⟶ T) (k : W ⟶ V) (s : Γ(V.left, ⊤)ˣ),
      k ≫ F g s = F (k ≫ g) (Units.map k.left.appTop.hom.toMonoidHom s))
    (hF' : ∀ ⦃V W : Over S⦄ (g : V ⟶ T) (k : W ⟶ V) (s : Γ(V.left, ⊤)ˣ),
      k ≫ F' g s = F' (k ≫ g) (Units.map k.left.appTop.hom.toMonoidHom s))
    (hroot : ∀ ⦃V : Over S⦄ (g : V ⟶ T) (s : Γ(V.left, ⊤)ˣ) (n : ℕ),
      s ^ (n + 1) = 1 → F g s = F' g s)

include hF hF' hroot

/-- On an affine test scheme, natural maps on units into a separated target are
determined by their values on roots of unity. -/
theorem units_natural_ext_affine {V : Over S} [IsAffine V.left]
    (g : V ⟶ T) (s : Γ(V.left, ⊤)ˣ) : F g s = F' g s := by
  let A := Γ(V.left, ⊤)
  let L := Localization.Away (X : A[X])
  let W : Over S := Over.mk (laurentProjection V.left ≫ V.hom)
  let j : W ⟶ V := Over.homMk (laurentProjection V.left) rfl
  let t : Γ(W.left, ⊤)ˣ := specUnit (laurentUnit A)
  have hu : F (j ≫ g) t = F' (j ≫ g) t := by
    apply Over.OverMorphism.ext
    have hI : (⨅ n : ULift.{u} ℕ, rootsOfUnityIdeal A n.down) = ⊥ := by
      simpa only [iInf_ulift, rootsOfUnityIdeal] using iInf_span_X_pow_sub_one A
    apply eq_of_eq_on_quotients Y.hom (fun n : ULift.{u} ℕ => rootsOfUnityIdeal A n.down) hI
    · exact (Over.w (F (j ≫ g) t)).trans (Over.w (F' (j ≫ g) t)).symm
    · rintro ⟨n⟩
      let R : CommRingCat := .of (L ⧸ rootsOfUnityIdeal A n)
      let v : Spec R ⟶ W.left :=
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (rootsOfUnityIdeal A n)))
      let Q : Over S := Over.mk (v ≫ W.hom)
      let k : Q ⟶ W := Over.homMk v rfl
      have hp : (Units.map k.left.appTop.hom.toMonoidHom t) ^ (n + 1) = 1 := by
        change (Units.map (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (rootsOfUnityIdeal A n)))).appTop.hom.toMonoidHom
          (specUnit (laurentUnit A))) ^ (n + 1) = 1
        rw [specUnit_map]
        change (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom
          (Units.map (Ideal.Quotient.mk (rootsOfUnityIdeal A n)).toMonoidHom
            (laurentUnit A))) ^ (n + 1) = 1
        rw [← map_pow, laurentUnit_quotient_pow A n, map_one]
      have hk : k ≫ F (j ≫ g) t = k ≫ F' (j ≫ g) t :=
        (hF (j ≫ g) k t).trans
          ((hroot (k ≫ (j ≫ g)) _ n hp).trans (hF' (j ≫ g) k t).symm)
      exact congrArg CommaMorphism.left hk
  let σ : V ⟶ W := Over.homMk (laurentSpecialization V.left s)
    (by
      change laurentSpecialization V.left s ≫ (laurentProjection V.left ≫ V.hom) = V.hom
      rw [← Category.assoc, laurentSpecialization_projection, Category.id_comp])
  have hσj : σ ≫ j = 𝟙 V := by
    ext1
    exact laurentSpecialization_projection V.left s
  have hσt : Units.map σ.left.appTop.hom.toMonoidHom t = s :=
    laurentSpecialization_unit V.left s
  have hf := hF (j ≫ g) σ t
  have hf' := hF' (j ≫ g) σ t
  rw [← Category.assoc, hσj, Category.id_comp, hσt] at hf hf'
  exact hf.symm.trans ((congrArg (fun a => σ ≫ a) hu).trans hf')

/-- Natural maps from units to a relatively separated scheme are determined by
their values on all roots of unity, over arbitrary test schemes. -/
theorem units_natural_ext {V : Over S} (g : V ⟶ T) (s : Γ(V.left, ⊤)ˣ) :
    F g s = F' g s := by
  apply Over.OverMorphism.ext
  apply V.left.affineCover.hom_ext
  intro i
  let W : Over S := Over.mk (V.left.affineCover.f i ≫ V.hom)
  let k : W ⟶ V := Over.homMk (V.left.affineCover.f i) rfl
  have : IsAffine W.left := by
    change IsAffine (V.left.affineCover.X i)
    infer_instance
  have hi := units_natural_ext_affine F F' hF hF' hroot
    (k ≫ g) (Units.map k.left.appTop.hom.toMonoidHom s)
  have hk : k ≫ F g s = k ≫ F' g s := (hF g k s).trans (hi.trans (hF' g k s).symm)
  exact congrArg CommaMorphism.left hk

end NaturalFamilies

end Langlands.GroupScheme.SL2CentralExtension

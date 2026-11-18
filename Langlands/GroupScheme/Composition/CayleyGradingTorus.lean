import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.Composition.CayleyTorusUpperBound
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.GeneralLinearSmoothProof

/-! # Split tori in Cayley automorphism group schemes from lattice gradings -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CayleyDatum

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type u} [Field K] (c : CayleyDatum K)

/-! ### The extended multiplication as a bilinear map -/

section Bilinear

variable {A : Type u} [CommRing A]

theorem multiplicationOver_comp_self (φ : K →+* A) (x y : CayleyVector K) :
    c.multiplicationOver φ (φ ∘ x) (φ ∘ y) = φ ∘ c.multiplication x y :=
  c.multiplicationOver_algebraMap φ x y

/-- The extended multiplication as an `A`-bilinear map. -/
def multiplicationBilin (φ : K →+* A) :
    (Fin 8 → A) →ₗ[A] (Fin 8 → A) →ₗ[A] (Fin 8 → A) :=
  LinearMap.mk₂ A (c.multiplicationOver φ)
    (fun x x' y => by
      funext i
      simp only [multiplicationOver, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib])
    (fun r x y => by
      funext i
      simp only [multiplicationOver, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring)
    (fun x y y' => by
      funext i
      simp only [multiplicationOver, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun r x y => by
      funext i
      simp only [multiplicationOver, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring)

@[simp] theorem multiplicationBilin_apply (φ : K →+* A) (x y : Fin 8 → A) :
    c.multiplicationBilin φ x y = c.multiplicationOver φ x y := rfl

end Bilinear

namespace Grading

variable {c} {I : Type u} [Fintype I] [DecidableEq I] (g : c.Grading (I → ℤ))

/-! ### Monomials in units -/

section Monomial

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The monomial `tᵐ = ∏ᵢ tᵢ^{mᵢ}` in a family of units. -/
abbrev monomial (t : I → Aˣ) (m : I → ℤ) : Aˣ :=
  splitTorus.exponentValue I t (Multiplicative.ofAdd m)

theorem monomial_apply (t : I → Aˣ) (m : I → ℤ) : monomial t m = ∏ i, t i ^ m i := rfl

omit [DecidableEq I] in
theorem monomial_add (t : I → Aˣ) (a b : I → ℤ) :
    monomial t (a + b) = monomial t a * monomial t b := by
  simp only [monomial_apply, Pi.add_apply, _root_.zpow_add, Finset.prod_mul_distrib]

omit [DecidableEq I] in
theorem monomial_zero (t : I → Aˣ) : monomial t 0 = 1 := by
  simp [monomial_apply]

omit [DecidableEq I] in
theorem monomial_neg (t : I → Aˣ) (a : I → ℤ) : monomial t (-a) = (monomial t a)⁻¹ := by
  simp only [monomial_apply, Pi.neg_apply, _root_.zpow_neg, Finset.prod_inv_distrib]

omit [DecidableEq I] in
theorem monomial_mul (t s : I → Aˣ) (m : I → ℤ) :
    monomial (t * s) m = monomial t m * monomial s m := by
  simp only [monomial_apply, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

omit [DecidableEq I] in
theorem monomial_one (m : I → ℤ) : monomial (1 : I → Aˣ) m = 1 := by
  simp [monomial_apply]

omit [DecidableEq I] in
theorem monomial_map (ψ : A →+* B) (t : I → Aˣ) (m : I → ℤ) :
    Units.map ψ.toMonoidHom (monomial t m) =
      monomial (fun i => Units.map ψ.toMonoidHom (t i)) m := by
  simp only [monomial_apply, map_prod, map_zpow]

theorem monomial_single (t : I → Aˣ) (i : I) : monomial t (Pi.single i 1) = t i :=
  splitTorus.exponentValue_single I t i

end Monomial

/-! ### Projections and the torus matrices over a coefficient ring -/

section Ring

variable {A B : Type u} [CommRing A] [CommRing B] (φ : K →+* A)

/-- The homogeneous projections with coefficients extended along `φ`. -/
def projOver (m : I → ℤ) : Matrix (Fin 8) (Fin 8) A := φ.mapMatrix (g.proj m)

omit [DecidableEq I] in
theorem projOver_mul_projOver (m n : I → ℤ) :
    g.projOver φ m * g.projOver φ n = if m = n then g.projOver φ m else 0 := by
  rw [projOver, projOver, ← map_mul, g.proj_mul_proj]
  split_ifs
  · rfl
  · exact map_zero _

omit [DecidableEq I] in
theorem sum_projOver : ∑ m ∈ g.support, g.projOver φ m = 1 := by
  simp only [projOver]
  rw [← map_sum, g.sum_proj, map_one]

omit [DecidableEq I] in
theorem sum_projOver_mulVec (x : Fin 8 → A) : ∑ m ∈ g.support, g.projOver φ m *ᵥ x = x := by
  rw [← Matrix.sum_mulVec, g.sum_projOver, Matrix.one_mulVec]

omit [DecidableEq I] in
theorem projOver_mulVec_comp (m : I → ℤ) (v : CayleyVector K) :
    g.projOver φ m *ᵥ (φ ∘ v) = φ ∘ (g.proj m *ᵥ v) :=
  map_mulVec_comp φ _ v

omit [DecidableEq I] in
theorem projOver_projOver (m n : I → ℤ) (x : Fin 8 → A) :
    g.projOver φ m *ᵥ (g.projOver φ n *ᵥ x) = if m = n then g.projOver φ m *ᵥ x else 0 := by
  rw [Matrix.mulVec_mulVec, g.projOver_mul_projOver]
  split_ifs
  · rfl
  · exact Matrix.zero_mulVec x

omit [DecidableEq I] in
/-- **Graded products over `A`.** The product of homogeneous vectors of degrees `a` and `b`
has degree `a + b`. -/
theorem projOver_multiplicationOver (a b m : I → ℤ) (x y : Fin 8 → A) :
    g.projOver φ m *ᵥ c.multiplicationOver φ (g.projOver φ a *ᵥ x) (g.projOver φ b *ᵥ y) =
      if m = a + b then
        c.multiplicationOver φ (g.projOver φ a *ᵥ x) (g.projOver φ b *ᵥ y) else 0 := by
  let F := (c.multiplicationBilin φ).compl₁₂ (g.projOver φ a).mulVecLin
    (g.projOver φ b).mulVecLin
  have key : F.compr₂ (g.projOver φ m).mulVecLin = if m = a + b then F else 0 := by
    apply LinearMap.ext_basis (Pi.basisFun A (Fin 8)) (Pi.basisFun A (Fin 8))
    intro j k
    have hb : ∀ l : Fin 8, Pi.basisFun A (Fin 8) l = φ ∘ (Pi.single l 1 : CayleyVector K) := by
      intro l
      funext i
      rw [Pi.basisFun_apply, Function.comp_apply, Pi.single_apply, Pi.single_apply,
        apply_ite φ, map_one, map_zero]
    have hK := g.proj_mulVec_of_eq (m := m)
      (g.proj_mul a b _ _ (g.proj_proj a (Pi.single j 1)) (g.proj_proj b (Pi.single k 1)))
    simp only [F, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Matrix.mulVecLin_apply,
      multiplicationBilin_apply]
    rw [hb, hb, g.projOver_mulVec_comp, g.projOver_mulVec_comp,
      c.multiplicationOver_comp_self, g.projOver_mulVec_comp, hK]
    split_ifs with h
    · simp only [LinearMap.compl₁₂_apply, Matrix.mulVecLin_apply, multiplicationBilin_apply,
        g.projOver_mulVec_comp, c.multiplicationOver_comp_self]
    · funext i
      simp
  have h := congrArg (fun F' : (Fin 8 → A) →ₗ[A] (Fin 8 → A) →ₗ[A] (Fin 8 → A) => F' x y) key
  simp only [F, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Matrix.mulVecLin_apply,
    multiplicationBilin_apply] at h
  rw [h]
  split_ifs
  · rfl
  · rfl

/-- Products of homogeneous vectors whose degrees sum outside the support vanish. -/
theorem multiplicationOver_eq_zero {a b : I → ℤ} (hab : a + b ∉ g.support) (x y : Fin 8 → A) :
    c.multiplicationOver φ (g.projOver φ a *ᵥ x) (g.projOver φ b *ᵥ y) = 0 := by
  rw [← g.sum_projOver_mulVec φ (c.multiplicationOver φ _ _)]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [g.projOver_multiplicationOver, if_neg]
  rintro rfl
  exact hab hm

/-- The matrix `∑ₘ tᵐ Pₘ` of the torus point with coordinates `t`. -/
def torusMatrix (t : I → Aˣ) : Matrix (Fin 8) (Fin 8) A :=
  ∑ m ∈ g.support, ((monomial t m : Aˣ) : A) • g.projOver φ m

omit [DecidableEq I] in
theorem torusMatrix_mulVec (t : I → Aˣ) (x : Fin 8 → A) :
    g.torusMatrix φ t *ᵥ x = ∑ m ∈ g.support, ((monomial t m : Aˣ) : A) • (g.projOver φ m *ᵥ x) := by
  rw [torusMatrix, Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun m _ => Matrix.smul_mulVec _ _ _

omit [DecidableEq I] in
theorem torusMatrix_mul (t s : I → Aˣ) :
    g.torusMatrix φ t * g.torusMatrix φ s = g.torusMatrix φ (t * s) := by
  unfold torusMatrix
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mul_sum]
  simp_rw [smul_mul_smul_comm, g.projOver_mul_projOver, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq, if_pos hm, monomial_mul, Units.val_mul]

omit [DecidableEq I] in
theorem torusMatrix_one : g.torusMatrix φ 1 = 1 := by
  simp only [torusMatrix, monomial_one, Units.val_one, one_smul]
  exact g.sum_projOver φ

/-- The torus matrices as a homomorphism to the general linear group. -/
def torusUnit : (I → Aˣ) →* GL (Fin 8) A where
  toFun t := ⟨g.torusMatrix φ t, g.torusMatrix φ t⁻¹,
    by rw [torusMatrix_mul, mul_inv_cancel, torusMatrix_one],
    by rw [torusMatrix_mul, inv_mul_cancel, torusMatrix_one]⟩
  map_one' := Units.ext (g.torusMatrix_one φ)
  map_mul' t s := Units.ext (g.torusMatrix_mul φ t s).symm

@[simp] theorem torusUnit_val (t : I → Aˣ) :
    (g.torusUnit φ t : Matrix (Fin 8) (Fin 8) A) = g.torusMatrix φ t := rfl

omit [DecidableEq I] in
theorem torusMatrix_map (ψ : A →+* B) (t : I → Aˣ) :
    (g.torusMatrix φ t).map ψ =
      g.torusMatrix (ψ.comp φ) (fun i => Units.map ψ.toMonoidHom (t i)) := by
  ext i j
  simp only [torusMatrix, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, projOver, RingHom.mapMatrix_apply, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← monomial_map]
  rfl

theorem torusUnit_map (ψ : A →+* B) (t : I → Aˣ) :
    Matrix.GeneralLinearGroup.map ψ (g.torusUnit φ t) =
      g.torusUnit (ψ.comp φ) (fun i => Units.map ψ.toMonoidHom (t i)) := by
  apply Units.ext
  exact g.torusMatrix_map φ ψ t

/-- The torus matrices are automorphism matrices. -/
theorem isAutomorphismMatrix_torusUnit (t : I → Aˣ) :
    c.IsAutomorphismMatrix φ (g.torusUnit φ t) := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [torusUnit_val, torusMatrix_mulVec, unitOver_eq]
    have hu : ∀ m, g.projOver φ m *ᵥ (fun i => φ (c.unit i)) =
        if m = 0 then (fun i => φ (c.unit i)) else 0 := by
      intro m
      have h := g.projOver_mulVec_comp φ m c.unit
      rw [g.proj_mulVec_of_eq g.proj_unit] at h
      change g.projOver φ m *ᵥ (φ ∘ c.unit) = _
      rw [h]
      split_ifs
      · rfl
      · funext i
        simp
    simp_rw [hu, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq', if_pos g.zero_mem_support, monomial_zero, Units.val_one, one_smul]
  · let Bl := c.multiplicationBilin φ
    have hx := g.sum_projOver_mulVec φ x
    have hy := g.sum_projOver_mulVec φ y
    rw [torusUnit_val, g.torusMatrix_mulVec φ t x, g.torusMatrix_mulVec φ t y]
    have hlhs : c.multiplicationOver φ x y =
        ∑ a ∈ g.support, ∑ b ∈ g.support,
          c.multiplicationOver φ (g.projOver φ a *ᵥ x) (g.projOver φ b *ᵥ y) := by
      have h : Bl x y = Bl (∑ a ∈ g.support, g.projOver φ a *ᵥ x)
          (∑ b ∈ g.support, g.projOver φ b *ᵥ y) := by rw [hx, hy]
      simp only [Bl, map_sum, LinearMap.sum_apply, multiplicationBilin_apply] at h
      first
        | exact h
        | exact h.trans Finset.sum_comm
    have hterm : ∀ a b, g.torusMatrix φ t *ᵥ
        c.multiplicationOver φ (g.projOver φ a *ᵥ x) (g.projOver φ b *ᵥ y) =
          ((monomial t a : Aˣ) : A) • ((monomial t b : Aˣ) : A) •
            c.multiplicationOver φ (g.projOver φ a *ᵥ x) (g.projOver φ b *ᵥ y) := by
      intro a b
      rw [torusMatrix_mulVec]
      simp_rw [g.projOver_multiplicationOver, smul_ite, smul_zero]
      rw [Finset.sum_ite_eq']
      split_ifs with hab
      · rw [monomial_add, Units.val_mul, mul_smul]
      · rw [g.multiplicationOver_eq_zero φ hab, smul_zero, smul_zero]
    have hrhs : c.multiplicationOver φ
        (∑ a ∈ g.support, ((monomial t a : Aˣ) : A) • (g.projOver φ a *ᵥ x))
        (∑ b ∈ g.support, ((monomial t b : Aˣ) : A) • (g.projOver φ b *ᵥ y)) =
          ∑ a ∈ g.support, ∑ b ∈ g.support,
            ((monomial t a : Aˣ) : A) • ((monomial t b : Aˣ) : A) •
              c.multiplicationOver φ (g.projOver φ a *ᵥ x) (g.projOver φ b *ᵥ y) := by
      change Bl _ _ = _
      simp only [Bl, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        multiplicationBilin_apply, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [smul_comm]
    rw [hrhs, hlhs, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun b _ => hterm a b

/-- If the support generates the lattice, the torus matrices determine the coordinates. -/
theorem torusUnit_injective (hgen : AddSubgroup.closure (g.support : Set (I → ℤ)) = ⊤) :
    Function.Injective (g.torusUnit φ) := by
  intro t s hts
  have hmat : g.torusMatrix φ t = g.torusMatrix φ s := congrArg Units.val hts
  have hsupp : ∀ m ∈ g.support, monomial t m = monomial s m := by
    intro m hm
    have hP : ∀ u : I → Aˣ, g.projOver φ m * g.torusMatrix φ u =
        ((monomial u m : Aˣ) : A) • g.projOver φ m := by
      intro u
      simp only [torusMatrix, Finset.mul_sum, mul_smul_comm, g.projOver_mul_projOver, smul_ite,
        smul_zero]
      rw [Finset.sum_ite_eq, if_pos hm]
    have h := congrArg (fun M => g.projOver φ m * M) hmat
    simp only [hP] at h
    obtain ⟨i, j, hij⟩ : ∃ i j, g.proj m i j ≠ 0 := by
      by_contra hne
      push Not at hne
      exact (g.mem_support m).mp hm (Matrix.ext hne)
    have hij' := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul, projOver, RingHom.mapMatrix_apply,
      Matrix.map_apply] at hij'
    have hu : IsUnit (φ (g.proj m i j)) := (Ne.isUnit hij).map φ
    exact Units.ext (hu.mul_left_inj.mp hij')
  let Λ : AddSubgroup (I → ℤ) :=
    { carrier := {m | monomial t m = monomial s m}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, monomial_add] at ha hb ⊢
        rw [ha, hb]
      zero_mem' := by simp only [Set.mem_ofPred_eq, monomial_zero]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, monomial_neg] at ha ⊢
        rw [ha] }
  have hle : AddSubgroup.closure (g.support : Set (I → ℤ)) ≤ Λ :=
    (AddSubgroup.closure_le Λ).mpr fun m hm => hsupp m hm
  rw [hgen] at hle
  funext i
  have hi : Pi.single i (1 : ℤ) ∈ Λ := hle (AddSubgroup.mem_top _)
  have hi' : monomial t (Pi.single i 1) = monomial s (Pi.single i 1) := hi
  rwa [monomial_single, monomial_single] at hi'

end Ring

/-! ### The split torus in the automorphism group scheme -/

section Scheme

open SplitTorusRepresentationWeights

variable {H : GroupScheme (Spec (CommRingCat.of K))}
  {iH : H ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)}
  (hrep : c.IsAutomorphismRepresentation iH)

/-- The coefficient map from `K` to the global sections of a test scheme. -/
abbrev sectionsMap (T : Over (Spec (CommRingCat.of K))) :
    K →+* ((algΓ (CommRingCat.of K)).obj T).unop :=
  algebraMap (CommRingCat.of K) ((algΓ (CommRingCat.of K)).obj T).unop

theorem sectionsMap_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) :
    a.left.appTop.hom.comp (sectionsMap T) = sectionsMap T' :=
  ((algΓ (CommRingCat.of K)).map a).unop.hom.comp_algebraMap

include hrep in
theorem isRepresentedBy_range : (SubgroupFunctor.range iH).IsRepresentedBy iH := by
  have h1 : IsClosedImmersion iH.hom.hom.left := hrep.1
  have : Mono iH.hom.hom.left := inferInstance
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- The torus matrices on points over a test scheme, as points of the range of `iH`. -/
def torusRangePoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) →* (SubgroupFunctor.range iH).carrier T :=
  MonoidHom.codRestrict
    (((GeneralLinear.pointsEquiv (Fin 8) (CommRingCat.of K) T).symm.toMonoidHom.comp
      (g.torusUnit (sectionsMap T))).comp (splitTorus.pointsEquiv I T).toMonoidHom)
    ((SubgroupFunctor.range iH).carrier T) fun x => by
      refine (hrep.2 T _).mpr ?_
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.apply_symm_apply]
      exact g.isAutomorphismMatrix_torusUnit _ _

/-- The torus points in `H`. -/
def torusPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) →* (T ⟶ H.X) :=
  ((isRepresentedBy_range hrep).pointsEquiv T).symm.toMonoidHom.comp (g.torusRangePoints hrep T)

theorem torusPoints_comp (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) :
    GeneralLinear.pointsEquiv (Fin 8) (CommRingCat.of K) T (g.torusPoints hrep T x ≫ iH.hom.hom) =
      g.torusUnit (sectionsMap T) (splitTorus.pointsEquiv I T x) := by
  rw [torusPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
  simp only [torusRangePoints, MonoidHom.codRestrict_apply, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, Function.comp_apply, MulEquiv.apply_symm_apply]
  rfl

theorem torusPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) :
    g.torusPoints hrep T' (a ≫ x) = a ≫ g.torusPoints hrep T x := by
  have hm : Mono iH.hom.hom := (isRepresentedBy_range hrep).1
  apply hm.right_cancellation
  apply (GeneralLinear.pointsEquiv (Fin 8) (CommRingCat.of K) T').injective
  rw [torusPoints_comp, Category.assoc, GeneralLinear.pointsEquiv_naturality, torusPoints_comp]
  erw [torusUnit_map]
  rw [sectionsMap_naturality, splitTorus.pointsEquiv_naturality]
  rfl

/-- The split torus `𝔾ₘ^I → H` defined by the grading. -/
def torusHom : splitTorus (Spec (CommRingCat.of K)) I ⟶ H :=
  homOfPoints (g.torusPoints hrep) (g.torusPoints_naturality hrep)

theorem mono_torusHom (hgen : AddSubgroup.closure (g.support : Set (I → ℤ)) = ⊤) :
    Mono (g.torusHom hrep).hom.hom := by
  constructor
  intro T x y hxy
  apply (splitTorus.pointsEquiv I T).injective
  apply g.torusUnit_injective (sectionsMap T) hgen
  rw [← g.torusPoints_comp hrep, ← g.torusPoints_comp hrep]
  rw [torusHom, comp_homOfPoints, comp_homOfPoints] at hxy
  rw [hxy]

include hrep in
theorem isAffineHom_X : IsAffineHom H.X.hom := by
  have : IsClosedImmersion iH.hom.hom.left := hrep.1
  have : IsAffineHom iH.hom.hom.left := inferInstance
  have : IsAffineHom (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme _ _
  have h : IsAffineHom (iH.hom.hom.left ≫
      (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom) := inferInstance
  simpa only [Over.w] using h

include hrep in
theorem locallyOfFiniteType_X : LocallyOfFiniteType H.X.hom := by
  have : IsClosedImmersion iH.hom.hom.left := hrep.1
  have : Smooth (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom :=
    GeneralLinear.smoothStatement _ _
  have h : LocallyOfFiniteType (iH.hom.hom.left ≫
      (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom) := inferInstance
  simpa only [Over.w] using h

theorem isClosedSubgroup_torusHom (hgen : AddSubgroup.closure (g.support : Set (I → ℤ)) = ⊤) :
    IsClosedSubgroup (g.torusHom hrep) := by
  have := isAffineHom_splitTorus (Spec (CommRingCat.of K)) I
  have := isAffineHom_X hrep
  have := locallyOfFiniteType_X hrep
  have := g.mono_torusHom hrep hgen
  exact IsTorus.isClosedSubgroup_of_mono
    (IsSplitTorus.isTorus (isSplitTorus_splitTorus _)) _

include hrep in
/-- **Lower bound.** A grading of a Cayley datum by `ℤ^I` whose degrees generate `ℤ^I` gives
a closed split torus of dimension `|I|` in its automorphism group scheme. -/
theorem card_le_splitRank (hgen : AddSubgroup.closure (g.support : Set (I → ℤ)) = ⊤) :
    (Nat.card I : ℕ∞) ≤ splitRank H :=
  Langlands.GroupScheme.card_le_splitRank I (g.torusHom hrep) (g.isClosedSubgroup_torusHom hrep hgen)

end Scheme

end Grading

end Langlands.GroupScheme.CayleyDatum

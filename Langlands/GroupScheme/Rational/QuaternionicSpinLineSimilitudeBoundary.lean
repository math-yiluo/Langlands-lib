import Langlands.GroupScheme.Rational.QuaternionicSpinLineReflection
import Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinKernelReduction
import Langlands.GroupScheme.CentralIsogeny.FiniteGaloisCoefficientLift
import Langlands.GroupScheme.GaloisPointTransitivity
import Langlands.Algebra.QuaternionCommutator

/-! # The spinor norm of a quaternionic line similitude -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Quaternionic Quaternionic.FirstKindInvolution

/-- Projection to the quotient commutes with coefficient maps. -/
theorem affinePointsTarget_affinePointMap {F : Type u} [Field F]
    {G H : GroupScheme (Spec (CommRingCat.of F))} (p : G ⟶ H)
    {A B : CommAlgCat.{u} (CommRingCat.of F)} (f : A ⟶ B) (a : G.affinePoints A) :
    G.affinePointsTarget p B (G.affinePointMap f a) =
      H.affinePointMap f (G.affinePointsTarget p A a) := by
  simp only [GroupScheme.affinePointsTarget_apply, GroupScheme.affinePointMap_apply,
    Category.assoc]

namespace QuaternionicLineSimilitude

section Quaternion

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] (hD : Module.finrank F D = 4)
  (σ : FirstKindInvolution F D) (c d : D) (N : F)

variable (F) in
/-- The pure part `d - Trd(d)/2` of a quaternion. -/
def purePart : D := d - algebraMap F D (CentralDivision.reducedTrace F D d / 2)

include hD in
theorem purePart_mul_self :
    purePart F d * purePart F d =
      -algebraMap F D (CentralSimple.reducedNorm F D F ((1 : F) ⊗ₜ[F] purePart F d)) := by
  have hdeg := FirstKindInvolution.reducedDegree_eq_two hD
  have hT : CentralDivision.reducedTrace F D (purePart F d) = 0 := by
    rw [purePart, CentralDivision.reducedTrace_sub, Algebra.algebraMap_eq_smul_one,
      CentralDivision.reducedTrace_smul, CentralDivision.reducedTrace_one F D hdeg]
    ring
  have h := CentralDivision.sq_sub_reducedTrace_add_reducedNorm F D hdeg (purePart F d)
  rw [hT, _root_.map_zero, zero_mul, sub_zero, pow_two] at h
  exact eq_neg_of_add_eq_zero_left h

omit [CharZero F] in
theorem purePart_commute : Commute (purePart F d) d := by
  unfold purePart
  exact (Commute.refl d).sub_left (Algebra.commutes _ d)

include hD in
/-- If `d c σ(d) = Nrd(d) c` with `Nrd(d) ≠ 0`, the pure part `w` of `d` satisfies
`w c σ(w) = Nrd(w) c`. -/
theorem purePart_mul_mul_map
    (hd : d * c * σ d = N • c)
    (hN : CentralSimple.reducedNorm F D F ((1 : F) ⊗ₜ[F] d) = N) (hN0 : N ≠ 0) :
    purePart F d * c * σ (purePart F d) =
      CentralSimple.reducedNorm F D F ((1 : F) ⊗ₜ[F] purePart F d) • c := by
  have hdeg := FirstKindInvolution.reducedDegree_eq_two hD
  set T := CentralDivision.reducedTrace F D d with hTdef
  have hCH := CentralDivision.sq_sub_reducedTrace_add_reducedNorm F D hdeg d
  rw [hN, ← hTdef, pow_two] at hCH
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, _root_.map_zero] at hN
    exact hN0 hN.symm
  -- `c σ(d) = (T - d) c`
  have hconj : c * σ d = (algebraMap F D T - d) * c := by
    have h1 : d * (algebraMap F D T - d) = algebraMap F D N := by
      rw [mul_sub, ← Algebra.commutes, ← sub_eq_zero,
        show algebraMap F D T * d - d * d - algebraMap F D N =
          -(d * d - algebraMap F D T * d + algebraMap F D N) by abel, hCH, neg_zero]
    have h2 : d * (c * σ d) = d * ((algebraMap F D T - d) * c) := by
      rw [← mul_assoc, ← mul_assoc, hd, h1, Algebra.smul_def]
    exact mul_left_cancel₀ hd0 h2
  have hw := purePart_mul_self hD d
  set w := purePart F d with hwdef
  have hσw : σ w = σ d - algebraMap F D (T / 2) := by
    rw [hwdef, purePart, FirstKindInvolution.map_sub, FirstKindInvolution.map_algebraMap]
  have hcw : c * σ w = -(w * c) := by
    rw [hσw, mul_sub, hconj, hwdef, purePart, ← hTdef, ← Algebra.commutes]
    have hT2 : algebraMap F D T = algebraMap F D (T / 2) + algebraMap F D (T / 2) := by
      rw [← _root_.map_add, add_halves]
    rw [hT2]
    noncomm_ring
  rw [mul_assoc, hcw, mul_neg, ← mul_assoc, hw, neg_mul, neg_neg, Algebra.smul_def]

end Quaternion

section Torus

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] (hD : Module.finrank F D = 4)
  (σ : FirstKindInvolution F D) {n : ℕ} (q : σ.QuadraticForms (Fin n)) (x : Fin n → D)
  (K : Type u) [Field K] [Algebra F K]

local notation "ι" => (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D)

variable (F) in
/-- The unit `r ⊗ y` of `K ⊗ D` for units `r` of `K` and `y` of `D`. -/
def scaledUnit (r : Kˣ) (y : Dˣ) : (K ⊗[F] D)ˣ :=
  Units.map (algebraMap K (K ⊗[F] D)).toMonoidHom r *
    Units.map (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D).toMonoidHom y

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem coe_scaledUnit (r : Kˣ) (y : Dˣ) :
    (scaledUnit F K r y : K ⊗[F] D) = algebraMap K (K ⊗[F] D) r * ι y :=
  rfl

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem scaledUnit_mul (r r' : Kˣ) (y y' : Dˣ) :
    scaledUnit F K r y * scaledUnit F K r' y' = scaledUnit F K (r * r') (y * y') := by
  apply Units.ext
  simp only [Units.val_mul, coe_scaledUnit, _root_.map_mul]
  rw [mul_assoc, ← mul_assoc (ι (y : D)), ← Algebra.commutes]
  simp only [mul_assoc]

include hD in
theorem mem_lineTorus_scaledUnit (r : Kˣ) (y : Dˣ) (m0 : F)
    (hy : (y : D) * σ.sesqForm (σ.polar q) x x * σ y = m0 • σ.sesqForm (σ.polar q) x x)
    (hNy : CentralSimple.reducedNorm F D F ((1 : F) ⊗ₜ[F] (y : D)) = m0)
    (hr : (r : K) ^ 2 * algebraMap F K m0 = 1) :
    scaledUnit F K r y ∈ σ.lineTorus q x K := by
  have hdeg := FirstKindInvolution.reducedDegree_eq_two hD
  rw [mem_lineTorus_iff]
  refine ⟨?_, ?_⟩
  · rw [coe_scaledUnit, FirstKindInvolution.map_mul]
    set a := algebraMap K (K ⊗[F] D) r with ha
    have hσr : σ.baseChange K a = a := by
      rw [ha, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        baseChange_tmul, FirstKindInvolution.map_one]
    rw [hσr, baseChange_includeRight]
    have hcomm : ∀ u : K ⊗[F] D, Commute a u := fun u => Algebra.commutes _ u
    calc a * ι y * ι (σ.sesqForm (σ.polar q) x x) * (ι (σ y) * a)
        = a * (ι y * ι (σ.sesqForm (σ.polar q) x x) * ι (σ y)) * a := by
          simp only [mul_assoc]
      _ = a * a * ι ((y : D) * σ.sesqForm (σ.polar q) x x * σ y) := by
          rw [mul_assoc, ← (hcomm _).eq, ← mul_assoc, _root_.map_mul, _root_.map_mul]
      _ = ι (σ.sesqForm (σ.polar q) x x) := by
          rw [hy, _root_.map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply F K (K ⊗[F] D),
            ← mul_assoc, ha, ← _root_.map_mul, ← _root_.map_mul, ← pow_two, hr, _root_.map_one,
            one_mul]
  · rw [coe_scaledUnit, _root_.map_mul]
    have h1 : CentralSimple.reducedNorm F D K (algebraMap K (K ⊗[F] D) r) = (r : K) ^ 2 := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        CentralSimple.reducedNorm_scalar, hdeg]
    have h2 : CentralSimple.reducedNorm F D K (ι y) = algebraMap F K m0 := by
      rw [show ι y = Algebra.TensorProduct.map (Algebra.ofId F K) (AlgHom.id F D)
          ((1 : F) ⊗ₜ[F] (y : D)) by simp, CentralSimple.reducedNorm_naturality, hNy]
      rfl
    rw [h1, h2, hr]

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem scaledUnit_comm (r r' : Kˣ) (y y' : Dˣ) (h : Commute (y : D) y') :
    scaledUnit F K r y * scaledUnit F K r' y' = scaledUnit F K r' y' * scaledUnit F K r y := by
  rw [scaledUnit_mul, scaledUnit_mul, mul_comm r r']
  congr 1
  exact Units.ext h.eq

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem scaledUnit_algebraMap (r : Kˣ) (a : Fˣ) :
    scaledUnit F K r (Units.map (algebraMap F D).toMonoidHom a) =
      Units.map (algebraMap K (K ⊗[F] D)).toMonoidHom (r * Units.map (algebraMap F K).toMonoidHom a) := by
  apply Units.ext
  simp only [coe_scaledUnit, Units.coe_map, Units.val_mul, _root_.map_mul]
  congr 1
  change (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D) (algebraMap F D a) =
    algebraMap K (K ⊗[F] D) (algebraMap F K a)
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem map_scaledUnit {K' : Type u} [Field K'] [Algebra F K'] (f : K →ₐ[F] K') (r : Kˣ)
    (y : Dˣ) :
    Units.map (Algebra.TensorProduct.map f (AlgHom.id F D)).toMonoidHom (scaledUnit F K r y) =
      scaledUnit F K' (Units.map f.toMonoidHom r) y := by
  apply Units.ext
  simp only [Units.coe_map, coe_scaledUnit, _root_.map_mul]
  congr 1
  simp

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem scaledUnit_neg (r : Kˣ) (y : Dˣ) : scaledUnit F K (-r) y = -scaledUnit F K r y := by
  apply Units.ext
  simp only [coe_scaledUnit, Units.val_neg, _root_.map_neg, neg_mul]

end Torus

section Kernel

variable {F : Type u} [Field F] {G H : GroupScheme (Spec (CommRingCat.of F))} {p : G ⟶ H}
  (hp : IsCentralIsogeny p) (e : kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp)

/-- The square root `-1` of unity. -/
def negOneRoot (K : Type u) [CommRing K] : rootsOfUnity 2 K :=
  ⟨-1, (mem_rootsOfUnity 2 _).mpr (by rw [neg_one_sq])⟩

/-- The kernel point attached to a square root of unity. -/
abbrev kappa (K : Type u) [Field K] [Algebra F K] (ζ : rootsOfUnity 2 K) :
    G.affinePoints (CommAlgCat.of F K) :=
  hp.kernelPointInclusion K ((hp.kernelRootsEquiv 2 e K).symm ζ)

theorem kappa_commute (K : Type u) [Field K] [Algebra F K] (ζ : rootsOfUnity 2 K)
    (g : G.affinePoints (CommAlgCat.of F K)) : Commute (kappa hp e K ζ) g :=
  commute_of_mem_center (hp.isCentral_kernelι _ _) g

theorem kappa_mul_self (K : Type u) [Field K] [Algebra F K] (ζ : rootsOfUnity 2 K) :
    kappa hp e K ζ * kappa hp e K ζ = 1 := by
  have hζ : ζ * ζ = 1 := by
    have h := (mem_rootsOfUnity 2 _).mp ζ.property
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h]; rfl)
  rw [← _root_.map_mul, ← _root_.map_mul, hζ, _root_.map_one, _root_.map_one]

theorem kappa_one (K : Type u) [Field K] [Algebra F K] : kappa hp e K 1 = 1 := by
  rw [kappa, _root_.map_one, _root_.map_one]

theorem project_kappa (K : Type u) [Field K] [Algebra F K] (ζ : rootsOfUnity 2 K) :
    G.affinePointsTarget p (CommAlgCat.of F K) (kappa hp e K ζ) = 1 :=
  (mem_range_kernelι_iff p _).mp (SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩)

theorem eq_one_or_eq_kappa (K : Type u) [Field K] [Algebra F K]
    (k : G.affinePoints (CommAlgCat.of F K))
    (hk : G.affinePointsTarget p (CommAlgCat.of F K) k = 1) :
    k = 1 ∨ k = kappa hp e K (negOneRoot K) := by
  obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp ((mem_range_kernelι_iff p k).mpr hk)
  set ζ := hp.kernelRootsEquiv 2 e K a with hζ
  have hk' : k = kappa hp e K ζ := by
    rw [kappa, hζ, MulEquiv.symm_apply_apply]
    exact ha.symm
  have hsq : ((ζ : Kˣ) : K) * (ζ : Kˣ) = 1 := by
    have h := (mem_rootsOfUnity 2 _).mp ζ.property
    have h' := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val, Units.val_one, pow_two] at h'
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · left
    rw [hk', show ζ = 1 from Subtype.ext (Units.ext h1), kappa_one]
  · right
    rw [hk', show ζ = negOneRoot K from Subtype.ext (Units.ext h1)]

theorem kappa_naturality {K K' : Type u} [Field K] [Algebra F K] [Field K'] [Algebra F K']
    (f : K →ₐ[F] K') :
    G.affinePointMap (CommAlgCat.ofHom f) (kappa hp e K (negOneRoot K)) =
      kappa hp e K' (negOneRoot K') := by
  have h : GroupScheme.affinePointMap hp.commutativeKernel.toGrp (CommAlgCat.ofHom f)
      ((hp.kernelRootsEquiv 2 e K).symm (negOneRoot K)) =
        (hp.kernelRootsEquiv 2 e K').symm (negOneRoot K') := by
    apply (hp.kernelRootsEquiv 2 e K').injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Units.ext
    rw [hp.kernelRootsEquiv_val, hp.kernelUnitMap_naturality, ← hp.kernelRootsEquiv_val,
      MulEquiv.apply_symm_apply]
    simp [negOneRoot]
  change (algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom f).op ≫
      ((hp.kernelRootsEquiv 2 e K).symm (negOneRoot K)) ≫ (kernelι p).hom.hom = _
  rw [← Category.assoc]
  change hp.kernelPointInclusion K' (GroupScheme.affinePointMap hp.commutativeKernel.toGrp
    (CommAlgCat.ofHom f) ((hp.kernelRootsEquiv 2 e K).symm (negOneRoot K))) = _
  rw [h]

include hp e in
theorem mul_self_eq_of_project_eq (K : Type u) [Field K] [Algebra F K]
    {a b : G.affinePoints (CommAlgCat.of F K)}
    (h : G.affinePointsTarget p (CommAlgCat.of F K) a = G.affinePointsTarget p (CommAlgCat.of F K) b) :
    a * a = b * b := by
  set k := b⁻¹ * a with hk
  have hpk : G.affinePointsTarget p (CommAlgCat.of F K) k = 1 := by
    rw [hk, _root_.map_mul, _root_.map_inv, h, inv_mul_cancel]
  have hcomm : Commute k b ∧ k * k = 1 := by
    rcases eq_one_or_eq_kappa hp e K k hpk with h1 | h1
    · rw [h1]; exact ⟨Commute.one_left b, one_mul 1⟩
    · rw [h1]; exact ⟨kappa_commute hp e K _ b, kappa_mul_self hp e K _⟩
  have ha : a = b * k := by rw [hk, mul_inv_cancel_left]
  rw [ha, mul_assoc, ← mul_assoc k, hcomm.1.eq, mul_assoc, ← mul_assoc, hcomm.2, mul_one]

end Kernel

section NegOne

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] (hD : Module.finrank F D = 4)
  (σ : FirstKindInvolution F D) {n : ℕ} [NeZero n] (q : σ.QuadraticForms (Fin n))
  (x : Fin n → D) (K : Type u) [CommRing K] [Algebra F K]

omit [CharZero F] [NeZero n] in
include hD in
theorem neg_one_mem_lineTorus : (-1 : (K ⊗[F] D)ˣ) ∈ σ.lineTorus q x K := by
  have hdeg := FirstKindInvolution.reducedDegree_eq_two hD
  rw [mem_lineTorus_iff]
  refine ⟨?_, ?_⟩
  · simp [FirstKindInvolution.map_neg, FirstKindInvolution.map_one]
  · rw [Units.val_neg, Units.val_one, Algebra.TensorProduct.one_def, ← TensorProduct.neg_tmul,
      CentralSimple.reducedNorm_scalar, hdeg]
    norm_num

/-- The negation of the line, as an element of the rotation group of the line. -/
def negOneTorus : σ.lineTorus q x K := ⟨-1, neg_one_mem_lineTorus hD σ q x K⟩

variable (hc : σ.sesqForm (σ.polar q) x x ≠ 0)

theorem lineRotationHom_negOne_val :
    (((σ.normOneIsometryAffinePointsEquiv q (CommAlgCat.of F K)
      (σ.lineRotationHom q x K hc (negOneTorus hD σ q x K))).val.val :
        (K ⊗[F] Matrix (Fin n) (Fin n) D)ˣ) : K ⊗[F] Matrix (Fin n) (Fin n) D) =
      (1 : K) ⊗ₜ[F] σ.lineReflection q x := by
  rw [lineRotationHom_val]
  change (FiniteAlgebraUnits.MatrixPoints.coefficientEquiv F D K).symm
    (σ.lineRotationMatrix q x K ((-1 : (K ⊗[F] D)ˣ) : K ⊗[F] D)) = _
  rw [Units.val_neg, Units.val_one, ← map_lineReflection,
    ← coefficientEquiv_one_tmul_eq_map, AlgEquiv.symm_apply_apply]

end NegOne

/-- If the commutator of `g` and `h` is central of order at most two, then `g²` commutes
with `h`. -/
theorem commute_sq_of_commutator {Γ : Type*} [Group Γ] {g h : Γ}
    (hk : ∀ y : Γ, Commute (g * h * g⁻¹ * h⁻¹) y)
    (hk2 : (g * h * g⁻¹ * h⁻¹) * (g * h * g⁻¹ * h⁻¹) = 1) : Commute (g * g) h := by
  set k := g * h * g⁻¹ * h⁻¹ with hkdef
  have hgh : g * h = k * h * g := by rw [hkdef]; group
  show g * g * h = h * (g * g)
  calc g * g * h = g * (g * h) := by group
    _ = g * (k * h * g) := by rw [hgh]
    _ = (g * k) * h * g := by group
    _ = (k * g) * h * g := by rw [(hk g).eq]
    _ = k * (g * h) * g := by group
    _ = k * (k * h * g) * g := by rw [hgh]
    _ = (k * k) * (h * (g * g)) := by group
    _ = h * (g * g) := by rw [hk2, one_mul]

/-- In a simply connected central cover with kernel identified with `μ₂`, a lift of the
negation of a nondegenerate quaternionic line squares to the kernel point corresponding
to `-1`. -/
theorem lift_mul_self_eq_kappa
    {F : Type u} [Field F] [CharZero F]
    {D : Type u} [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D]
    (hD : Module.finrank F D = 4) (σ : FirstKindInvolution F D)
    (hσ : Module.finrank F σ.symmetricSubspace = 3) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (q : σ.QuadraticForms (Fin n)) (hq : σ.IsNondegenerateQuadratic q)
    {G : GroupScheme (Spec (CommRingCat.of F))} {p : G ⟶ σ.normOneIsometryGroup q}
    (hG : IsSimplyConnected G) (hp : IsCentralIsogeny p)
    (e : kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp)
    (x : Fin n → D) (hx : σ.sesqForm (σ.polar q) x x ≠ 0)
    (E : Type u) [Field E] [Algebra F E] (y : G.affinePoints (CommAlgCat.of F E))
    (hy : G.affinePointsTarget p (CommAlgCat.of F E) y =
      σ.lineRotationHom q x E hx (negOneTorus hD σ q x E)) :
    y * y = kappa hp e E (negOneRoot E) := by
  have hsq : negOneTorus hD σ q x E * negOneTorus hD σ q x E = 1 := by
    apply Subtype.ext
    change (-1 : (E ⊗[F] D)ˣ) * -1 = 1
    rw [neg_one_mul, neg_neg]
  have hker : G.affinePointsTarget p (CommAlgCat.of F E) (y * y) = 1 := by
    rw [_root_.map_mul, hy, ← _root_.map_mul, hsq, _root_.map_one]
  rcases eq_one_or_eq_kappa hp e E (y * y) hker with h1 | h1
  · exfalso
    let Ω := AlgebraicClosure E
    let f : E →ₐ[F] Ω := IsScalarTower.toAlgHom F E Ω
    let y' := G.affinePointMap (CommAlgCat.ofHom f) y
    have hnegmap : σ.lineTorusMap q x f (negOneTorus hD σ q x E) = negOneTorus hD σ q x Ω := by
      apply Subtype.ext
      change Units.map (Algebra.TensorProduct.map f (AlgHom.id F D)).toMonoidHom (-1) = -1
      ext
      simp
    have hy' : G.affinePointsTarget p (CommAlgCat.of F Ω) y' =
        σ.lineRotationHom q x Ω hx (negOneTorus hD σ q x Ω) := by
      have h0 : G.affinePointsTarget p (CommAlgCat.of F Ω) y' =
          (σ.normOneIsometryGroup q).affinePointMap (CommAlgCat.ofHom f)
            (G.affinePointsTarget p (CommAlgCat.of F E) y) := by
        simp only [y', GroupScheme.affinePointsTarget_apply, GroupScheme.affinePointMap_apply,
          Category.assoc]
      rw [h0, hy, lineRotationHom_naturality, hnegmap]
    have hval := lineRotationHom_negOne_val hD σ q x Ω hx
    rw [← hy'] at hval
    apply lineReflection_lift_mul_self_ne_one hD σ hσ hn q hq hG hp x hx Ω y' hval
    change G.affinePointMap (CommAlgCat.ofHom f) y * G.affinePointMap (CommAlgCat.ofHom f) y = 1
    rw [← _root_.map_mul, h1, _root_.map_one]
  · exact h1

section Descent

open GaloisPoint

variable {F : Type u} [Field F] {G H : GroupScheme (Spec (CommRingCat.of F))} {p : G ⟶ H}
  (hp : IsCentralIsogeny p) (e : kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp)

theorem rootValue_eq_one {M : Type u} [Field M] [Algebra F M] (N : Fˣ) (z : Mˣ)
    (hz : z ^ 2 = Units.map (algebraMap F M) N) (s : M ≃ₐ[F] M) (h : s (z : M) = z) :
    KummerCocycle.rootValue 2 N hz s = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ((s • z / z : Mˣ) : M) = 1
  rw [Units.val_div_eq_div_val]
  change s (z : M) / z = 1
  rw [h, div_self z.ne_zero]

theorem rootValue_eq_negOneRoot {M : Type u} [Field M] [Algebra F M] (N : Fˣ) (z : Mˣ)
    (hz : z ^ 2 = Units.map (algebraMap F M) N) (s : M ≃ₐ[F] M) (h : s (z : M) = -z) :
    KummerCocycle.rootValue 2 N hz s = negOneRoot M := by
  apply Subtype.ext
  apply Units.ext
  change ((s • z / z : Mˣ) : M) = -1
  rw [Units.val_div_eq_div_val]
  change s (z : M) / z = -1
  rw [h, neg_div, div_self z.ne_zero]

theorem eq_or_eq_neg_of_sq {M : Type u} [Field M] [Algebra F M] (N : Fˣ) (z : Mˣ)
    (hz : z ^ 2 = Units.map (algebraMap F M) N) (s : M ≃ₐ[F] M) :
    s (z : M) = z ∨ s (z : M) = -z := by
  have h2 : ((z : M)) * z = algebraMap F M N := by
    have h := congrArg Units.val hz
    rwa [Units.val_pow_eq_pow_val, pow_two] at h
  have h3 : s (z : M) * s z = z * z := by
    rw [← _root_.map_mul, h2, AlgEquiv.commutes]
  exact mul_self_eq_mul_self_iff.mp h3

/-- The Kummer image is trivial when the square root is fixed by every automorphism. -/
theorem kummerImageTrivial_of_forall_fixed
    (M : Type u) [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
    (N : Fˣ) (z : Mˣ) (hz : z ^ 2 = Units.map (algebraMap F M) N)
    (h : ∀ s : M ≃ₐ[F] M, s (z : M) = z) :
    KummerImageTrivial hp e F M N z hz := by
  refine ⟨1, fun s => ?_⟩
  rw [rootValue_eq_one N z hz s (h s), _root_.map_one, _root_.map_one, _root_.map_one, inv_one,
    mul_one]

/-- Let `F ⊆ M ⊆ E` be fields with `M/F` and `E/F` finite Galois, and let `z ∈ Mˣ` square to
`N ∈ Fˣ`. Take an affine source `G` of a central isogeny with kernel identified with `μ₂`.
Suppose `b' ∈ G(E)` is fixed by the automorphisms over `F` fixing `z` and is multiplied by
the kernel point of `-1` by those negating `z`. Then `b'` descends to a point giving a
coboundary for the image of the Kummer cocycle on `Spec M → Spec F`. -/
theorem kummerImageTrivial_of_twisted [IsAffine G.X.left]
    (M : Type u) [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [Algebra M E] [IsScalarTower F M E]
    (N : Fˣ) (z : Mˣ) (hz : z ^ 2 = Units.map (algebraMap F M) N)
    (b' : G.affinePoints (CommAlgCat.of F E))
    (hfix : ∀ s : E ≃ₐ[F] E, s (algebraMap M E z) = algebraMap M E z →
      conjugate F E G s b' = b')
    (hneg : ∀ s : E ≃ₐ[F] E, s (algebraMap M E z) = -algebraMap M E z →
      conjugate F E G s b' = kappa hp e E (negOneRoot E) * b') :
    KummerImageTrivial hp e F M N z hz := by
  have : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  have hb' : b' ∈ relativeFixedSubgroup F M E G := by
    intro τ
    exact hfix (τ.restrictScalars F) (τ.commutes (z : M))
  set b := (relativeFixedEquiv F M E G).symm ⟨b', hb'⟩ with hbdef
  have hext : relativeExtend F M E G b = b' :=
    congrArg Subtype.val ((relativeFixedEquiv F M E G).apply_symm_apply ⟨b', hb'⟩)
  refine ⟨b, fun s => ?_⟩
  have hlift : relativeExtend F M E G (relativeConjugate F F M G s b) =
      conjugate F E G (s.liftNormal E) b' := by
    rw [← hext]
    exact relativeExtend_conjugate_lift F M E G s b
  have hcomm : s.liftNormal E (algebraMap M E z) = algebraMap M E (s z) :=
    AlgEquiv.liftNormal_commutes s E (z : M)
  rcases eq_or_eq_neg_of_sq N z hz s with h | h
  · rw [rootValue_eq_one N z hz s h, _root_.map_one, _root_.map_one]
    have hb : relativeConjugate F F M G s b = b := by
      apply relativeExtend_injective F M E G
      rw [hlift, hfix _ (by rw [hcomm, h]), hext]
    rw [hb, mul_inv_cancel]
  · rw [rootValue_eq_negOneRoot N z hz s h]
    have hb : relativeConjugate F F M G s b = kappa hp e M (negOneRoot M) * b := by
      apply relativeExtend_injective F M E G
      rw [hlift, hneg _ (by rw [hcomm, h, _root_.map_neg]), _root_.map_mul, hext]
      congr 1
      exact (kappa_naturality hp e (IsScalarTower.toAlgHom F M E)).symm
    rw [hb, _root_.mul_inv_rev, mul_inv_cancel_left]
    exact (inv_eq_of_mul_eq_one_right (kappa_mul_self hp e M _)).symm

end Descent

/-- Let `h` and `g` lift the rotations of commuting elements `t₀` and `t₁` of the line torus of
a nondegenerate line, with `t₁²` the negation of the line. Then `g²` lifts the negation, so its
square is the nontrivial kernel point, and every lift of the product of the negation with `t₀`
squares to the nontrivial kernel point times `h²`. -/
theorem mul_self_eq_kappa_mul_of_lifts
    {F : Type u} [Field F] [CharZero F]
    {D : Type u} [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D]
    (hD : Module.finrank F D = 4) (σ : FirstKindInvolution F D)
    (hσ : Module.finrank F σ.symmetricSubspace = 3) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (q : σ.QuadraticForms (Fin n)) (hq : σ.IsNondegenerateQuadratic q)
    {G : GroupScheme (Spec (CommRingCat.of F))} {p : G ⟶ σ.normOneIsometryGroup q}
    (hG : IsSimplyConnected G) (hp : IsCentralIsogeny p)
    (e : kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp)
    (x : Fin n → D) (hx : σ.sesqForm (σ.polar q) x x ≠ 0)
    (E : Type u) [Field E] [Algebra F E] (t₀ t₁ : σ.lineTorus q x E) (hcomm : Commute t₀ t₁)
    (h₁ : t₁ * t₁ = negOneTorus hD σ q x E)
    (h g : G.affinePoints (CommAlgCat.of F E))
    (hh : G.affinePointsTarget p (CommAlgCat.of F E) h = σ.lineRotationHom q x E hx t₀)
    (hg : G.affinePointsTarget p (CommAlgCat.of F E) g = σ.lineRotationHom q x E hx t₁)
    (a : G.affinePoints (CommAlgCat.of F E))
    (ha : G.affinePointsTarget p (CommAlgCat.of F E) a =
      σ.lineRotationHom q x E hx (negOneTorus hD σ q x E * t₀)) :
    a * a = kappa hp e E (negOneRoot E) * (h * h) := by
  set y := g * g with hy
  have hpy : G.affinePointsTarget p (CommAlgCat.of F E) y =
      σ.lineRotationHom q x E hx (negOneTorus hD σ q x E) := by
    rw [hy, _root_.map_mul, hg, ← _root_.map_mul, h₁]
  have hyy := lift_mul_self_eq_kappa hD σ hσ hn q hq hG hp e x hx E y hpy
  set k := g * h * g⁻¹ * h⁻¹ with hk
  have hpk : G.affinePointsTarget p (CommAlgCat.of F E) k = 1 := by
    rw [hk, _root_.map_mul, _root_.map_mul, _root_.map_mul, _root_.map_inv, _root_.map_inv, hg, hh,
      ← _root_.map_inv, ← _root_.map_inv, ← _root_.map_mul, ← _root_.map_mul, ← _root_.map_mul,
      hcomm.symm.eq, mul_inv_cancel_right, mul_inv_cancel, _root_.map_one]
  have hkc : (∀ w, Commute k w) ∧ k * k = 1 := by
    rcases eq_one_or_eq_kappa hp e E k hpk with h1 | h1
    · rw [h1]; exact ⟨fun w => Commute.one_left w, one_mul 1⟩
    · rw [h1]; exact ⟨kappa_commute hp e E _, kappa_mul_self hp e E _⟩
  have hyh : Commute y h := commute_sq_of_commutator hkc.1 hkc.2
  have hpa : G.affinePointsTarget p (CommAlgCat.of F E) a =
      G.affinePointsTarget p (CommAlgCat.of F E) (y * h) := by
    rw [ha, _root_.map_mul, _root_.map_mul, hpy, hh]
  rw [mul_self_eq_of_project_eq hp e E hpa, ← hyy]
  calc y * h * (y * h) = y * (h * y) * h := by simp only [mul_assoc]
    _ = y * y * (h * h) := by rw [← hyh.eq]; simp only [mul_assoc]

/-- A finite extension of `M` containing a square root of a given element of `F`. -/
theorem exists_sqrt_extension (F M : Type u) [Field F] [Field M] [Algebra F M]
    [FiniteDimensional F M] (β : F) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra M L) (_ : Algebra F L) (_ : IsScalarTower F M L)
      (_ : FiniteDimensional F L), ∃ l : L, l * l = algebraMap F L β := by
  let f : Polynomial M := Polynomial.X ^ 2 - Polynomial.C (algebraMap F M β)
  have hf : (f.map (algebraMap M f.SplittingField)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]
    norm_num
  obtain ⟨l, hl⟩ := (Polynomial.SplittingField.splits f).exists_eval_eq_zero hf
  refine ⟨f.SplittingField, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.Finite.trans M f.SplittingField, l, ?_⟩
  simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hl
  rw [← pow_two, IsScalarTower.algebraMap_apply F M f.SplittingField]
  exact sub_eq_zero.mp hl

end QuaternionicLineSimilitude

open QuaternionicLineSimilitude

set_option maxHeartbeats 800000 in
/-- **The spinor norm of a line similitude.** Let `c = h(x, x) ≠ 0` and `d c σ(d) = N c` with
`N = Nrd(d) ∈ Fˣ`. For a simply connected central cover of the norm-one isometry group with
kernel identified with `μ₂`, the image of the Kummer cocycle of `N` is a coboundary on each
finite Galois cover containing a square root of `N`. -/
theorem quaternionicSpinLineSimilitudeBoundary :
    QuaternionicSpinLineSimilitudeBoundaryStatement.{u} := by
  intro F _ _ D _ _ _ _ hD σ hσ n _ hn q hq G p hG hp e x d N hx hd hN M _ _ _ _ z hz
  have : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hdeg := FirstKindInvolution.reducedDegree_eq_two hD
  by_cases hw : purePart F d = 0
  · -- `d` is a scalar `a`, so `N = a²` and the square root `z` lies in `F`
    set a := CentralDivision.reducedTrace F D d / 2 with ha
    have hda : d = algebraMap F D a := by
      rw [purePart, sub_eq_zero] at hw
      exact hw
    have hNa : (N : F) = a * a := by
      rw [← hN, hda, show (1 : F) ⊗ₜ[F] algebraMap F D a = a ⊗ₜ[F] (1 : D) by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          smul_eq_mul, mul_one],
        CentralSimple.reducedNorm_scalar, hdeg, pow_two]
    have hz2 : (z : M) * z = algebraMap F M a * algebraMap F M a := by
      have h := congrArg Units.val hz
      rw [Units.val_pow_eq_pow_val, pow_two] at h
      rw [h, Units.coe_map, MonoidHom.coe_ofClass, hNa, _root_.map_mul]
    apply kummerImageTrivial_of_forall_fixed hp e M N z hz
    intro s
    rcases mul_self_eq_mul_self_iff.mp hz2 with h | h <;> rw [h] <;> simp
  · -- the pure part `w` of `d` is a unit with `w² = -β`
    set w := purePart F d with hwdef
    set β := CentralSimple.reducedNorm F D F ((1 : F) ⊗ₜ[F] w) with hβdef
    have hww : w * w = -algebraMap F D β := purePart_mul_self hD d
    have hβ0 : β ≠ 0 := by
      intro h0
      rw [h0, _root_.map_zero, neg_zero] at hww
      exact hw (mul_self_eq_zero.mp hww)
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [TensorProduct.tmul_zero, _root_.map_zero] at hN
      exact N.ne_zero hN.symm
    have hwc := purePart_mul_mul_map hD σ (σ.sesqForm (σ.polar q) x x) d N hd hN N.ne_zero
    -- a field `L ⊇ M` containing a square root `l` of `β`
    obtain ⟨L, _, _, _, _, _, l, hl⟩ := exists_sqrt_extension F M β
    have hβL : algebraMap F L β ≠ 0 := (map_ne_zero _).mpr hβ0
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hl
      exact hβL hl.symm
    set lU := Units.mk0 l hl0
    set zL : Lˣ := Units.map (algebraMap M L) z with hzL
    set dU := Units.mk0 d hd0
    set wU := Units.mk0 w hw
    have hzL2 : ((zL : L)) ^ 2 = algebraMap F L N := by
      have h := congrArg (fun u : Mˣ => algebraMap M L (u : M)) hz
      simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass,
        _root_.map_pow] at h
      rw [IsScalarTower.algebraMap_apply F M L, ← h]
      rfl
    have ht₀ : scaledUnit F L zL⁻¹ dU ∈ σ.lineTorus q x L :=
      mem_lineTorus_scaledUnit hD σ q x L zL⁻¹ dU N hd hN (by
        rw [Units.val_inv_eq_inv_val, inv_pow, hzL2,
          inv_mul_cancel₀ ((map_ne_zero _).mpr N.ne_zero)])
    have ht₁ : scaledUnit F L lU⁻¹ wU ∈ σ.lineTorus q x L :=
      mem_lineTorus_scaledUnit hD σ q x L lU⁻¹ wU β hwc rfl (by
        rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, pow_two, hl, inv_mul_cancel₀ hβL])
    -- lifts of the two rotations over a finite Galois extension `E ⊇ L`
    obtain ⟨E, _, _, _, _, _, _, hlift⟩ := hp.exists_finiteGalois_coefficient_lifts
      ![σ.lineRotationHom q x L hx ⟨_, ht₀⟩, σ.lineRotationHom q x L hx ⟨_, ht₁⟩]
    obtain ⟨h, hh⟩ := hlift 0
    obtain ⟨g, hg⟩ := hlift 1
    let : Algebra M E := ((algebraMap L E).comp (algebraMap M L)).toAlgebra
    have : IsScalarTower F M E := IsScalarTower.of_algebraMap_eq (fun r => by
      change algebraMap F E r = algebraMap L E (algebraMap M L (algebraMap F M r))
      rw [← IsScalarTower.algebraMap_apply F M L, ← IsScalarTower.algebraMap_apply F L E])
    set jE := IsScalarTower.toAlgHom F L E with hjE
    set t₀ := σ.lineTorusMap q x jE ⟨_, ht₀⟩ with ht₀def
    set t₁ := σ.lineTorusMap q x jE ⟨_, ht₁⟩ with ht₁def
    have hh' : G.affinePointsTarget p (CommAlgCat.of F E) h = σ.lineRotationHom q x E hx t₀ := by
      rw [hh, Matrix.cons_val_zero]
      exact lineRotationHom_naturality _ _ _ _ _ _
    have hg' : G.affinePointsTarget p (CommAlgCat.of F E) g = σ.lineRotationHom q x E hx t₁ := by
      rw [hg, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact lineRotationHom_naturality _ _ _ _ _ _
    have ht₀v : (t₀ : (E ⊗[F] D)ˣ) = scaledUnit F E (Units.map jE.toMonoidHom zL⁻¹) dU :=
      map_scaledUnit L jE zL⁻¹ dU
    have ht₁v : (t₁ : (E ⊗[F] D)ˣ) = scaledUnit F E (Units.map jE.toMonoidHom lU⁻¹) wU :=
      map_scaledUnit L jE lU⁻¹ wU
    have hcomm : Commute t₀ t₁ := by
      apply Subtype.ext
      change (t₀ : (E ⊗[F] D)ˣ) * t₁ = t₁ * t₀
      rw [ht₀v, ht₁v]
      exact scaledUnit_comm E _ _ dU wU (purePart_commute d).symm
    have h₁ : t₁ * t₁ = negOneTorus hD σ q x E := by
      apply Subtype.ext
      change (t₁ : (E ⊗[F] D)ˣ) * t₁ = -1
      rw [ht₁v, scaledUnit_mul]
      have hr : ((Units.map jE.toMonoidHom lU⁻¹ * Units.map jE.toMonoidHom lU⁻¹ : Eˣ) : E) *
          algebraMap F E β = 1 := by
        rw [← jE.commutes β, Units.val_mul, Units.coe_map]
        change jE ((lU⁻¹ : Lˣ) : L) * jE ((lU⁻¹ : Lˣ) : L) * jE (algebraMap F L β) = 1
        rw [← _root_.map_mul, ← _root_.map_mul, ← hl, Units.val_inv_eq_inv_val, Units.val_mk0,
          show l⁻¹ * l⁻¹ * (l * l) = 1 by field_simp, _root_.map_one]
      apply Units.ext
      rw [coe_scaledUnit, Units.val_neg, Units.val_one]
      change algebraMap E (E ⊗[F] D) _ *
        (Algebra.TensorProduct.includeRight : D →ₐ[F] E ⊗[F] D) (w * w) = -1
      rw [hww, _root_.map_neg, AlgHom.commutes, mul_neg,
        IsScalarTower.algebraMap_apply F E (E ⊗[F] D), ← _root_.map_mul, hr, _root_.map_one]
    have hr₀ : ((Units.map jE.toMonoidHom zL⁻¹ : Eˣ) : E) = (algebraMap M E z)⁻¹ := by
      rw [Units.coe_map]
      change jE ((zL⁻¹ : Lˣ) : L) = _
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      rfl
    have hconj : ∀ s : E ≃ₐ[F] E, G.affinePointsTarget p (CommAlgCat.of F E)
        (GaloisPoint.conjugate F E G s h) =
          σ.lineRotationHom q x E hx (σ.lineTorusMap q x s.toAlgHom t₀) := by
      intro s
      change G.affinePointsTarget p (CommAlgCat.of F E)
        (G.affinePointMap (CommAlgCat.ofHom s.toAlgHom) h) = _
      rw [affinePointsTarget_affinePointMap, hh', lineRotationHom_naturality]
    have hmap : ∀ s : E ≃ₐ[F] E, ((σ.lineTorusMap q x s.toAlgHom t₀ : σ.lineTorus q x E) :
        (E ⊗[F] D)ˣ) = scaledUnit F E
          (Units.map s.toAlgHom.toMonoidHom (Units.map jE.toMonoidHom zL⁻¹)) dU := by
      intro s
      change Units.map _ (t₀ : (E ⊗[F] D)ˣ) = _
      rw [ht₀v]
      exact map_scaledUnit E s.toAlgHom _ dU
    apply kummerImageTrivial_of_twisted hp e M E N z hz (h * h)
    · intro s hs
      rw [_root_.map_mul]
      apply mul_self_eq_of_project_eq hp e E
      rw [hconj, hh']
      congr 1
      apply Subtype.ext
      rw [hmap, ht₀v]
      congr 1
      apply Units.ext
      rw [Units.coe_map]
      change s _ = _
      rw [hr₀, map_inv₀, hs]
    · intro s hs
      rw [_root_.map_mul]
      apply mul_self_eq_kappa_mul_of_lifts hD σ hσ hn q hq hG hp e x hx E t₀ t₁ hcomm h₁ h g hh' hg'
      rw [hconj]
      congr 1
      apply Subtype.ext
      change _ = (-1 : (E ⊗[F] D)ˣ) * t₀
      rw [hmap, ht₀v, neg_one_mul, ← scaledUnit_neg]
      congr 1
      apply Units.ext
      rw [Units.coe_map, Units.val_neg, hr₀]
      change s _ = _
      rw [map_inv₀, hs, inv_neg]

end Langlands.GroupScheme

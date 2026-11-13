import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.Quaternionic.NormSquareCover
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.AdjoinRoot

/-!
# Descent of the reduced norm along lifts of the Levi subgroup

Let `π : S ⟶ G` be a homomorphism of group schemes over a field `K` whose kernel is central,
`D` a finite-dimensional central division algebra over `K` of reduced degree two, and
`Λ : GL₁(D) ⟶ G` a homomorphism. Let `μ : 𝔾_m ⟶ S` and `ψ : SL₁(D) ⟶ S` lift `Λ` on the
scalars and on the reduced-norm-one units. For a `K`-algebra `A` and `u ∈ μ₂(A)` put
`z(u) = μ(u) ψ(u · 1)`, a point of `ker π` over `A`.

The kernel condition `KernelGenerator hdeg π μ ψ` says that `z` is a bijection from `μ₂(A)`
onto the points of `ker π` over `A`, for every `K`-algebra `A`. Under it, the main theorem
`exists_sq_eq_reducedNorm_of_comp_eq` shows: if a rational point `s` of `S` lies over `Λ(a)`,
then the reduced norm of `a` is a square in `K`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

open Langlands.CentralSimple

/-! ### Algebra -/

/-- Over a field `K`, an element `x` of a `K`-algebra `R` with `x ⊗ 1 = 1 ⊗ x` in
`R ⊗[K] R` is a scalar. -/
theorem exists_algebraMap_eq_of_tmul_eq {K R : Type*} [Field K] [Ring R] [Algebra K R]
    {x : R} (hx : x ⊗ₜ[K] (1 : R) = (1 : R) ⊗ₜ[K] x) : ∃ c : K, algebraMap K R c = x := by
  by_contra hne
  have hx1 : x ∉ K ∙ (1 : R) := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact hne ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  obtain ⟨f, hfx, hf1⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx1 inferInstance
  have hf1' : f 1 = 0 := by
    have h : f 1 ∈ (K ∙ (1 : R)).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self 1)
    rw [hf1] at h
    exact h
  have hR : (1 : R) ≠ 0 := by
    intro h
    apply hne
    refine ⟨0, ?_⟩
    rw [map_zero]
    calc (0 : R) = x * 0 := (mul_zero x).symm
      _ = x := by rw [← h, mul_one]
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero K hR
  have h := congrArg (TensorProduct.lift ((LinearMap.mul K K).compl₁₂ f g)) hx
  simp only [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
    hf1', zero_mul] at h
  exact mul_ne_zero hfx hg h

section QuadraticRoot

variable {K : Type u} [Field K] (c : K)

/-- The `K`-algebra `K[t]/(t² - c)`. -/
abbrev QuadraticRoot : Type u := AdjoinRoot (X ^ 2 - C c)

theorem quadraticRoot_root_sq :
    (AdjoinRoot.root (X ^ 2 - C c)) ^ 2 = algebraMap K (QuadraticRoot c) c := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C c)
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  rw [h, AdjoinRoot.algebraMap_eq]

instance quadraticRoot_nontrivial : Nontrivial (QuadraticRoot c) :=
  AdjoinRoot.nontrivial _ (by rw [degree_X_pow_sub_C (by norm_num)]; norm_num)

variable {c}

/-- The root `t` of `t² = c` is a unit when `c ≠ 0`. -/
def quadraticRootUnit (hc : c ≠ 0) : (QuadraticRoot c)ˣ :=
  Units.mkOfMulEqOne (AdjoinRoot.root (X ^ 2 - C c))
    (AdjoinRoot.root (X ^ 2 - C c) * algebraMap K (QuadraticRoot c) c⁻¹) (by
      rw [← mul_assoc, ← pow_two, quadraticRoot_root_sq, ← map_mul, mul_inv_cancel₀ hc,
        map_one])

@[simp] theorem quadraticRootUnit_val (hc : c ≠ 0) :
    (quadraticRootUnit hc : QuadraticRoot c) = AdjoinRoot.root (X ^ 2 - C c) := rfl

theorem quadraticRootUnit_sq (hc : c ≠ 0) :
    ((quadraticRootUnit hc : QuadraticRoot c)) ^ 2 = algebraMap K (QuadraticRoot c) c :=
  quadraticRoot_root_sq c

/-- **Descent along `K[t]/(t² - c)`.** Let `t` be the root and `w ∈ K[t]/(t² - c)` with
`w² = 1`. If `1 ⊗ w = (1 ⊗ t)(t⁻¹ ⊗ 1)(w ⊗ 1)` in `K[t]/(t² - c) ⊗ K[t]/(t² - c)`, then `c` is a
square in `K`: the element `w t` satisfies `wt ⊗ 1 = 1 ⊗ wt`, so it is a scalar `x`, and
`x² = w² t² = c`. -/
theorem exists_sq_of_tmul_relation (hc : c ≠ 0) (w : QuadraticRoot c) (hw : w ^ 2 = 1)
    (h : (1 : QuadraticRoot c) ⊗ₜ[K] w =
      (1 ⊗ₜ[K] (quadraticRootUnit hc : QuadraticRoot c)) *
        ((((quadraticRootUnit hc)⁻¹ : (QuadraticRoot c)ˣ) : QuadraticRoot c) ⊗ₜ[K] 1) *
          (w ⊗ₜ[K] 1)) :
    ∃ x : K, c = x ^ 2 := by
  set t : QuadraticRoot c := (quadraticRootUnit hc : QuadraticRoot c) with ht
  set ti : QuadraticRoot c := (((quadraticRootUnit hc)⁻¹ : (QuadraticRoot c)ˣ) : QuadraticRoot c)
    with hti
  have hinv : (t ⊗ₜ[K] (1 : QuadraticRoot c)) * (ti ⊗ₜ[K] 1) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ht, hti, Units.mul_inv, one_mul,
      Algebra.TensorProduct.one_def]
  have hsq : ((1 : QuadraticRoot c) ⊗ₜ[K] t) * (1 ⊗ₜ[K] t) = (t ⊗ₜ[K] 1) * (t ⊗ₜ[K] 1) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      ← pow_two, ht, quadraticRootUnit_sq hc, Algebra.algebraMap_eq_smul_one,
      ← TensorProduct.smul_tmul]
  have heqt : (w * t) ⊗ₜ[K] (1 : QuadraticRoot c) = (1 : QuadraticRoot c) ⊗ₜ[K] (w * t) := by
    have e1 : (w * t) ⊗ₜ[K] (1 : QuadraticRoot c) = (w ⊗ₜ[K] 1) * (t ⊗ₜ[K] 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have e2 : (1 : QuadraticRoot c) ⊗ₜ[K] (w * t) = (1 ⊗ₜ[K] w) * (1 ⊗ₜ[K] t) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e1, e2, h]
    linear_combination (-(w ⊗ₜ[K] (1 : QuadraticRoot c)) * (t ⊗ₜ[K] 1)) * hinv +
      (-(w ⊗ₜ[K] (1 : QuadraticRoot c)) * (ti ⊗ₜ[K] 1)) * hsq
  obtain ⟨x, hx⟩ := exists_algebraMap_eq_of_tmul_eq heqt
  have key : algebraMap K (QuadraticRoot c) (x ^ 2) = algebraMap K (QuadraticRoot c) c := by
    rw [map_pow, hx, mul_pow, hw, one_mul, ht]
    exact quadraticRootUnit_sq hc
  exact ⟨x, ((algebraMap K (QuadraticRoot c)).injective key).symm⟩

end QuadraticRoot

/-! ### Coefficient points -/

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D]

/-- `𝔾_m(A) = Aˣ`. -/
abbrev gmPoint (A : CommAlgCat.{u} (CommRingCat.of K)) :
    Aˣ ≃* GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp A :=
  (Gm.affineUnitsEquiv (CommRingCat.of K) A).symm

/-- `GL₁(D)(A) = (A ⊗ D)ˣ`. -/
abbrev unitPoint (A : CommAlgCat.{u} (CommRingCat.of K)) :
    (A ⊗[K] D)ˣ ≃* (CentralSimpleUnits.groupScheme K D).affinePoints A :=
  (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K D) A).symm

/-- `SL₁(D)(A)`. -/
abbrev normOnePoint (A : CommAlgCat.{u} (CommRingCat.of K)) :
    reducedNormOne K D A ≃* (CentralSimpleUnits.normOne K D).affinePoints A :=
  (CentralSimpleUnits.normOneAffinePointsEquiv K D A).symm

theorem gmPoint_naturality {A B : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B) (t : Aˣ) :
    GroupScheme.affinePointMap (Gm (Spec (CommRingCat.of K))).toGrp f (gmPoint A t) =
      gmPoint B (Units.map f.hom.toRingHom.toMonoidHom t) := by
  apply (Gm.affineUnitsEquiv (CommRingCat.of K) B).injective
  rw [Gm.affineUnitsEquiv_naturality]
  simp

omit [Algebra.IsCentral K D] in
theorem unitPoint_naturality {A B : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B)
    (a : (A ⊗[K] D)ˣ) :
    (CentralSimpleUnits.groupScheme K D).affinePointMap f (unitPoint A a) =
      unitPoint B (Units.map (Algebra.TensorProduct.map f.hom (AlgHom.id K D)).toMonoidHom a) := by
  apply (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K D) B).injective
  rw [GroupScheme.affinePointMap_apply, FiniteAlgebraUnits.affinePointsEquiv_naturality]
  simp only [unitPoint, MulEquiv.apply_symm_apply]

theorem normOnePoint_comp_normOneι (A : CommAlgCat.{u} (CommRingCat.of K))
    (b : reducedNormOne K D A) :
    normOnePoint A b ≫ (CentralSimpleUnits.normOneι K D).hom.hom = unitPoint A b.val := by
  apply (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K D) A).injective
  rw [← CentralSimpleUnits.normOneAffinePointsEquiv_val]
  simp only [unitPoint, normOnePoint, MulEquiv.apply_symm_apply]

/-- The restriction of `SL₁(D)` points along a coefficient map. -/
def normOneMap {A B : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B) :
    reducedNormOne K D A →* reducedNormOne K D B :=
  ((Units.map (Algebra.TensorProduct.map f.hom (AlgHom.id K D)).toMonoidHom).comp
    (reducedNormOne K D A).subtype).codRestrict _ (fun b => by
      change reducedNormUnits K D B _ = 1
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, reducedNormUnits_naturality,
        show reducedNormUnits K D A b.val = 1 from b.2, map_one])

@[simp] theorem normOneMap_val {A B : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B)
    (b : reducedNormOne K D A) :
    (normOneMap f b).val =
      Units.map (Algebra.TensorProduct.map f.hom (AlgHom.id K D)).toMonoidHom b.val := rfl

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
theorem normCoverScalarUnits_map {A B : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B)
    (t : Aˣ) :
    Units.map (Algebra.TensorProduct.map f.hom (AlgHom.id K D)).toMonoidHom
        (normCoverScalarUnits K D A t) =
      normCoverScalarUnits K D B (Units.map f.hom.toRingHom.toMonoidHom t) := by
  apply Units.ext
  simp [normCoverScalarUnits_val, Algebra.TensorProduct.map_tmul]

theorem normOnePoint_naturality {A B : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B)
    (b : reducedNormOne K D A) :
    (CentralSimpleUnits.normOne K D).affinePointMap f (normOnePoint A b) =
      normOnePoint B (normOneMap f b) := by
  apply (CentralSimpleUnits.normOneAffinePointsEquiv K D B).injective
  apply Subtype.ext
  rw [CentralSimpleUnits.normOneAffinePointsEquiv_val, MulEquiv.apply_symm_apply,
    normOneMap_val, GroupScheme.affinePointMap_apply, Category.assoc,
    FiniteAlgebraUnits.affinePointsEquiv_naturality, ← CentralSimpleUnits.normOneAffinePointsEquiv_val,
    MulEquiv.apply_symm_apply]

variable (hdeg : reducedDegree K D = 2)

/-- The scalar `u · 1 ∈ SL₁(D)(A)` for `u ∈ μ₂(A)`. -/
def scalarNormOne (A : CommAlgCat.{u} (CommRingCat.of K)) :
    rootsOfUnity 2 A →* reducedNormOne K D A :=
  ((normCoverScalarUnits K D A).comp (rootsOfUnity 2 A).subtype).codRestrict _ (fun u => by
    change reducedNormUnits K D A _ = 1
    rw [MonoidHom.comp_apply, reducedNormUnits_normCoverScalarUnits K D A hdeg]
    exact (mem_rootsOfUnity 2 _).mp u.2)

@[simp] theorem scalarNormOne_val (A : CommAlgCat.{u} (CommRingCat.of K))
    (u : rootsOfUnity 2 A) :
    (scalarNormOne hdeg A u).val = normCoverScalarUnits K D A (u : Aˣ) := rfl

/-! ### The kernel map `z` and the kernel condition -/

variable {S G : GroupScheme (Spec (CommRingCat.of K))} (π : S ⟶ G)
  (mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S) (psi : CentralSimpleUnits.normOne K D ⟶ S)

theorem affinePointMap_comp_hom {H : GroupScheme (Spec (CommRingCat.of K))}
    {A B : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B) (g : H ⟶ S) (x : H.affinePoints A) :
    S.affinePointMap f (x ≫ g.hom.hom) = H.affinePointMap f x ≫ g.hom.hom := by
  rw [GroupScheme.affinePointMap_apply, GroupScheme.affinePointMap_apply, Category.assoc]

/-- `z(u) = μ(u) ψ(u · 1)` for `u ∈ μ₂(A)`. -/
def kernelPoint (A : CommAlgCat.{u} (CommRingCat.of K)) (u : rootsOfUnity 2 A) :
    S.affinePoints A :=
  (gmPoint A (u : Aˣ) ≫ mu.hom.hom) * (normOnePoint A (scalarNormOne hdeg A u) ≫ psi.hom.hom)

/-- **Kernel condition.** For every `K`-algebra `A`, every point `k` of `S` over `A` with
`π(k) = 1` is `z(u)` for exactly one `u ∈ μ₂(A)`. -/
def KernelGenerator : Prop :=
  ∀ (A : CommAlgCat.{u} (CommRingCat.of K)) (k : S.affinePoints A), k ≫ π.hom.hom = 1 →
    ∃! u : rootsOfUnity 2 A, kernelPoint hdeg mu psi A u = k

variable {hdeg π mu psi}

theorem kernelPoint_naturality {A B : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B)
    (w : rootsOfUnity 2 A) :
    S.affinePointMap f (kernelPoint hdeg mu psi A w) =
      kernelPoint hdeg mu psi B (restrictRootsOfUnity f.hom 2 w) := by
  have hu : Units.map f.hom.toRingHom.toMonoidHom (w : Aˣ) =
      ((restrictRootsOfUnity f.hom 2 w : rootsOfUnity 2 B) : Bˣ) := by
    apply Units.ext
    rw [restrictRootsOfUnity_coe_apply]
    rfl
  have hb : normOneMap f (scalarNormOne hdeg A w) =
      scalarNormOne hdeg B (restrictRootsOfUnity f.hom 2 w) :=
    Subtype.ext (by
      rw [normOneMap_val, scalarNormOne_val, scalarNormOne_val, normCoverScalarUnits_map, hu])
  rw [kernelPoint, kernelPoint, map_mul, affinePointMap_comp_hom, affinePointMap_comp_hom,
    gmPoint_naturality, normOnePoint_naturality, hu, hb]

/-- `z` is multiplicative when its values are central. -/
theorem kernelPoint_mul (A : CommAlgCat.{u} (CommRingCat.of K))
    (hz : ∀ v : rootsOfUnity 2 A, ∀ y : S.affinePoints A, Commute (kernelPoint hdeg mu psi A v) y)
    (u v : rootsOfUnity 2 A) :
    kernelPoint hdeg mu psi A (u * v) =
      kernelPoint hdeg mu psi A u * kernelPoint hdeg mu psi A v := by
  have hpsi : Commute (normOnePoint A (scalarNormOne hdeg A u) ≫ psi.hom.hom)
      (normOnePoint A (scalarNormOne hdeg A v) ≫ psi.hom.hom) := by
    rw [Commute, SemiconjBy, ← MonObj.mul_comp, ← MonObj.mul_comp, ← map_mul, ← map_mul,
      ← map_mul, ← map_mul, mul_comm u v]
  have hv := hz v (normOnePoint A (scalarNormOne hdeg A u) ≫ psi.hom.hom)
  unfold kernelPoint at hv ⊢
  simp only [map_mul, Subgroup.coe_mul, MonObj.mul_comp]
  calc _ = (gmPoint A (u : Aˣ) ≫ mu.hom.hom) * ((gmPoint A (v : Aˣ) ≫ mu.hom.hom) *
        ((normOnePoint A (scalarNormOne hdeg A u) ≫ psi.hom.hom) *
          (normOnePoint A (scalarNormOne hdeg A v) ≫ psi.hom.hom))) := by
          simp only [mul_assoc]
    _ = (gmPoint A (u : Aˣ) ≫ mu.hom.hom) * ((normOnePoint A (scalarNormOne hdeg A u) ≫
          psi.hom.hom) * ((gmPoint A (v : Aˣ) ≫ mu.hom.hom) *
            (normOnePoint A (scalarNormOne hdeg A v) ≫ psi.hom.hom))) := by
          congr 1
          rw [hpsi.eq, ← mul_assoc, hv.eq]
    _ = _ := by simp only [mul_assoc]

variable (Λ : CentralSimpleUnits.groupScheme K D ⟶ G)

/-- Postcomposition with `Λ` on `(A ⊗ D)ˣ`. -/
abbrev unitMap (A : CommAlgCat.{u} (CommRingCat.of K)) : (A ⊗[K] D)ˣ →* G.affinePoints A :=
  ((CentralSimpleUnits.groupScheme K D).affinePointsTarget Λ A).comp
    (unitPoint A).toMonoidHom

omit [Algebra.IsCentral K D] in
theorem unitMap_apply (A : CommAlgCat.{u} (CommRingCat.of K)) (a : (A ⊗[K] D)ˣ) :
    unitMap Λ A a = unitPoint A a ≫ Λ.hom.hom := rfl

variable {Λ}

theorem comp_psi_comp (hpsi : psi ≫ π = CentralSimpleUnits.normOneι K D ≫ Λ)
    (A : CommAlgCat.{u} (CommRingCat.of K)) (b : reducedNormOne K D A) :
    (normOnePoint A b ≫ psi.hom.hom) ≫ π.hom.hom = unitMap Λ A b.val := by
  rw [Category.assoc, ← Grp.comp_hom_hom, hpsi, Grp.comp_hom_hom, ← Category.assoc,
    normOnePoint_comp_normOneι, unitMap_apply]

theorem kernelPoint_comp
    (hmu : ∀ (A : CommAlgCat.{u} (CommRingCat.of K)) (t : Aˣ),
      (gmPoint A t ≫ mu.hom.hom) ≫ π.hom.hom = unitMap Λ A (normCoverScalarUnits K D A t))
    (hpsi : psi ≫ π = CentralSimpleUnits.normOneι K D ≫ Λ)
    (A : CommAlgCat.{u} (CommRingCat.of K)) (w : rootsOfUnity 2 A) :
    kernelPoint hdeg mu psi A w ≫ π.hom.hom = 1 := by
  have hw : (w : Aˣ) * w = 1 := by rw [← pow_two]; exact (mem_rootsOfUnity 2 _).mp w.2
  rw [kernelPoint, MonObj.mul_comp, hmu, comp_psi_comp hpsi, scalarNormOne_val, ← map_mul,
    ← map_mul, hw, map_one, map_one]

theorem rationalCoeffEquiv_comp_hom {H : GroupScheme (Spec (CommRingCat.of K))} (f : S ⟶ H)
    (x : rationalPoints S) :
    GaloisPointComparison.rationalCoeffEquiv K S x ≫ f.hom.hom =
      GaloisPointComparison.rationalCoeffEquiv K H (rationalPoints.map f x) := by
  rw [← GroupScheme.affinePointsTarget_apply]
  exact (GaloisPointComparison.rationalCoeffEquiv_map K f x).symm

omit [Algebra.IsCentral K D] in
/-- The `K`-point of `GL₁(D)` given by `a ∈ Dˣ` is `1 ⊗ a ∈ (K ⊗ D)ˣ`. -/
theorem affinePointsEquiv_rationalCoeffEquiv_symm (a : Dˣ) :
    ((FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K D)
        (CommAlgCat.of (CommRingCat.of K) K)
        (GaloisPointComparison.rationalCoeffEquiv K _
          ((FiniteAlgebraUnits.rationalPointsEquiv (Module.finBasis K D)).symm a)) :
        (K ⊗[K] D)ˣ) : K ⊗[K] D) = 1 ⊗ₜ[K] (a : D) := by
  have h := (FiniteAlgebraUnits.rationalPointsEquiv (Module.finBasis K D)).apply_symm_apply a
  have h' := congrArg Units.val h
  rw [← Algebra.TensorProduct.lid_symm_apply, ← h']
  exact ((Algebra.TensorProduct.lid K D).symm_apply_apply _).symm

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
theorem units_map_tensorMap_comp {A B C : CommAlgCat.{u} (CommRingCat.of K)} (f : A ⟶ B)
    (g : B ⟶ C) (x : (A ⊗[K] D)ˣ) :
    Units.map (Algebra.TensorProduct.map g.hom (AlgHom.id K D)).toMonoidHom
        (Units.map (Algebra.TensorProduct.map f.hom (AlgHom.id K D)).toMonoidHom x) =
      Units.map (Algebra.TensorProduct.map (f ≫ g).hom (AlgHom.id K D)).toMonoidHom x := by
  apply Units.ext
  change Algebra.TensorProduct.map g.hom (AlgHom.id K D)
      (Algebra.TensorProduct.map f.hom (AlgHom.id K D) (x : A ⊗[K] D)) =
    Algebra.TensorProduct.map (f ≫ g).hom (AlgHom.id K D) (x : A ⊗[K] D)
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  rfl

/-- Over a coefficient algebra `A`, let `s` be a point of `S` over `Λ(a)`, `t ∈ Aˣ`, and
`b = t⁻¹ a ∈ SL₁(D)(A)`. Then `k = s⁻¹ μ(t) ψ(b)` lies in the kernel of `π`. -/
theorem descentPoint_comp_eq_one
    (hmu : ∀ (A : CommAlgCat.{u} (CommRingCat.of K)) (t : Aˣ),
      (gmPoint A t ≫ mu.hom.hom) ≫ π.hom.hom = unitMap Λ A (normCoverScalarUnits K D A t))
    (hpsi : psi ≫ π = CentralSimpleUnits.normOneι K D ≫ Λ)
    {A : CommAlgCat.{u} (CommRingCat.of K)} (sA : S.affinePoints A) (aA : (A ⊗[K] D)ˣ)
    (hsA : sA ≫ π.hom.hom = unitMap Λ A aA) (t : Aˣ) (b : reducedNormOne K D A)
    (hb : (b : (A ⊗[K] D)ˣ) = normCoverScalarUnits K D A t⁻¹ * aA) :
    (sA⁻¹ * ((gmPoint A t ≫ mu.hom.hom) * (normOnePoint A b ≫ psi.hom.hom))) ≫ π.hom.hom =
      1 := by
  change S.affinePointsTarget π A _ = 1
  simp only [map_mul, map_inv, GroupScheme.affinePointsTarget_apply]
  rw [hsA, hmu, comp_psi_comp hpsi, ← map_mul, ← map_inv, ← map_mul, hb,
    ← mul_assoc (normCoverScalarUnits K D A t), ← map_mul, mul_inv_cancel, map_one, one_mul,
    inv_mul_cancel, map_one]

/-- **The cocycle relation.** Let `j₁ j₂ : A ⟶ B` agree on `s` and on `a`, and let
`j₂(t) = j₁(t) u'` with `u' ∈ μ₂(B)`. Then the two images of `k = s⁻¹ μ(t) ψ(t⁻¹ a)` differ by
the central factor `z(u')`: `j₂(k) = z(u') j₁(k)`. -/
theorem descentPoint_map_eq
    (hcent : ∀ (A : CommAlgCat.{u} (CommRingCat.of K)) (x y : S.affinePoints A),
      x ≫ π.hom.hom = 1 → Commute x y)
    (hmu : ∀ (A : CommAlgCat.{u} (CommRingCat.of K)) (t : Aˣ),
      (gmPoint A t ≫ mu.hom.hom) ≫ π.hom.hom = unitMap Λ A (normCoverScalarUnits K D A t))
    (hpsi : psi ≫ π = CentralSimpleUnits.normOneι K D ≫ Λ)
    {A B : CommAlgCat.{u} (CommRingCat.of K)} (j₁ j₂ : A ⟶ B)
    (sA : S.affinePoints A) (aA : (A ⊗[K] D)ˣ) (t : Aˣ) (b : reducedNormOne K D A)
    (hb : (b : (A ⊗[K] D)ˣ) = normCoverScalarUnits K D A t⁻¹ * aA)
    (hs : S.affinePointMap j₁ sA = S.affinePointMap j₂ sA)
    (ha : Units.map (Algebra.TensorProduct.map j₂.hom (AlgHom.id K D)).toMonoidHom aA =
      Units.map (Algebra.TensorProduct.map j₁.hom (AlgHom.id K D)).toMonoidHom aA)
    (u' : rootsOfUnity 2 B)
    (ht : Units.map j₂.hom.toRingHom.toMonoidHom t =
      Units.map j₁.hom.toRingHom.toMonoidHom t * (u' : Bˣ)) :
    S.affinePointMap j₂ (sA⁻¹ * ((gmPoint A t ≫ mu.hom.hom) * (normOnePoint A b ≫ psi.hom.hom))) =
      kernelPoint hdeg mu psi B u' *
        S.affinePointMap j₁ (sA⁻¹ * ((gmPoint A t ≫ mu.hom.hom) *
          (normOnePoint A b ≫ psi.hom.hom))) := by
  have hu'u' : u' * u' = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact (mem_rootsOfUnity 2 _).mp u'.2)
  have hu'inv : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hu'u'
  have hts : Units.map j₂.hom.toRingHom.toMonoidHom t⁻¹ =
      ((u'⁻¹ : rootsOfUnity 2 B) : Bˣ) * Units.map j₁.hom.toRingHom.toMonoidHom t⁻¹ := by
    rw [map_inv, map_inv, ht, mul_inv_rev, Subgroup.coe_inv]
  have hb₂ : normOneMap j₂ b = scalarNormOne hdeg B u' * normOneMap j₁ b := by
    rw [← hu'inv]
    apply Subtype.ext
    rw [Subgroup.coe_mul, normOneMap_val, normOneMap_val, scalarNormOne_val, hb, map_mul,
      map_mul, normCoverScalarUnits_map, normCoverScalarUnits_map, hts, map_mul, mul_assoc, ha]
  have hz := fun y => hcent B (kernelPoint hdeg mu psi B u') y (kernelPoint_comp hmu hpsi B u')
  simp only [map_mul, map_inv, affinePointMap_comp_hom, gmPoint_naturality,
    normOnePoint_naturality]
  rw [← hs, ht, hb₂, map_mul, MonObj.mul_comp, map_mul, MonObj.mul_comp]
  calc _ = (S.affinePointMap j₁ sA)⁻¹ *
        ((gmPoint B (Units.map j₁.hom.toRingHom.toMonoidHom t) ≫ mu.hom.hom) *
          (kernelPoint hdeg mu psi B u' *
            (normOnePoint B (normOneMap j₁ b) ≫ psi.hom.hom))) := by
        rw [kernelPoint]
        simp only [mul_assoc]
    _ = _ := by
        rw [(hz _).symm.left_comm, (hz _).symm.left_comm]

/-- **Descent of the reduced norm.** Let `π : S ⟶ G` have central kernel, `Λ : GL₁(D) ⟶ G`,
and let `μ : 𝔾_m ⟶ S` and `ψ : SL₁(D) ⟶ S` lift `Λ` on scalars and on `SL₁(D)`. If the kernel
condition holds and a rational point `s` of `S` lies over `Λ(a)`, then the reduced norm of `a`
is a square in `K`. -/
theorem exists_sq_eq_reducedNorm_of_comp_eq
    (hcent : ∀ (A : CommAlgCat.{u} (CommRingCat.of K)) (x y : S.affinePoints A),
      x ≫ π.hom.hom = 1 → Commute x y)
    (hmu : ∀ (A : CommAlgCat.{u} (CommRingCat.of K)) (t : Aˣ),
      (gmPoint A t ≫ mu.hom.hom) ≫ π.hom.hom = unitMap Λ A (normCoverScalarUnits K D A t))
    (hpsi : psi ≫ π = CentralSimpleUnits.normOneι K D ≫ Λ)
    (hZ : KernelGenerator hdeg π mu psi)
    (s : rationalPoints S) (a : Dˣ)
    (hs : rationalPoints.map π s = rationalPoints.map Λ
      ((FiniteAlgebraUnits.rationalPointsEquiv (Module.finBasis K D)).symm a)) :
    ∃ x : K, reducedNorm K D K (1 ⊗ₜ[K] (a : D)) = x ^ 2 := by
  let K0 : CommAlgCat.{u} (CommRingCat.of K) := CommAlgCat.of (CommRingCat.of K) K
  obtain ⟨aK, haKdef⟩ : ∃ aK : (K0 ⊗[K] D)ˣ, unitPoint K0 aK =
      GaloisPointComparison.rationalCoeffEquiv K _
        ((FiniteAlgebraUnits.rationalPointsEquiv (Module.finBasis K D)).symm a) :=
    ⟨_, MulEquiv.symm_apply_apply _ _⟩
  have haK : (aK : K ⊗[K] D) = 1 ⊗ₜ[K] (a : D) := by
    rw [← affinePointsEquiv_rationalCoeffEquiv_symm a, ← haKdef]
    exact congrArg (fun x : (K0 ⊗[K] D)ˣ => (x : K ⊗[K] D))
      (MulEquiv.apply_symm_apply _ aK).symm
  set c := reducedNorm K D K (1 ⊗ₜ[K] (a : D)) with hc_def
  have hc : c ≠ 0 := by
    have h := (reducedNormUnits K D K aK).ne_zero
    rwa [reducedNormUnits_val, haK] at h
  let RA : CommAlgCat.{u} (CommRingCat.of K) := CommAlgCat.of (CommRingCat.of K) (QuadraticRoot c)
  let RRA : CommAlgCat.{u} (CommRingCat.of K) :=
    CommAlgCat.of (CommRingCat.of K) (QuadraticRoot c ⊗[K] QuadraticRoot c)
  let iK : K0 ⟶ RA := CommAlgCat.ofHom (Algebra.ofId K (QuadraticRoot c))
  let j₁ : RA ⟶ RRA := CommAlgCat.ofHom
    (Algebra.TensorProduct.includeLeft : QuadraticRoot c →ₐ[K] _)
  let j₂ : RA ⟶ RRA := CommAlgCat.ofHom
    (Algebra.TensorProduct.includeRight : QuadraticRoot c →ₐ[K] _)
  let t : (QuadraticRoot c)ˣ := quadraticRootUnit hc
  let aR : (RA ⊗[K] D)ˣ :=
    Units.map (Algebra.TensorProduct.map iK.hom (AlgHom.id K D)).toMonoidHom aK
  have hbmem : normCoverScalarUnits K D RA t⁻¹ * aR ∈ reducedNormOne K D RA := by
    change reducedNormUnits K D RA _ = 1
    rw [map_mul, reducedNormUnits_normCoverScalarUnits K D RA hdeg, reducedNormUnits_naturality]
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one]
    change ((t⁻¹ : (QuadraticRoot c)ˣ) : QuadraticRoot c) ^ 2 *
      (Algebra.ofId K (QuadraticRoot c)) (reducedNorm K D K (aK : K ⊗[K] D)) = 1
    rw [haK, Algebra.ofId_apply, ← quadraticRootUnit_sq hc, ← mul_pow, Units.inv_mul, one_pow]
  let b : reducedNormOne K D RA := ⟨_, hbmem⟩
  let sR := S.affinePointMap iK (GaloisPointComparison.rationalCoeffEquiv K S s)
  have hsR : sR ≫ π.hom.hom = unitMap Λ RA aR := by
    show S.affinePointMap iK (GaloisPointComparison.rationalCoeffEquiv K S s) ≫ π.hom.hom = _
    rw [← affinePointMap_comp_hom, rationalCoeffEquiv_comp_hom, hs, ← rationalCoeffEquiv_comp_hom,
      ← haKdef, affinePointMap_comp_hom, unitPoint_naturality]
    rfl
  have hk := descentPoint_comp_eq_one hmu hpsi sR aR hsR t b rfl
  obtain ⟨w, hw, -⟩ := hZ RA _ hk
  -- the two images of the root `t` in `R ⊗ R`
  have hTsq : ∀ j : RA ⟶ RRA,
      ((Units.map j.hom.toRingHom.toMonoidHom t : RRAˣ) : RRA) ^ 2 = algebraMap K RRA c := by
    intro j
    rw [Units.coe_map]
    change (j.hom (t : QuadraticRoot c)) ^ 2 = _
    rw [← map_pow, quadraticRootUnit_sq hc]
    exact j.hom.commutes c
  have hTT : (Units.map j₂.hom.toRingHom.toMonoidHom t) ^ 2 =
      (Units.map j₁.hom.toRingHom.toMonoidHom t) ^ 2 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hTsq j₂, hTsq j₁]
  have hu'mem : Units.map j₂.hom.toRingHom.toMonoidHom t *
      (Units.map j₁.hom.toRingHom.toMonoidHom t)⁻¹ ∈ rootsOfUnity 2 RRA := by
    rw [mem_rootsOfUnity, mul_pow, hTT, ← mul_pow, mul_inv_cancel, one_pow]
  obtain ⟨u', hu'def⟩ : ∃ u' : rootsOfUnity 2 RRA, (u' : RRAˣ) =
      Units.map j₂.hom.toRingHom.toMonoidHom t * (Units.map j₁.hom.toRingHom.toMonoidHom t)⁻¹ :=
    ⟨⟨_, hu'mem⟩, rfl⟩
  have hT₂ : Units.map j₂.hom.toRingHom.toMonoidHom t =
      Units.map j₁.hom.toRingHom.toMonoidHom t * (u' : RRAˣ) := by
    rw [hu'def, mul_comm (Units.map j₂.hom.toRingHom.toMonoidHom t), ← mul_assoc,
      mul_inv_cancel, one_mul]
  -- the two images of `K` agree
  have hiK : iK ≫ j₁ = iK ≫ j₂ := CommAlgCat.hom_ext (AlgHom.ext fun x =>
    ((iK ≫ j₁).hom.commutes x).trans ((iK ≫ j₂).hom.commutes x).symm)
  have hsj : S.affinePointMap j₁ sR = S.affinePointMap j₂ sR := by
    have e : ∀ j : RA ⟶ RRA, S.affinePointMap j sR =
        S.affinePointMap (iK ≫ j) (GaloisPointComparison.rationalCoeffEquiv K S s) := by
      intro j
      rw [GroupScheme.affinePointMap_comp]
      rfl
    rw [e, e, hiK]
  have haRj : Units.map (Algebra.TensorProduct.map j₂.hom (AlgHom.id K D)).toMonoidHom aR =
      Units.map (Algebra.TensorProduct.map j₁.hom (AlgHom.id K D)).toMonoidHom aR := by
    rw [units_map_tensorMap_comp, units_map_tensorMap_comp, hiK]
  have hkk := descentPoint_map_eq (hdeg := hdeg) hcent hmu hpsi j₁ j₂ sR aR t b rfl hsj haRj u' hT₂
  -- comparison in `μ₂(R ⊗ R)`
  have hz' : ∀ v : rootsOfUnity 2 RRA, ∀ y : S.affinePoints RRA,
      Commute (kernelPoint hdeg mu psi RRA v) y :=
    fun v y => hcent RRA _ y (kernelPoint_comp hmu hpsi RRA v)
  have hkn : ∀ j : RA ⟶ RRA, S.affinePointMap j
      (sR⁻¹ * ((gmPoint RA t ≫ mu.hom.hom) * (normOnePoint RA b ≫ psi.hom.hom))) =
      kernelPoint hdeg mu psi RRA (restrictRootsOfUnity j.hom 2 w) := fun j => by
    rw [← hw, kernelPoint_naturality]
  have heq : restrictRootsOfUnity j₂.hom 2 w = u' * restrictRootsOfUnity j₁.hom 2 w := by
    have hk₂π := ((affinePointMap_comp_hom j₂ π _).symm.trans
      (congrArg (G.affinePointMap j₂) hk)).trans (map_one _)
    obtain ⟨u₀, -, huniq⟩ := hZ RRA _ hk₂π
    rw [huniq _ (hkn j₂).symm, huniq (u' * restrictRootsOfUnity j₁.hom 2 w)]
    show kernelPoint hdeg mu psi RRA (u' * restrictRootsOfUnity j₁.hom 2 w) = _
    rw [kernelPoint_mul RRA hz', ← hkn j₁, ← hkk]
  have hwv : j₂.hom ((w : RAˣ) : QuadraticRoot c) =
      (((Units.map j₂.hom.toRingHom.toMonoidHom t : RRAˣ) : RRA) *
        (((Units.map j₁.hom.toRingHom.toMonoidHom t)⁻¹ : RRAˣ) : RRA)) *
          j₁.hom ((w : RAˣ) : QuadraticRoot c) := by
    have h := congrArg (fun x : rootsOfUnity 2 RRA => ((x : RRAˣ) : RRA)) heq
    simp only [Subgroup.coe_mul, Units.val_mul, restrictRootsOfUnity_coe_apply, hu'def] at h
    exact h
  have hw2 : ((w : RAˣ) : QuadraticRoot c) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 2 _).mp w.2, Units.val_one]
  exact exists_sq_of_tmul_relation hc _ hw2 hwv

end Langlands.GroupScheme.Quaternionic.SpinKernel

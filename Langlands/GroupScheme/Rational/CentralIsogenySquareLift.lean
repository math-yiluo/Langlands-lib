import Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinKernelReduction
import Langlands.GroupScheme.CentralIsogeny.FiniteGaloisCoefficientLift

/-! # Squares of rational points lift through a central isogeny with kernel `μ₂`

Let `f : G → H` be a central isogeny over a field `k` whose kernel is identified with `μ₂`.
Over a field `L ⊇ k` of characteristic zero, every point of `H(L)` lifts to `G` over a finite
Galois extension `E/L`. For affine `G` and `H`, this yields a lift of the square of any
`u ∈ H(L)` over `L`. If `b` lifts `u`, then `σ(b) b⁻¹` lies in the kernel for every
`σ ∈ Gal(E/L)`. Kernel points are central of order dividing two, so `b²` is Galois fixed
and descends to a point of `G(L)` lifting `u²`.

For affine `G` and `H`, if `f` is surjective on `L`-points, the image in `G` of the Kummer
cocycle of `a ∈ Lˣ` is a coboundary only when `a` is a square. A trivializing point `b`
maps to a Galois-fixed point of `H` that descends to `H(L)` and lifts to `G(L)`. Thus `b`
differs from a rational point by a kernel point. Kernel points are `±1` and Galois fixed,
so the Kummer cocycle is trivial and the radical lies in `L`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

open Langlands.AlgebraicGeometry.AlgebraicSpace.FieldSchemePoints GaloisPoint

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f)

include hf in
/-- A point of the target over a field of characteristic zero lifts through a central isogeny
after a finite Galois extension of that field. -/
theorem exists_finiteGalois_lift (L : Type u) [Field L] [Algebra k L] [CharZero L]
    (a : H.affinePoints (CommAlgCat.of k L)) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra L E) (_ : FiniteDimensional L E)
      (_ : IsGalois L E) (_ : Algebra k E) (_ : IsScalarTower k L E)
      (b : G.affinePoints (CommAlgCat.of k E)),
      G.affinePointsTarget f (CommAlgCat.of k E) b = relativeExtend k L E H a := by
  let X := coefficientLiftFiber f a
  let π : X ⟶ Spec (CommRingCat.of L) := pullback.fst a.left f.hom.hom.left
  let : IsFinite f.hom.hom.left := hf.isFinite
  let : Surjective f.hom.hom.left := hf.surjective
  let : LocallyOfFiniteType π :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst a.left f.hom.hom.left))
  obtain ⟨x, hx⟩ : ∃ x : X, IsClosed ({x} : Set X) := by
    let : Surjective π := inferInstanceAs (Surjective (pullback.fst a.left f.hom.hom.left))
    obtain ⟨x, _⟩ := π.surjective (IsLocalRing.closedPoint L)
    obtain ⟨z, hz, _⟩ := exists_closed_specialization π x
    exact ⟨z, hz⟩
  let R := X.residueField x
  let : Algebra L R := residueFieldAlgebra π x
  let : FiniteDimensional L R := residueField_finiteDimensional π x hx
  obtain ⟨E, hEfin, hEgal, ⟨φ⟩⟩ := exists_finite_galois_algHom L R
  let : Algebra k E := ((algebraMap L E).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨E, inferInstance, inferInstance, hEfin, hEgal, inferInstance, inferInstance, ?_⟩
  let θ : R →+* E := φ.toRingHom
  have hθ : θ.comp (algebraMap L R) = algebraMap L E := by
    apply RingHom.ext
    intro t
    exact φ.commutes t
  let r := X.fromSpecResidueField x
  have hr : r ≫ π = Spec.map (CommRingCat.ofHom (algebraMap L R)) := by
    change r ≫ π = Spec.map (Spec.preimage (r ≫ π))
    exact (Spec.map_preimage _).symm
  let y := Spec.map (CommRingCat.ofHom θ) ≫ r ≫ pullback.snd a.left f.hom.hom.left
  have hy : y ≫ f.hom.hom.left = Spec.map (CommRingCat.ofHom (algebraMap L E)) ≫ a.left := by
    simp only [y, Category.assoc]
    rw [← pullback.condition, ← Category.assoc r, hr, ← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun g : L →+* E => Spec.map (CommRingCat.ofHom g) ≫ a.left) hθ
  let b : G.affinePoints (CommAlgCat.of k E) := Over.homMk y (by
    change y ≫ G.X.hom = Spec.map (CommRingCat.ofHom (algebraMap k E))
    rw [← Over.w f.hom.hom, ← Category.assoc, hy, Category.assoc, Over.w a]
    change Spec.map (CommRingCat.ofHom (algebraMap L E)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) = _
    rw [← Spec.map_comp]
    rfl)
  exact ⟨b, Over.OverMorphism.ext hy⟩

omit hf in
/-- Coefficient extension commutes with a homomorphism of group schemes. -/
theorem target_relativeExtend (L E : Type u) [Field L] [Field E] [Algebra k L] [Algebra k E]
    [Algebra L E] [IsScalarTower k L E] (g : G.affinePoints (CommAlgCat.of k L)) :
    G.affinePointsTarget f (CommAlgCat.of k E) (relativeExtend k L E G g) =
      relativeExtend k L E H (G.affinePointsTarget f (CommAlgCat.of k L) g) :=
  (DFunLike.congr_fun (G.affinePointsTarget_naturality f
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L E))) g).symm

omit hf in
/-- The relative Galois action commutes with a homomorphism of group schemes. -/
theorem target_relativeConjugate (L E : Type u) [Field L] [Field E] [Algebra k L] [Algebra k E]
    [Algebra L E] [IsScalarTower k L E] (σ : E ≃ₐ[L] E) (g : G.affinePoints (CommAlgCat.of k E)) :
    G.affinePointsTarget f (CommAlgCat.of k E) (relativeConjugate k L E G σ g) =
      relativeConjugate k L E H σ (G.affinePointsTarget f (CommAlgCat.of k E) g) :=
  (DFunLike.congr_fun (G.affinePointsTarget_naturality f
    (CommAlgCat.ofHom (σ.restrictScalars k).toAlgHom)) g).symm

/-- Kernel points are central. -/
theorem kernelPointInclusion_commute_points (N : Type u) [Field N] [Algebra k N]
    (c : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of k N))
    (b : G.affinePoints (CommAlgCat.of k N)) : Commute (hf.kernelPointInclusion N c) b :=
  commute_of_mem_center (hf.isCentral_kernelι _ c) b

/-- A point killed by the isogeny is a kernel point. -/
theorem exists_kernelPoint_of_target_eq_one (N : Type u) [Field N] [Algebra k N]
    (b : G.affinePoints (CommAlgCat.of k N))
    (hb : G.affinePointsTarget f (CommAlgCat.of k N) b = 1) :
    ∃ c, hf.kernelPointInclusion N c = b :=
  (mem_range_kernelι_iff f b).mpr hb

/-- Kernel points map to the identity. -/
theorem target_kernelPointInclusion (N : Type u) [Field N] [Algebra k N]
    (c : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of k N)) :
    G.affinePointsTarget f (CommAlgCat.of k N) (hf.kernelPointInclusion N c) = 1 :=
  (mem_range_kernelι_iff f _).mp ⟨c, rfl⟩

/-- The inclusion of kernel points is injective. -/
theorem kernelPointInclusion_injective' (N : Type u) [Field N] [Algebra k N] :
    Function.Injective (hf.kernelPointInclusion N) :=
  fun _ _ h => (cancel_mono (kernelι f).hom.hom).mp h

variable (e : kernel f ≅ (mu (Spec (CommRingCat.of k)) 2).toGrp)

local notation "χ" => (Iso.hom e ≫ Additive.toMul (mu.incl (Spec (CommRingCat.of k)) 2))

include e in
/-- Kernel points identified with `μ₂` square to one. -/
theorem kernelPoint_mul_self (N : Type u) [Field N] [Algebra k N]
    (c : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of k N)) : c * c = 1 := by
  apply (hf.kernelRootsEquiv 2 e N).injective
  rw [map_mul, map_one]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, OneMemClass.coe_one]
  rw [← pow_two]
  exact (mem_rootsOfUnity 2 _).mp (hf.kernelRootsEquiv 2 e N c).property

include e in
/-- Kernel points identified with `μ₂` are fixed by every coefficient automorphism. -/
theorem kernelPoint_conjugate_eq (N : Type u) [Field N] [Algebra k N] (σ : N ≃ₐ[k] N)
    (c : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of k N)) :
    conjugate k N hf.commutativeKernel.toGrp σ c = c := by
  apply hf.kernelUnitMap_mu_injective 2 e
  change hf.kernelUnitMap (χ) N (GroupScheme.affinePointMap hf.commutativeKernel.toGrp
    (CommAlgCat.ofHom σ.toAlgHom) c) = _
  rw [hf.kernelUnitMap_naturality]
  have hsq : hf.kernelUnitMap (χ) N c * hf.kernelUnitMap (χ) N c = 1 := by
    rw [← map_mul, hf.kernelPoint_mul_self e N c, map_one]
  have hval : ((hf.kernelUnitMap (χ) N c : Nˣ) : N) = 1 ∨
      ((hf.kernelUnitMap (χ) N c : Nˣ) : N) = -1 := by
    have h := congrArg (fun t : Nˣ => (t : N)) hsq
    simp only [Units.val_mul, Units.val_one] at h
    exact mul_self_eq_one_iff.mp h
  apply Units.ext
  change σ ((hf.kernelUnitMap (χ) N c : Nˣ) : N) = _
  rcases hval with h | h <;> rw [h] <;> simp

include hf e in
/-- Squares of points over a field of characteristic zero lift through a central isogeny whose
kernel is identified with `μ₂`. -/
theorem exists_target_eq_mul_self [IsAffine G.X.left] [IsAffine H.X.left]
    (L : Type u) [Field L] [Algebra k L] [CharZero L] (u : H.affinePoints (CommAlgCat.of k L)) :
    ∃ g : G.affinePoints (CommAlgCat.of k L),
      G.affinePointsTarget f (CommAlgCat.of k L) g = u * u := by
  obtain ⟨E, _, _, _, _, _, _, b, hb⟩ := hf.exists_finiteGalois_lift L u
  have hfix (σ : E ≃ₐ[L] E) : relativeConjugate k L E G σ (b * b) = b * b := by
    have hp : G.affinePointsTarget f (CommAlgCat.of k E) (relativeConjugate k L E G σ b) =
        G.affinePointsTarget f (CommAlgCat.of k E) b := by
      rw [target_relativeConjugate, hb, relativeConjugate_extend]
    obtain ⟨c, hc⟩ := hf.exists_kernelPoint_of_target_eq_one E
      (relativeConjugate k L E G σ b * b⁻¹) (by rw [map_mul, map_inv, hp, mul_inv_cancel])
    have hb' : relativeConjugate k L E G σ b = hf.kernelPointInclusion E c * b := by
      rw [hc, inv_mul_cancel_right]
    have hcomm := hf.kernelPointInclusion_commute_points E c b
    rw [map_mul, hb']
    calc hf.kernelPointInclusion E c * b * (hf.kernelPointInclusion E c * b)
        = hf.kernelPointInclusion E c * (b * hf.kernelPointInclusion E c) * b := by group
      _ = hf.kernelPointInclusion E c * (hf.kernelPointInclusion E c * b) * b := by
          rw [hcomm.eq]
      _ = hf.kernelPointInclusion E (c * c) * (b * b) := by rw [map_mul]; group
      _ = b * b := by rw [hf.kernelPoint_mul_self e E c, map_one, one_mul]
  let w : relativeFixedSubgroup k L E G := ⟨b * b, hfix⟩
  refine ⟨relativeDescend k L E G w, ?_⟩
  apply relativeExtend_injective k L E H
  rw [← target_relativeExtend, relativeExtend_descend, map_mul, hb, map_mul]

include hf e in
/-- Let a central isogeny of affine groups with kernel identified with `μ₂` be surjective on
`K`-points. If the Kummer cocycle of `a ∈ Kˣ` on a finite Galois cover of `Spec K` has image
a coboundary in the source group, then `a` is a square in `K`. -/
theorem isSquare_of_kummerImageTrivial [IsAffine G.X.left] [IsAffine H.X.left]
    (K M : Type u) [Field K] [Field M] [Algebra k K] [Algebra k M] [Algebra K M]
    [IsScalarTower k K M] [FiniteDimensional K M] [IsGalois K M]
    (hsurj : ∀ h : H.affinePoints (CommAlgCat.of k K),
      ∃ g, G.affinePointsTarget f (CommAlgCat.of k K) g = h)
    (a : Kˣ) (z : Mˣ) (hz : z ^ 2 = Units.map (algebraMap K M) a)
    (hK : KummerImageTrivial hf e K M a z hz) : IsSquare (a : K) := by
  obtain ⟨b, hb⟩ := hK
  let P := G.affinePointsTarget f (CommAlgCat.of k M)
  have hfix (σ : M ≃ₐ[K] M) : relativeConjugate k K M H σ (P b) = P b := by
    have h1 := congrArg P (hb σ)
    rw [target_kernelPointInclusion, map_mul, map_inv, target_relativeConjugate] at h1
    exact (mul_inv_eq_one.mp h1.symm).symm
  let w : relativeFixedSubgroup k K M H := ⟨P b, hfix⟩
  obtain ⟨g₀, hg₀⟩ := hsurj (relativeDescend k K M H w)
  let b₀ := relativeExtend k K M G g₀
  have htarget : P b₀ = P b := by
    change G.affinePointsTarget f (CommAlgCat.of k M) (relativeExtend k K M G g₀) = P b
    rw [target_relativeExtend, hg₀, relativeExtend_descend]
  obtain ⟨c, hc⟩ := hf.exists_kernelPoint_of_target_eq_one M (b₀⁻¹ * b)
    (by rw [map_mul, map_inv, htarget, inv_mul_cancel])
  have hbeq : b = b₀ * hf.kernelPointInclusion M c := by rw [hc, mul_inv_cancel_left]
  have hone (σ : M ≃ₐ[K] M) : b * (relativeConjugate k K M G σ b)⁻¹ = 1 := by
    have hcσ : relativeConjugate k K M G σ (hf.kernelPointInclusion M c) =
        hf.kernelPointInclusion M c := by
      have h := DFunLike.congr_fun
        (GroupScheme.affinePointsTarget_naturality hf.commutativeKernel.toGrp (kernelι f)
          (CommAlgCat.ofHom (σ.restrictScalars k).toAlgHom)) c
      refine h.trans ?_
      exact congrArg (hf.kernelPointInclusion M)
        (hf.kernelPoint_conjugate_eq e M (σ.restrictScalars k) c)
    rw [hbeq, map_mul, relativeConjugate_extend, hcσ, mul_inv_cancel]
  have hroot (σ : M ≃ₐ[K] M) : KummerCocycle.rootValue 2 a hz σ = 1 := by
    have h := (hb σ).trans (hone σ)
    rw [← map_one (hf.kernelPointInclusion M)] at h
    have h' := hf.kernelPointInclusion_injective' M h
    rw [MulEquiv.symm_apply_eq, map_one] at h'
    exact h'
  have hzfix (σ : M ≃ₐ[K] M) : σ (z : M) = z := by
    have h := congrArg (fun t : rootsOfUnity 2 M => ((t : Mˣ) : M)) (hroot σ)
    change ((σ • z / z : Mˣ) : M) = 1 at h
    rw [Units.val_div_eq_div_val, div_eq_one_iff_eq (Units.ne_zero z)] at h
    exact h
  obtain ⟨t, ht⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (z : M)).mpr hzfix
  refine ⟨t, (algebraMap K M).injective ?_⟩
  have h2 := congrArg (fun s : Mˣ => (s : M)) hz
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass] at h2
  rw [map_mul, ht, ← h2, pow_two]

end Langlands.GroupScheme.IsCentralIsogeny

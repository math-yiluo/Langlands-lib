import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.CocycleKernelTwist
import Langlands.GroupScheme.CentralIsogeny.FiniteGaloisCoefficientLift
import Langlands.GroupScheme.Rational.CentralMuKummerCocycle
import Langlands.GroupScheme.Rational.NumberFieldSpecialOrthogonalHasse
import Langlands.Global.Arithmetic.ArchimedeanAlgebraicClosure
import Langlands.LinearAlgebra.NumberFieldSpinorNorm

/-! # Scalar spin Hasse reduction through the central spinor norm -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open GaloisPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {F : Type u} [Field F] {G H : GroupScheme (Spec (CommRingCat.of F))}
  {p : G ⟶ H} (hp : IsCentralIsogeny p)
  (e : kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp)

local notation "χ" => (Iso.hom e ≫ Additive.toMul (mu.incl (Spec (CommRingCat.of F)) 2))

/-- A coefficient-field form of the spinor-norm boundary formula. A Kummer class becomes
trivial in the covering group exactly when its square class is a product of an even list
of nonzero values of the scalar quadratic form. -/
def ScalarSpinorNormBoundary [CharZero F] {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) : Prop :=
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  ∀ (K M : Type u) [Field K] [Field M] [Algebra F K] [Algebra F M] [Algebra K M]
    [IsScalarTower F K M] [FiniteDimensional K M] [IsGalois K M]
    (a : Kˣ) (z : Mˣ) (hz : z ^ 2 = Units.map (algebraMap K M) a),
    (∃ b : G.affinePoints (CommAlgCat.of F M), ∀ σ : M ≃ₐ[K] M,
      hp.kernelPointInclusion M ((hp.kernelRootsEquiv 2 e M).symm
        (KummerCocycle.rootValue 2 a hz σ)) = b * (relativeConjugate F K M G σ b)⁻¹) ↔
    ∃ (l : List {v : K ⊗[F] V // (Q.baseChange K) v ≠ 0}) (t : K),
      Even l.length ∧ t ≠ 0 ∧ QuadraticForm.reflectionWordValue (Q.baseChange K) l = (a : K) * t ^ 2

variable [NumberField F]

include hp in
theorem Cocycle.isTrivial_of_kernelHasse
    (hkernel : ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (α : Cocycle (kernel p) (GaloisCocycle.cover F L)),
      (α.map (kernelι p)).LocallyTrivial → (α.map (kernelι p)).IsTrivial)
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial)
    (hquot : (ξ.map p).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨b, hb⟩ := hquot
  obtain ⟨E, _, _, _, _, _, _, hlift⟩ := hp.exists_finiteGalois_coefficient_lifts (fun _ : Unit => b)
  obtain ⟨g, hg⟩ := hlift ()
  let r := GaloisCocycle.coverMap F L E
  let ξ' := ξ.refine r
  have hq {Z : Over (Spec (CommRingCat.of F))} (x y : Z ⟶ GaloisCocycle.cover F E) :
      (ξ'.map p).toFun x y = (Cocycle.coboundary (g ≫ p.hom.hom)).toFun x y := by
    change g ≫ p.hom.hom = r ≫ b at hg
    rw [hg]
    simpa only [ξ', Cocycle.refine_toFun, Cocycle.map, Cocycle.coboundary, Category.assoc]
      using hb (x ≫ r) (y ≫ r)
  let α := ξ'.kernelTwist p g hq
  have hα {Z : Over (Spec (CommRingCat.of F))} (x y : Z ⟶ GaloisCocycle.cover F E) :
      (α.map (kernelι p)).toFun x y = (ξ'.twist g).toFun x y :=
    Cocycle.kernelTwist_toFun_comp ξ' p g hq x y
  have hlocal : (α.map (kernelι p)).LocallyTrivial := by
    intro v
    let k := Spec.algebraMap F (Global.placeCompletion F v)
    let W := (Over.pullback k).obj (GaloisCocycle.cover F E)
    let s := (Over.mapPullbackAdj k).counit.app (GaloisCocycle.cover F E)
    obtain ⟨t, ht⟩ := hξ.refine r v
    let g' := (baseChangePointsEquiv k G W).symm (s ≫ g)
    refine ⟨g'⁻¹ * t, fun x y => ?_⟩
    apply (baseChangePointsEquiv k G _).injective
    change baseChangePointsEquiv k G _ (((α.map (kernelι p)).baseChange k W s).toFun x y) =
      baseChangePointsEquiv k G _ ((x ≫ (g'⁻¹ * t)) * (y ≫ (g'⁻¹ * t))⁻¹)
    rw [Cocycle.baseChange_toFun, hα]
    have htxy : (ξ'.baseChange k W s).toFun x y = (x ≫ t) * (y ≫ t)⁻¹ := ht x y
    have hh := congrArg (baseChangePointsEquiv k G _) htxy
    rw [Cocycle.baseChange_toFun, map_mul, map_inv, baseChangePointsEquiv_naturality,
      baseChangePointsEquiv_naturality] at hh
    have hg' : baseChangePointsEquiv k G
        ((Over.pullback (algebraBaseMap F (Global.placeCompletion F v))).obj
          (GaloisCocycle.cover F E)) g' = s ≫ g :=
      (baseChangePointsEquiv k G W).apply_symm_apply _
    simp only [Cocycle.twist, MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv,
      baseChangePointsEquiv_naturality, hg', Category.assoc, hh]
    group
  obtain ⟨t, ht⟩ := hkernel E α hlocal
  have hξ' : ξ'.IsTrivial := (show (ξ'.twist g).IsTrivial from
    ⟨t, fun x y => (hα x y).symm.trans (ht x y)⟩).of_twist
  obtain ⟨hs, hf, hqc⟩ := fieldExtension_fpqc F E
  let : Surjective (GaloisCocycle.cover F E).hom := hs
  let : Flat (GaloisCocycle.cover F E).hom := hf
  let : QuasiCompact (GaloisCocycle.cover F E).hom := hqc
  exact Cocycle.IsTrivial.of_refine_fpqcCover r hξ'

private theorem kernelMapHasse_of_spinorNormBoundary
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) (hrank : 4 ≤ Module.finrank F V)
    (hboundary : ScalarSpinorNormBoundary hp e Q)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (α : Cocycle (kernel p) (GaloisCocycle.cover F L)) (hα : (α.map (kernelι p)).LocallyTrivial) :
    (α.map (kernelι p)).IsTrivial := by
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  let c (σ : L ≃ₐ[F] L) := hp.kernelUnitMap (χ) L (GaloisCocycle.value α σ)
  have hc : groupCohomology.IsMulCocycle₁ c := by
    intro σ τ
    have hnat := hp.kernelUnitMap_naturality (χ) σ.toAlgHom (GaloisCocycle.value α τ)
    change hp.kernelUnitMap (χ) L (conjugate F L (kernel p) σ (GaloisCocycle.value α τ)) =
      σ • c τ at hnat
    calc
      c (σ * τ) = c σ * hp.kernelUnitMap (χ) L
          (conjugate F L (kernel p) σ (GaloisCocycle.value α τ)) :=
        (congrArg (hp.kernelUnitMap (χ) L) (GaloisCocycle.value_mul α σ τ)).trans (map_mul _ _ _)
      _ = σ • c τ * c σ := by rw [hnat, mul_comm]
  have hc₂ (σ : L ≃ₐ[F] L) : c σ ^ 2 = 1 := by
    rw [show c σ = _ from (hp.kernelRootsEquiv_val 2 e L (GaloisCocycle.value α σ)).symm]
    exact (mem_rootsOfUnity 2 _).mp (hp.kernelRootsEquiv 2 e L (GaloisCocycle.value α σ)).property
  obtain ⟨a, z, hz, hr⟩ := KummerCocycle.exists_radical 2 c hc hc₂
  have hroot (σ : L ≃ₐ[F] L) :
      (hp.kernelRootsEquiv 2 e L).symm (KummerCocycle.rootValue 2 a hz σ) =
        GaloisCocycle.value α σ := by
    apply hp.kernelUnitMap_mu_injective 2 e
    rw [hp.kernelUnitMap_kernelRootsEquiv_symm]
    exact hr σ
  have hv (v : InfinitePlace F) :
      let K := v.Completion
      let qv := Q.baseChange K
      ∃ (l : List {y : K ⊗[F] V // qv y ≠ 0}) (t : K),
        Even l.length ∧ t ≠ 0 ∧ QuadraticForm.reflectionWordValue qv l =
          algebraMap F K (a : F) * t ^ 2 := by
    let K := v.Completion
    let M := AlgebraicClosure K
    let : FiniteDimensional K M := Global.finiteArchimedeanAlgebraicClosure F v
    let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
    let : IsGalois K M := isGalois_iff.mpr ⟨inferInstance, ⟨fun _ => IsAlgClosed.splits _⟩⟩
    let j : L →ₐ[F] M := IsAlgClosed.lift
    let : Algebra L M := j.toRingHom.toAlgebra
    let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    let a₀ : Kˣ := Units.map (algebraMap F K) a
    let z₀ : Mˣ := Units.map (algebraMap L M) z
    have hz₀ : z₀ ^ 2 = Units.map (algebraMap K M) a₀ := by
      simp only [z₀, ← map_pow, hz]
      apply Units.ext
      change algebraMap L M (algebraMap F L (a : F)) = algebraMap K M (algebraMap F K (a : F))
      rw [← IsScalarTower.algebraMap_apply F L M, ← IsScalarTower.algebraMap_apply F K M]
    obtain ⟨b, hb⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial
      (K := K) (M := M) (α.map (kernelι p)) (hα (.inl v))
    apply (hboundary K M a₀ z₀ hz₀).mp
    refine ⟨b, fun σ => ?_⟩
    change _ = b * (conjugate F M G (σ.restrictScalars F) b)⁻¹
    refine Eq.trans ?_ (hb σ)
    let ρ := (σ.restrictScalars F).restrictNormal L
    change hp.kernelPointInclusion M ((hp.kernelRootsEquiv 2 e M).symm
        (KummerCocycle.rootValue 2 a₀ hz₀ σ)) =
      hp.kernelPointInclusion M (relativeExtend F L M (kernel p) (GaloisCocycle.value α ρ))
    congr 1
    apply hp.kernelUnitMap_mu_injective 2 e
    have hnat : hp.kernelUnitMap (χ) M (relativeExtend F L M (kernel p)
        (GaloisCocycle.value α ρ)) = Units.map (algebraMap L M) (c ρ) :=
      hp.kernelUnitMap_naturality (χ) (IsScalarTower.toAlgHom F L M) (GaloisCocycle.value α ρ)
    rw [hp.kernelUnitMap_kernelRootsEquiv_symm, hnat, ← hr ρ]
    change KummerCocycle.value z₀ σ = Units.map (algebraMap L M) (KummerCocycle.value z ρ)
    rw [KummerCocycle.value, KummerCocycle.value, map_div]
    congr 1
    apply Units.ext
    exact ((σ.restrictScalars F).restrictNormal_commutes L (z : L)).symm
  obtain ⟨x, hx⟩ : ∃ x, Q x ≠ 0 := by
    by_contra! h
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact hx (hQ.1 x (fun w => by
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h, sub_zero]))
  obtain ⟨y, hy⟩ := QuadraticForm.numberFieldSpinorNormRepresentation F V Q (a : F) hQ hrank hv x hx
  have hy₀ : Q y ≠ 0 := hy.symm ▸ mul_ne_zero a.ne_zero hx
  let Q₀ := Q.baseChange F
  have hval (w : V) : Q₀ ((1 : F) ⊗ₜ[F] w) = Q w := by
    simp [Q₀, QuadraticForm.baseChange_tmul]
  let x₀ : {v : F ⊗[F] V // Q₀ v ≠ 0} := ⟨1 ⊗ₜ[F] x, (hval x).trans_ne hx⟩
  let y₀ : {v : F ⊗[F] V // Q₀ v ≠ 0} := ⟨1 ⊗ₜ[F] y, (hval y).trans_ne hy₀⟩
  have he : Even [x₀, y₀].length := ⟨1, rfl⟩
  have hxy : QuadraticForm.reflectionWordValue Q₀ [x₀, y₀] = (a : F) * (Q x) ^ 2 := by
    change Q₀ ((1 : F) ⊗ₜ[F] x) * (Q₀ ((1 : F) ⊗ₜ[F] y) * 1) = _
    rw [hval, hval, hy]
    ring
  obtain ⟨b, hb⟩ := (hboundary F L a z hz).mpr ⟨[x₀, y₀], Q x, he, hx, hxy⟩
  refine (GaloisCocycle.isTrivial_iff _).mpr ⟨b, fun σ => ?_⟩
  change hp.kernelPointInclusion L (GaloisCocycle.value α σ) = _
  rw [← hroot σ]
  exact hb σ

/-- The scalar spinor-norm formula and the special orthogonal Hasse kernel imply
triviality on the original finite Galois cover. -/
theorem isTrivial_of_scalarSpinorNormBoundary
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate) (hrank : 4 ≤ Module.finrank F V)
    (hboundary : ScalarSpinorNormBoundary hp e Q)
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial)
    (hquot : (ξ.map p).IsTrivial) : ξ.IsTrivial :=
  Cocycle.isTrivial_of_kernelHasse hp (kernelMapHasse_of_spinorNormBoundary hp e Q hQ hrank hboundary)
    ξ hξ hquot

open Quaternionic Langlands.LinearAlgebra.OrthogonalCocycleDescent in
/-- For a cover of the actual scalar determinant-one isometry group, the boundary formula
is sufficient for the Hasse kernel. -/
theorem isTrivial_scalarSpinCover_of_boundary {n : ℕ} [NeZero n]
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))
    (hq : (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q) (hn : 4 ≤ n)
    {π : G ⟶ (FirstKindInvolution.scalar F).normOneIsometryGroup q}
    (hπ : IsCentralIsogeny π) (ε : kernel π ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp)
    (hboundary : ScalarSpinorNormBoundary hπ ε
      ((FirstKindInvolution.scalar F).polar q).toQuadraticForm')
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  let B := (FirstKindInvolution.scalar F).polar q
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  have hB : B.transpose = B := OrthogonalMatrix.scalar_polar_transpose q
  exact isTrivial_of_scalarSpinorNormBoundary hπ ε B.toQuadraticForm'
    (polar_nondegenerate_of_symmetric_unit hB hq) (by simpa using hn) hboundary ξ hξ
    (numberFieldSpecialOrthogonalGaloisHasseKernel F n q hq L (ξ.map π) (hξ.map π))

end Langlands.GroupScheme

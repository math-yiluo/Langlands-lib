import Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinHasseKernels

/-! # The central quaternionic spin Hasse kernel from spinor-norm inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open Quaternionic GaloisPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

section KummerImage

variable {F : Type u} [Field F] {G H : GroupScheme (Spec (CommRingCat.of F))} {p : G ⟶ H}

/-- The image in `G` of the Kummer cocycle of `a ∈ Kˣ`, read through an identification of the
kernel of the central isogeny `p` with `μ₂`, is a coboundary of `M/K`-points of `G`. Here
`z ∈ Mˣ` is a square root of `a`, and the Kummer cocycle is `s ↦ s(z)/z`. -/
def KummerImageTrivial (hp : IsCentralIsogeny p)
    (e : kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp)
    (K M : Type u) [Field K] [Field M] [Algebra F K] [Algebra F M] [Algebra K M]
    [IsScalarTower F K M] [FiniteDimensional K M] [IsGalois K M]
    (a : Kˣ) (z : Mˣ) (hz : z ^ 2 = Units.map (algebraMap K M) a) : Prop :=
  ∃ b : G.affinePoints (CommAlgCat.of F M), ∀ s : M ≃ₐ[K] M,
    hp.kernelPointInclusion M ((hp.kernelRootsEquiv 2 e M).symm
      (KummerCocycle.rootValue 2 a hz s)) = b * (relativeConjugate F K M G s b)⁻¹

end KummerImage

namespace Quaternionic.FirstKindInvolution

variable {F : Type u} [Field F] {D : Type u} [DivisionRing D] [Algebra F D]
  (σ : FirstKindInvolution F D) {n : ℕ} (q : σ.QuadraticForms (Fin n))

/-- Over a field `K` containing `F`, either `K ⊗ D` is a division ring or the hermitian form
`h(y, y) = ∑ j k, y j * Q j k * σ(y k)` of `q`, with `Q` the polar Gram matrix, is anisotropic
on `(K ⊗ D)^n`. -/
def DivisionOrAnisotropicAt (K : Type u) [Field K] [Algebra F K] : Prop :=
  (∀ y : K ⊗[F] D, y ≠ 0 → IsUnit y) ∨
    ∀ y : Fin n → K ⊗[F] D,
      ∑ j, ∑ k, y j * ((1 : K) ⊗ₜ[F] σ.polar q j k) * σ.baseChange K (y k) = 0 → y = 0

end Quaternionic.FirstKindInvolution

/-- The kernel of a central isogeny from a simply connected group onto the reduced-norm-one
isometry group of a nondegenerate quadratic form of rank at least three over a quaternion
division algebra with an orthogonal involution, in characteristic zero, is `μ₂`. -/
def QuaternionicSpinKernelMuStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F]
    (D : Type u) [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D],
    Module.finrank F D = 4 → ∀ (σ : FirstKindInvolution F D),
    Module.finrank F σ.symmetricSubspace = 3 →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (q : σ.QuadraticForms (Fin n)),
    σ.IsNondegenerateQuadratic q →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) (p : G ⟶ σ.normOneIsometryGroup q),
    IsSimplyConnected G → IsCentralIsogeny p →
    Nonempty (kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp)

/-- The spinor norm of a line similitude. Let `x` be a row with nonzero hermitian value
`c = h(x, x)` and let `d ∈ D` satisfy `d c σ(d) = N c` with `N = Nrd(d) ≠ 0`. Then the image
in the simply connected cover of the Kummer cocycle of `N` is a coboundary on every finite
Galois extension containing a square root of `N`. -/
def QuaternionicSpinLineSimilitudeBoundaryStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F]
    (D : Type u) [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D],
    Module.finrank F D = 4 → ∀ (σ : FirstKindInvolution F D),
    Module.finrank F σ.symmetricSubspace = 3 →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (q : σ.QuadraticForms (Fin n)),
    σ.IsNondegenerateQuadratic q →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) (p : G ⟶ σ.normOneIsometryGroup q),
    IsSimplyConnected G → ∀ (hp : IsCentralIsogeny p)
    (e : kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp) (x : Fin n → D) (d : D) (N : Fˣ),
    σ.sesqForm (σ.polar q) x x ≠ 0 →
    d * σ.sesqForm (σ.polar q) x x * σ d = (N : F) • σ.sesqForm (σ.polar q) x x →
    CentralSimple.reducedNorm F D F ((1 : F) ⊗ₜ[F] d) = N →
    ∀ (M : Type u) [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
      (z : Mˣ) (hz : z ^ 2 = Units.map (algebraMap F M) N),
      KummerImageTrivial hp e F M N z hz

/-- At a real place where `D` stays a division algebra or the form stays anisotropic, the
image in the simply connected cover of the Kummer cocycle of `a` is a coboundary only when
`a` is a square of the completion. -/
def NumberFieldQuaternionicSpinRealBoundaryStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (D : Type u) [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D],
    Module.finrank F D = 4 → ∀ (σ : FirstKindInvolution F D),
    Module.finrank F σ.symmetricSubspace = 3 →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (q : σ.QuadraticForms (Fin n)),
    σ.IsNondegenerateQuadratic q →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) (p : G ⟶ σ.normOneIsometryGroup q),
    IsSimplyConnected G → ∀ (hp : IsCentralIsogeny p)
    (e : kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp) (v : InfinitePlace F), v.IsReal →
    σ.DivisionOrAnisotropicAt q v.Completion →
    ∀ (M : Type u) [Field M] [Algebra v.Completion M] [Algebra F M]
      [IsScalarTower F v.Completion M] [FiniteDimensional v.Completion M]
      [IsGalois v.Completion M] (a : v.Completionˣ) (z : Mˣ)
      (hz : z ^ 2 = Units.map (algebraMap v.Completion M) a),
      KummerImageTrivial hp e v.Completion M a z hz → IsSquare (a : v.Completion)

/-- A number-field element that is a square at every real place where `D` stays a division
algebra or the form stays anisotropic is, up to a square, the multiplier `Nrd(d)` of a line
similitude `d c σ(d) = Nrd(d) c` of a nonzero hermitian value `c = h(x, x)`. -/
def NumberFieldQuaternionicSpinorValueStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (D : Type u) [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D],
    Module.finrank F D = 4 → ∀ (σ : FirstKindInvolution F D),
    Module.finrank F σ.symmetricSubspace = 3 →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (q : σ.QuadraticForms (Fin n)),
    σ.IsNondegenerateQuadratic q →
    ∀ a : Fˣ, (∀ v : InfinitePlace F, v.IsReal → σ.DivisionOrAnisotropicAt q v.Completion →
        IsSquare (algebraMap F v.Completion a)) →
      ∃ (x : Fin n → D) (d : D) (s : Fˣ), σ.sesqForm (σ.polar q) x x ≠ 0 ∧
        d * σ.sesqForm (σ.polar q) x x * σ d =
          CentralSimple.reducedNorm F D F ((1 : F) ⊗ₜ[F] d) • σ.sesqForm (σ.polar q) x x ∧
        CentralSimple.reducedNorm F D F ((1 : F) ⊗ₜ[F] d) = a * s ^ 2

private theorem cocycle_eq_of_toFun' {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}
    {ξ ζ : Cocycle G U} (h : ∀ {Z : Over S} (a b : Z ⟶ U), ξ.toFun a b = ζ.toFun a b) :
    ξ = ζ := by
  obtain ⟨f, _, _⟩ := ξ
  obtain ⟨g, _, _⟩ := ζ
  have : @f = @g := funext fun Z => funext fun a => funext fun b => h a b
  subst this
  rfl

section Reduction

variable {F : Type u} [Field F] [NumberField F]
  {D : Type u} [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D]
  {σ : FirstKindInvolution F D} {n : ℕ} [NeZero n] {q : σ.QuadraticForms (Fin n)}
  {G : GroupScheme (Spec (CommRingCat.of F))} {p : G ⟶ σ.normOneIsometryGroup q}
  (hp : IsCentralIsogeny p) (e : kernel p ≅ (mu (Spec (CommRingCat.of F)) 2).toGrp)

local notation "χ" => (Iso.hom e ≫ Additive.toMul (mu.incl (Spec (CommRingCat.of F)) 2))

include hp e in
/-- The four inputs give the central Hasse kernel for a central isogeny onto the
reduced-norm-one isometry group whose kernel is identified with `μ₂`. -/
private theorem kernelMapHasse_of_boundaries
    (h2 : QuaternionicSpinLineSimilitudeBoundaryStatement.{u})
    (h3 : NumberFieldQuaternionicSpinRealBoundaryStatement.{u})
    (h4 : NumberFieldQuaternionicSpinorValueStatement.{u})
    (hD : Module.finrank F D = 4) (hσ : Module.finrank F σ.symmetricSubspace = 3) (hn : 3 ≤ n)
    (hq : σ.IsNondegenerateQuadratic q) (hG : IsSimplyConnected G)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (α : Cocycle (kernel p) (GaloisCocycle.cover F L))
    (hα : (α.map (kernelι p)).LocallyTrivial) :
    (α.map (kernelι p)).IsTrivial := by
  let c (s : L ≃ₐ[F] L) := hp.kernelUnitMap (χ) L (GaloisCocycle.value α s)
  have hc : groupCohomology.IsMulCocycle₁ c := by
    intro s t
    have hnat := hp.kernelUnitMap_naturality (χ) s.toAlgHom (GaloisCocycle.value α t)
    change hp.kernelUnitMap (χ) L (conjugate F L (kernel p) s (GaloisCocycle.value α t)) =
      s • c t at hnat
    calc
      c (s * t) = c s * hp.kernelUnitMap (χ) L
          (conjugate F L (kernel p) s (GaloisCocycle.value α t)) :=
        (congrArg (hp.kernelUnitMap (χ) L) (GaloisCocycle.value_mul α s t)).trans (map_mul _ _ _)
      _ = s • c t * c s := by rw [hnat, mul_comm]
  have hc₂ (s : L ≃ₐ[F] L) : c s ^ 2 = 1 := by
    rw [show c s = _ from (hp.kernelRootsEquiv_val 2 e L (GaloisCocycle.value α s)).symm]
    exact (mem_rootsOfUnity 2 _).mp (hp.kernelRootsEquiv 2 e L (GaloisCocycle.value α s)).property
  obtain ⟨a, z, hz, hr⟩ := KummerCocycle.exists_radical 2 c hc hc₂
  have hroot (s : L ≃ₐ[F] L) :
      (hp.kernelRootsEquiv 2 e L).symm (KummerCocycle.rootValue 2 a hz s) =
        GaloisCocycle.value α s := by
    apply hp.kernelUnitMap_mu_injective 2 e
    rw [hp.kernelUnitMap_kernelRootsEquiv_symm]
    exact hr s
  have hv (v : InfinitePlace F) (hvr : v.IsReal)
      (hcond : σ.DivisionOrAnisotropicAt q v.Completion) :
      IsSquare (algebraMap F v.Completion (a : F)) := by
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
    have hK : KummerImageTrivial hp e K M a₀ z₀ hz₀ := by
      refine ⟨b, fun s => ?_⟩
      change _ = b * (conjugate F M G (s.restrictScalars F) b)⁻¹
      refine Eq.trans ?_ (hb s)
      let ρ := (s.restrictScalars F).restrictNormal L
      change hp.kernelPointInclusion M ((hp.kernelRootsEquiv 2 e M).symm
          (KummerCocycle.rootValue 2 a₀ hz₀ s)) =
        hp.kernelPointInclusion M (relativeExtend F L M (kernel p) (GaloisCocycle.value α ρ))
      congr 1
      apply hp.kernelUnitMap_mu_injective 2 e
      have hnat : hp.kernelUnitMap (χ) M (relativeExtend F L M (kernel p)
          (GaloisCocycle.value α ρ)) = Units.map (algebraMap L M) (c ρ) :=
        hp.kernelUnitMap_naturality (χ) (IsScalarTower.toAlgHom F L M) (GaloisCocycle.value α ρ)
      rw [hp.kernelUnitMap_kernelRootsEquiv_symm, hnat, ← hr ρ]
      change KummerCocycle.value z₀ s = Units.map (algebraMap L M) (KummerCocycle.value z ρ)
      rw [KummerCocycle.value, KummerCocycle.value, map_div]
      congr 1
      apply Units.ext
      exact ((s.restrictScalars F).restrictNormal_commutes L (z : L)).symm
    exact h3 F D hD σ hσ n hn q hq G p hG hp e v hvr hcond M a₀ z₀ hz₀ hK
  obtain ⟨x, d, s, hx, hd, hN⟩ := h4 F D hD σ hσ n hn q hq a hv
  let N : Fˣ := a * s ^ 2
  have hdN : CentralSimple.reducedNorm F D F ((1 : F) ⊗ₜ[F] d) = (N : F) := by
    rw [hN]
    simp [N]
  let z' : Lˣ := z * Units.map (algebraMap F L) s
  have hz' : z' ^ 2 = Units.map (algebraMap F L) N := by
    simp only [z', N, mul_pow, hz, map_mul, map_pow]
  obtain ⟨b, hb⟩ := h2 F D hD σ hσ n hn q hq G p hG hp e x d N hx (by rw [hd, hdN]) hdN L z' hz'
  have hrv (t : L ≃ₐ[F] L) :
      KummerCocycle.rootValue 2 N hz' t = KummerCocycle.rootValue 2 a hz t := by
    apply Subtype.ext
    change KummerCocycle.value z' t = KummerCocycle.value z t
    have hs : t • Units.map (algebraMap F L : F →* L) s =
        Units.map (algebraMap F L : F →* L) s := by
      ext
      simp
    simp only [KummerCocycle.value, z', smul_mul', hs, mul_div_mul_right_eq_div]
  refine (GaloisCocycle.isTrivial_iff _).mpr ⟨b, fun t => ?_⟩
  change hp.kernelPointInclusion L (GaloisCocycle.value α t) = _
  rw [← hroot t, ← hrv t]
  exact hb t

end Reduction

/-- The four inputs prove the central part of the quaternionic spin Hasse kernel. -/
theorem numberFieldQuaternionicSpinKernelHasse_of_boundaries
    (h1 : QuaternionicSpinKernelMuStatement.{u})
    (h2 : QuaternionicSpinLineSimilitudeBoundaryStatement.{u})
    (h3 : NumberFieldQuaternionicSpinRealBoundaryStatement.{u})
    (h4 : NumberFieldQuaternionicSpinorValueStatement.{u}) :
    NumberFieldQuaternionicSpinKernelHasseStatement.{u} := by
  intro F _ _ D _ _ _ _ hD σ hσ n hn q hq G π hπ L _ _ _ _ α hα
  have : NeZero n := ⟨by omega⟩
  have := hπ.smooth
  have hG := hπ.isSimplyConnected
  obtain ⟨p₀, hp₀, hpπ⟩ := hπ.exists_centralIsogeny
  let e₀ := σ.connectedIsometryIsoNormOne q p₀ hp₀ hG.isSemisimple
    (quaternionicNormOneIsometryConnectedness F D hD σ hσ n q hq)
  have hp : IsCentralIsogeny (p₀ ≫ e₀.hom) := hp₀.comp_iso e₀
  obtain ⟨e⟩ := h1 F D hD σ hσ n (by omega) q hq G (p₀ ≫ e₀.hom) hG hp
  let incl := identityComponentι (σ.isometryGroup q)
  have key : ∀ (π' : G ⟶ σ.isometryGroup q), p₀ ≫ incl = π' →
      ∃ k : kernel π' ⟶ kernel (p₀ ≫ e₀.hom), k ≫ kernelι (p₀ ≫ e₀.hom) = kernelι π' := by
    rintro π' rfl
    refine ⟨(kernelPostcompIso p₀ incl).hom ≫ (kernelPostcompIso p₀ e₀.hom).inv, ?_⟩
    rw [Category.assoc, (Iso.inv_comp_eq _).mpr (kernelPostcompIso_hom_ι p₀ e₀.hom).symm,
      kernelPostcompIso_hom_ι]
  obtain ⟨k, hk⟩ := key π hpπ
  have heq : (α.map k).map (kernelι (p₀ ≫ e₀.hom)) = α.map (kernelι π) := by
    apply cocycle_eq_of_toFun'
    intro Z a b
    change (α.toFun a b ≫ k.hom.hom) ≫ (kernelι (p₀ ≫ e₀.hom)).hom.hom =
      α.toFun a b ≫ (kernelι π).hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hk]
  rw [← heq] at hα ⊢
  exact kernelMapHasse_of_boundaries hp e h2 h3 h4 hD hσ (by omega) hq hG L (α.map k) hα

end Langlands.GroupScheme

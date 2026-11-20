import Langlands.GroupScheme.IntermediatePointNorm
import Langlands.GroupScheme.Torus.WeilCocharacterTransfer
import Langlands.Algebra.QuadraticOrbitProduct
import Mathlib.Analysis.Real.Sqrt

/-! # Intermediate point norms at a quadratic extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RealTorusNorm

variable (F K M : Type u) [Field F] [Field K] [Field M]
  [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

local notation "P" => Lie.AffinePoints T.toGrp M
local notation "j" => IsScalarTower.toAlgHom F K M
local notation "conj" σ:max => GaloisPoint.conjugate F M T.toGrp (AlgEquiv.restrictScalars F σ)

/-- The norm product as an endomorphism of the extension-field points. -/
def quadraticProduct (σ : M ≃ₐ[K] M) : P →* P := MonoidHom.id P * conj σ

/-- A point class modulo the subgroup of products with the conjugate. -/
def quadraticClass (σ : M ≃ₐ[K] M) : P →* P ⧸ (quadraticProduct F K M T σ).range :=
  QuotientGroup.mk' _

@[simp] theorem quadraticClass_product (σ : M ≃ₐ[K] M) (x : P) :
    quadraticClass F K M T σ (x * (conj σ) x) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩

/-- Equality of norm classes means that the two points differ by a norm product. -/
theorem quadraticClass_eq_iff (σ : M ≃ₐ[K] M) (x y : P) :
    quadraticClass F K M T σ x = quadraticClass F K M T σ y ↔
      ∃ r : P, x = y * (r * (conj σ) r) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := QuotientGroup.eq_iff_div_mem.mp h
    change r * (conj σ) r = x / y at hr
    exact ⟨r, by rw [hr, mul_comm y, div_mul_cancel]⟩
  · rintro ⟨r, rfl⟩
    rw [map_mul, quadraticClass_product, mul_one]

/-- For a quadratic Galois extension, an embedding fixed pointwise by its
nonidentity automorphism factors through the base field. -/
theorem exists_baseEmbedding [FiniteDimensional K M] [IsGalois K M]
    (hcard : Nat.card (M ≃ₐ[K] M) = 2) (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1)
    {B : Type u} [Field B] [Algebra F B] (g : B →ₐ[F] M) (hg : ∀ x, σ (g x) = g x) :
    ∃ f : B →ₐ[F] K, (j).comp f = g := by
  obtain ⟨τ, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : M ≃ₐ[K] M)).mp hcard
  have hmem (b : B) : g b ∈ (j).range := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (g b)).mpr
    intro γ
    by_cases hγ : γ = 1
    · rw [hγ]; rfl
    · rw [huniq γ hγ, ← huniq σ hσ, hg]
  let d := AlgEquiv.ofInjective (j) (j).injective
  refine ⟨d.symm.toAlgHom.comp (g.codRestrict _ hmem), ?_⟩
  exact AlgHom.ext fun b => congrArg Subtype.val (d.apply_symm_apply ⟨g b, hmem b⟩)

private theorem conjugate_affineMap_base (σ : M ≃ₐ[K] M) (y : Lie.AffinePoints T.toGrp K) :
    (conj σ) (Lie.affineMap T.toGrp j y) = Lie.affineMap T.toGrp j y := by
  change Lie.affineMap T.toGrp (σ.restrictScalars F).toAlgHom (Lie.affineMap T.toGrp j y) = _
  rw [← Lie.affineMap_comp]
  have h : (σ.restrictScalars F).toAlgHom.comp j = j := AlgHom.ext σ.commutes
  rw [h]

variable {B : Type u} [Field B] [Algebra F B]

local notation "V" ν:max => WeilGm.cocharacterValue F B T (CommGroupScheme.groupHom ν) B

private theorem exists_unit_sq_of_pos (e : K ≃+* ℝ) (c : Kˣ) (h : 0 < e (c : K)) :
    ∃ b : Kˣ, b ^ 2 = c := by
  let b := e.symm (Real.sqrt (e (c : K)))
  have hb : b ^ 2 = (c : K) := by
    apply e.injective
    rw [map_pow, show e b = Real.sqrt (e (c : K)) from e.apply_symm_apply _, Real.sq_sqrt h.le]
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, zero_pow two_ne_zero] at hb
    exact c.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, Units.ext hb⟩

/-- At a real embedding, a positive unit gives the trivial norm class. -/
theorem quadraticClass_cocharacter_of_pos (σ : M ≃ₐ[K] M) (e : K ≃+* ℝ)
    (f : B →ₐ[F] K) (ν : cocharacterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap F B)).obj T)) (a : Bˣ) (ha : 0 < e (f a)) :
    quadraticClass F K M T σ (Lie.affineMap T.toGrp ((j).comp f) ((V ν) a)) = 1 := by
  let : Algebra B K := f.toRingHom.toAlgebra
  let : IsScalarTower F B K := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let g : B →ₐ[B] K := Algebra.ofId B K
  let c := Units.map g.toMonoidHom a
  obtain ⟨b, hb⟩ := exists_unit_sq_of_pos K e c ha
  let y := WeilGm.cocharacterValue F B T (CommGroupScheme.groupHom ν) K b
  have hg : g.restrictScalars F = f := AlgHom.ext fun _ => rfl
  have hy : y ^ 2 = Lie.affineMap T.toGrp f ((V ν) a) := by
    change (WeilGm.cocharacterValue F B T (CommGroupScheme.groupHom ν) K b) ^ 2 = _
    rw [← map_pow, hb]
    exact (WeilGm.cocharacterValue_naturality F B T (CommGroupScheme.groupHom ν) g a).trans
      (congrArg (fun φ => Lie.affineMap T.toGrp φ ((V ν) a)) hg)
  rw [Lie.affineMap_comp, ← hy, map_pow, pow_two]
  let z := Lie.affineMap T.toGrp j y
  change quadraticClass F K M T σ (z * z) = 1
  calc
    _ = quadraticClass F K M T σ (z * (conj σ) z) :=
      congrArg (fun z' => quadraticClass F K M T σ (z * z'))
        (conjugate_affineMap_base F K M T σ y).symm
    _ = 1 := quadraticClass_product F K M T σ z

/-- At a real embedding, a negative unit gives the class of the same
cocharacter evaluated at `-1`. -/
theorem quadraticClass_cocharacter_of_neg (σ : M ≃ₐ[K] M) (e : K ≃+* ℝ)
    (f : B →ₐ[F] K) (ν : cocharacterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap F B)).obj T)) (a : Bˣ) (ha : e (f a) < 0) :
    quadraticClass F K M T σ (Lie.affineMap T.toGrp ((j).comp f) ((V ν) a)) =
      quadraticClass F K M T σ (Lie.affineMap T.toGrp ((j).comp f) ((V ν) (-1))) := by
  have hp : 0 < e (f (-a : Bˣ)) := by
    change 0 < e (f (-(a : B)))
    rw [map_neg, map_neg, neg_pos]
    exact ha
  have h : a = (-1 : Bˣ) * (-a) := by
    apply Units.ext
    change (a : B) = -1 * (-(a : B))
    rw [neg_one_mul, neg_neg]
  let φ := (quadraticClass F K M T σ).comp ((Lie.affineMap T.toGrp ((j).comp f)).comp (V ν))
  change φ a = φ (-1)
  have hpos : φ (-a) = 1 := quadraticClass_cocharacter_of_pos F K M T σ e f ν (-a) hp
  calc
    φ a = φ ((-1) * (-a)) := congrArg φ h
    _ = φ (-1) := by rw [map_mul, hpos, mul_one]

variable (E : Type u) [Field E] [Algebra F E] [Algebra E M] [IsScalarTower F E M]
  [IsGalois F E] (N : IntermediateField F E)

local notation "eEM" => IsScalarTower.toAlgHom F E M

/-- Conjugate an intermediate-field embedding by restricting the local automorphism. -/
def conjugateEmbedding (σ : M ≃ₐ[K] M) (i : N →ₐ[F] E) : N →ₐ[F] E :=
  ((σ.restrictScalars F).restrictNormal E).toAlgHom.comp i

/-- The image of the conjugated embedding is conjugated pointwise. -/
theorem conjugateEmbedding_apply (σ : M ≃ₐ[K] M) (i : N →ₐ[F] E) (x : N) :
    eEM (conjugateEmbedding F K M E N σ i x) = σ (eEM (i x)) :=
  AlgEquiv.restrictNormal_commutes (σ.restrictScalars F) E (i x)

open scoped Classical in
/-- The terms that survive in a quadratic norm class are the fixed embeddings. -/
theorem quadraticClass_intermediateNorm [FiniteDimensional F E] [IsAffine T.X.left] (σ : M ≃ₐ[K] M)
    (hσ : σ * σ = 1) (x : Lie.AffinePoints T.toGrp N) :
    quadraticClass F K M T σ (GaloisPoint.extend F M T.toGrp
      (GaloisPoint.intermediateNorm F E N T x)) =
        ∏ i ∈ Finset.univ with conjugateEmbedding F K M E N σ i = i,
          quadraticClass F K M T σ (Lie.affineMap T.toGrp ((eEM).comp i) x) := by
  classical
  let s := conjugateEmbedding F K M E N σ
  let f : (N →ₐ[F] E) → P := fun i => Lie.affineMap T.toGrp ((eEM).comp i) x
  have hs : Function.Involutive s := by
    intro i
    apply AlgHom.ext
    intro a
    apply (eEM).injective
    change eEM (conjugateEmbedding F K M E N σ (conjugateEmbedding F K M E N σ i) a) = _
    rw [conjugateEmbedding_apply, conjugateEmbedding_apply]
    change (σ * σ) (eEM (i a)) = _
    rw [hσ]; rfl
  have hf (i : N →ₐ[F] E) : f (s i) = (conj σ) (f i) := by
    change Lie.affineMap T.toGrp ((eEM).comp (s i)) x =
      Lie.affineMap T.toGrp (σ.restrictScalars F).toAlgHom (Lie.affineMap T.toGrp ((eEM).comp i) x)
    rw [← Lie.affineMap_comp]
    have hcomp : (eEM).comp (s i) = (σ.restrictScalars F).toAlgHom.comp ((eEM).comp i) :=
      AlgHom.ext (conjugateEmbedding_apply F K M E N σ i)
    rw [hcomp]
  obtain ⟨r, hr⟩ := Langlands.Algebra.quadraticOrbitProduct _ _ s hs (conj σ) f hf
  rw [GaloisPoint.map_intermediateNorm F E N T eEM x]
  change quadraticClass F K M T σ (∏ i, f i) = _
  rw [hr, map_mul, quadraticClass_product, mul_one, map_prod]

open scoped Classical in
/-- The intermediate point norm reduces to the product at fixed embeddings
modulo products with the conjugate. -/
def QuadraticIntermediateNormStatement : Prop :=
  ∀ (F K M : Type u) [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    (E : Type u) [Field E] [Algebra F E] [Algebra E M] [IsScalarTower F E M]
    [IsGalois F E] [FiniteDimensional F E] (N : IntermediateField F E)
    (σ : M ≃ₐ[K] M), σ * σ = 1 → ∀ x : Lie.AffinePoints T.toGrp N,
      quadraticClass F K M T σ (GaloisPoint.extend F M T.toGrp
        (GaloisPoint.intermediateNorm F E N T x)) =
          ∏ i ∈ Finset.univ with conjugateEmbedding F K M E N σ i = i,
            quadraticClass F K M T σ (Lie.affineMap T.toGrp
              ((IsScalarTower.toAlgHom F E M).comp i) x)

theorem quadraticIntermediateNorm : QuadraticIntermediateNormStatement.{u} := by
  intro F K M _ _ _ _ _ _ _ T _ E _ _ _ _ _ _ N σ hσ x
  exact quadraticClass_intermediateNorm F K M T E N σ hσ x

end Langlands.GroupScheme.RealTorusNorm

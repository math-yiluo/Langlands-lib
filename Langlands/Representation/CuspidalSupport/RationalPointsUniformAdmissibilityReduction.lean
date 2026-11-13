import Langlands.Representation.CuspidalSupport.RationalNormKernelSupportGeometry
import Langlands.Representation.CuspidalSupport.UniformAdmissibilityStatements
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement
import Langlands.Representation.Plancherel.RationalImageLattice
import Langlands.Representation.Plancherel.RationalNormKernelCompactOpenTransport
import Langlands.Representation.Aubert.General.UnipotentIntersectionHaarDeterminant

/-! # Renard VI.2.3 for `G(F)`, conditional on the Chapter V structure and VI.2.2 -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Hecke

universe uG uM

section Generic

open scoped IsMulCommutative

variable {G : Type uG} [Group G]

/-- A monoid homomorphism twisted by a central-valued one: `x ↦ f x * g x`. -/
def centralTwistHom {M : Type uM} [Monoid M] (f g : M →* G)
    (hg : ∀ x, g x ∈ Subgroup.center G) : M →* G where
  toFun x := f x * g x
  map_one' := by simp
  map_mul' a b := by
    have hc : f b * g a = g a * f b := Subgroup.mem_center_iff.mp (hg a) (f b)
    rw [map_mul, map_mul, mul_assoc, ← mul_assoc (f b), hc, mul_assoc, mul_assoc]

/-- An element of an intersection of subgroups of `H` maps into the intersection of
the image subgroups. -/
theorem subtype_mem_map_inf (H : Subgroup G) {A B : Subgroup H} {y : H}
    (hy : y ∈ A ⊓ B) : (y : G) ∈ A.map H.subtype ⊓ B.map H.subtype :=
  ⟨⟨_, hy.1, rfl⟩, ⟨_, hy.2, rfl⟩⟩

/-- An element of an intersection of image subgroups comes from the intersection. -/
theorem exists_mem_inf_of_mem_map_inf (H : Subgroup G) {A B : Subgroup H} {x : G}
    (hx : x ∈ A.map H.subtype ⊓ B.map H.subtype) : ∃ y : H, y ∈ A ⊓ B ∧ (y : G) = x := by
  obtain ⟨⟨y, hy, rfl⟩, ⟨y', hy', hyy'⟩⟩ := hx
  have : y' = y := H.subtype_injective hyy'
  subst this
  exact ⟨y', ⟨hy, hy'⟩, rfl⟩

/-- Positive elements of a subgroup stay positive for the image subgroups. -/
theorem subtype_mem_iwahoriPositiveMonoid_map (H : Subgroup G)
    {K N M Nbar : Subgroup H} {a : H}
    (ha : a ∈ iwahoriPositiveMonoid K N M Nbar) :
    (a : G) ∈ iwahoriPositiveMonoid (K.map H.subtype) (N.map H.subtype)
      (M.map H.subtype) (Nbar.map H.subtype) := by
  have key := fun {A B : Subgroup H} {x : G} =>
    exists_mem_inf_of_mem_map_inf H (A := A) (B := B) (x := x)
  have back := fun {A B : Subgroup H} {y : H} =>
    subtype_mem_map_inf H (A := A) (B := B) (y := y)
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨y, hy, rfl⟩ := key hu
    exact back (ha.1 y hy)
  · intro l hl
    obtain ⟨y, hy, rfl⟩ := key hl
    exact back (ha.2.1 y hy)
  · intro m hm
    obtain ⟨y, hy, rfl⟩ := key hm
    exact back (ha.2.2 y hy)

/-- Precomposition of exponent vectors, as a monoid homomorphism. -/
def exponentPrecompHom {α β : Type*} (f : α → β) :
    Multiplicative (β → ℕ) →* Multiplicative (α → ℕ) where
  toFun n := .ofAdd (n.toAdd ∘ f)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Products of powers of finitely many elements of a commutative monoid, as a
monoid homomorphism on exponent vectors. -/
def powProdHom {C J : Type*} [CommMonoid C] [Fintype J] (c : J → C) :
    Multiplicative (J → ℕ) →* C where
  toFun n := ∏ j, c j ^ n.toAdd j
  map_one' := by simp
  map_mul' a b := by simp [pow_add, Finset.prod_mul_distrib]

/-- Finitely many central elements whose monoid span covers the image of the
centre under a homomorphism to a finitely generated commutative group. -/
theorem exists_center_monoid_generators {B : Type uM} [CommGroup B] (P : G →* B)
    [Module.Finite ℤ (Additive B)] :
    ∃ (r : ℕ) (c : Fin r → Subgroup.center G), ∀ z : Subgroup.center G,
      ∃ n : Fin r → ℕ, P z = P ((∏ j, c j ^ n j : Subgroup.center G) : G) := by
  classical
  let Pc : Subgroup.center G →* B := P.comp (Subgroup.center G).subtype
  let Q : Subgroup B := Pc.range
  have hQ : Q.FG := (Subgroup.fg_iff_add_fg Q).mpr
    ((Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule Q.toAddSubgroup)).mp
      (IsNoetherian.noetherian _))
  obtain ⟨S, hS⟩ := (Subgroup.fg_iff_submonoid_fg Q).mp hQ
  have hmem : ∀ b : S, ∃ y : Subgroup.center G, Pc y = b := by
    intro b
    have : (b : B) ∈ Q.toSubmonoid := hS ▸ Submonoid.subset_closure b.2
    exact this
  choose pre hpre using hmem
  let c : Fin S.card → Subgroup.center G := fun j => pre (S.equivFin.symm j)
  refine ⟨S.card, c, fun z => ?_⟩
  have hrange : Set.range (fun j => Pc (c j)) = (S : Set B) := by
    ext b
    constructor
    · rintro ⟨j, rfl⟩
      simp only [c, hpre]
      exact (S.equivFin.symm j).2
    · intro hb
      refine ⟨S.equivFin ⟨b, hb⟩, ?_⟩
      simp [c, hpre]
  have hz : Pc z ∈ Submonoid.closure (Set.range (fun j => Pc (c j))) := by
    rw [hrange, hS]
    exact ⟨z, rfl⟩
  obtain ⟨n, hn⟩ := Submonoid.mem_closure_range_iff_of_fintype.mp hz
  refine ⟨n, ?_⟩
  change Pc z = Pc (∏ j, c j ^ n j)
  rw [hn, map_prod]
  simp only [map_pow]

end Generic

end Langlands.Hecke

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology
open BruhatTits.SpecialCompact Langlands.Plancherel.RenardCartan
open scoped IsMulCommutative

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}

local instance rationalPointsUniformAdmissibilityPointTopology :
    TopologicalSpace (RationalPoint F G.X) := pointTopology

variable {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} [Fintype (SimpleRoot i ν)]

/-- Renard VI.2.3 for `G(F)`, from the joint special-compact basis, the
standard-cocharacter and relative-root-system statements, and VI.2.2: one bound
for the `K`-fixed vectors of every irreducible smooth representation. -/
theorem exists_uniform_fixedVectors_rank_bound
    (hjoint : JointSpecialCompactBasisExistenceStatement.{uF})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{uF})
    (hRoots : letI := hi.isSplitSubtorus.mono; HasRelativeRootSystem i)
    (hadm : RationalPointsIrreducibleAdmissibleStatement.{uF, uV})
    (K : OpenSubgroup (RationalPoint F G.X)) :
    ∃ c : ℕ, ∀ A : SmoothRep.{0, uF, uV} ℂ (RationalPoint F G.X), A.IsIrreducible →
      Module.rank ℂ (fixedVectors A.representation K.toSubgroup) ≤ c := by
  classical
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hi.isSplitSubtorus.mono
  let : IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
  have : T2Space F := BruhatTits.localField_t2Space F
  have : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
  have : LocallyCompactSpace (RationalPoint F G.X) := rationalPoint_locallyCompactSpace F G
  have : NonarchimedeanGroup (RationalPoint F G.X) := affineRationalPoint_nonarchimedeanGroup G
  let : MeasurableSpace (RationalPoint F G.X) := borel _
  have : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
  let H := Plancherel.rationalCommonNormKernel G
  -- The joint special-compact geometry and the central Cartan factorization of `G(F)`.
  obtain ⟨d⟩ := nonempty_normKernelFundamentalCocharacters hG hi hν hStandard hRoots
  obtain ⟨D, x, Z, j, s, -, -, hsj, h, -, hsc, -, -, -, -, hcompat, hbasis⟩ :=
    hjoint F G hG T i hi ν hν
  obtain ⟨F₀, hF₀⟩ := exists_isFiniteLatticeTransversal D x ν hcompat
  obtain ⟨R, hR, hcover⟩ :=
    d.exists_finite_centralCartanFactorization hG hi hν hStandard D x j s h hsj
      hcompat hF₀
  let K0 := D.specialCompactSubgroup x
  have hK0 : IsCompact (K0 : Set (RationalPoint F G.X)) := hsc.2.1.1
  -- One common norm-kernel level below `K`.
  let U : OpenSubgroup H := K.comap H.subtype continuous_subtype_val
  obtain ⟨L⟩ := nonempty_normKernelCompressionLevel hG hi hν hStandard hRoots d K0 hbasis U
  let KL : OpenSubgroup (RationalPoint F G.X) :=
    Plancherel.rationalNormKernelAmbientLevel G L.level
  have hKL : IsCompact (KL : Set (RationalPoint F G.X)) :=
    Plancherel.isCompact_rationalNormKernelAmbientLevel G L.level L.compact
  have hKLK : KL.toSubgroup ≤ K.toSubgroup := by
    rintro g ⟨k, hk, rfl⟩
    exact L.le_prescribed hk
  -- Finitely many central directions modulo the compact central part of `H`.
  have : Module.Finite ℤ (rationalCharacters G) := (rationalCharacterLattice F G hG).2
  obtain ⟨r, c, hc⟩ :=
    Hecke.exists_center_monoid_generators (Plancherel.rationalValuationImageProjection G)
  let N' := (normKernelUnipotent i ν ∅).map H.subtype
  let M' := (normKernelLevi i ν ∅).map H.subtype
  let Nbar' := (normKernelStandardOpposite (i := i) (ν := ν) ∅).map H.subtype
  let f₁ : Multiplicative (SimpleRoot i ν ⊕ Fin r → ℕ) →* RationalPoint F G.X :=
    H.subtype.comp (d.orthantHom.comp (Hecke.exponentPrecompHom Sum.inl))
  let f₂ : Multiplicative (SimpleRoot i ν ⊕ Fin r → ℕ) →* RationalPoint F G.X :=
    (Subgroup.center (RationalPoint F G.X)).subtype.comp
      ((Hecke.powProdHom c).comp (Hecke.exponentPrecompHom Sum.inr))
  have hf₂ : ∀ n, f₂ n ∈ Subgroup.center (RationalPoint F G.X) := fun n =>
    (((Hecke.powProdHom c).comp (Hecke.exponentPrecompHom Sum.inr)) n).2
  let e : Multiplicative (SimpleRoot i ν ⊕ Fin r → ℕ) →* RationalPoint F G.X :=
    Hecke.centralTwistHom f₁ f₂ hf₂
  have he_apply : ∀ n, e n = f₁ n * f₂ n := fun n => rfl
  -- The norm-kernel level data, transported to `G(F)`.
  have hfactor : ∀ k ∈ KL, ∃ l ∈ KL.toSubgroup ⊓ Nbar',
      ∃ m ∈ KL.toSubgroup ⊓ M', ∃ u ∈ KL.toSubgroup ⊓ N', k = l * m * u := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨l, hl, m, hm, u, hu, hk'⟩ := L.factor k hk
    refine ⟨l, Hecke.subtype_mem_map_inf H hl, m, Hecke.subtype_mem_map_inf H hm,
      u, Hecke.subtype_mem_map_inf H hu, ?_⟩
    rw [hk']
    rfl
  have he : ∀ n, e (Multiplicative.ofAdd n) ∈
      Hecke.iwahoriPositiveMonoid KL.toSubgroup N' M' Nbar' := by
    intro n
    refine Submonoid.mul_mem _ ?_ (Hecke.center_le_iwahoriPositiveMonoid _ _ _ _ (hf₂ _))
    exact Hecke.subtype_mem_iwahoriPositiveMonoid_map H (L.positive (n ∘ Sum.inl))
  have hmid : ∀ n, ∀ m ∈ KL.toSubgroup ⊓ M',
      e (Multiplicative.ofAdd n) * m * (e (Multiplicative.ofAdd n))⁻¹ ∈ KL := by
    intro n m hm
    obtain ⟨m', hm', rfl⟩ := Hecke.exists_mem_inf_of_mem_map_inf H hm
    have hz := Subgroup.mem_center_iff.mp (hf₂ (Multiplicative.ofAdd n))
    have hconj : e (Multiplicative.ofAdd n) * (m' : RationalPoint F G.X) *
        (e (Multiplicative.ofAdd n))⁻¹ =
        f₁ (Multiplicative.ofAdd n) * m' * (f₁ (Multiplicative.ofAdd n))⁻¹ := by
      rw [he_apply, mul_inv_rev, mul_assoc (f₁ _) (f₂ _), ← hz]
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [hconj]
    exact ⟨_, L.forward_levi (n ∘ Sum.inl) m' hm', rfl⟩
  -- The compact normalizing subgroup absorbs the compact central part of `H`.
  let Γ : Subgroup (RationalPoint F G.X) :=
    K0 ⊔ (H ⊓ Subgroup.center (RationalPoint F G.X))
  have hΓc : IsCompact (Γ : Set (RationalPoint F G.X)) :=
    isCompact_sup_of_central K0 _ hK0
      (Plancherel.isCompact_rationalCommonNormKernel_inf_center G hG) inf_le_right
  have hΓ : Γ ≤ Subgroup.normalizer (KL.toSubgroup : Set (RationalPoint F G.X)) :=
    sup_le (L.ambient_normalized hG hK0)
      (inf_le_right.trans (Subgroup.center_le_normalizer _))
  -- Every element of `G(F)` is a positive Cartan element up to `Γ` and `R`.
  have hdecomp : ∀ g : RationalPoint F G.X, ∃ a ∈ Γ, ∃ b ∈ Γ, ∃ f ∈ R,
      ∃ n : SimpleRoot i ν ⊕ Fin r → ℕ,
        g = a * (e (Multiplicative.ofAdd n) * f) * b := by
    intro g
    obtain ⟨n, k₁, hk₁, t, ht, k₂, hk₂, z, hz, hg⟩ := hcover g
    obtain ⟨m, hm⟩ := hc ⟨z, hz⟩
    let cm : Subgroup.center (RationalPoint F G.X) := ∏ j, c j ^ m j
    obtain ⟨w, hwZ, hwH, hz'⟩ : ∃ w ∈ Subgroup.center (RationalPoint F G.X), w ∈ H ∧
        z = (cm : RationalPoint F G.X) * w := by
      refine ⟨(cm : RationalPoint F G.X)⁻¹ * z,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ cm.2) hz, ?_, by group⟩
      change _ ∈ Plancherel.rationalCommonNormKernel G
      rw [← Plancherel.rationalValuationImageProjection_ker G, MonoidHom.mem_ker, map_mul,
        map_inv]
      change (Plancherel.rationalValuationImageProjection G (cm : RationalPoint F G.X))⁻¹ *
        Plancherel.rationalValuationImageProjection G
          ((⟨z, hz⟩ : Subgroup.center (RationalPoint F G.X)) : RationalPoint F G.X) = 1
      rw [hm, inv_mul_cancel]
    refine ⟨k₁, Subgroup.mem_sup_left hk₁, k₂ * w,
      Γ.mul_mem (Subgroup.mem_sup_left hk₂) (Subgroup.mem_sup_right ⟨hwH, hwZ⟩),
      t, ht, Sum.elim n m, ?_⟩
    have hcz := Subgroup.mem_center_iff.mp cm.2
    have he' : e (Multiplicative.ofAdd (Sum.elim n m)) =
        (d.orthantHom (.ofAdd n) : RationalPoint F G.X) * cm := rfl
    rw [he', hg, hz']
    simp only [mul_assoc]
    rw [← mul_assoc k₂ (cm : RationalPoint F G.X) w, hcz k₂,
      mul_assoc (cm : RationalPoint F G.X) k₂ w, ← mul_assoc t (cm : RationalPoint F G.X),
      hcz t, mul_assoc (cm : RationalPoint F G.X) t]
  -- The finite sandwich data at `KL` and the dimension bound.
  obtain ⟨S⟩ := Hecke.nonempty_fixedLevelSandwich_of_residual_iwahoriCartan KL hKL
    (Measure.haar (G := RationalPoint F G.X)) N' M' Nbar' hfactor e he hmid Γ hΓc hΓ
    R hR hdecomp
  refine ⟨S.dimensionBound, fun A hA => ?_⟩
  have hfin : FiniteDimensional ℂ (fixedVectors A.representation KL.toSubgroup) :=
    (hadm F G hG A hA).2 KL
  have hb := S.finrank_le A.representation A.isSmooth hA hfin
  calc Module.rank ℂ (fixedVectors A.representation K.toSubgroup)
      ≤ Module.rank ℂ (fixedVectors A.representation KL.toSubgroup) :=
        Submodule.rank_mono (fixedVectors_antitone A.representation hKLK)
    _ = (Module.finrank ℂ (fixedVectors A.representation KL.toSubgroup) : Cardinal) :=
        (Module.finrank_eq_rank ℂ _).symm
    _ ≤ S.dimensionBound := by exact_mod_cast hb

end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.CuspidalSupport

open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open GroupScheme

universe u v

/-- Renard VI.2.3, Theorem, for `G(F)`, conditional on the joint special-compact basis
(Chapter V), the standard-cocharacter and relative-root-system statements, and
VI.2.2 (irreducible implies admissible). -/
def RationalPointsUniformAdmissibilityReductionStatement : Prop :=
  BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
    StandardCocharacterStatement.{u} → RelativeRootSystemStatement.{u} →
      RationalPointsIrreducibleAdmissibleStatement.{u, v} →
        RationalPointsUniformAdmissibilityStatement.{u, v}

/-- Proof of the conditional reduction: choose a maximal split torus with a
generic cocharacter and apply the fixed-level sandwich bound. -/
theorem rationalPointsUniformAdmissibilityReduction :
    RationalPointsUniformAdmissibilityReductionStatement.{u, v} := by
  intro hjoint hStandard hRootsAll hadm F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro K _
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have : Finite (SimpleRoot i ν) := finite_simpleRoot hG hi ν
  let : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
  exact exists_uniform_fixedVectors_rank_bound hjoint hG hi hν hStandard
    (hRootsAll F G hG T i hi) hadm K

end Langlands.CuspidalSupport

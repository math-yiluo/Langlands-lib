import Langlands.AbelianScheme.Multiplication
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.FppfHomLocality
import Langlands.GroupScheme.QuasiFiniteCommutativeUniformExponentStatement

/-! # Locality of uniform exponents of commutative group schemes -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.UniformExponentLocality

variable {S : Scheme.{u}} (G : GroupScheme S) [IsCommMonObj G.X]

/-- An all-test exponent is equivalent to vanishing of its actual multiplication map. -/
theorem points_pow_iff (n : ℕ) :
    (∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1) ↔
      multiplication G (n : ℤ) = 1 := by
  constructor
  · intro h
    apply Grp.hom_ext
    simpa only [multiplication_hom, zpow_natCast, Grp.Hom.hom_one,
      Mon.Hom.hom_one] using h G.X (𝟙 G.X)
  · intro h T x
    have he := congrArg (fun f : G ⟶ G => x ≫ f.hom.hom) h
    simpa only [points_multiplication, zpow_natCast, Grp.Hom.hom_one,
      Mon.Hom.hom_one, MonObj.comp_one] using he

/-- An all-test exponent is preserved by arbitrary base change. -/
theorem points_pow_baseChange {n : ℕ}
    (h : ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1)
    {S' : Scheme.{u}} (b : S' ⟶ S) :
    ∀ (T : Over S') (x : T ⟶ ((baseChange b).obj G).X), x ^ n = 1 := by
  intro T x
  apply (baseChangePointsEquiv b G T).injective
  rw [map_pow, map_one]
  exact h _ _

/-- A multiple of an all-test exponent is again an all-test exponent. -/
theorem points_pow_of_dvd {m n : ℕ}
    (h : ∀ (T : Over S) (x : T ⟶ G.X), x ^ m = 1) (hmn : m ∣ n) :
    ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 := by
  obtain ⟨r, rfl⟩ := hmn
  intro T x
  rw [pow_mul, h T x, one_pow]

/-- Positive local exponents on an open neighborhood of every base point
have one common positive multiple over a quasi-compact base. -/
theorem exists_points_pow_of_open_neighborhoods [CompactSpace S]
    (hloc : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S),
      IsOpenImmersion b ∧ s ∈ Set.range b ∧
        ∃ n : ℕ, 0 < n ∧
          ∀ (V : Over T) (x : V ⟶ ((baseChange b).obj G).X), x ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 := by
  classical
  choose T b hb hs n hn hpow using hloc
  let (s : S) : IsOpenImmersion (b s) := hb s
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s => Set.range (b s))
    (fun s => (b s).isOpenMap.isOpen_range)
    (fun s _ => Set.mem_iUnion.mpr ⟨s, hs s⟩)
  let N : ℕ := ∏ s ∈ t, n s
  refine ⟨N, Finset.prod_pos (fun s _ => hn s), (points_pow_iff G N).mpr ?_⟩
  apply hom_ext_of_pointwise_etale_baseChange
  intro s
  obtain ⟨i, hi, hsi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ s))
  have hNi : n i ∣ N := Finset.dvd_prod_of_mem n hi
  have he : multiplication ((baseChange (b i)).obj G) (N : ℤ) = 1 :=
    (points_pow_iff _ N).mp (points_pow_of_dvd _ (hpow i) hNi)
  refine ⟨T i, b i, inferInstance, hsi, ?_⟩
  simpa only [multiplication_baseChange, Functor.map_one] using he

/-- The affine-base version of the uniform exponent theorem. -/
def AffineStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))),
    IsCommMonObj G.X →
    LocallyOfFinitePresentation G.X.hom → QuasiCompact G.X.hom →
    QuasiSeparated G.X.hom → LocallyQuasiFinite G.X.hom →
    ∃ n : ℕ, 0 < n ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ G.X), x ^ n = 1

/-- The affine-base theorem suffices for the unchanged quasi-compact-base target. -/
theorem uniformExponent_of_affine (h : AffineStatement.{u}) :
    QuasiFiniteCommutativeUniformExponentStatement.{u} := by
  intro S G hS hcomm hfp hqc hqs hqf
  let := hS
  let := hcomm
  let := hfp
  let := hqc
  let := hqs
  let := hqf
  apply exists_points_pow_of_open_neighborhoods G
  intro s
  let i := S.affineOpenCover.idx s
  let R := S.affineOpenCover.X i
  let b := S.affineOpenCover.f i
  let H := (baseChange b).obj G
  have hcommH : IsCommMonObj H.X := by
    exact baseChange_isCommMonObj b G
  have hfpH : LocallyOfFinitePresentation H.X.hom := by
    change LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hqcH : QuasiCompact H.X.hom := by
    change QuasiCompact (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hqsH : QuasiSeparated H.X.hom := by
    change QuasiSeparated (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hqfH : LocallyQuasiFinite H.X.hom := by
    change LocallyQuasiFinite (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  exact ⟨Spec R, b, inferInstance, S.affineOpenCover.covers s,
    h R H hcommH hfpH hqcH hqsH hqfH⟩

end Langlands.GroupScheme.UniformExponentLocality

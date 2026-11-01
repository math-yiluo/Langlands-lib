import Langlands.AlgebraicGeometry.Modules.SectionCoefficients
import Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAmpleExistenceDescentStatement
import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormProof
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteSetSectionProof
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Descent of ample line-bundle existence along finite field extensions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.SchemeModule Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

namespace NormDescent

/-- Restricting a function twice is restricting it once. -/
lemma presheaf_map_map {Z : Scheme.{u}} {A B C : Z.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B)
    (f : Γ(Z, A)) :
    Z.presheaf.map (homOfLE h₂).op (Z.presheaf.map (homOfLE h₁).op f) =
      Z.presheaf.map (homOfLE (h₂.trans h₁)).op f := by
  change (Z.presheaf.map (homOfLE h₁).op ≫ Z.presheaf.map (homOfLE h₂).op) f = _
  rw [← Functor.map_comp]
  rfl

variable {X Y : Scheme.{u}} (π : Y ⟶ X) {P : Y.Modules} {ι : Type u}
  (T : ι → X.Opens) (S : ι → GlobalSections P)
  (hT : ∀ i, π ⁻¹ᵁ T i ≤ trivializationOpen P (S i))

/-- The coefficient of `S j` against `S i` on the preimage of `T i`. -/
noncomputable def coeff (i j : ι) : Γ(Y, π ⁻¹ᵁ T i) :=
  (exists_smul_sectionRes_eq (hT i) (sectionRes P (S j) (π ⁻¹ᵁ T i))).choose

lemma coeff_spec (i j : ι) :
    coeff π T S hT i j • sectionRes P (S i) (π ⁻¹ᵁ T i) = sectionRes P (S j) (π ⁻¹ᵁ T i) :=
  (exists_smul_sectionRes_eq (hT i) (sectionRes P (S j) (π ⁻¹ᵁ T i))).choose_spec

/-- The restriction of a coefficient to the preimage of a smaller open. -/
noncomputable abbrev coeffRes (i j : ι) {W : X.Opens} (hW : W ≤ T i) : Γ(Y, π ⁻¹ᵁ W) :=
  Y.presheaf.map (homOfLE (π.preimage_mono hW)).op (coeff π T S hT i j)

lemma coeffRes_spec (i j : ι) {W : X.Opens} (hW : W ≤ T i) :
    coeffRes π T S hT i j hW • sectionRes P (S i) (π ⁻¹ᵁ W) =
      sectionRes P (S j) (π ⁻¹ᵁ W) :=
  smul_sectionRes_res _ (coeff_spec π T S hT i j)

lemma coeffRes_res (i j : ι) {W W' : X.Opens} (hW : W ≤ T i) (h : W' ≤ W) :
    Y.presheaf.map (homOfLE (π.preimage_mono h)).op (coeffRes π T S hT i j hW) =
      coeffRes π T S hT i j (h.trans hW) :=
  presheaf_map_map _ _ _

lemma coeffRes_mul (i j k : ι) {W : X.Opens} (hi : W ≤ T i) (hj : W ≤ T j) :
    coeffRes π T S hT i k hi = coeffRes π T S hT i j hi * coeffRes π T S hT j k hj := by
  rw [mul_comm]
  exact coeff_mul ((π.preimage_mono hi).trans (hT i)) (coeffRes_spec π T S hT i j hi)
    (coeffRes_spec π T S hT j k hj) (coeffRes_spec π T S hT i k hi)

lemma coeffRes_self (i : ι) {W : X.Opens} (hi : W ≤ T i) :
    coeffRes π T S hT i i hi = 1 := by
  apply smul_sectionRes_injective ((π.preimage_mono hi).trans (hT i))
  rw [coeffRes_spec, one_smul]

lemma basicOpen_coeff (i k : ι) :
    Y.basicOpen (coeff π T S hT i k) = π ⁻¹ᵁ T i ⊓ trivializationOpen P (S k) :=
  basicOpen_coeff_eq (hT i) (coeff_spec π T S hT i k)

variable (Nm : ∀ U : X.Opens, Γ(Y, π ⁻¹ᵁ U) →* Γ(X, U))
  (hNm : ∀ (U V : X.Opens) (hUV : U ≤ V) (f : Γ(Y, π ⁻¹ᵁ V)),
    X.presheaf.map (homOfLE hUV).op (Nm V f) =
      Nm U (Y.presheaf.map (homOfLE (π.preimage_mono hUV)).op f))

include hNm in
lemma norm_coeffRes_res (i j : ι) {W W' : X.Opens} (hW : W ≤ T i) (h : W' ≤ W) :
    X.presheaf.map (homOfLE h).op (Nm W (coeffRes π T S hT i j hW)) =
      Nm W' (coeffRes π T S hT i j (h.trans hW)) := by
  rw [hNm _ _ h, coeffRes_res π T S hT i j hW h]

/-- The norms of the coefficients on overlaps, as units. -/
noncomputable def cocycle (i j : ι) : (Γ(X, T i ⊓ T j))ˣ where
  val := Nm _ (coeffRes π T S hT i j inf_le_left)
  inv := Nm _ (coeffRes π T S hT j i inf_le_right)
  val_inv := by
    rw [← map_mul, ← coeffRes_mul, coeffRes_self, map_one]
  inv_val := by
    rw [← map_mul, ← coeffRes_mul, coeffRes_self, map_one]

include hNm in
lemma cocycle_cond (i j k : ι) :
    X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ⊓ T k ≤ T i ⊓ T j)).op
        (cocycle π T S hT Nm i j : Γ(X, T i ⊓ T j)) *
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        T i ⊓ T j ⊓ T k ≤ T j ⊓ T k)).op (cocycle π T S hT Nm j k : Γ(X, T j ⊓ T k)) =
    X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        T i ⊓ T j ⊓ T k ≤ T i ⊓ T k)).op (cocycle π T S hT Nm i k : Γ(X, T i ⊓ T k)) := by
  change X.presheaf.map _ (Nm _ (coeffRes π T S hT i j _)) *
      X.presheaf.map _ (Nm _ (coeffRes π T S hT j k _)) =
    X.presheaf.map _ (Nm _ (coeffRes π T S hT i k _))
  rw [norm_coeffRes_res π T S hT Nm hNm, norm_coeffRes_res π T S hT Nm hNm,
    norm_coeffRes_res π T S hT Nm hNm, ← map_mul, ← coeffRes_mul]

include hNm in
lemma family_compatible (k i j : ι) :
    X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op
        (Nm (T i) (coeff π T S hT i k)) =
      (cocycle π T S hT Nm i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
          (Nm (T j) (coeff π T S hT j k)) := by
  rw [hNm, hNm]
  change Nm _ (coeffRes π T S hT i k inf_le_left) =
    Nm _ (coeffRes π T S hT i j inf_le_left) * Nm _ (coeffRes π T S hT j k inf_le_right)
  rw [← map_mul, ← coeffRes_mul]

include hT hNm in
/-- The cocycle of norms glues to a line bundle on `X` having, for every index `k`, a
global section whose generation open is exactly `T k`. -/
theorem exists_lineBundle (h2 : CocycleLineBundleStatement.{u}) (hcov : (⨆ i, T i) = ⊤)
    (hNmBasic : ∀ (U : X.Opens) (f : Γ(Y, π ⁻¹ᵁ U)),
      (X.basicOpen (Nm U f) : Set X) =
        {x : X | x ∈ U ∧ ∀ y : Y, π.base y = x → y ∈ Y.basicOpen f})
    (hTset : ∀ i, (T i : Set X) =
      {x : X | ∀ y : Y, π.base y = x → y ∈ trivializationOpen P (S i)}) :
    ∃ N : LineBundle X, ∀ k : ι, ∃ t : GlobalSections N.obj,
      trivializationOpen N.obj t = T k := by
  obtain ⟨N, hN⟩ := h2 X ι T hcov (cocycle π T S hT Nm) (cocycle_cond π T S hT Nm hNm)
  refine ⟨N, fun k ↦ ?_⟩
  obtain ⟨t, ht⟩ := hN (fun i ↦ Nm (T i) (coeff π T S hT i k))
    (family_compatible π T S hT Nm hNm k)
  refine ⟨t, ?_⟩
  have key : ∀ i, T i ⊓ trivializationOpen N.obj t = T i ⊓ T k := by
    intro i
    rw [ht i]
    apply SetLike.coe_injective
    rw [hNmBasic, basicOpen_coeff, Opens.coe_inf, hTset k]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx, fun y hyx ↦ (hy y hyx).2⟩
    · rintro ⟨hx, hy⟩
      refine ⟨hx, fun y hyx ↦ ⟨?_, hy y hyx⟩⟩
      change π.base y ∈ T i
      rw [hyx]
      exact hx
  ext x
  have hx : x ∈ ⨆ i, T i := hcov ▸ (trivial : x ∈ (⊤ : X.Opens))
  rw [Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  have := congrArg (x ∈ ·) (key i)
  simp only [Opens.mem_inf, eq_iff_iff] at this
  exact ⟨fun h ↦ (this.mp ⟨hi, h⟩).2, fun h ↦ (this.mpr ⟨hi, h⟩).2⟩

end NormDescent

/-- Finitely many sections of positive powers of a line bundle can be replaced by
sections of one common positive power with the same generation opens. -/
theorem exists_common_degree {Y : Scheme.{u}} (M : LineBundle Y) {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i)
    (s : ∀ i, M.powSections (n i)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ S : ι → M.powSections m,
      ∀ i, M.sectionOpen (S i) = M.sectionOpen (s i) := by
  classical
  have hm : 0 < ∏ i, n i := Finset.prod_pos fun i _ ↦ hn i
  have hdvd : ∀ i, n i ∣ ∏ i, n i := fun i ↦ Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  have hk : ∀ i, n i * ((∏ i, n i) / n i) = ∏ i, n i := fun i ↦ Nat.mul_div_cancel' (hdvd i)
  have hkpos : ∀ i, 0 < (∏ i, n i) / n i := fun i ↦
    Nat.div_pos (Nat.le_of_dvd hm (hdvd i)) (hn i)
  refine ⟨∏ i, n i, hm, fun i ↦ (eqToIso (congrArg (tensorPow M.obj) (hk i))).hom.app ⊤
    ((tensorPowMulIso M.obj (n i) ((∏ i, n i) / n i)).hom.app ⊤
      (sectionPow (tensorPow M.obj (n i)) (s i) ((∏ i, n i) / n i))), fun i ↦ ?_⟩
  exact (trivializationOpen_mapIso _ _).trans ((trivializationOpen_mapIso _ _).trans
    (trivializationOpen_sectionPow
      ⟨tensorPow M.obj (n i), tensorPow_isLocallyFreeRankOne Y M (n i)⟩ (s i) (hkpos i)))

/-- The descent, from a surjective closed morphism with finite fibres carrying norm maps
with the stated basic-open property, and the separate statements it relies on. -/
theorem exists_isAmple_of_norm {X Y : Scheme.{u}} (π : Y ⟶ X)
    (hsurj : Function.Surjective π.base) (hclosed : IsClosedMap π.base)
    (hfin : ∀ x : X, (π.base ⁻¹' {x}).Finite)
    (Nm : ∀ U : X.Opens, Γ(Y, π ⁻¹ᵁ U) →* Γ(X, U))
    (hNm : ∀ (U V : X.Opens) (hUV : U ≤ V) (f : Γ(Y, π ⁻¹ᵁ V)),
      X.presheaf.map (homOfLE hUV).op (Nm V f) =
        Nm U (Y.presheaf.map (homOfLE (π.preimage_mono hUV)).op f))
    (hNmBasic : ∀ (U : X.Opens) (f : Γ(Y, π ⁻¹ᵁ U)),
      (X.basicOpen (Nm U f) : Set X) =
        {x : X | x ∈ U ∧ ∀ y : Y, π.base y = x → y ∈ Y.basicOpen f})
    (h2 : CocycleLineBundleStatement.{u}) (h3 : AmpleFiniteSetSectionStatement.{u})
    (M : LineBundle Y) (hM : M.IsAmple) : ∃ N : LineBundle X, N.IsAmple := by
  classical
  -- an affine open neighbourhood of every point
  have hV : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  choose V hVaff hxV using hV
  -- a section of a positive power whose generation open contains the fibre over `x`
  have hs : ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : M.powSections n,
      π.base ⁻¹' {x} ⊆ (M.sectionOpen s : Set Y) ∧ M.sectionOpen s ≤ π ⁻¹ᵁ V x := by
    intro x
    refine h3 Y M hM (π.base ⁻¹' {x}) (π ⁻¹ᵁ V x) (hfin x) fun y hy ↦ ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    change π.base y ∈ V x
    rw [hy]
    exact hxV x
  choose n hn s hEs hsV using hs
  -- the points whose whole fibre lies in that generation open
  let T : X → X.Opens := fun x ↦
    ⟨(π.base '' (M.sectionOpen (s x) : Set Y)ᶜ)ᶜ,
      (hclosed _ (M.sectionOpen (s x)).isOpen.isClosed_compl).isOpen_compl⟩
  have hTset : ∀ x, (T x : Set X) =
      {x' : X | ∀ y : Y, π.base y = x' → y ∈ M.sectionOpen (s x)} := by
    intro x
    ext x'
    simp only [T, Opens.coe_mk, Set.mem_compl_iff, Set.mem_image, Set.mem_ofPred_eq,
      SetLike.mem_coe, not_exists, not_and]
    constructor
    · intro h y hy
      by_contra hn
      exact h y hn hy
    · intro h y hn hy
      exact hn (h y hy)
  have hxT : ∀ x, x ∈ T x := by
    intro x
    change x ∈ (T x : Set X)
    rw [hTset]
    intro y hy
    exact hEs x hy
  have hTV : ∀ x, T x ≤ V x := by
    intro x x' hx'
    obtain ⟨y, rfl⟩ := hsurj x'
    have hx'' : π.base y ∈ (T x : Set X) := hx'
    rw [hTset] at hx''
    exact hsV x (hx'' y rfl)
  -- quasi-compactness of `X` and a finite subcover
  have : CompactSpace Y := hM.1
  have hXc : CompactSpace X := hsurj.compactSpace π.continuous
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (T x : Set X))
    (fun x ↦ (T x).isOpen) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxT x⟩
  have hcover : ∀ x : X, ∃ i : t, x ∈ T i := by
    intro x
    have := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hx⟩ := this
    exact ⟨⟨i, hi⟩, hx⟩
  -- one common positive power
  obtain ⟨m, -, S, hS⟩ := exists_common_degree M (fun i : t ↦ n i)
    (fun i ↦ hn i) fun i ↦ s i
  have hTset' : ∀ i : t, (T i : Set X) =
      {x : X | ∀ y : Y, π.base y = x → y ∈ trivializationOpen (tensorPow M.obj m) (S i)} := by
    intro i
    rw [hTset]
    change _ = {x : X | ∀ y : Y, π.base y = x → y ∈ M.sectionOpen (S i)}
    rw [hS i]
  have hT : ∀ i : t, π ⁻¹ᵁ T i ≤ trivializationOpen (tensorPow M.obj m) (S i) := by
    intro i y hy
    have hy' : π.base y ∈ (T i : Set X) := hy
    rw [hTset'] at hy'
    exact hy' y rfl
  have hcov : (⨆ i : t, T i) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨i, hi⟩ := hcover x
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  -- the descended line bundle
  obtain ⟨N, hN⟩ := NormDescent.exists_lineBundle π (fun i : t ↦ T i) S hT Nm hNm h2 hcov
    hNmBasic hTset'
  refine ⟨N, hXc, fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := hcover x
  obtain ⟨r, hr⟩ := hN i
  have hr1 : N.sectionOpen (sectionPow N.obj r 1) = T i :=
    (trivializationOpen_sectionPow N r one_pos).trans hr
  refine ⟨1, le_rfl, sectionPow N.obj r 1, ?_, ?_⟩
  · rw [hr1]
    exact hi
  · rw [hr1]
    have := affineGenerationLocusIntersection X N r (V i) (hVaff i)
    rwa [hr, inf_eq_right.mpr (hTV i)] at this

/-- The descent of ample line-bundle existence, from the norm, cocycle-gluing and
finite-set-section statements. -/
theorem descent_of_statements (h1 : FiniteFieldExtensionNormStatement.{u})
    (h2 : CocycleLineBundleStatement.{u}) (h3 : AmpleFiniteSetSectionStatement.{u}) :
    FiniteFieldExtensionAmpleExistenceDescentStatement.{u} := by
  intro K L _ _ _ _ X p ⟨M, hM⟩
  obtain ⟨Nm, hNm, -, hNmBasic⟩ := h1 K L X p
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact exists_isAmple_of_norm (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (Scheme.Hom.surjective _) (Scheme.Hom.isClosedMap _)
    (fun x ↦ Scheme.Hom.finite_preimage_singleton _ x) Nm hNm hNmBasic h2 h3 M hM

/-- Descent of ample line-bundle existence along finite field extensions: if the base change
of `X` to a finite extension `L / K` carries an ample line bundle, then so does `X`. -/
theorem finiteFieldExtensionAmpleExistenceDescent :
    FiniteFieldExtensionAmpleExistenceDescentStatement.{u} :=
  descent_of_statements finiteFieldExtensionNorm cocycleLineBundle ampleFiniteSetSection

end Langlands.AlgebraicGeometry.Picard

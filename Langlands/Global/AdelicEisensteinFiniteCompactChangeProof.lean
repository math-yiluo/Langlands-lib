import Langlands.Global.AdelicEisensteinFiniteCompactChangeStatement
import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.FiniteAdelicGroupCompactOpen
import Mathlib.Topology.LocallyConstant.Basic

/-! # Finite changes of the adelic Iwasawa compact -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

section Iwasawa

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K K₂ : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hK₂ : IsIwasawaCompact p K₂)

/-- When the intersection is relatively open in the first compact, the
difference between the heights has finite range on the entire adelic group. -/
theorem IsIwasawaCompact.finite_range_height_sub
    (hopen : IsOpen {k : K | k.val ∈ K₂}) :
    (Set.range fun g => hK.height g - hK₂.height g).Finite := by
  let Δ (g : AdelicGroupPoints F G) := hK.height g - hK₂.height g
  let δ (k : K) := Δ k.val
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have hloc : IsLocallyConstant δ := by
    apply (IsLocallyConstant.iff_exists_open δ).mpr
    intro k
    refine ⟨{x : K | (k⁻¹ * x).val ∈ K₂},
      hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · change (k⁻¹ * k).val ∈ K₂
      rw [inv_mul_cancel]
      exact K₂.one_mem
    · intro x hx
      change (k⁻¹ * x).val ∈ K₂ at hx
      have heq : k.val * (k⁻¹ * x).val = x.val :=
        congrArg Subtype.val (mul_inv_cancel_left k x)
      change hK.height x.val - hK₂.height x.val = hK.height k.val - hK₂.height k.val
      rw [← heq, hK.height_mul_right _ (k⁻¹ * x).property, hK₂.height_mul_right _ hx]
  apply hloc.range_finite.subset
  rintro _ ⟨g, rfl⟩
  obtain ⟨a, k, hk, rfl⟩ := hK.exists_eq g
  refine ⟨⟨k, hk⟩, ?_⟩
  change hK.height k - hK₂.height k =
    hK.height (map F P G p a * k) - hK₂.height (map F P G p a * k)
  rw [hK.height_map_mul, hK₂.height_map_mul]
  abel

open Classical in
/-- A finite change of Iwasawa heights expresses the parameter twist as a
finite sum with height scalars and inducing functions cut along clopen sets. -/
theorem IsIwasawaCompact.exists_parameterTwist_clopen_decomposition
    (hopen : IsOpen {k : K | k.val ∈ K₂}) :
    let Δ := fun g => hK.height g - hK₂.height g
    ∃ S : Finset (RealCharacterDual F P),
      (∀ d, IsClopen {g | Δ g = d}) ∧
      ∀ (φ : AdelicGroupPoints F G → ℂ)
        (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G),
        hK.parameterTwist φ lam g =
          ∑ d ∈ S, Complex.exp (complexParameterPairing F P lam d) *
            hK₂.parameterTwist (fun x => if Δ x = d then φ x else 0) lam g := by
  classical
  let Δ (g : AdelicGroupPoints F G) := hK.height g - hK₂.height g
  have hfinite : (Set.range Δ).Finite := hK.finite_range_height_sub hK₂ hopen
  have hcont : Continuous Δ := hK.continuous_height.sub hK₂.continuous_height
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro d
    have hcomp : {g | Δ g = d} = (Δ ⁻¹' (Set.range Δ \ {d}))ᶜ := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff,
        Set.mem_singleton_iff, Set.mem_range_self, true_and, not_not]
    refine ⟨isClosed_singleton.preimage hcont, ?_⟩
    rw [hcomp]
    exact ((hfinite.subset Set.sdiff_subset).isClosed.preimage hcont).isOpen_compl
  · intro φ lam g
    rw [Finset.sum_eq_single (Δ g)]
    · simp only [IsIwasawaCompact.parameterTwist, IsIwasawaCompact.heightPower]
      have hcut : hK.height g - hK₂.height g = Δ g := rfl
      rw [ite_eq_left hcut]
      have hheight : hK.height g = Δ g + hK₂.height g := (sub_add_cancel _ _).symm
      conv_lhs => rw [hheight, map_add, Complex.exp_add]
      ring
    · intro d _ hd
      have hcut : hK.height g - hK₂.height g ≠ d := Ne.symm hd
      simp [IsIwasawaCompact.parameterTwist, hcut]
    · intro h
      exact (h (hfinite.mem_toFinset.mpr (Set.mem_range_self g))).elim

end Iwasawa

private theorem isOpen_of_maximalCompact_of_compactOpenSubgroup
    {H : Type*} [Group H] [TopologicalSpace H] [T2Space H] [IsTopologicalGroup H]
    (K : Subgroup H) (hK : IsCompact (K : Set H))
    (hmax : ∀ K' : Subgroup H, IsCompact (K' : Set H) → K ≤ K' → K' = K)
    (J : OpenSubgroup H) (hJ : IsCompact (J : Set H)) :
    IsOpen (K : Set H) := by
  let C : Subgroup H := ⨅ k : K, J.toSubgroup.comap (MulAut.conj k.val).toMonoidHom
  have hC (x : H) : x ∈ C ↔ ∀ k : K, k.val * x * k.val⁻¹ ∈ J := by
    simp [C, MulAut.conj_apply]
  have hCJ : (C : Set H) ⊆ J := by
    intro x hx
    simpa using (hC x).mp hx (1 : K)
  have hCclosed : IsClosed (C : Set H) := by
    have heq : (C : Set H) = ⋂ k : K, {x | k.val * x * k.val⁻¹ ∈ J} := by
      ext x
      change x ∈ C ↔ _
      simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using hC x
    rw [heq]
    exact isClosed_iInter fun k =>
      J.isClosed.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hCcompact := hJ.of_isClosed_subset hCclosed hCJ
  have hComm : K ≤ Subgroup.normalizer (C : Set H) := by
    intro k hk
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    simp only [hC]
    constructor
    · intro hx a
      have h := hx (a * ⟨k, hk⟩)
      change (a.val * k) * x * (a.val * k)⁻¹ ∈ J at h
      simpa only [mul_inv_rev, mul_assoc] using h
    · intro hx a
      have h := hx (a * ⟨k⁻¹, K.inv_mem hk⟩)
      change (a.val * k⁻¹) * (k * x * k⁻¹) * (a.val * k⁻¹)⁻¹ ∈ J at h
      rwa [show (a.val * k⁻¹) * (k * x * k⁻¹) * (a.val * k⁻¹)⁻¹ =
        a.val * x * a.val⁻¹ by group] at h
  have hSup : IsCompact ((K ⊔ C : Subgroup H) : Set H) := by
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hComm]
    exact hK.mul hCcompact
  have hCK : C ≤ K := hmax _ hSup le_sup_left ▸ le_sup_right
  let U : Set (H × H) := {p | p.1 * p.2 * p.1⁻¹ ∈ J}
  have hU : IsOpen U :=
    J.isOpen.preimage ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  have hKU : (K : Set H) ×ˢ ({1} : Set H) ⊆ U := by
    rintro ⟨k, x⟩ ⟨_, hx⟩
    have hx' : x = 1 := hx
    change k * x * k⁻¹ ∈ J
    rw [hx', mul_one, mul_inv_cancel]
    exact J.one_mem
  obtain ⟨V, W, _, hW, hKV, h1W, hVW⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hKU
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset (hW.mem_nhds (h1W (Set.mem_singleton 1))) ?_
  intro x hx
  apply hCK
  exact (hC x).mpr fun k => hVW (a := (k.val, x)) ⟨hKV k.property, hx⟩

section MaximalCompact

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)

include hK in
/-- A maximal compact in the full adelic group is the product of its two
coordinate projections. -/
theorem IsMaximalCompactSubgroup.eq_comap_prod :
    K = ((K.map (infinite F G).toMonoidHom).prod (K.map (finite F G).toMonoidHom)).comap
      (split F G).toMonoidHom := by
  let Ki := K.map (infinite F G).toMonoidHom
  let Kf := K.map (finite F G).toMonoidHom
  have hi : IsCompact (Ki : Set (InfiniteAdelicGroupPoints F G)) :=
    hK.1.image (infinite F G).continuous
  have hf : IsCompact (Kf : Set (FiniteAdelicGroupPoints F G)) :=
    hK.1.image (finite F G).continuous
  let A := (Ki.prod Kf).comap (split F G).toMonoidHom
  exact (hK.2 A ((split F G).toHomeomorph.isCompact_preimage.mpr (hi.prod hf))
    (fun _ hx => ⟨⟨_, hx, rfl⟩, ⟨_, hx, rfl⟩⟩)).symm

include hK in
/-- The finite projection of a maximal compact in the full adelic group is
an open subgroup of the finite adelic group. -/
theorem IsMaximalCompactSubgroup.isOpen_finite [LocallyOfFiniteType G.X.hom] :
    IsOpen (K.map (finite F G).toMonoidHom : Set (FiniteAdelicGroupPoints F G)) := by
  let Ki := K.map (infinite F G).toMonoidHom
  let Kf := K.map (finite F G).toMonoidHom
  have hi : IsCompact (Ki : Set (InfiniteAdelicGroupPoints F G)) :=
    hK.1.image (infinite F G).continuous
  have hf : IsCompact (Kf : Set (FiniteAdelicGroupPoints F G)) :=
    hK.1.image (finite F G).continuous
  refine isOpen_of_maximalCompact_of_compactOpenSubgroup Kf hf ?_
    (FiniteAdelicGroupPoints.compactOpenSubgroup F G)
    (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G)
  intro L hL hincl
  let A := (Ki.prod L).comap (split F G).toMonoidHom
  have hAK : A = K := hK.2 A
    ((split F G).toHomeomorph.isCompact_preimage.mpr (hi.prod hL))
    (fun _ hg => ⟨⟨_, hg, rfl⟩, hincl ⟨_, hg, rfl⟩⟩)
  refine le_antisymm (fun y hy => ?_) hincl
  have hg : pair F G 1 y ∈ A := by
    change infinite F G (pair F G 1 y) ∈ Ki ∧ finite F G (pair F G 1 y) ∈ L
    rw [infinite_pair, finite_pair]
    exact ⟨Ki.one_mem, hy⟩
  rw [hAK] at hg
  exact ⟨pair F G 1 y, hg, finite_pair F G _ _⟩

/-- Two maximal adelic compacts with the same infinite projection have an
intersection that is relatively open in the first compact. -/
theorem IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq
    [LocallyOfFiniteType G.X.hom] (K₂ : Subgroup (AdelicGroupPoints F G))
    (hK₂ : IsMaximalCompactSubgroup F G K₂)
    (heq : K.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom) :
    IsOpen {k : K | k.val ∈ K₂} := by
  let proj : K → FiniteAdelicGroupPoints F G := fun k => finite F G k.val
  have hproj : Continuous proj := (finite F G).continuous.comp continuous_subtype_val
  have htest : {k : K | k.val ∈ K₂} = proj ⁻¹'
      (K₂.map (finite F G).toMonoidHom : Set (FiniteAdelicGroupPoints F G)) := by
    ext k
    have hInf : infinite F G k.val ∈ K₂.map (infinite F G).toMonoidHom :=
      heq ▸ (show infinite F G k.val ∈ K.map (infinite F G).toMonoidHom from
        ⟨k.val, k.property, rfl⟩)
    change k.val ∈ K₂ ↔ finite F G k.val ∈ K₂.map (finite F G).toMonoidHom
    conv_lhs => rw [IsMaximalCompactSubgroup.eq_comap_prod F G K₂ hK₂]
    exact and_iff_right hInf
  rw [htest]
  exact (IsMaximalCompactSubgroup.isOpen_finite F G K₂ hK₂).preimage hproj

end MaximalCompact

section InfiniteSlices

open NumberField IsDedekindDomain

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G}

private theorem infinite_map_for_height (q : AdelicGroupPoints F P) :
    infinite F G (map F P G p q) =
      P.affinePointsTarget p (CommAlgCat.of F (InfiniteAdeleRing F)) (infinite F P q) :=
  DFunLike.congr_fun (P.affinePointsTarget_naturality p
    (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) q

private theorem finite_map_for_height (q : AdelicGroupPoints F P) :
    finite F G (map F P G p q) =
      P.affinePointsTarget p (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)) (finite F P q) :=
  DFunLike.congr_fun (P.affinePointsTarget_naturality p
    (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) q

variable [IsClosedImmersion p.hom.hom.left]

/-- A change between compacts with the same infinite projection changes the
Iwasawa height by a function of the finite coordinate. -/
theorem IsIwasawaCompact.height_sub_pair_eq_of_infinite_eq
    {K K₂ : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) (hK₂ : IsIwasawaCompact p K₂)
    (hmax : IsMaximalCompactSubgroup F G K) (hmax₂ : IsMaximalCompactSubgroup F G K₂)
    (heq : K.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom)
    (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    hK.height (pair F G a b) - hK₂.height (pair F G a b) =
      hK.height (ofFinite F G b) - hK₂.height (ofFinite F G b) := by
  obtain ⟨q, k, hk, hfact⟩ := hK.exists_eq (ofInfinite F G a)
  let qInf := ofInfinite F P (infinite F P q)
  let kInf := ofInfinite F G (infinite F G k)
  have hinf : infinite F G k ∈ K.map (infinite F G).toMonoidHom := ⟨k, hk, rfl⟩
  have hkInf : kInf ∈ K := by
    rw [IsMaximalCompactSubgroup.eq_comap_prod F G K hmax]
    change infinite F G kInf ∈ K.map (infinite F G).toMonoidHom ∧
      finite F G kInf ∈ K.map (finite F G).toMonoidHom
    dsimp only [kInf]
    rw [infinite_ofInfinite, finite_ofInfinite]
    exact ⟨hinf, one_mem _⟩
  have hkInf₂ : kInf ∈ K₂ := by
    rw [IsMaximalCompactSubgroup.eq_comap_prod F G K₂ hmax₂]
    change infinite F G kInf ∈ K₂.map (infinite F G).toMonoidHom ∧
      finite F G kInf ∈ K₂.map (finite F G).toMonoidHom
    dsimp only [kInf]
    rw [infinite_ofInfinite, finite_ofInfinite, ← heq]
    exact ⟨hinf, one_mem _⟩
  have hArch :
      P.affinePointsTarget p (CommAlgCat.of F (InfiniteAdeleRing F)) (infinite F P q) *
        infinite F G k = a := by
    simpa only [map_mul, infinite_map_for_height, infinite_ofInfinite] using
      congrArg (infinite F G) hfact
  have hfact' : map F P G p qInf * (ofFinite F G b * kInf) = pair F G a b := by
    apply (split F G).injective
    apply Prod.ext
    · change infinite F G (map F P G p qInf * (ofFinite F G b * kInf)) =
        infinite F G (pair F G a b)
      rw [infinite_pair]
      simpa only [map_mul, infinite_ofFinite,
        infinite_map_for_height, qInf, kInf, infinite_ofInfinite, one_mul] using hArch
    · change finite F G (map F P G p qInf * (ofFinite F G b * kInf)) =
        finite F G (pair F G a b)
      rw [finite_pair]
      simp only [map_mul, finite_ofFinite, finite_map_for_height,
        qInf, kInf, finite_ofInfinite, map_one, mul_one, one_mul]
  rw [← hfact', hK.height_map_mul, hK₂.height_map_mul, hK.height_mul_right _ hkInf,
    hK₂.height_mul_right _ hkInf₂]
  abel

end InfiniteSlices

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

private def finiteIndicator (S : Set (FiniteAdelicGroupPoints F G)) :
    (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) where
  toFun f := ((finite F G) ⁻¹' S).indicator f
  map_add' f h := by
    funext x
    by_cases hx : finite F G x ∈ S <;> simp [Set.indicator, hx]
  map_smul' z f := by
    funext x
    by_cases hx : finite F G x ∈ S <;> simp [Set.indicator, hx]

/-- Cutting along a clopen set of finite adelic coordinates preserves
automorphy when the set respects left invariance and a common open level. -/
theorem IsAutomorphicFunctionOn.indicator_finite
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
    {Γ : Subgroup (AdelicGroupPoints F G)} {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {φ : AdelicGroupPoints F G → ℂ} (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ)
    (S : Set (FiniteAdelicGroupPoints F G)) (hS : IsClopen S)
    (hLeft : ∀ x ∈ Γ, ∀ g : AdelicGroupPoints F G, finite F G (x * g) ∈ S ↔ finite F G g ∈ S)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (hRight : ∀ k ∈ L, ∀ b : FiniteAdelicGroupPoints F G, b * k ∈ S ↔ b ∈ S) :
    IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho (((finite F G) ⁻¹' S).indicator φ) := by
  classical
  let cut := finiteIndicator S
  change IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho (cut φ)
  obtain ⟨hInv, hSmooth, hFinite, hCenter, hGrowth⟩ := hφ
  have hSlice (b : FiniteAdelicGroupPoints F G) :
      functionInfiniteSlice F G (cut φ) b =
        if b ∈ S then functionInfiniteSlice F G φ b else 0 := by
    funext a
    by_cases hb : b ∈ S <;> simp [functionInfiniteSlice, cut, finiteIndicator, Set.indicator, hb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx g
    have hχ := hLeft x hx g
    rw [map_mul] at hχ
    by_cases hg : finite F G g ∈ S <;>
      simp [cut, finiteIndicator, Set.indicator, hχ, hg, hInv x hx g]
  · obtain ⟨L₀, hL₀, hFixed⟩ := hSmooth.2.2
    refine ⟨(hS.preimage (finite F G).continuous).continuous_indicator hSmooth.1,
      ?_, L₀ ⊓ L.toSubgroup, hL₀.inter L.isOpen, ?_⟩
    · intro b
      rw [hSlice]
      split
      · exact hSmooth.2.1 b
      · exact (InfinitePlotSmoothFunctions F G).zero_mem
    · intro k hk g
      change k ∈ L₀ ⊓ L.toSubgroup at hk
      have hφLevel := hFixed k hk.1 g
      rw [ofFinite_eq_pair] at hφLevel
      by_cases hg : finite F G g ∈ S <;>
        simp [cut, finiteIndicator, Set.indicator, map_mul, hRight k hk.2, hg, hφLevel]
  · let orbitSpan (f : AdelicGroupPoints F G → ℂ) :=
      Submodule.span ℂ (Set.range fun k : Kinf =>
        fun g : AdelicGroupPoints F G => f (g * ofInfinite F G k.val))
    let : FiniteDimensional ℂ (orbitSpan φ) := hFinite
    change FiniteDimensional ℂ (orbitSpan (cut φ))
    apply Submodule.finiteDimensional_of_le (S₂ := (orbitSpan φ).map cut)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    funext g
    simp [cut, finiteIndicator, Set.indicator, map_mul]
  · obtain ⟨I, hI, hAnn⟩ := hCenter
    refine ⟨I, hI, fun z hz b h => ?_⟩
    by_cases hb : b ∈ S
    · have heq :
          (⟨functionInfiniteSlice F G (cut φ) b, h⟩ : InfinitePlotSmoothFunctions F G) =
            ⟨functionInfiniteSlice F G φ b, hSmooth.2.1 b⟩ :=
        Subtype.ext (by simp [hSlice, hb])
      rw [heq]
      exact hAnn z hz b (hSmooth.2.1 b)
    · have heq : (⟨functionInfiniteSlice F G (cut φ) b, h⟩ : InfinitePlotSmoothFunctions F G) = 0 :=
        Subtype.ext (by simp [hSlice, hb])
      rw [heq, map_zero]
  · obtain ⟨C, hC, R, hR⟩ := hGrowth
    refine ⟨C, hC, R, fun g => ?_⟩
    by_cases hg : finite F G g ∈ S
    · simpa [cut, finiteIndicator, Set.indicator, hg] using hR g
    · simp only [cut, finiteIndicator, LinearMap.coe_mk, AddHom.coe_mk,
        Set.indicator, Set.mem_preimage, ite_eq_right hg, norm_zero]
      exact (norm_nonneg _).trans (hR g)

open Classical in
/-- The finite change of heights between compacts with a common infinite
projection uses a fixed finite family of automorphic inducing functions. -/
theorem IsAutomorphicFunctionOn.exists_parameterTwist_of_infinite_eq
    [LocallyOfFiniteType G.X.hom]
    {P M U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    {K K₂ : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) (hK₂ : IsIwasawaCompact p K₂)
    (hmax : IsMaximalCompactSubgroup F G K) (hmax₂ : IsMaximalCompactSubgroup F G K₂)
    (heq : K.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom)
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l) Kinf rho φ) :
    ∃ (S : Finset (RealCharacterDual F P))
      (cut : RealCharacterDual F P → AdelicGroupPoints F G → ℂ),
      (∀ v ∈ S, IsAutomorphicFunctionOn F G hsmooth hcalc
        (parabolicQuotientSubgroup F p iU l) Kinf rho (cut v)) ∧
      ∀ (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G),
        hK.parameterTwist φ lam g =
          ∑ v ∈ S, Complex.exp (complexParameterPairing F P lam v) * hK₂.parameterTwist (cut v) lam g := by
  classical
  let Δ (g : AdelicGroupPoints F G) := hK.height g - hK₂.height g
  let δ (b : FiniteAdelicGroupPoints F G) := Δ (ofFinite F G b)
  let L : OpenSubgroup (FiniteAdelicGroupPoints F G) :=
    ⟨K.map (finite F G).toMonoidHom ⊓ K₂.map (finite F G).toMonoidHom,
      (IsMaximalCompactSubgroup.isOpen_finite F G K hmax).inter
        (IsMaximalCompactSubgroup.isOpen_finite F G K₂ hmax₂)⟩
  have hOpen := IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq F G K K₂ hmax₂ heq
  obtain ⟨S, hFiber, hTwist⟩ := hK.exists_parameterTwist_clopen_decomposition hK₂ hOpen
  have hΔ (g : AdelicGroupPoints F G) : Δ g = δ (finite F G g) := by
    simpa only [pair_projections] using hK.height_sub_pair_eq_of_infinite_eq hK₂ hmax hmax₂ heq
      (infinite F G g) (finite F G g)
  have hParabolic : parabolicQuotientSubgroup F p iU l ≤
      (AdelicGroupPoints.map F P G p).toMonoidHom.range := by
    apply sup_le
    · rintro _ ⟨x, rfl⟩
      exact ⟨AdelicGroupPoints.map F U P iU x, (map_comp_apply_of_hom iU x).symm⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨AdelicGroupPoints.map F M P l (rational F M x),
        (map_comp_apply_of_hom l (rational F M x)).symm⟩
  have ofFinite_mem {C : Subgroup (AdelicGroupPoints F G)}
      (hC : IsMaximalCompactSubgroup F G C) {k : FiniteAdelicGroupPoints F G}
      (hk : k ∈ C.map (finite F G).toMonoidHom) : ofFinite F G k ∈ C := by
    rw [IsMaximalCompactSubgroup.eq_comap_prod F G C hC]
    change infinite F G (ofFinite F G k) ∈ C.map (infinite F G).toMonoidHom ∧
      finite F G (ofFinite F G k) ∈ C.map (finite F G).toMonoidHom
    rw [infinite_ofFinite, finite_ofFinite]
    exact ⟨one_mem _, hk⟩
  refine ⟨S, fun v g => if Δ g = v then φ g else 0, ?_, hTwist φ⟩
  intro v _
  let T : Set (FiniteAdelicGroupPoints F G) := {b | δ b = v}
  have hT : IsClopen T := (hFiber v).preimage (ofFinite F G).continuous
  have hLeft (x : AdelicGroupPoints F G) (hx : x ∈ parabolicQuotientSubgroup F p iU l)
      (g : AdelicGroupPoints F G) : finite F G (x * g) ∈ T ↔ finite F G g ∈ T := by
    obtain ⟨q, rfl⟩ := hParabolic hx
    change δ (finite F G (AdelicGroupPoints.map F P G p q * g)) = v ↔ δ (finite F G g) = v
    rw [← hΔ, ← hΔ]
    have hh : Δ (AdelicGroupPoints.map F P G p q * g) = Δ g := by
      dsimp only [Δ]
      rw [hK.height_map_mul, hK₂.height_map_mul]
      abel
    rw [hh]
  have hRight (k : FiniteAdelicGroupPoints F G) (hk : k ∈ L)
      (b : FiniteAdelicGroupPoints F G) : b * k ∈ T ↔ b ∈ T := by
    have hk₁ := ofFinite_mem hmax (show k ∈ K.map (finite F G).toMonoidHom from hk.1)
    have hk₂ := ofFinite_mem hmax₂ (show k ∈ K₂.map (finite F G).toMonoidHom from hk.2)
    change Δ (ofFinite F G (b * k)) = v ↔ Δ (ofFinite F G b) = v
    rw [map_mul]
    dsimp only [Δ]
    rw [hK.height_mul_right _ hk₁, hK₂.height_mul_right _ hk₂]
  convert hφ.indicator_finite T hT hLeft L hRight using 1
  funext g
  simp only [Set.indicator, Set.mem_preimage, T, Set.mem_ofPred_eq, ← hΔ g]

end Langlands.Automorphic.GroupSchemeFunctions


namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The automorphic cutoffs implement the finite change of Iwasawa height. -/
theorem eisensteinFiniteCompactChange : EisensteinFiniteCompactChangeStatement.{u} := by
  intro F _ _ G P M U _ _ _ p _ iU l K K₂ hK hK₂ hmax hmax₂ heq N d rho hsmooth hcalc Kinf φ hφ
  exact hφ.exists_parameterTwist_of_infinite_eq iU l hK hK₂ hmax hmax₂ heq

end Langlands.Global

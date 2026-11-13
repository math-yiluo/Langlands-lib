import Langlands.Sheaf.Renard.ClosedRestrictionExactStatements
import Langlands.Sheaf.Renard.CompactSectionStalksProof
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite

namespace Langlands.Sheaf.Renard.ClosedRestriction

open VectorSheafScalars

variable {X : Type} [TopologicalSpace X] (F : VectorSheaf X)

/-- The open restriction detects precisely the same zero germs as the original sheaf. -/
theorem open_germ_eq_zero_iff (U : Opens (TopCat.of X))
    (s : (U.isOpenEmbedding.functor.op ⋙ F.presheaf).obj (op ⊤)) (y : U) :
    TopCat.Presheaf.Γgerm (U.isOpenEmbedding.functor.op ⋙ F.presheaf) y s = 0 ↔
      F.presheaf.germ (U.isOpenEmbedding.functor.obj ⊤) y.1
        ⟨y, trivial, rfl⟩ s = 0 := by
  let R : (TopCat.of U).Presheaf (ModuleCat ℂ) := U.isOpenEmbedding.functor.op ⋙ F.presheaf
  constructor
  · intro h
    obtain ⟨W, hyW, i, j, hW⟩ := R.germ_eq y (U := ⊤) (V := ⊤)
      trivial trivial s 0 (by simpa [TopCat.Presheaf.Γgerm] using h)
    have hW0 : R.map i.op s = 0 := by simpa using hW
    rw [← F.presheaf.germ_res_apply (U.isOpenEmbedding.functor.map i)
      y.1 (show y.1 ∈ U.isOpenEmbedding.functor.obj W from ⟨y, hyW, rfl⟩) s]
    change F.presheaf.germ _ _ _ (R.map i.op s) = 0
    rw [hW0, map_zero]
  · intro h
    obtain ⟨W, hyW, i, j, hW⟩ := F.presheaf.germ_eq y.1
      (U := U.isOpenEmbedding.functor.obj ⊤) (V := U.isOpenEmbedding.functor.obj ⊤)
      ⟨y, trivial, rfl⟩ ⟨y, trivial, rfl⟩ s 0 (by simpa using h)
    have hW0 : F.presheaf.map i.op s = 0 := by simpa using hW
    let W' : Opens (TopCat.of U) := (Opens.map U.inclusion').obj W
    have hyW' : y ∈ W' := hyW
    let a : U.isOpenEmbedding.functor.obj W' ⟶ W :=
      homOfLE (by rintro x ⟨z, hz, rfl⟩; exact hz)
    let b : W' ⟶ ⊤ := homOfLE le_top
    have hb : U.isOpenEmbedding.functor.map b = a ≫ i := Subsingleton.elim _ _
    have hz : R.map b.op s = 0 := by
      change F.presheaf.map (U.isOpenEmbedding.functor.map b).op s = 0
      rw [hb]
      change F.presheaf.map (i.op ≫ a.op) s = 0
      rw [F.presheaf.map_comp]
      change F.presheaf.map a.op (F.presheaf.map i.op s) = 0
      rw [hW0, map_zero]
    change R.germ ⊤ y trivial s = 0
    simpa only [map_zero] using
      (R.germ_ext (U := ⊤) (V := ⊤) (x := y) (hxU := trivial) (hxV := trivial)
        W' hyW' b b (sV := 0) (by simpa only [map_zero] using hz))

/-- Support in the open restriction is the family of original nonzero germs. -/
theorem open_support_eq (U : Opens (TopCat.of X))
    (s : (U.isOpenEmbedding.functor.op ⋙ F.presheaf).obj (op ⊤)) :
    CompactSupport.support (U.isOpenEmbedding.functor.op ⋙ F.presheaf) s =
      {y : U | F.presheaf.germ (U.isOpenEmbedding.functor.obj ⊤) y.1
        ⟨y, trivial, rfl⟩ s ≠ 0} := by
  ext y
  exact not_congr (open_germ_eq_zero_iff F U s y)

/-- On its defining clopen, the compact extension has the original germs. -/
theorem germ_compactExtension (W : Opens (TopCat.of X))
    (hc : IsCompact (W : Set X)) (hcl : IsClosed (W : Set X))
    (s : F.presheaf.obj (op W)) (x : X) (hx : x ∈ W) :
    F.presheaf.Γgerm x (CompactGerms.compactExtension F W hcl hc s).1 =
      F.presheaf.germ W x hx s := by
  change F.presheaf.Γgerm x (CompactGerms.extend F W hcl s) = _
  rw [← F.presheaf.Γgerm_res_apply x hx _ (i := homOfLE (show W ≤ ⊤ from le_top)),
    CompactGerms.restrict_extend]

/-- A global section has zero germs off the support of its clopen extension. -/
theorem germ_compactExtension_of_notMem (W : Opens (TopCat.of X))
    (hc : IsCompact (W : Set X)) (hcl : IsClosed (W : Set X))
    (s : F.presheaf.obj (op W)) (x : X) (hx : x ∉ W) :
    F.presheaf.Γgerm x (CompactGerms.compactExtension F W hcl hc s).1 = 0 := by
  by_contra h
  exact hx (CompactGerms.support_extend_subset F W hcl s h)

/-- Zero extensions are determined by their restriction and their germs outside the open. -/
theorem zeroExtension_unique (U : Opens (TopCat.of X))
    {s : (U.isOpenEmbedding.functor.op ⋙ F.presheaf).obj (op ⊤)}
    {φ ψ : F.presheaf.obj (op ⊤)}
    (hφ : IsZeroExtension F U s φ) (hψ : IsZeroExtension F U s ψ) : ψ = φ := by
  apply ext_germ F
  intro x _
  change F.presheaf.Γgerm x ψ = F.presheaf.Γgerm x φ
  by_cases hx : x ∈ U
  · have hx' : x ∈ U.isOpenEmbedding.functor.obj ⊤ := ⟨⟨x, hx⟩, trivial, rfl⟩
    rw [← F.presheaf.Γgerm_res_apply x hx' ψ
      (i := homOfLE (show U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤ from le_top)),
      ← F.presheaf.Γgerm_res_apply x hx' φ
      (i := homOfLE (show U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤ from le_top)), hφ.1, hψ.1]
  · rw [hφ.2 x hx, hψ.2 x hx]

/-- Compact support in an open admits an actual compact extension by zero. -/
theorem exists_zeroExtension (hX : Langlands.Topology.IsLocallyProfinite X)
    (U : Opens (TopCat.of X))
    (s : (U.isOpenEmbedding.functor.op ⋙ F.presheaf).obj (op ⊤))
    (hs : s ∈ openCompactSections F U) :
    ∃ φ ∈ CompactSupport.submodule F.presheaf,
      IsZeroExtension F U s φ ∧ ∀ ψ, IsZeroExtension F U s ψ → ψ = φ := by
  classical
  let : T2Space X := hX.t2Space
  let K := Subtype.val '' CompactSupport.support
    (U.isOpenEmbedding.functor.op ⋙ F.presheaf) s
  have hK : IsCompact K := hs.image continuous_subtype_val
  have hKU : K ⊆ (U : Set X) := by rintro _ ⟨y, _, rfl⟩; exact y.2
  obtain ⟨V, hVo, hVc, hKV, hVU⟩ :=
    CompactSectionStalks.exists_isCompact_isOpen_between hX.2 hK U.isOpen hKU
  let W : Opens (TopCat.of X) := ⟨V, hVo⟩
  have hWA : W ≤ U.isOpenEmbedding.functor.obj ⊤ := by
    rw [Opens.isOpenEmbedding_obj_top]
    exact hVU
  let t := F.presheaf.map (homOfLE hWA).op s
  let φ := CompactGerms.compactExtension F W hVc.isClosed hVc t
  have he : IsZeroExtension F U s φ.1 := by
    constructor
    · apply ext_germ F
      intro x hx
      rw [F.presheaf.germ_res_apply]
      change F.presheaf.Γgerm x φ.1 = _
      by_cases hxW : x ∈ W
      · rw [germ_compactExtension F W hVc hVc.isClosed t x hxW]
        exact F.presheaf.germ_res_apply (homOfLE hWA) x hxW s
      · rw [germ_compactExtension_of_notMem F W hVc hVc.isClosed t x hxW]
        symm
        have hxU : x ∈ U := by simpa using hx
        apply (open_germ_eq_zero_iff F U s ⟨x, hxU⟩).mp
        by_contra hn
        apply hxW
        apply hKV
        exact ⟨⟨x, hxU⟩, hn, rfl⟩
    · intro x hx
      exact germ_compactExtension_of_notMem F W hVc hVc.isClosed t x
        (fun hxW => hx (hVU hxW))
  exact ⟨φ.1, φ.2, he, fun ψ hψ => zeroExtension_unique F U he hψ⟩

/-- Restricting a global section has the preimage of its original support. -/
theorem open_support_restrict (U : Opens (TopCat.of X))
    (φ : F.presheaf.obj (op ⊤)) :
    CompactSupport.support (U.isOpenEmbedding.functor.op ⋙ F.presheaf)
      (F.presheaf.map (homOfLE (show U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤ from le_top)).op φ) =
      Subtype.val ⁻¹' CompactSupport.support F.presheaf φ := by
  rw [open_support_eq]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, CompactSupport.support]
  rw [F.presheaf.germ_res_apply]
  rfl

/-- The kernel of restriction consists of compact zero extensions. -/
theorem kernel_zeroExtension (U : Opens (TopCat.of X))
    (φ : CompactSupport.submodule F.presheaf)
    (hφ : restrictToClosed F ((U : Set X)ᶜ) U.isOpen.isClosed_compl φ = 0) :
    ∃ s ∈ openCompactSections F U, IsZeroExtension F U s φ.1 := by
  have hzero : ∀ x : X, x ∉ U → F.presheaf.Γgerm x φ.1 = 0 := by
    intro x hx
    exact congrArg (fun t => t.1 ⟨x, hx⟩) hφ
  have hsub : CompactSupport.support F.presheaf φ.1 ⊆ (U : Set X) := by
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  let s := F.presheaf.map
    (homOfLE (show U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤ from le_top)).op φ.1
  refine ⟨s, ?_, rfl, hzero⟩
  change IsCompact (CompactSupport.support (U.isOpenEmbedding.functor.op ⋙ F.presheaf) s)
  rw [open_support_restrict]
  exact Topology.IsInducing.subtypeVal.isCompact_preimage' φ.2
    (by simpa only [Subtype.range_coe] using hsub)

/-- A compact locally representable family on a closed set extends to a compact section. -/
theorem restrictToClosed_surjective (hX : Langlands.Topology.IsLocallyProfinite X)
    (Z : Set X) (hZ : IsClosed Z) : Function.Surjective (restrictToClosed F Z hZ) := by
  classical
  let : T2Space X := hX.t2Space
  intro t
  choose V hzV σ hσ using t.2.1
  let K : Set X := Subtype.val '' {z : Z | t.1 z ≠ 0}
  have hK : IsCompact K := t.2.2.image continuous_subtype_val
  have hcover : K ⊆ ⋃ z, (V z : Set X) := by
    rintro x ⟨z, _, rfl⟩
    exact Set.mem_iUnion.mpr ⟨z, hzV z⟩
  obtain ⟨n, W, hW, hdisj, hKW, hWV⟩ :=
    Langlands.Topology.LocallyProfiniteProof.finiteDisjointRefinement
      X hX K hK Z (fun z => (V z : Set X)) (fun z => (V z).isOpen) hcover
  choose i hi using hWV
  let O : Fin n → Opens (TopCat.of X) := fun j => ⟨W j, (hW j).1⟩
  let τ := fun j => F.presheaf.map (homOfLE (show O j ≤ V (i j) from hi j)).op (σ (i j))
  let e := fun j => CompactGerms.compactExtension F (O j)
    (hW j).2.isClosed (hW j).2 (τ j)
  let φ : CompactSupport.submodule F.presheaf := ∑ j, e j
  refine ⟨φ, ?_⟩
  apply Subtype.ext
  funext z
  change F.presheaf.Γgerm (z : X) φ.1 = t.1 z
  have hsum : F.presheaf.Γgerm (z : X) φ.1 =
      ∑ j, F.presheaf.Γgerm (z : X) (e j).1 := by simp [φ]
  rw [hsum]
  by_cases hz : ∃ j, (z : X) ∈ W j
  · obtain ⟨j, hzj⟩ := hz
    rw [Finset.sum_eq_single j]
    · rw [germ_compactExtension F (O j) (hW j).2 (hW j).2.isClosed (τ j) z hzj]
      rw [F.presheaf.germ_res_apply]
      exact hσ (i j) z (hi j hzj)
    · intro k _ hkj
      exact germ_compactExtension_of_notMem F (O k) (hW k).2 (hW k).2.isClosed
        (τ k) z (fun hzk => Set.disjoint_left.mp (hdisj hkj) hzk hzj)
    · simp
  · have ht0 : t.1 z = 0 := by
      by_contra ht
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hKW ⟨z, ht, rfl⟩)
      exact hz ⟨j, hj⟩
    rw [ht0]
    apply Finset.sum_eq_zero
    intro j _
    exact germ_compactExtension_of_notMem F (O j) (hW j).2 (hW j).2.isClosed
      (τ j) z (fun hj => hz ⟨j, hj⟩)

/-- A choice of the unique compact extension by zero. -/
def compactZeroExtension (hX : Langlands.Topology.IsLocallyProfinite X)
    (U : Opens (TopCat.of X)) (s : openCompactSections F U) :
    CompactSupport.submodule F.presheaf :=
  ⟨(exists_zeroExtension F hX U s.1 s.2).choose,
    (exists_zeroExtension F hX U s.1 s.2).choose_spec.1⟩

/-- The chosen compact extension satisfies the defining germ and restriction conditions. -/
theorem compactZeroExtension_spec (hX : Langlands.Topology.IsLocallyProfinite X)
    (U : Opens (TopCat.of X)) (s : openCompactSections F U) :
    IsZeroExtension F U s.1 (compactZeroExtension F hX U s).1 :=
  (exists_zeroExtension F hX U s.1 s.2).choose_spec.2.1

/-- Extension by zero is a linear map, by uniqueness of zero extensions. -/
def zeroExtensionLinear (hX : Langlands.Topology.IsLocallyProfinite X)
    (U : Opens (TopCat.of X)) :
    openCompactSections F U →ₗ[ℂ] CompactSupport.submodule F.presheaf where
  toFun := compactZeroExtension F hX U
  map_add' s t := by
    apply Subtype.ext
    apply zeroExtension_unique F U _ (compactZeroExtension_spec F hX U (s + t))
    constructor
    · change F.presheaf.map _ ((compactZeroExtension F hX U s).1 +
        (compactZeroExtension F hX U t).1) = s.1 + t.1
      rw [map_add]
      exact congrArg₂ (· + ·) (compactZeroExtension_spec F hX U s).1
        (compactZeroExtension_spec F hX U t).1
    · intro x hx
      change F.presheaf.Γgerm x ((compactZeroExtension F hX U s).1 +
        (compactZeroExtension F hX U t).1) = 0
      rw [map_add, (compactZeroExtension_spec F hX U s).2 x hx,
        (compactZeroExtension_spec F hX U t).2 x hx, add_zero]
  map_smul' c s := by
    apply Subtype.ext
    apply zeroExtension_unique F U _ (compactZeroExtension_spec F hX U (c • s))
    constructor
    · change F.presheaf.map _ (c • (compactZeroExtension F hX U s).1) = c • s.1
      rw [map_smul]
      exact congrArg (c • ·) (compactZeroExtension_spec F hX U s).1
    · intro x hx
      change F.presheaf.Γgerm x (c • (compactZeroExtension F hX U s).1) = 0
      rw [map_smul, (compactZeroExtension_spec F hX U s).2 x hx, smul_zero]

/-- Restriction back to the open makes extension by zero injective. -/
theorem zeroExtensionLinear_injective (hX : Langlands.Topology.IsLocallyProfinite X)
    (U : Opens (TopCat.of X)) : Function.Injective (zeroExtensionLinear F hX U) := by
  intro s t h
  apply Subtype.ext
  have he := congrArg (fun φ : CompactSupport.submodule F.presheaf =>
    F.presheaf.map (homOfLE (show U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤ from le_top)).op φ.1) h
  exact (compactZeroExtension_spec F hX U s).1.symm.trans
    (he.trans (compactZeroExtension_spec F hX U t).1)

/-- Renard II.2.5: exactness of compact sections and of their algebraic duals. -/
theorem closedRestrictionExact : ClosedRestrictionExactStatement := by
  intro X _ hX F U
  let pZ := restrictToClosed F ((U : Set X)ᶜ) U.isOpen.isClosed_compl
  have hp : Function.Surjective pZ :=
    restrictToClosed_surjective F hX _ U.isOpen.isClosed_compl
  refine ⟨exists_zeroExtension F hX U, kernel_zeroExtension F U, hp,
    LinearMap.dualMap_injective_of_surjective hp, ?_, ?_⟩
  · intro l hl
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective pZ hp]
    apply (Submodule.mem_dualAnnihilator l).mpr
    intro φ hφ
    obtain ⟨s, hs, he⟩ := kernel_zeroExtension F U φ hφ
    exact hl ⟨s, hs⟩ φ he
  · intro m
    obtain ⟨l, hl⟩ := LinearMap.dualMap_surjective_of_injective
      (zeroExtensionLinear_injective F hX U) m
    refine ⟨l, fun s φ hφ => ?_⟩
    have he : φ = zeroExtensionLinear F hX U s := by
      apply Subtype.ext
      exact zeroExtension_unique F U (compactZeroExtension_spec F hX U s) hφ
    rw [he]
    exact congrArg (fun f : Module.Dual ℂ (openCompactSections F U) => f s) hl

end Langlands.Sheaf.Renard.ClosedRestriction
